//! `evict`: letting go of bytes another copy holds.
//!
//! The proposal *Bytes held elsewhere*. A store that holds a payload another
//! copy also offers may let go of its own, and become a store that names bytes
//! it does not hold — the state a fetch that left them behind produces, and
//! the one `record`, `update` and `status` read as *held elsewhere*.
//!
//! This is not [`forget`](super::forget). Forgetting destroys bytes for every
//! copy, and writes the document that says so, which travels. Evicting writes
//! nothing that travels: no other copy learns that this one let go, and this
//! one can fetch the bytes again whenever it likes.
//!
//! # What it refuses
//!
//! - **A payload the copy does not offer.** Letting go of it would leave it
//!   nowhere anybody has said they hold it. The copy's listing is the
//!   publisher's word, not proof (decision 0049): the only proof is to fetch
//!   and hash the whole file, which is what evicting exists to avoid. So the
//!   listing is believed, and this is said rather than assumed.
//! - **A payload a revision here names as a file's lines.** A file of lines is
//!   replayed onto the payload that created it, so without that payload the
//!   file could not be read, diffed or edited at any revision.
//!
//! A payload this store no longer holds is not refused: an eviction that was
//! interrupted let go of the store's copy and not the folder's, and running
//! it again finishes it. One something here forgets is passed over, since
//! there is nothing to let go of and no copy should be remembered for it.
//!
//! # The folder
//!
//! The folder's copy of each file holding exactly those bytes goes too, since
//! freeing the space is the point. That is [`crate::update::plan_eviction`],
//! applied after [`Store::evict`]: an interruption between the two leaves the
//! folder holding bytes the head names, which `record` reads as unchanged,
//! where the other order would leave a folder missing a file the store holds
//! — which `record` reads as a deletion.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use crate::core::RevisionId;
use crate::fs::Filesystem;

use super::prune::remove_empty_directories;
use super::{FetchError, Fetched, OPERATIONS_DIR, OfferKind, Offered, Source, Store, StoreError};

/// What letting go of some payloads would do, worked out before anything is
/// removed.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct Eviction {
    /// Each payload, with where the copy offers it.
    pub offered: Vec<Offered>,
    /// The paged manifest's base, whose memory learns where these are.
    base: Option<RevisionId>,
}

impl Eviction {
    /// The payloads this would let go of.
    pub fn payloads(&self) -> impl Iterator<Item = &RevisionId> {
        self.offered.iter().map(|entry| &entry.digest)
    }
}

impl<F: Filesystem> Store<F> {
    /// Whether these payloads may be let go of, and where the copy at
    /// `manifest` offers each.
    ///
    /// Reads the whole listing, every page, since a payload is offered or not
    /// by the copy as it stands and not by the pages this store last read.
    pub fn eviction_plan<S: Source + ?Sized>(
        &self,
        source: &S,
        manifest: &str,
        wanted: &[RevisionId],
    ) -> Result<Eviction, EvictError> {
        let (text, _) = self.named_payloads()?;
        let mut asked: BTreeSet<RevisionId> = BTreeSet::new();
        for payload in wanted {
            if text.contains(payload) {
                return Err(EvictError::Text { payload: *payload });
            }
            if self.forgotten_payload(payload)?.is_some() || !self.forgetting(payload)?.is_empty() {
                continue;
            }
            asked.insert(*payload);
        }
        if asked.is_empty() {
            return Ok(Eviction {
                offered: Vec::new(),
                base: None,
            });
        }

        let mut fetched = Fetched::default();
        let (whole, base) = self.whole_listing(source, manifest, &mut fetched)?;
        let offers: BTreeMap<RevisionId, &Offered> = whole
            .of(OfferKind::Payload)
            .map(|entry| (entry.digest, entry))
            .collect();
        let mut offered = Vec::new();
        for payload in asked {
            let Some(entry) = offers.get(&payload) else {
                return Err(EvictError::NotOffered { payload });
            };
            offered.push((*entry).clone());
        }
        Ok(Eviction { offered, base })
    }

    /// Let go of what a plan names, and return the payloads removed.
    ///
    /// Each is found by hashing it before it is removed, as every payload
    /// read is, so a catalogue wrong about where a digest sits cannot make
    /// this remove some other file. One already gone is passed over.
    pub fn evict(&mut self, plan: &Eviction) -> Result<Vec<RevisionId>, EvictError> {
        // Remembered before anything goes, so that a fetch reading only the
        // pages after this store's last one still knows where to take them
        // from again, however far this gets. A payload remembered and still
        // held is one a fetch passes over.
        if let Some(base) = &plan.base {
            self.rewrite_left(base, |left| {
                let held: BTreeSet<RevisionId> = left.iter().map(|entry| entry.digest).collect();
                left.extend(
                    plan.offered
                        .iter()
                        .filter(|entry| !held.contains(&entry.digest))
                        .cloned(),
                );
            });
        }
        let mut evicted = Vec::new();
        for entry in &plan.offered {
            let Some(path) = self.payload_file(&entry.digest)? else {
                continue;
            };
            self.filesystem()
                .remove_file(&path)
                .map_err(|error| StoreError::io(&path, error))?;
            evicted.push(entry.digest);
        }
        for payload in &evicted {
            self.catalogue_mut()?.remove(payload);
        }
        // The catalogue maps digests to paths that have just gone.
        self.forget_catalogue();
        remove_empty_directories(self.filesystem(), &self.root.join(OPERATIONS_DIR))?;
        Ok(evicted)
    }
}

/// Why nothing was let go of.
#[derive(Debug)]
#[non_exhaustive]
pub enum EvictError {
    /// A revision here names this payload as a file's lines.
    Text {
        /// The payload.
        payload: RevisionId,
    },
    /// The copy does not offer the payload.
    NotOffered {
        /// The payload.
        payload: RevisionId,
    },
    /// The copy's listing could not be read.
    Fetch(FetchError),
    /// This store could not be read or written.
    Store(StoreError),
}

impl From<FetchError> for EvictError {
    fn from(error: FetchError) -> Self {
        Self::Fetch(error)
    }
}

impl From<StoreError> for EvictError {
    fn from(error: StoreError) -> Self {
        Self::Store(error)
    }
}

impl fmt::Display for EvictError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EvictError::Text { payload } => write!(
                f,
                "{payload} is the text a file of lines is replayed onto, and \
                 without it that file could not be read at any revision; only \
                 files of bytes are let go of"
            ),
            EvictError::NotOffered { payload } => write!(
                f,
                "the copy does not offer {payload}, so letting go of it would \
                 leave it nowhere anybody has said they hold it"
            ),
            EvictError::Fetch(error) => error.fmt(f),
            EvictError::Store(error) => error.fmt(f),
        }
    }
}

impl std::error::Error for EvictError {}
