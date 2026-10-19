//! Carrying a chain away — *the store as a set of objects, and the manifest a
//! reader fetches by.*
//!
//! Historica's own transport is two decisions: `export` builds the copy a
//! stranger should have (0042/0052 — the target's ancestry, closed, with the
//! forgetting that touches it, and without the bookmarks and rules marked
//! private), and `offer` lists that copy so a fetcher can ask for exactly
//! what it lacks (0048) — every entry named by the digest of its bytes, so
//! nothing arrives unverified. Neither needs a server that does anything but
//! hand back a file it was asked for by name.
//!
//! What a *publish* adds is that the names must not be paths and the bytes
//! must not be readable in transit or at rest. So the export is written into
//! memory rather than onto disk, and what leaves here is the manifest text
//! plus every file it lists, keyed by digest — which is what a sealing layer
//! names and encrypts. Every digest is content-addressed, so an unchanged
//! history seals to unchanged objects and a republish uploads only what
//! moved; a file the new manifest no longer lists (a forgetting's destroyed
//! original) is one the publish deletes.
//!
//! An [`Export`] is also a [`Source`] in its own right, which is the
//! plaintext transport: two chains on one disk, a test, a courier trusted
//! with the bytes — and what a sealed transport becomes once it has unwrapped
//! the objects.
//!
//! # What travels beside the revisions
//!
//! Nothing this crate arranges. Historica carries a reserved directory by its
//! class (decision 0053), and its registry says `claims/` travels and
//! `trust/` does not — so the signed claims that vouch for a chain are in the
//! offer as `reserved` entries, named by the digest of their bytes like
//! everything else, and a fetch verifies them like everything else.
//!
//! That is worth stating because the obvious alternative is wrong. A tool
//! could carry claims *beside* the offer, in an index of its own, on the
//! reading of 0046 that leaves claims-in-an-export to the tool. It would
//! work, and every byte of it would arrive unverified — the offer is what
//! names a file by its digest, so a file the offer does not list is a file
//! nothing checks. Letting historica carry them is both less code and the
//! only version that is safe.
//!
//! And `trust/` staying home is not an omission to be fixed later. A claim
//! arriving says *here is a fact*, which commits this copy to nothing; an
//! opinion about a key arriving would say *believe more*, and a copy seeded
//! with a stranger's key verifies the stranger's history. Believing a key is
//! a person on this machine deciding, and nothing else.

use std::collections::BTreeMap;
use std::path::Path;
use std::sync::Arc;

use historica::fs::Filesystem;
use historica::store::{Offer, STORE_DIR, Source, Store, Unreachable};

use crate::error::{Result, history};

use super::memory::Memory;
use super::repo::{MANIFEST_PATH, Repo, current_heads};

/// The manifest's directory in the in-memory copy, and the prefix the offer
/// addresses the store under — so every listed path is `store/history/…` and
/// resolves against the manifest's own directory, as a fetcher expects.
const EXPORT_ROOT: &str = "/export";
const STORE_PREFIX: &str = "store";

/// A chain, ready to leave: what a reader fetches by, and every file it
/// names.
#[derive(Debug, Clone)]
pub struct Export {
    /// Whatever the caller calls this chain. Carried so a receiver can be
    /// told what arrived; nothing here reads it.
    pub label: String,
    /// The head the copy was built at.
    pub head: String,
    /// The `offer` manifest, verbatim — `historica-offer-1`, the heads, then
    /// one line per file: kind, digest, what it forgets, path.
    pub manifest: String,
    /// Every file the manifest lists, keyed by the digest it lists it under.
    ///
    /// The claims that vouch for the chain are among them, as `reserved`
    /// entries — see the module note. There is no separate map for them
    /// because there is no separate transport for them.
    pub files: BTreeMap<String, Vec<u8>>,
}

/// Build the copy of `repo`'s chain a reader should be given, in memory.
/// `None` for a store holding no revision. `label` only names the [`Export`].
pub(crate) fn export_at<F: Filesystem>(repo: &Repo<F>, label: &str) -> Result<Option<Export>> {
    let store = repo.store()?;
    let Some(head) = current_heads(&store).first().copied() else {
        return Ok(None);
    };

    let memory = Arc::new(Memory::default());
    let root = Path::new(EXPORT_ROOT);
    let copy = root.join(STORE_PREFIX);
    memory.create_directory(root)?;
    store
        .export_onto(Arc::clone(&memory), &copy, &head)
        .map_err(history)?;

    // The manifest is the copy's, not the origin's: what it lists are the
    // copy's own filenames, and the copy is what has already had the private
    // rules and names withheld from it.
    let published = Store::open_on(Arc::clone(&memory), copy.join(STORE_DIR)).map_err(history)?;
    let offer = published.offer(STORE_PREFIX).map_err(history)?;
    let mut files = BTreeMap::new();
    for entry in offer.entries() {
        let bytes = memory.read(&root.join(&entry.path))?;
        files.insert(entry.digest.to_string(), bytes);
    }
    Ok(Some(Export {
        label: label.to_string(),
        head: head.to_string(),
        manifest: offer.to_string(),
        files,
    }))
}

/// The manifest at [`MANIFEST_PATH`], and every listed path answered by the
/// file its digest names.
///
/// Every path but the manifest's own is one the offer lists, which is what
/// makes this a source that cannot serve a byte nothing checks: a path the
/// offer does not name has no digest to answer under, and is answered
/// `None`.
impl Source for Export {
    fn get(&self, path: &str) -> std::result::Result<Option<Vec<u8>>, Unreachable> {
        if path == MANIFEST_PATH {
            return Ok(Some(self.manifest.clone().into_bytes()));
        }
        let offer = Offer::parse(&self.manifest)
            .map_err(|e| Unreachable::saying(format!("the manifest would not parse: {e}")))?;
        Ok(offer
            .entries()
            .iter()
            .find(|entry| entry.path == path)
            .and_then(|entry| self.files.get(&entry.digest.to_string()).cloned()))
    }
}
