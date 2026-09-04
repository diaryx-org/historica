//! `fetch`: taking what is missing from a directory nothing can list.
//!
//! Decision 0048's other half. [`offer`](super::offer) writes the listing a URL
//! cannot give; this reads one and takes the difference. Everything between
//! those two sentences was already settled in 0003: every file under a store is
//! immutable and named by the digest of its bytes, so a reader that has been
//! handed a listing can ask for exactly the ones it lacks, hash each on
//! arrival, and stop. No session, no negotiation, no state at either end, and
//! nothing on the server but files.
//!
//! # The one method
//!
//! A fetch is given a [`Source`], which answers `get(path)`. That is the whole
//! of the transport seam, and it is decision 0025's shape applied a second
//! time: the library does the algorithm and the caller brings the TLS, the
//! redirects and the proxy settings. It keeps a local directory an honest
//! implementation rather than a special case, which is what every test here
//! uses, and it is what lets a host with no sockets of its own — a wasm guest,
//! an application holding its documents through a document provider — fetch by
//! handing over the one function it does have.
//!
//! **Absence is an answer.** [`Source::get`] returns `Ok(None)` for a path the
//! source says is not there, and an error only where it could not ask. That
//! parting is load-bearing rather than tidy: a publisher who re-exports,
//! `arrange`s or prunes between the manifest being read and the files being
//! taken moves the paths a fetcher is still working through, and those requests
//! 404. A 404 is ordinary here, and the answer to it is to read the manifest
//! again and want what is still wanted.
//!
//! The error is opaque prose, unlike [`Filesystem`](crate::fs::Filesystem),
//! which trades in [`std::io::Error`] because it branches on two of its kinds.
//! Nothing here branches on anything: the one distinction a fetch reasons about
//! is absence, and absence is in the return type. So what is left is a sentence
//! for whoever typed the command, carried rather than translated.
//!
//! # What it does, in order
//!
//! **The receiver checks itself first.** A store `check` calls broken does not
//! fetch, for `export` and `prune`'s reason: a copy of a fault is two faults.
//!
//! **Relatedness is read from the listing**, and decision 0052 is explicit that
//! this is stricter than decision 0029's. Of `related`'s three arms, two are
//! answerable from a listing of digests — a revision both hold, and *our*
//! revision naming a parent or supersession the listing names. The third —
//! *their* revision naming an edge we hold — needs their revision documents,
//! which a manifest deliberately omits, and an export is precisely the store
//! with dangling `supersedes` edges. So it fails toward refusal rather than
//! toward a wrong join, and `--join-unrelated` is the escape. An empty store
//! may always be seeded.
//!
//! **Content first and revisions last**, which is `receive`'s order and
//! `export`'s: payloads, then the documents of `operations/`, then compliance
//! with forgetting, then revisions, then the rules and the files of another
//! tool that no revision names. One invariant holds at every moment in between
//! — *no revision in this store names bytes this store does not hold* — so an
//! interruption understates what is reachable rather than leaving a revision
//! pointing at content that never arrived, and `prune` collects what is left
//! unreachable.
//!
//! **Nothing enters unverified.** Every arriving file is hashed against the
//! digest the manifest gave before it is written, and it is written through
//! *this* store's own [`Filesystem`](crate::fs::Filesystem) under *this*
//! store's digest-derived names. A fetched path is an address, not a name
//! (decision 0048): it is used to ask and then discarded, `arrange` gives the
//! file a readable name here, and no two stores ever have to agree about a
//! filename. So a lying manifest costs a wasted request and cannot produce a
//! wrong store.
//!
//! **The receiver checks itself again at the end**, which is where a
//! contradiction the remote was harbouring becomes this store's problem —
//! visibly, at a moment, rather than silently. Decision 0048 priced that
//! plainly: the source's internal consistency is what a fetch gives up in
//! exchange for not reading the whole remote store, and it is paid in a `check`
//! failure rather than in corruption.
//!
//! # The two kinds nothing here reads
//!
//! A `rule` line lands in `skipped/` under the union `receive` already applies
//! (decision 0045): a rule the source states and this store does not is added,
//! under whatever label *this* store derives, and a rule already stated is left
//! where it is. Two replicas that each wrote a rule were never disagreeing.
//!
//! A `reserved` line is a file historica carries and cannot read, and decision
//! 0056 is emphatic that **the fetcher asks its own registry** rather than the
//! manifest. The kind says only that the publisher's historica thought this
//! travelled; whether it travels *into here* is a question about
//! [`RESERVED_DIRS`](super::RESERVED_DIRS) on this side. A directory this build
//! knows as [`Travel::TravelsAndUnions`] is written add-only with `create_new`
//! and a name already taken is left exactly as it is, unread. Anything else —
//! `local-only`, `derived`, or a directory this build has never heard of — is
//! not written, so a manifest cannot talk a store into filling a directory it
//! does not know.
//!
//! 0056 deferred whether that decline should be said out loud. It should, and
//! decision 0057 settles it: an **observation**, counted per directory in
//! [`Fetched::declined`] and printed. Not an error, because there is nothing
//! wrong — the publisher and the recipient simply run tools of different ages,
//! which is the case decision 0053 built the registry for. And not silence,
//! because the recipient is the only party who can install the tool that would
//! read those files, and they cannot go looking for what nobody mentioned.
//!
//! # What is not touched
//!
//! **The folder.** A fetch adds history and stops; `update` is the folder's
//! catch-up as it has been since decision 0030. Two commands, because a fetch
//! that moved a person's files under them is a different operation than the one
//! they asked for.
//!
//! **Divergence.** A fetch from a remote whose head is not this store's head is
//! a fetch, not a refusal. Divergence is a thing this store holds and `merge`
//! resolves; only `update` and `cat` need one answer.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::io;

use crate::core::RevisionId;
use crate::format::{self, OperationDocument, ResolutionDocument, RevisionDocument, digest};
use crate::fs::Filesystem;
use crate::working::{Rule, SKIPPED_DIR, Skipped};

use super::{
    Body, Bookmark, NAME_SUFFIX, NAMES_DIR, OPERATION_SUFFIX, Offer, OfferError, OfferKind,
    Offered, REVISION_SUFFIX, Report, STORE_DIR, Store, StoreError, Travel, check_name, travel,
    walk,
};

/// How many times a fetch will read the manifest again before giving up.
///
/// Decision 0048 says *bounded* and does not say how far, because the number is
/// not the argument — the argument is that a publisher must not have to hold
/// still. Three is what a publisher racing a fetcher costs: an addition-only
/// run moves nothing, so the only way to lose a path is a run that withdrew
/// one, and a fetcher that lost three races in succession to a publisher
/// withdrawing files is one that should say so rather than keep asking.
const REFETCHES: usize = 3;

/// Where a fetch asks for bytes.
///
/// One method, which is decision 0048's whole transport story. What answers it
/// may be a web client, a directory on disk, or anything else that can turn a
/// path into bytes; nothing here learns which, and nothing here constructs a
/// path that is not written in the manifest.
///
/// Paths arrive exactly as the manifest spells them — relative to the
/// manifest's own directory, per decision 0052 — so resolving them against a
/// URL, a base directory, or nothing at all is the implementation's business.
pub trait Source {
    /// The bytes at `path`, or [`None`] where the source says nothing is there.
    ///
    /// **A missing path is `Ok(None)`, never an error.** It is the ordinary
    /// outcome of a publisher who withdrew a file between the manifest being
    /// written and this request being made, and a fetch answers it by reading
    /// the manifest again. An implementation that reported it as a failure
    /// would turn the one recoverable case into the one unrecoverable one.
    ///
    /// The error is for the cases where nothing was learned at all: no route,
    /// no name, a refusal, a body that would not finish. Nothing here reads it
    /// — it is carried to whoever typed the command.
    fn get(&self, path: &str) -> Result<Option<Vec<u8>>, Unreachable>;

    /// The same bytes, handed over in pieces.
    ///
    /// Decision 0067, and the reason it is defaulted: a transport that has only
    /// whole bodies keeps compiling and keeps answering, because the default
    /// *is* [`get`](Source::get) with the one piece it produced fed straight
    /// through. There is no third answer meaning "I do not stream" — a source
    /// that declines to override this still streams, in runs of one.
    ///
    /// `false` is [`get`](Source::get)'s `None`: the source says nothing is
    /// there, `each` was not called, and a fetch answers it by reading the
    /// manifest again. `true` means the pieces were fed, and concatenating them
    /// gives exactly what [`get`](Source::get) would have returned.
    ///
    /// **Resumption is not this.** A piece feed that stops halfway is a failure
    /// of the whole request, and what the fetcher does about it is ask again
    /// from the beginning — nothing here carries an offset, and a partial file
    /// is never written, because the digest is checked before anything lands.
    fn get_in_pieces(
        &self,
        path: &str,
        each: &mut dyn FnMut(&[u8]) -> Result<(), Unreachable>,
    ) -> Result<bool, Unreachable> {
        match self.get(path)? {
            Some(bytes) => {
                each(&bytes)?;
                Ok(true)
            }
            None => Ok(false),
        }
    }
}

/// Forward to whatever is inside the pointer, so `Arc<dyn Source>` is a source.
macro_rules! forwarding {
    ($holder:ty) => {
        impl<T: Source + ?Sized> Source for $holder {
            fn get(&self, path: &str) -> Result<Option<Vec<u8>>, Unreachable> {
                (**self).get(path)
            }
            fn get_in_pieces(
                &self,
                path: &str,
                each: &mut dyn FnMut(&[u8]) -> Result<(), Unreachable>,
            ) -> Result<bool, Unreachable> {
                (**self).get_in_pieces(path, each)
            }
        }
    };
}

forwarding!(&T);
forwarding!(Box<T>);
forwarding!(std::rc::Rc<T>);
forwarding!(std::sync::Arc<T>);

/// What a source says when it could not answer at all.
///
/// Prose, because nothing in this crate reads it. A transport's failures are a
/// vocabulary the transport owns — a certificate, a proxy, a name that does not
/// resolve — and translating them into a set historica invented would make
/// every implementation translate in and every caller translate back out for no
/// decision either of them makes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Unreachable {
    because: String,
}

impl Unreachable {
    /// Say why, in the transport's own words.
    pub fn saying(because: impl fmt::Display) -> Self {
        Self {
            because: because.to_string(),
        }
    }

    /// What the transport said.
    pub fn because(&self) -> &str {
        &self.because
    }
}

impl fmt::Display for Unreachable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.because)
    }
}

impl std::error::Error for Unreachable {}

/// A file of a reserved directory this store declined to take.
///
/// Decision 0053's default, applied and then said out loud (decision 0057).
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct Declined {
    /// The reserved directory, as the manifest's path named it.
    pub directory: String,
    /// How this store classes it, which is why nothing was written.
    ///
    /// [`Travel::LocalOnly`] covers both a directory reserved that way here and
    /// one this build has never heard of, which decision 0053 makes the same
    /// answer on purpose: leaving something behind is the recoverable way to be
    /// wrong about it.
    pub travel: Travel,
    /// How many files of it the manifest named.
    pub files: usize,
}

/// What one fetch would take, worked out before anything is asked for.
#[derive(Debug, Clone, Default)]
pub struct FetchPlan {
    payloads: Vec<Offered>,
    documents: Vec<Offered>,
    revisions: Vec<Offered>,
    rules: Vec<Offered>,
    reserved: Vec<Offered>,
    names: Vec<Offered>,
    kept: usize,
    declined: Vec<Declined>,
    destroys: BTreeSet<RevisionId>,
}

impl FetchPlan {
    /// Whole-content payloads this store lacks.
    pub fn payloads(&self) -> &[Offered] {
        &self.payloads
    }

    /// Content documents this store lacks, in either of decision 0032's
    /// grammars.
    pub fn documents(&self) -> &[Offered] {
        &self.documents
    }

    /// Revision documents this store lacks.
    pub fn revisions(&self) -> &[Offered] {
        &self.revisions
    }

    /// Rule files whose bytes this store's `skipped/` does not already hold.
    pub fn rules(&self) -> &[Offered] {
        &self.rules
    }

    /// Files of a reserved directory this store carries and does not hold under
    /// that name.
    pub fn reserved(&self) -> &[Offered] {
        &self.reserved
    }

    /// Bookmarks the publisher states and this store does not hold.
    ///
    /// Decision 0062: only those. A bookmark this store already has is one it
    /// keeps, whatever the publisher's says — `fetch` is *taking what is
    /// missing*, and a name it holds is not missing.
    pub fn names(&self) -> &[Offered] {
        &self.names
    }

    /// Bookmarks the publisher states that this store holds under its own
    /// reading, and therefore leaves alone.
    pub fn kept(&self) -> usize {
        self.kept
    }

    /// Reserved directories the manifest named and this store will not fill.
    pub fn declined(&self) -> &[Declined] {
        &self.declined
    }

    /// Forgotten originals this store still holds, which arriving forgetting
    /// documents destroy.
    pub fn destroys(&self) -> &BTreeSet<RevisionId> {
        &self.destroys
    }

    /// Whether taking this plan would change anything.
    pub fn is_empty(&self) -> bool {
        self.payloads.is_empty()
            && self.documents.is_empty()
            && self.revisions.is_empty()
            && self.rules.is_empty()
            && self.reserved.is_empty()
            && self.names.is_empty()
            && self.destroys.is_empty()
    }

    /// Every entry to ask for, in the order they must be asked for.
    fn wanted(&self) -> Vec<(OfferKind, &Offered)> {
        fn group(kind: OfferKind, entries: &[Offered]) -> Vec<(OfferKind, &Offered)> {
            entries.iter().map(|entry| (kind, entry)).collect()
        }
        // One list rather than a chain of iterators: the groups are the
        // difference between two stores rather than a store, and the order
        // between them is the whole of what makes an interruption safe.
        let mut order = group(OfferKind::Payload, &self.payloads);
        order.extend(group(OfferKind::Operation, &self.documents));
        order.extend(group(OfferKind::Revision, &self.revisions));
        order.extend(group(OfferKind::Rule, &self.rules));
        order.extend(group(OfferKind::Reserved, &self.reserved));
        order.extend(group(OfferKind::Name, &self.names));
        order
    }
}

/// What one fetch changed.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct Fetched {
    /// Whole-content payloads taken.
    pub payloads: usize,
    /// Content documents taken, in either grammar.
    pub documents: usize,
    /// Revision documents taken, by digest, in the order they were written.
    ///
    /// The digests rather than a count of them, for the reason [`Received`]
    /// carries its own: `fetch --fields` says where to look under decision
    /// 0074, and how many is `revisions.len()`.
    pub revisions: Vec<RevisionId>,
    /// Rules taken, counting only those this store did not already state.
    pub rules: usize,
    /// Files another tool wrote, unioned add-only by their class.
    ///
    /// Nothing in `historica-wrote-1` reports these, and decision 0074 defers
    /// a line kind for them rather than owing one: a claim arriving can only
    /// ever move a revision from unvouched to vouched, never the other way, so
    /// a wrapper verifying after a receive asks the store as it stands rather
    /// than asking what came.
    pub reserved: usize,
    /// Bookmarks taken, by name, which are those this store did not already
    /// hold.
    pub names: Vec<String>,
    /// Bookmarks the publisher states and this store kept its own reading of.
    pub kept: usize,
    /// Reserved directories the manifest named and this store did not fill.
    pub declined: Vec<Declined>,
    /// Originals destroyed in compliance with arriving forgetting documents.
    pub destroyed: usize,
    /// How many times the source was asked for anything, the manifest
    /// included.
    pub requests: usize,
    /// How many times the manifest had to be read again because a path had
    /// moved underneath the fetch.
    pub refetches: usize,
}

impl<F: Filesystem> Store<F> {
    /// Take from `source` everything a manifest names and this store lacks.
    ///
    /// `manifest` is the manifest's own name relative to its own directory —
    /// `offer.txt`, conventionally — because decision 0052 resolves every path
    /// in a manifest against the directory the manifest sits in, and that makes
    /// the manifest's own name one more path in the same namespace. So the
    /// source is asked about one flat space of paths and the fetch can read the
    /// listing again for itself, which is what staleness needs.
    ///
    /// Writes nothing outside this store, and nothing at all into the folder
    /// beside it: `update` is the folder's catch-up (decision 0030).
    pub fn fetch<S: Source + ?Sized>(
        &mut self,
        source: &S,
        manifest: &str,
        join_unrelated: bool,
    ) -> Result<Fetched, FetchError> {
        // A copy of a fault is two faults. The far end cannot be checked at all
        // without downloading the whole of it, which decision 0048 says would
        // be the operation's own defeat; this end can, and is.
        if !Store::check_on(self.filesystem(), self.root()).is_ok() {
            return Err(FetchError::BrokenStore);
        }

        let mut fetched = Fetched::default();
        let mut offer = read_manifest(source, manifest, &mut fetched)?;
        let mut refetches = REFETCHES;
        loop {
            let plan = self.fetch_plan(&offer, join_unrelated)?;
            // Stated from the plan rather than accumulated across passes: it is
            // a description of what the manifest holds, and reading the
            // manifest twice does not mean twice as many files were declined.
            fetched.declined = plan.declined.clone();
            // Decision 0062, and stated from the plan for the same reason:
            // a bookmark this store kept is a fact about the two readings,
            // not something a second pass keeps again.
            fetched.kept = plan.kept;
            match self.take(source, &plan, &mut fetched)? {
                None => break,
                // Decision 0048: a path that is not there is the publisher
                // having moved on, so read the listing again and want what is
                // still wanted. A digest gone from the new listing was
                // forgotten or pruned at the source, which is an answer and not
                // an error — the next plan simply does not name it.
                Some(moved) => {
                    if refetches == 0 {
                        return Err(FetchError::Stale { path: moved });
                    }
                    refetches -= 1;
                    fetched.refetches += 1;
                    offer = read_manifest(source, manifest, &mut fetched)?;
                }
            }
        }

        // Where a contradiction the remote was harbouring becomes this store's
        // problem: at a moment, and out loud. What arrived stays — it is
        // verified bytes filed under their own digests — and what is wrong with
        // it is what `check` says.
        let report = Store::check_on(self.filesystem(), self.root());
        if !report.is_ok() {
            return Err(FetchError::Contradiction {
                report: Box::new(report),
            });
        }
        Ok(fetched)
    }

    /// Work out what a manifest would add, without asking for a byte of it.
    pub fn fetch_plan(&self, offer: &Offer, join_unrelated: bool) -> Result<FetchPlan, FetchError> {
        if !join_unrelated && !related_to(self, offer) {
            return Err(FetchError::Unrelated);
        }

        // What either side forgets, which is decision 0014 travelling. A
        // fetcher that took a plain set difference would keep an original that
        // an arriving forgetting document destroys, so the fourth field is read
        // before anything is wanted rather than after something has been kept.
        let forgotten: BTreeSet<RevisionId> = self
            .bodies()?
            .values()
            .filter_map(Body::forgets)
            .chain(offer.entries().iter().filter_map(|entry| entry.forgets))
            .collect();
        let documents: BTreeSet<RevisionId> = self.bodies()?.into_keys().collect();
        let payloads = self.payloads()?;

        let mut plan = FetchPlan {
            destroys: forgotten
                .iter()
                .filter(|id| documents.contains(id) || payloads.contains_key(id))
                .copied()
                .collect(),
            ..FetchPlan::default()
        };
        plan.payloads = wanted(offer, OfferKind::Payload, |entry| {
            !payloads.contains_key(&entry.digest) && !forgotten.contains(&entry.digest)
        });
        plan.documents = wanted(offer, OfferKind::Operation, |entry| {
            !documents.contains(&entry.digest) && !forgotten.contains(&entry.digest)
        });
        plan.revisions = wanted(offer, OfferKind::Revision, |entry| {
            !self.holds(&entry.digest)
        });

        // Decision 0045: a rule is its text, and a rule file is that text and
        // nothing else, so two replicas stating one rule hold one set of bytes
        // — and the digest is enough to say which rules are already here
        // without opening anything. What the *file* is called differs, and does
        // not matter: a fetched path is an address, and `add_skipped` derives
        // the label on this side.
        let mut held: BTreeSet<RevisionId> = BTreeSet::new();
        for path in walk(&self.files, &self.root, SKIPPED_DIR)?.files {
            held.insert(
                crate::fs::digest_of(&self.files, &path)
                    .map_err(|error| StoreError::io(&path, error))?,
            );
        }
        plan.rules = wanted(offer, OfferKind::Rule, |entry| {
            !held.contains(&entry.digest)
        });

        // Decision 0062: the one kind whose path is a name. A fetcher who took
        // `main` once and then recorded onto it has a `main` of its own, and a
        // fetch that moved it back would be the only place in this design
        // where transport overwrites a mutable value without asking — which
        // would also mean a publisher moving `main` forward broke every
        // fetcher who ever took it. `receive` is where two stores reconcile.
        let mut kept = 0;
        plan.names = wanted(offer, OfferKind::Name, |entry| {
            match named_by(&entry.path) {
                Some(name) if self.names.contains_key(name) => {
                    kept += 1;
                    false
                }
                Some(_) => true,
                // A path naming no bookmark inside a store is one this reader
                // cannot place, and an unplaceable line is discarded on the
                // standing rule decision 0056 gives an unknown kind.
                None => false,
            }
        });
        plan.kept = kept;

        // Decision 0056: the path carries the directory, and this store asks
        // its own registry about it rather than the manifest. Compared by name,
        // because decision 0053's class promises that two stores holding one
        // name hold one file.
        let ours: BTreeSet<String> = self.travelling_files()?.into_iter().collect();
        let mut declined: BTreeMap<String, (Travel, usize)> = BTreeMap::new();
        let mut taken: BTreeSet<String> = BTreeSet::new();
        for entry in offer.of(OfferKind::Reserved) {
            // A path naming no file inside a store is one this reader cannot
            // place, and an unplaceable line is discarded on the standing
            // decision 0056 gives an unknown kind.
            let Some(label) = filed_under(&entry.path) else {
                continue;
            };
            let Some(directory) = label.split('/').next().filter(|name| !name.is_empty()) else {
                continue;
            };
            let travels = travel(directory);
            if travels != Travel::TravelsAndUnions {
                let counted = declined.entry(directory.to_owned()).or_insert((travels, 0));
                counted.1 += 1;
                continue;
            }
            if !ours.contains(label) && taken.insert(label.to_owned()) {
                plan.reserved.push(entry.clone());
            }
        }
        plan.declined = declined
            .into_iter()
            .map(|(directory, (travel, files))| Declined {
                directory,
                travel,
                files,
            })
            .collect();

        Ok(plan)
    }

    /// Ask for everything one plan names, in the order it names it.
    ///
    /// `Ok(None)` where the whole plan arrived; `Ok(Some(path))` where a path
    /// was no longer there, which is the caller's cue to read the manifest
    /// again. Whatever had already been written stays written — every group is
    /// finished before the next begins, so the store is short of content rather
    /// than short of the bytes a revision names.
    fn take<S: Source + ?Sized>(
        &mut self,
        source: &S,
        plan: &FetchPlan,
        fetched: &mut Fetched,
    ) -> Result<Option<String>, FetchError> {
        let mut rules: Vec<Rule> = Vec::new();
        // Already true where nothing is forgotten, because complying is a pass
        // over `operations/` that hashes every file in it — the cost decision
        // 0036's catalogue exists to avoid, and not one to pay on every fetch
        // for the sake of a set that is usually empty.
        let mut complied = plan.destroys.is_empty();
        for (kind, entry) in plan.wanted() {
            // Decision 0014 complies where `receive` complies with it: after
            // the documents and before the revisions, so a forgetting document
            // that arrived in this pass has destroyed what it stands in for
            // before anything names either.
            if kind == OfferKind::Revision && !complied {
                complied = true;
                fetched.destroyed += self.comply_with_forgetting(&plan.destroys)?;
            }
            // Decision 0067: a payload goes from the transport into the store's
            // own file without ever being one buffer, so fetching a repository
            // of photographs costs a piece at a time. The check that made the
            // whole-body path safe is unchanged and is what makes the streamed
            // one safe: the digest is taken as the pieces pass, and a total
            // that is not what the manifest offered refuses at the last piece,
            // which leaves nothing written.
            if kind == OfferKind::Payload {
                if self.fetch_payload(source, entry, fetched)? {
                    fetched.payloads += 1;
                } else {
                    return Ok(Some(entry.path.clone()));
                }
                continue;
            }
            let Some(bytes) = ask(source, &entry.path, fetched)? else {
                return Ok(Some(entry.path.clone()));
            };
            // Decision 0036 one level out: the catalogue says where to look, it
            // never says what is there. Hashed before it is written, and then
            // written under the digest this side computed — so the refusal is
            // what makes a lie visible, and the naming is what makes it
            // harmless.
            let found = digest(&bytes);
            if found != entry.digest {
                return Err(FetchError::Tampered {
                    path: entry.path.clone(),
                    offered: entry.digest,
                    found,
                });
            }
            match kind {
                OfferKind::Payload => {
                    self.insert_payload_at(&bytes, &found.to_string())?;
                    fetched.payloads += 1;
                }
                OfferKind::Operation => {
                    // Written back in the grammar it was read in: a resolution
                    // rewritten as anything else would be a different digest,
                    // and the `edit` line naming it would stop finding it.
                    let name = format!("{found}{OPERATION_SUFFIX}");
                    if format::is_forgotten_payload(&bytes) {
                        // Decision 0066's grammar, which is a document like
                        // any other and travels as one: two headers saying
                        // which payload went and how long it was.
                        let document = format::ForgottenPayload::parse(&bytes)
                            .map_err(|error| unusable(&entry.path, error))?;
                        self.insert_forgotten_payload_at(&document, &name)?;
                    } else if format::is_resolution(&bytes) {
                        let document = ResolutionDocument::parse(&bytes)
                            .map_err(|error| unusable(&entry.path, error))?;
                        self.insert_resolution_at(&document, &name)?;
                    } else {
                        let document = OperationDocument::parse(&bytes)
                            .map_err(|error| unusable(&entry.path, error))?;
                        self.insert_operation_at(&document, &name)?;
                    }
                    fetched.documents += 1;
                }
                OfferKind::Revision => {
                    let document = RevisionDocument::parse(&bytes)
                        .map_err(|error| unusable(&entry.path, error))?;
                    self.insert_at(&document, &format!("{found}{REVISION_SUFFIX}"))?;
                    fetched.revisions.push(found);
                }
                OfferKind::Rule => {
                    let text = String::from_utf8(bytes)
                        .map_err(|_| unusable(&entry.path, "a rule file that is not text"))?;
                    // A file stating no rule states nothing a recipient needs,
                    // which is what the note `init` leaves is.
                    if let Some(rule) =
                        Skipped::rule_in(&text).map_err(|error| unusable(&entry.path, error))?
                    {
                        rules.push(rule);
                    }
                }
                OfferKind::Reserved => {
                    let Some(label) = filed_under(&entry.path) else {
                        continue;
                    };
                    if self.carry_travelling(label, &bytes)? {
                        fetched.reserved += 1;
                    }
                }
                OfferKind::Name => {
                    let Some(name) = named_by(&entry.path) else {
                        continue;
                    };
                    // Add-only, and the plan was worked out from a listing
                    // rather than held under a lock, so a bookmark that
                    // appeared in between is one this store now has and keeps.
                    if self.names.contains_key(name) {
                        continue;
                    }
                    let text = String::from_utf8(bytes)
                        .map_err(|_| unusable(&entry.path, "a bookmark file that is not text"))?;
                    let bookmark =
                        Bookmark::parse(&text).map_err(|because| unusable(&entry.path, because))?;
                    let name = name.to_owned();
                    self.set_bookmark(&name, bookmark)?;
                    fetched.names.push(name.clone());
                }
            }
        }
        // Where the plan named no revisions, which is the ordinary shape of a
        // fetch that only had documents to collect.
        if !complied {
            fetched.destroyed += self.comply_with_forgetting(&plan.destroys)?;
        }
        // Decision 0045's union, applied where `receive` applies it: a rule
        // already stated is left under whatever label states it, and what is
        // new is written under the label this store derives.
        fetched.rules += self.add_skipped(&rules)?.len();
        Ok(None)
    }

    /// Fetch one payload straight into `operations/`, without holding it.
    ///
    /// Decision 0067. `false` is [`Source::get`]'s absence — a publisher who
    /// withdrew the file between the manifest and this request — which the
    /// caller answers by reading the manifest again.
    ///
    /// The digest is taken over the pieces as they pass and checked before
    /// anything lands, so the two things the whole-body path promised are both
    /// kept: a source that offered one digest and served another is
    /// [`FetchError::Tampered`], and nothing it served is on disk. What is
    /// given up is nothing, because the whole body was never trusted either —
    /// it was hashed after being buffered, and this hashes it instead of
    /// buffering it.
    fn fetch_payload<S: Source + ?Sized>(
        &mut self,
        source: &S,
        entry: &Offered,
        fetched: &mut Fetched,
    ) -> Result<bool, FetchError> {
        fetched.requests += 1;
        let mut missing = false;
        let mut unreachable = None;
        let landed =
            self.insert_payload_in_pieces(&entry.digest, &entry.digest.to_string(), &mut |into| {
                match source.get_in_pieces(&entry.path, &mut |piece| {
                    into.write_all(piece).map_err(Unreachable::saying)
                }) {
                    Ok(true) => Ok(()),
                    Ok(false) => {
                        missing = true;
                        Err(io::Error::new(
                            io::ErrorKind::NotFound,
                            "the source says nothing is there",
                        ))
                    }
                    Err(error) => {
                        unreachable = Some(error);
                        Err(io::Error::other("the source could not answer"))
                    }
                }
            });
        if let Some(error) = unreachable {
            return Err(FetchError::Unreachable {
                path: entry.path.clone(),
                because: error.because().to_owned(),
            });
        }
        if missing {
            return Ok(false);
        }
        match landed {
            Ok(_) => Ok(true),
            // Decision 0036 one level out: the catalogue says where to look, it
            // never says what is there, and neither does a manifest.
            Err(StoreError::PayloadMismatch { found, .. }) => Err(FetchError::Tampered {
                path: entry.path.clone(),
                offered: entry.digest,
                found,
            }),
            Err(error) => Err(error.into()),
        }
    }
}

/// Read the manifest, and refuse a spelling this reader does not know.
fn read_manifest<S: Source + ?Sized>(
    source: &S,
    manifest: &str,
    fetched: &mut Fetched,
) -> Result<Offer, FetchError> {
    let Some(bytes) = ask(source, manifest, fetched)? else {
        return Err(FetchError::NoManifest {
            path: manifest.to_owned(),
        });
    };
    let text = String::from_utf8(bytes).map_err(|_| FetchError::Offer {
        error: OfferError::UnknownFormat {
            found: "not text at all".to_owned(),
        },
    })?;
    Offer::parse(&text).map_err(|error| FetchError::Offer { error })
}

/// One request, counted.
fn ask<S: Source + ?Sized>(
    source: &S,
    path: &str,
    fetched: &mut Fetched,
) -> Result<Option<Vec<u8>>, FetchError> {
    fetched.requests += 1;
    source.get(path).map_err(|error| FetchError::Unreachable {
        path: path.to_owned(),
        because: error.because().to_owned(),
    })
}

/// One group of the plan: what the manifest names, minus what is held, minus
/// the second copy of anything named twice.
///
/// A manifest names every file at the path it is at, so one set of bytes may be
/// named twice — which is right for a listing and would be a second request
/// here for bytes this store would file once.
fn wanted(offer: &Offer, kind: OfferKind, mut keep: impl FnMut(&Offered) -> bool) -> Vec<Offered> {
    let mut seen: BTreeSet<RevisionId> = BTreeSet::new();
    offer
        .of(kind)
        .filter(|entry| keep(entry) && seen.insert(entry.digest))
        .cloned()
        .collect()
}

/// Where a manifest's path sits inside the store it names, or nothing where it
/// names nothing inside one.
///
/// Decision 0056: a fetcher subtracts the exported directory's name, which it
/// constructed, and `history/`, which is the one directory name this format
/// fixes. What is left is the path the file already had at the origin, which is
/// what makes a reserved directory union wherever it lands.
fn filed_under(path: &str) -> Option<&str> {
    let head = format!("{STORE_DIR}/");
    if let Some(rest) = path.strip_prefix(&head) {
        return Some(rest);
    }
    let separated = format!("/{STORE_DIR}/");
    let at = path.find(&separated)?;
    Some(&path[at + separated.len()..])
}

/// The bookmark a manifest path names, if it names one.
///
/// Decision 0062: every other kind's path is an address and this one's is a
/// name, because a bookmark's filename is its identity. So the reading is a
/// parse of the path rather than a place to put bytes, and a path that is not
/// one bookmark file directly under `names/` names no bookmark at all.
fn named_by(path: &str) -> Option<&str> {
    let label = filed_under(path)?;
    let name = label.strip_prefix(&format!("{NAMES_DIR}/"))?;
    let name = name.strip_suffix(NAME_SUFFIX)?;
    // Decision 0071: a name may have structure in it, so the refusal that
    // used to be "no `/`" is now the grammar itself. It is doing the same work
    // it was doing before and more of it: a manifest is a file written
    // elsewhere, and `..` or a leading `/` in a name is that file choosing
    // where in this store to put bytes. `set_bookmark` asks again when the
    // bookmark is written, which is the guard rather than this; this is what
    // keeps an unplaceable line out of the plan.
    check_name(name).ok()?;
    Some(name)
}

/// Whether this store and the copy a manifest describes are two views of one
/// history.
///
/// Decision 0052: two of decision 0029's three arms, and the third left out
/// because a manifest carries no parent edges to answer it with. Failing toward
/// refusal is deliberate — the escape is a flag somebody typed on purpose.
fn related_to<F: Filesystem>(here: &Store<F>, offer: &Offer) -> bool {
    let theirs: BTreeSet<RevisionId> = offer.of(OfferKind::Revision).map(|e| e.digest).collect();
    // An empty store may always be seeded, in either direction: decision 0029's
    // first arm, and the case a first fetch after `init` is.
    if here.is_empty() || theirs.is_empty() {
        return true;
    }
    if here.revisions().any(|(id, _)| theirs.contains(id)) {
        return true;
    }
    here.revisions().any(|(_, revision)| {
        revision
            .parents
            .iter()
            .chain(revision.supersedes.iter())
            .any(|id| theirs.contains(id))
    })
}

/// A file that arrived, hashed correctly, and then would not parse.
fn unusable(path: &str, because: impl fmt::Display) -> FetchError {
    FetchError::Unusable {
        path: path.to_owned(),
        because: because.to_string(),
    }
}

/// Why a fetch stopped.
#[derive(Debug)]
#[non_exhaustive]
pub enum FetchError {
    /// This store fails `check`, so nothing was asked for.
    BrokenStore,
    /// This store and the copy the manifest describes share nothing a listing
    /// can see.
    Unrelated,
    /// The manifest could not be read.
    Offer {
        /// Which way.
        error: OfferError,
    },
    /// There is no manifest at that path.
    NoManifest {
        /// The path asked for.
        path: String,
    },
    /// The source could not be asked at all.
    Unreachable {
        /// The path being asked for.
        path: String,
        /// What the transport said, in its own words.
        because: String,
    },
    /// A file's bytes are not the digest the manifest gave for them.
    Tampered {
        /// Where it was asked for.
        path: String,
        /// What the manifest said it would be.
        offered: RevisionId,
        /// What arrived.
        found: RevisionId,
    },
    /// A file arrived under the right digest and is not what it claims to be.
    Unusable {
        /// Where it was asked for.
        path: String,
        /// What was wrong with it.
        because: String,
    },
    /// A path kept moving out from under the fetch.
    Stale {
        /// The last path that was no longer there.
        path: String,
    },
    /// Everything arrived, and this store no longer passes `check`.
    Contradiction {
        /// What `check` said, boxed: it is far the largest thing here.
        report: Box<Report>,
    },
    /// Reading or writing this store failed.
    Store(StoreError),
}

impl From<StoreError> for FetchError {
    fn from(error: StoreError) -> Self {
        Self::Store(error)
    }
}

impl fmt::Display for FetchError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FetchError::BrokenStore => write!(
                f,
                "this store does not pass `check`, and a fetch into a store \
                 that cannot be trusted would make one fault two; \
                 `historica check` says what is wrong"
            ),
            FetchError::Unrelated => write!(
                f,
                "this store and that copy share no revision a listing can see; \
                 use `--join-unrelated` only if combining two histories is \
                 intended. a manifest names digests and no parent edges, so it \
                 cannot show that *their* revision stands on one of ours — this \
                 refusal is the stricter one a listing can support"
            ),
            FetchError::Offer { error } => error.fmt(f),
            FetchError::NoManifest { path } => write!(
                f,
                "there is no manifest at `{path}`; a publisher writes one \
                 beside the copy `export` made, conventionally as `offer.txt`"
            ),
            FetchError::Unreachable { path, because } => {
                write!(f, "{path} could not be fetched: {because}")
            }
            FetchError::Tampered {
                path,
                offered,
                found,
            } => write!(
                f,
                "{path} holds {found}, and the manifest offered it as \
                 {offered}; nothing that does not hash to what was offered is \
                 written, so this store is as it was"
            ),
            FetchError::Unusable { path, because } => {
                write!(f, "{path} arrived intact and cannot be read: {because}")
            }
            FetchError::Stale { path } => write!(
                f,
                "{path} was gone every time it was asked for, across \
                 {REFETCHES} readings of the manifest; the publisher is \
                 rewriting the copy faster than it can be fetched, and what \
                 arrived is here — running the fetch again finishes it"
            ),
            FetchError::Contradiction { report: _ } => write!(
                f,
                "everything the manifest named is here, and this store no \
                 longer passes `check`. a fetch verifies every arriving file \
                 against the listing and cannot verify that the copy agreed \
                 with itself, which is what a `receive` against a local \
                 directory does and a fetch cannot; `historica check` says what \
                 contradicts what"
            ),
            FetchError::Store(error) => error.fmt(f),
        }
    }
}

impl std::error::Error for FetchError {}
