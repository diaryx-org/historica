//! `offer`: the listing a directory has no way to give.
//!
//! Decision 0048, as decision 0052 amends it. Every other way a store travels
//! hands the reader a directory it can walk — `cp -r`, rsync, a mounted disk,
//! an archive somebody unpacked — and every one of decision 0029's rules is
//! written against a source that can be listed. A URL cannot be listed. There
//! is no `entries()` over HTTP, no listing a static file server is obliged to
//! serve, and no guessing at the answer: decision 0003 made filenames
//! presentation, 0019 made the readable names the default and 0041 put a month
//! directory in front of them, so where a document sits is a thing the
//! publisher chose and `arrange` exists to change.
//!
//! So what is missing at the far end of a URL is not a set difference — a
//! fetcher already knows its own half — but a directory listing, for a
//! directory that has no way to say what it holds. This module writes one.
//!
//! # What it is pointed at
//!
//! The published copy, which decision 0052 makes an `export` rather than the
//! live store: a manifest sits *beside* the exported directory, and every path
//! in it resolves against the manifest's own directory. So the paths begin
//! with that directory's name — `store/history/operations/…` for a manifest
//! beside a `store/` — and [`Store::offer`] takes that name as its prefix
//! because it is the one thing a listing of a directory cannot read out of the
//! directory. Nothing here asks anything of the origin: an offer is a
//! rendering of the published artifact, not a claim about a store somewhere
//! else.
//!
//! # The grammar
//!
//! ```text
//! historica-offer-1
//! head <digest>
//! <kind> <digest> <forgets|-> <path>
//! ```
//!
//! One `head` line per head, then one line per transferable file. The path is
//! last on decision 0043's reason — a path is the one field that may hold a
//! space, so it ends the line and nothing needs escaping — and nothing here is
//! escaped or quoted. It is text rather than JSON because every other document
//! this format has is line-oriented text, and a reader that can split on a
//! space is a reader that needs nothing installed.
//!
//! The header carries a number, unlike a document's preamble (decision 0047).
//! A document is permanent and a store's grammar is a promise; an offer is
//! neither. It is refetchable, and a reader that meets a spelling it does not
//! know discards it whole and falls back to fetching the archive, which never
//! stopped working — the standing `historica-working-1` already has.
//!
//! The heads answer *relatedness* and nothing else. Decision 0052 is explicit
//! that they are not a currency check: a forgetting document changes the set
//! without moving a head, so equal heads cannot mean equal content, and a
//! fetcher that stopped there would be the one path a redaction never travels.
//! They are the graph's heads, superseded ones included, because a listing
//! decides nothing about what is worth showing — `log` is where that policy
//! lives.
//!
//! # The kinds
//!
//! Decision 0048 named three, which is what `receive` already sorts the world
//! into: `revision`, `operation` and `payload`. Decision 0056 adds the two
//! that decisions 0051 and 0053 put into the transferable set after it, and
//! the parting line between them is what historica can read:
//!
//! - **`rule`** is a file of `skipped/`. Historica owns that grammar, answers
//!   for it in `check`, and can therefore say which rules travel — so the
//!   listing states the shared ones and never the `private` ones, which makes
//!   it safe wherever it is pointed rather than only at an export.
//! - **`reserved`** is a file historica carries and cannot read: a file of a
//!   reserved directory whose class is [`Travel::TravelsAndUnions`]. One kind
//!   for the class rather than one per directory, because decision 0053's
//!   whole point is that transport never learns which directory it is holding
//!   — a token per reservation would be the per-tool special case that
//!   decision refused, in the grammar this time. The path carries the
//!   directory, and a fetcher asks its *own* registry what that directory's
//!   class is before writing a byte of it.
//!
//! A forgetting document is an `operation`: it lives in `operations/`, it is
//! written in one of the two grammars decision 0032 gave that directory, and
//! what parts it from its neighbours is the fourth field rather than the
//! first. A resolution is an `operation` for the same reason.
//!
//! # The fourth field
//!
//! **What an entry forgets** is decision 0014 travelling. A fetcher that took
//! a plain set difference would keep an original that an arriving forgetting
//! document destroys, so the listing states the relationship exactly as a
//! catalogue entry does (decision 0036) and the fetcher honours it without
//! opening anything. Only an `operation` can carry it: a revision document
//! forgets nothing, a payload has no grammar to say it in, a rule file's
//! grammar has no such key, and a `reserved` file is one nothing here has
//! read — decision 0054's deferred revocation is the reserving tool's to
//! define and to act on. All four are `-`.
//!
//! # What is listed, and what is not
//!
//! `historica.txt` and `format.txt` are neither listed nor fetched: a fetcher
//! has a store already, with its own, and a store that did not would have
//! nothing to fetch into. `names/` and `cache/` are not listed — for an export
//! that is an observation rather than a rule, since an export has neither, and
//! for a live store it is decision 0042's answer unchanged: bookmarks are the
//! publisher's and a cache is nobody's. Neither directory is walked, so a
//! store that has them costs a listing nothing.
//!
//! # What it costs, and what it does not write
//!
//! `operations/` is measured through decision 0036's catalogue, which already
//! holds a digest and a forgetting relationship per file and reads only what
//! `cache/` cannot account for — the property that keeps a history with
//! photographs in it from being hashed end to end on every publish. What that
//! catalogue is keyed by is a digest, so it collapses two files holding one
//! set of bytes to one path; the pass that *builds* it does not, and this
//! takes the pass, because a listing names every file at the path it is at.
//!
//! `revisions/` has no catalogue, and decision 0048 left the choice between
//! giving it one and walking it as a measurement rather than a design. It is
//! walked. A revision document is a few hundred bytes and there is one per
//! revision rather than one per file per revision, so the directory is the
//! small half of the store by construction — the store reads all of it at
//! `open` already, and what `open` does not keep is *where* each one is, which
//! is one walk away. A second index in `cache/` would buy back the hashing of
//! the cheapest files in the store and cost a second thing that can be stale.
//!
//! One claim here is believed rather than read, and it is the catalogue's:
//! where a digest is. A file somebody edited in place would be listed under
//! the digest it used to have. That costs a fetcher one wasted request and
//! cannot produce a wrong store, because nothing enters a store unverified —
//! which is decision 0048's own price for a listing it cannot check, paid on
//! this side of the wire instead.
//!
//! **The listing is written nowhere.** Not into the store and not beside it:
//! an enumeration living in `history/` would be derived mutable state going
//! stale next to the thing it describes, which is what decision 0030 refused
//! and what 0042 leaned on. This is a rendering, with the standing `log` and
//! `status` have, and the publisher redirects it — conventionally to
//! `offer.txt` beside the exported directory, written last, after `export` has
//! left a consistent copy. What the store may still refresh while producing it
//! is `cache/`, exactly as every other reading command does, which decision
//! 0035 makes disposable and 0036 makes silent about failing.
//!
//! [`Travel::TravelsAndUnions`]: super::Travel::TravelsAndUnions

use std::fmt;
use std::io;
use std::path::Path;

use crate::core::RevisionId;
use crate::fs::Filesystem;
use crate::working::SKIPPED_DIR;

use super::{
    REVISION_SUFFIXES, REVISIONS_DIR, STORE_DIR, Store, StoreError, catalogue, files_claiming,
    label_of, within,
};

/// The line a manifest starts with.
///
/// Numbered, for the reason the module documentation gives: a reader that does
/// not know this spelling discards the whole file rather than half-reading it,
/// and refetching costs one request.
pub const OFFER_HEADER: &str = "historica-offer-1";

/// What sort of file one line of a manifest names.
///
/// Decision 0048 named the first three and decision 0056 the last two. Not
/// exhaustive, because the set has grown once and a reader is expected to
/// discard a line it cannot classify rather than to refuse the manifest.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
pub enum OfferKind {
    /// A revision document: who recorded what, when, and after what.
    Revision,
    /// A content document of `operations/`, in either of decision 0032's
    /// grammars, and including the forgetting documents decision 0014 writes.
    Operation,
    /// Decision 0017's content that arrives whole, carrying no format.
    Payload,
    /// One file of `skipped/`, stating one rule that travels (decision 0051).
    Rule,
    /// A file of a reserved directory that travels and unions (decision 0053).
    ///
    /// One word for the class rather than one per directory: transport never
    /// learns whose the directory is, and neither does this listing. The path
    /// names the directory, and a reader consults its own registry about it.
    Reserved,
}

impl OfferKind {
    /// The word this kind is written as.
    pub fn as_str(self) -> &'static str {
        match self {
            OfferKind::Revision => "revision",
            OfferKind::Operation => "operation",
            OfferKind::Payload => "payload",
            OfferKind::Rule => "rule",
            OfferKind::Reserved => "reserved",
        }
    }

    /// The kind a word names, or nothing where a reader has met a spelling a
    /// later version writes and this one has never heard of.
    pub fn parse(word: &str) -> Option<Self> {
        Some(match word {
            "revision" => OfferKind::Revision,
            "operation" => OfferKind::Operation,
            "payload" => OfferKind::Payload,
            "rule" => OfferKind::Rule,
            "reserved" => OfferKind::Reserved,
            _ => return None,
        })
    }
}

impl fmt::Display for OfferKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// One transferable file, as a manifest names it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Offered {
    /// What sort of file it is.
    pub kind: OfferKind,
    /// The digest of its bytes, which is what a fetcher hashes it against.
    pub digest: RevisionId,
    /// What it forgets, for a forgetting document. `None` for everything else.
    pub forgets: Option<RevisionId>,
    /// Where it is, relative to the manifest's own directory.
    ///
    /// An address rather than a name (decision 0048): bytes land in the
    /// receiving store under its own digest-derived names, and `arrange` gives
    /// them readable ones there. So no two stores ever have to agree about a
    /// filename — which is just as well, since a store and a partial copy of
    /// it genuinely cannot.
    pub path: String,
}

impl fmt::Display for Offered {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} ", self.kind, self.digest)?;
        match self.forgets {
            Some(target) => write!(f, "{target} ")?,
            None => write!(f, "- ")?,
        }
        // Last, and written raw: decision 0043's convention is what stands in
        // for an escaping story.
        f.write_str(&self.path)
    }
}

/// The listing of one published copy's transferable files.
///
/// Rendered by [`fmt::Display`], which is the whole file: the header, the
/// heads, and one line per file.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Offer {
    heads: Vec<RevisionId>,
    entries: Vec<Offered>,
}

impl Offer {
    /// Every head the copy has, in digest order.
    pub fn heads(&self) -> &[RevisionId] {
        &self.heads
    }

    /// Every transferable file, in the order the manifest states them.
    ///
    /// **The order is specified**, rather than whatever a walk happened to
    /// produce. Two things want it. A manifest a publisher regenerates on a
    /// timer should be one set of bytes for one copy, so that a copy nothing
    /// has changed produces a file nothing has changed. And the groups are in
    /// decision 0048's fetch order — payloads, then documents, then revisions
    /// — so a fetcher working from the top understates what is reachable at
    /// every moment, rather than leaving a revision naming bytes that never
    /// arrived. Rules and the files of another tool come last: they are
    /// outside that invariant entirely, since no revision names them.
    ///
    /// Within a group the order is the path's, which is a walk's own order and
    /// stable for a given copy.
    pub fn entries(&self) -> &[Offered] {
        &self.entries
    }

    /// Every entry of one kind.
    pub fn of(&self, kind: OfferKind) -> impl Iterator<Item = &Offered> {
        self.entries.iter().filter(move |entry| entry.kind == kind)
    }
}

impl fmt::Display for Offer {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "{OFFER_HEADER}")?;
        for head in &self.heads {
            writeln!(f, "head {head}")?;
        }
        for entry in &self.entries {
            writeln!(f, "{entry}")?;
        }
        Ok(())
    }
}

impl<F: Filesystem> Store<F> {
    /// List every transferable file this store holds, for a reader that cannot
    /// walk the directory it is in.
    ///
    /// `prefix` is the name of the directory the manifest will sit beside —
    /// `store` for a manifest published next to a `store/` — and every path is
    /// written under it, because decision 0052 resolves a manifest's paths
    /// against the manifest's own directory. An empty prefix writes the paths
    /// from `history/` down, which is the same convention for a manifest
    /// published inside the copy's own root.
    ///
    /// Reads, and writes nothing anywhere. No `check` is run: a manifest
    /// describes what a directory holds rather than vouching for it, the
    /// command that leaves the copy consistent is `export`, and a fetcher
    /// hashes every arriving file regardless — so there is nothing here for a
    /// check to protect.
    pub fn offer(&self, prefix: &str) -> Result<Offer, StoreError> {
        // Decision 0036's pass, which reads only what `cache/` cannot account
        // for — and taken one entry per file rather than one per digest, since
        // an offer is a listing of a directory rather than a lookup.
        let mut payloads: Vec<Offered> = Vec::new();
        let mut documents: Vec<Offered> = Vec::new();
        for (id, filed) in catalogue::read(&self.files, &self.root, self.cached)?.filings {
            let entry = Offered {
                kind: match filed.document {
                    true => OfferKind::Operation,
                    false => OfferKind::Payload,
                },
                digest: id,
                // Only a document can forget, and only a document is ever
                // catalogued as forgetting.
                forgets: filed.forgets,
                path: addressed(prefix, &spelled(&filed.path)),
            };
            match filed.document {
                true => documents.push(entry),
                false => payloads.push(entry),
            }
        }

        // Walked and hashed, which is the measurement decision 0048 deferred:
        // these are the small files, the store reads all of them at `open`
        // regardless, and the only thing `open` does not keep is where each one
        // sits. Decision 0043 takes the digest in pieces, so nothing here is
        // held whole to be hashed.
        let mut revisions: Vec<Offered> = Vec::new();
        for path in files_claiming(&self.files, &self.root, REVISIONS_DIR, &REVISION_SUFFIXES)? {
            let Some(label) = label_of(&self.root, &path) else {
                continue;
            };
            let Some(digest) = digest_at(&self.files, &path)? else {
                continue;
            };
            revisions.push(Offered {
                kind: OfferKind::Revision,
                digest,
                forgets: None,
                path: addressed(prefix, &label),
            });
        }

        // Decision 0052 lists `skipped/` and gives the reason: an export's
        // holds shared rules and nothing else, so listing it is safe by
        // construction. This is pointed at a directory rather than told what
        // made it, so it applies decision 0051's axis itself rather than
        // assuming somebody already did — a `private` rule's *filename* is
        // derived from its text (decision 0045), and naming one in a listing
        // published to the world would be the disclosure 0051 wrote the key to
        // prevent. Every rule that travels is named; nothing else under
        // `skipped/` is, the note `init` leaves included, because a file
        // stating no rule states nothing a recipient needs.
        let mut rules: Vec<Offered> = Vec::new();
        let skipped = self.root.join(SKIPPED_DIR);
        for (rule, file) in self.skipped.stating() {
            if !rule.travels() {
                continue;
            }
            let Some(file) = file else { continue };
            let Some(digest) = digest_at(&self.files, &within(&skipped, file))? else {
                continue;
            };
            rules.push(Offered {
                kind: OfferKind::Rule,
                digest,
                forgets: None,
                path: addressed(prefix, &format!("{SKIPPED_DIR}/{file}")),
            });
        }

        // Decision 0053: found by the walk everything else is found by, and
        // never opened. The class is the whole of what this knows about them,
        // and the path is the whole of what it says.
        let mut reserved: Vec<Offered> = Vec::new();
        for label in self.travelling_files()? {
            let Some(digest) = digest_at(&self.files, &within(&self.root, &label))? else {
                continue;
            };
            reserved.push(Offered {
                kind: OfferKind::Reserved,
                digest,
                forgets: None,
                path: addressed(prefix, &label),
            });
        }

        // The order [`Offer::entries`] states: content first and revisions
        // last, which is `receive`'s order and a fetcher's, then the two kinds
        // no revision names.
        let mut entries: Vec<Offered> = Vec::new();
        for group in [
            &mut payloads,
            &mut documents,
            &mut revisions,
            &mut rules,
            &mut reserved,
        ] {
            group.sort_by(|left, right| left.path.cmp(&right.path));
            entries.append(group);
        }

        Ok(Offer {
            // The graph's heads, superseded ones included: a listing is not a
            // rendering, and every one of them answers relatedness.
            heads: self.history().heads().into_iter().collect(),
            entries,
        })
    }
}

/// One store-relative label, said as a fetcher will ask for it.
fn addressed(prefix: &str, label: &str) -> String {
    match prefix.is_empty() {
        true => format!("{STORE_DIR}/{label}"),
        false => format!("{prefix}/{STORE_DIR}/{label}"),
    }
}

/// One relative path, said with `/` for a separator.
///
/// A manifest is read on a machine that is not this one, so the separator is
/// the format's rather than the platform's — the rule decision 0033 already
/// applies to every path a document holds.
fn spelled(path: &Path) -> String {
    path.components()
        .map(|part| part.as_os_str().to_string_lossy())
        .collect::<Vec<_>>()
        .join("/")
}

/// What a file hashes to, or nothing where it is no longer there.
///
/// A listing is worked out from a walk rather than held under a lock, so a
/// file somebody removed in between is a file the next listing will not name.
/// Refusing to render the whole manifest over one of them would be a worse
/// answer than a manifest one line shorter.
fn digest_at<F: Filesystem + ?Sized>(
    files: &F,
    path: &Path,
) -> Result<Option<RevisionId>, StoreError> {
    match crate::fs::digest_of(files, path) {
        Ok(digest) => Ok(Some(digest)),
        Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(None),
        Err(error) => Err(StoreError::io(path, error)),
    }
}
