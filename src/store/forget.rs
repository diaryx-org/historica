//! `forget`: destroying an item's payload while preserving its shape.
//!
//! Decision 0014. An operation's arithmetic and an operation's payload are
//! different bytes, and only the payload has to be destroyed: a forgetting
//! document states the same operations, at the same positions, with the same
//! counts, and replaces the items it forgets with a `\ forgotten` marker.
//!
//! An item forgotten once is forgotten everywhere it is quoted — the insert
//! that wrote it, and every delete that quotes it back so replay can check
//! itself — so `forget` is a walk over a file's history rather than an edit
//! to one document. That walk is [`crate::merge::quotes`], and the cost is
//! real: finding the deletes that quote a run means replaying the file.
//!
//! Decision 0066 adds the other extent, and it is the cheap one. A payload of
//! bytes has no items, no grammar and no chain (0017), so there is no shape
//! to preserve and no walk to make: a payload is quoted by its digest, so
//! destroying the one file destroys every quote of it at once, and what
//! stands in its place says which digest went and how long it was.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::path::{Path, PathBuf};

use crate::core::{FileId, RevisionId};
use crate::format::{OperationDocument, Piece};
use crate::fs::Filesystem;
use crate::merge::{self, MergeError, Quoted};
use crate::tree::Kind;

use super::{
    Body, MaterialiseError, OPERATION_SUFFIX, OPERATION_SUFFIXES, OPERATIONS_DIR, Store,
    StoreError, files_claiming, payload_files, prune::remove_empty_directories,
};

/// What a person asks to forget: some of one file, at one revision.
#[derive(Debug, Clone)]
pub struct Forgetting {
    /// The revision the file is read at.
    pub revision: RevisionId,
    /// The file.
    pub file: FileId,
    /// How much of it goes.
    pub extent: Extent,
}

/// How much of a file one forgetting destroys.
///
/// Which of these a file takes is not a choice: decision 0017 fixes a file's
/// kind when it is added, so the tool already knows whether the thing in
/// front of it has lines to count. Asking for the other one is an error that
/// names the spelling that would have worked.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Extent {
    /// A span of lines, of a file that has them.
    ///
    /// Lines rather than items, because a person counts what `cat` shows
    /// them; one-based, because every editor they have ever used is.
    Lines {
        /// The first line of the span, one-based.
        first: usize,
        /// The last line of the span, inclusive.
        last: usize,
    },
    /// The whole content of a file of bytes, which is the only extent one
    /// has: decision 0017 gives a payload no items, so there is nothing
    /// smaller to name and nothing left over to keep.
    Whole,
}

/// What forgetting destroys, and what stands in for it.
///
/// [`Store::forget`] acts on exactly this, so `--dry-run` and the real thing
/// can never describe different bytes.
#[derive(Debug, Clone, Default)]
pub struct Forgotten {
    /// The digests whose bytes are destroyed.
    pub targets: Vec<RevisionId>,
    /// The forgetting documents written, one per destroyed digest that did
    /// not already have an equally thorough stand-in, each in the grammar of
    /// the document it stands in for.
    pub writes: Vec<Body>,
    /// Every file destroyed, relative to the store root.
    pub destroys: Vec<PathBuf>,
    /// How much of what was asked for was already forgotten: one per item of
    /// a span that was, or one for a payload whose bytes are already gone.
    pub already: usize,
    /// Other content the same file holds elsewhere in its history, which this
    /// forgetting does not touch.
    ///
    /// Decision 0066: a file of bytes is replaced whole, so each version of
    /// it is its own payload under its own digest, and forgetting the
    /// photograph at one revision leaves every other one legible. That is
    /// 0014's rule that redaction is per item rather than per file, arriving
    /// where a person is least likely to expect it, so it is counted here and
    /// said out loud.
    pub elsewhere: Vec<RevisionId>,
}

impl Forgotten {
    /// Whether forgetting would touch nothing, which forgetting twice does.
    pub fn is_empty(&self) -> bool {
        self.writes.is_empty() && self.destroys.is_empty()
    }
}

impl<F: Filesystem> Store<F> {
    /// What forgetting this would destroy, without destroying anything.
    ///
    /// The two extents meet here and nowhere else. A file's kind decides
    /// which is even askable, so a request for the other one is refused
    /// before anything is read — and the walk over the directory that finds
    /// the bytes to destroy is one walk, whichever extent named them.
    pub fn forget_plan(&self, forgetting: &Forgetting) -> Result<Forgotten, ForgetError> {
        let tree = self.tree(&forgetting.revision)?;
        let entry = tree
            .entry(&forgetting.file)
            .ok_or(MaterialiseError::NoSuchFile {
                file: forgetting.file,
            })?;
        let mut plan = match (forgetting.extent, entry.kind) {
            (Extent::Lines { first, last }, Kind::Lines) => {
                self.forget_lines(forgetting, first, last)?
            }
            (Extent::Whole, Kind::Whole) => self.forget_whole(forgetting, entry.payload)?,
            // Decision 0017 fixed the kind when the file was added, so this
            // is not a guess about content: it is the store saying what this
            // file is, and the spelling that would have worked.
            (Extent::Lines { .. }, Kind::Whole) => {
                return Err(ForgetError::NotLines {
                    file: forgetting.file,
                });
            }
            (Extent::Whole, Kind::Lines) => {
                return Err(ForgetError::NotWhole {
                    file: forgetting.file,
                    lines: self.content(&forgetting.revision, &forgetting.file)?.len(),
                });
            }
            // Decision 0040: a link holds no content at all. Where it points
            // is a revision-document fact, which is the path case 0014
            // defers, and for the same reason: a revision cannot be rewritten.
            (_, Kind::Link) => {
                return Err(ForgetError::IsALink {
                    file: forgetting.file,
                });
            }
        };

        // Every file whose bytes are a destroyed digest, found by content as
        // everything in a store is.
        let files = self.filesystem();
        for path in files_claiming(files, &self.root, OPERATIONS_DIR, &OPERATION_SUFFIXES)?
            .into_iter()
            .chain(payload_files(files, &self.root)?)
        {
            // Decision 0043: found by content, and content is what it hashes
            // to — so the bytes about to be destroyed are not held in order to
            // decide that they should be.
            let id =
                crate::fs::digest_of(files, &path).map_err(|error| StoreError::io(&path, error))?;
            if plan.targets.contains(&id) {
                plan.destroys.push(self.relative(&path));
            }
        }
        Ok(plan)
    }

    /// What forgetting a payload of bytes would destroy.
    ///
    /// Decision 0066. There is no shape to preserve and no arithmetic to
    /// restate, so the stand-in is two headers: the digest whose bytes were
    /// destroyed, and how many of them there were.
    fn forget_whole(
        &self,
        forgetting: &Forgetting,
        payload: Option<RevisionId>,
    ) -> Result<Forgotten, ForgetError> {
        let target = payload.ok_or(MaterialiseError::ContestedContent {
            file: forgetting.file,
        })?;
        let mut plan = Forgotten {
            elsewhere: self.other_payloads(&forgetting.file, &target)?,
            ..Forgotten::default()
        };
        // Measured rather than read: what the stand-in states is a count, and
        // decision 0043's rule is that a file nobody wants is not held in
        // memory to be asked a question about.
        let held = self.measure(&target)?;
        let standing = self.forgotten_payload(&target)?;
        let Some(length) = held.or_else(|| standing.map(|document| document.length)) else {
            // Neither the bytes nor a record of them: there is nothing here
            // to destroy, and nothing here that could say how much there was.
            return Err(ForgetError::MissingPayload { payload: target });
        };
        if held.is_none() {
            // Already forgotten, which forgetting twice is. Every quote of a
            // payload is its digest, so one destruction covered them all.
            plan.already = 1;
            return Ok(plan);
        }
        plan.targets.push(target);
        let document = crate::format::ForgottenPayload {
            forgets: target,
            length,
        };
        // A stand-in the store already holds says everything this would, and
        // the bytes beside it are what `check` calls resurrection: destroy
        // them, and write nothing twice.
        if standing != Some(document) {
            plan.writes.push(Body::Forgotten(document));
        }
        Ok(plan)
    }

    /// Where a stand-in for a destroyed payload goes: the name the payload
    /// had, plus the suffix that says this one is a document.
    ///
    /// Decision 0016 files what a revision did under that revision, at the
    /// path each file had, and 0017 puts payloads there under the file's own
    /// name. So a person who opens a revision's folder looking for the
    /// photograph should find an answer at the name they were looking for
    /// rather than an absence — and the extension, which is the one thing
    /// that tells a document from a payload, is kept whatever else happens to
    /// the name.
    ///
    /// `None` where the name is taken or the payload sat somewhere this
    /// cannot describe, which sends the document to its digest instead: the
    /// one name nothing else can claim, and where `forget` filed every
    /// stand-in before this.
    fn beside_destroyed(&self, destroyed: &[PathBuf]) -> Result<Option<String>, ForgetError> {
        let operations = self.root.join(OPERATIONS_DIR);
        let Some(name) = destroyed
            .first()
            .and_then(|relative| super::label_of(&operations, &self.root.join(relative)))
        else {
            return Ok(None);
        };
        let name = format!("{name}{OPERATION_SUFFIX}");
        let taken = self
            .filesystem()
            .look(&super::within(&operations, &name))
            .map_err(|error| StoreError::io(&operations, error))?;
        Ok(taken.is_none().then_some(name))
    }

    /// How long a payload this store holds is, or `None` if it holds none.
    ///
    /// The catalogue says where the digest is and is asked first; what it
    /// cannot be believed about is *nothing here has these bytes*, so an
    /// absence pays for the walk, exactly as [`Store::payload`] arranges it.
    fn measure(&self, target: &RevisionId) -> Result<Option<usize>, ForgetError> {
        if let Some(path) = self.payloads()?.get(target).cloned()
            && let Some(length) = self.measured(&path, target)?
        {
            return Ok(Some(length));
        }
        for path in payload_files(self.filesystem(), &self.root)? {
            if let Some(length) = self.measured(&path, target)? {
                return Ok(Some(length));
            }
        }
        Ok(None)
    }

    /// How long one file is, if it is the digest asked for.
    ///
    /// Decision 0043 in both halves: the file is hashed in pieces rather than
    /// held, and it is counted in the same pass — so measuring a payload
    /// before destroying it never reads the bytes into memory, however large
    /// the thing about to go is.
    fn measured(&self, path: &Path, target: &RevisionId) -> Result<Option<usize>, ForgetError> {
        let files = self.filesystem();
        let mut hasher = crate::format::Hasher::new();
        let mut length = 0;
        let streamed = match files.read_in_pieces(path, &mut |piece| {
            hasher.update(piece);
            length += piece.len();
        }) {
            Ok(streamed) => streamed,
            // The file the catalogue named and the directory has since lost,
            // which is a file this store does not hold.
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(None),
            Err(error) => return Err(StoreError::io(path, error).into()),
        };
        if streamed.is_none() {
            let bytes = files
                .read(path)
                .map_err(|error| StoreError::io(path, error))?;
            hasher.update(&bytes);
            length = bytes.len();
        }
        Ok((hasher.finish() == *target).then_some(length))
    }

    /// Every other payload the same file holds, that this store still has.
    fn other_payloads(
        &self,
        file: &FileId,
        target: &RevisionId,
    ) -> Result<Vec<RevisionId>, ForgetError> {
        let mut others: BTreeSet<RevisionId> = BTreeSet::new();
        for (_, document) in self.documents()? {
            if let Some(named) = document.bytes.get(file)
                && named != target
                && self.forgotten_payload(named)?.is_none()
            {
                others.insert(*named);
            }
        }
        Ok(others.into_iter().collect())
    }

    /// What forgetting a span of lines would destroy.
    fn forget_lines(
        &self,
        forgetting: &Forgetting,
        first: usize,
        last: usize,
    ) -> Result<Forgotten, ForgetError> {
        if first == 0 || last < first {
            return Err(ForgetError::NotASpan { first, last });
        }

        // The span, named: the file at that revision, and the identity of
        // each visible item in it — which revision wrote it, and where in
        // that revision's document.
        let reachable = self.reachable(&forgetting.revision)?;
        let at_revision = self.quotes_over(&reachable, &forgetting.file)?;
        let visible: Vec<&Quoted> = at_revision.iter().filter(|quoted| quoted.visible).collect();
        if last > visible.len() {
            return Err(ForgetError::PastTheEnd {
                last,
                lines: visible.len(),
            });
        }
        let mut span: BTreeSet<(RevisionId, usize, usize)> = visible[first - 1..last]
            .iter()
            .map(|quoted| (quoted.written_by, quoted.write.0, quoted.write.1))
            .collect();

        // Every quote of those items, across the whole history this store
        // holds — the deletes included, which is the walk's whole point.
        let every: Vec<(RevisionId, &crate::format::RevisionDocument)> = self
            .documents()?
            .into_iter()
            .map(|(id, document)| (*id, document))
            .collect();
        let everywhere = self.quotes_over(&every, &forgetting.file)?;

        copies_into(&mut span, &everywhere);

        // The document each revision names for this file, which is what the
        // quote indices index into.
        let named: BTreeMap<RevisionId, RevisionId> = every
            .iter()
            .filter_map(|(id, document)| {
                document
                    .edited
                    .get(&forgetting.file)
                    .or_else(|| document.text.get(&forgetting.file))
                    .map(|names| (*id, *names))
            })
            .collect();

        let mut items: BTreeMap<RevisionId, BTreeSet<(usize, usize)>> = BTreeMap::new();
        let mut already = 0;
        for quoted in &everywhere {
            if !span.contains(&(quoted.written_by, quoted.write.0, quoted.write.1)) {
                continue;
            }
            if quoted.forgotten {
                already += 1;
            }
            if let Some(target) = named.get(&quoted.written_by) {
                items.entry(*target).or_default().insert(quoted.write);
            }
            for (revision, operation, item) in &quoted.deletes {
                if let Some(target) = named.get(revision) {
                    items
                        .entry(*target)
                        .or_default()
                        .insert((*operation, *item));
                }
            }
        }

        // One forgetting document per destroyed digest, skipped where the
        // stand-ins the store already holds say everything this would.
        let mut plan = Forgotten {
            already,
            ..Forgotten::default()
        };
        for (target, forget) in &items {
            plan.targets.push(*target);
            // Decision 0032 gave `operations/` two grammars, and a stand-in
            // must have the shape of what it stands in for, so which one this
            // digest is written in decides which one is written here.
            if let Some(base) = self.effective_resolution(target)? {
                let mut document = base.clone();
                document.forgets = Some(*target);
                // Decision 0031's rule, and 0014's reason for it: the file
                // this assembles is now the destroyed state, and a digest
                // would confirm a guess at it.
                document.result = None;
                for (piece, item) in forget {
                    // Only an `insert` mints, and only what a document minted
                    // is its own to destroy. A `keep` carries a reference and
                    // no text, and is redacted where its items were written.
                    if let Some(Piece::Insert { items }) = document.pieces.get_mut(*piece) {
                        let held = &mut items[*item];
                        if !held.forgotten {
                            *held = held.forgetting();
                        }
                    }
                }
                let mut said = base;
                said.forgets = document.forgets;
                said.result = None;
                if document != said {
                    plan.writes.push(Body::Resolution(document));
                }
                continue;
            }
            let base = self
                .effective_operation(target)?
                .or_else(|| self.creation_base(target))
                .ok_or(ForgetError::MissingQuoted { document: *target })?;
            let mut document = base.clone();
            document.forgets = Some(*target);
            // Decision 0031: a forgetting document states no result. The
            // base's result names the destroyed state, and a digest of
            // destroyed content would confirm a guess at it.
            document.result = None;
            for (operation, item) in forget {
                let held = &mut document.operations[*operation].items[*item];
                if !held.forgotten {
                    *held = held.forgetting();
                }
            }
            let mut said = base;
            said.forgets = document.forgets;
            if document != said {
                plan.writes.push(Body::Operation(document));
            }
        }

        Ok(plan)
    }

    /// Forget a span: write the stand-ins, then destroy the originals.
    ///
    /// In that order, so an interruption leaves a store holding both a
    /// document and a forgetting document naming it — the state `check`
    /// calls resurrection and syncing already produces — rather than a store
    /// that destroyed bytes and recorded nothing about them.
    pub fn forget(&mut self, forgetting: &Forgetting) -> Result<Forgotten, ForgetError> {
        let plan = self.forget_plan(forgetting)?;
        for document in &plan.writes {
            match document {
                Body::Operation(document) => self.insert_operation(document)?,
                Body::Resolution(document) => {
                    let id = crate::format::digest(&document.write());
                    self.insert_resolution_at(document, &format!("{id}{OPERATION_SUFFIX}"))?
                }
                Body::Forgotten(document) => {
                    let id = document.id();
                    let name = self
                        .beside_destroyed(&plan.destroys)?
                        .unwrap_or_else(|| format!("{id}{OPERATION_SUFFIX}"));
                    self.insert_forgotten_payload_at(document, &name)?
                }
            };
        }
        for relative in &plan.destroys {
            let path = self.root.join(relative);
            self.filesystem()
                .remove_file(&path)
                .map_err(|error| StoreError::io(&path, error))?;
        }
        for target in &plan.targets {
            self.catalogue_mut()?.remove(target);
        }
        // The payload index maps digests to paths that may just have gone.
        self.forget_catalogue();
        // Decision 0014 destroys bytes, and `cache/` is where copies of them
        // would be. Everything there is replayable, so this loses nothing
        // that forgetting was not meant to take.
        self.clear_cache();
        remove_empty_directories(self.filesystem(), &self.root.join(OPERATIONS_DIR))?;
        Ok(plan)
    }

    /// Every item every revision ever wrote to one file, quotes and all.
    fn quotes_over(
        &self,
        documents: &[(RevisionId, &crate::format::RevisionDocument)],
        file: &FileId,
    ) -> Result<Vec<Quoted>, ForgetError> {
        let held = self.effective_for(documents, file)?;
        let events: Vec<merge::Event<'_>> = documents
            .iter()
            .map(|(revision, document)| {
                let parents = document.parents.iter().copied().collect();
                match held.get(revision) {
                    Some(stated) => stated.event(*revision, parents),
                    None => merge::Event::nothing(*revision, parents),
                }
            })
            .collect();
        Ok(merge::quotes(events)?)
    }

    /// The creation document standing behind a `text` payload digest, if the
    /// digest is one.
    fn creation_base(&self, target: &RevisionId) -> Option<OperationDocument> {
        let named_by = self
            .documents()
            .ok()?
            .into_iter()
            .find(|(_, document)| document.text.values().any(|payload| payload == target))
            .map(|(id, _)| *id)?;
        self.creation_for(target, named_by).ok().flatten()
    }
}

/// Grow a span to hold every copy a resolution made of an item in it.
///
/// Decision 0032 states a merge's file as references, and says why: "a
/// restated line would be a new item, and the first merge reaching across
/// this one would meet the same text twice." A resolution cannot reorder the
/// items it keeps — the walk records which survive, never where they go — so
/// a person who moves a run while resolving leaves the recorder no way to
/// name it, and it is minted again under the resolution's own name.
///
/// That copy is the same text with a different name, which is exactly what
/// forgetting must not miss: redacting the original alone destroys the bytes,
/// passes `check`, and leaves the text readable at the head.
///
/// The pairing is narrow on purpose. Only an item *this* resolution dropped
/// is matched against what *this* resolution minted, so a line that reads the
/// same because somebody typed it again is a different item and stays one —
/// which is decision 0014's rule that redaction is per item, not per text. To
/// a fixpoint, because a later merge can copy the copy.
fn copies_into(span: &mut BTreeSet<(RevisionId, usize, usize)>, everywhere: &[Quoted]) {
    loop {
        let mut grew = false;
        for quoted in everywhere {
            if !span.contains(&(quoted.written_by, quoted.write.0, quoted.write.1)) {
                continue;
            }
            // An item already forgotten has no text to have been copied, and
            // nothing to match a copy against.
            if quoted.forgotten {
                continue;
            }
            for dropped_by in &quoted.dropped_by {
                for candidate in everywhere {
                    // What a merge wrote is what its resolution minted: a
                    // kept item is still written by whoever wrote it.
                    if candidate.written_by != *dropped_by || candidate.text != quoted.text {
                        continue;
                    }
                    let name = (candidate.written_by, candidate.write.0, candidate.write.1);
                    grew |= span.insert(name);
                }
            }
        }
        if !grew {
            return;
        }
    }
}

/// Why nothing was forgotten.
#[derive(Debug)]
#[non_exhaustive]
pub enum ForgetError {
    /// A span that names no lines.
    NotASpan {
        /// The first line, as given.
        first: usize,
        /// The last line, as given.
        last: usize,
    },
    /// A span past the end of the file.
    PastTheEnd {
        /// The last line asked for.
        last: usize,
        /// How many lines the file has there.
        lines: usize,
    },
    /// A span asked of a file of bytes, which has no lines to count.
    NotLines {
        /// The file.
        file: FileId,
    },
    /// A whole file asked of a file of lines, which is forgotten by span.
    NotWhole {
        /// The file.
        file: FileId,
        /// How many lines it has at that revision, so the refusal can name
        /// the span that would have covered all of them.
        lines: usize,
    },
    /// A file that is a link, whose target is a revision-document fact.
    IsALink {
        /// The file.
        file: FileId,
    },
    /// A payload this store neither holds nor has a record of destroying.
    MissingPayload {
        /// The payload.
        payload: RevisionId,
    },
    /// A quoted document this store holds nothing of, so there is nothing to
    /// preserve the shape of.
    MissingQuoted {
        /// The document.
        document: RevisionId,
    },
    /// The file's history could not be materialised.
    Materialise(Box<MaterialiseError>),
    /// The file's history could not be merged.
    Merge(Box<MergeError>),
    /// The store could not be read or written.
    Store(StoreError),
}

impl From<MaterialiseError> for ForgetError {
    fn from(error: MaterialiseError) -> Self {
        Self::Materialise(Box::new(error))
    }
}

impl From<MergeError> for ForgetError {
    fn from(error: MergeError) -> Self {
        Self::Merge(Box::new(error))
    }
}

impl From<StoreError> for ForgetError {
    fn from(error: StoreError) -> Self {
        Self::Store(error)
    }
}

impl fmt::Display for ForgetError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ForgetError::NotASpan { first, last } => write!(
                f,
                "lines {first}..{last} name no span: lines count from 1, and \
                 the last is not before the first"
            ),
            ForgetError::PastTheEnd { last, lines } => write!(
                f,
                "the file has {lines} lines there, and line {last} is past \
                 the end of it"
            ),
            ForgetError::NotLines { file } => write!(
                f,
                "the file {file} is bytes rather than lines, so a span names \
                 nothing in it; forgetting it without a span destroys the \
                 whole of what it holds there, which is all a file of bytes \
                 has"
            ),
            ForgetError::NotWhole { file, lines } => write!(
                f,
                "the file {file} is lines rather than bytes, and a redaction \
                 is exact: name the span, as `--lines <first>..<last>`. It \
                 has {lines} lines there, so `--lines 1..{lines}` is all of \
                 them"
            ),
            ForgetError::IsALink { file } => write!(
                f,
                "the file {file} is a link, and holds no content to destroy: \
                 where it points is stated in the revision document, which is \
                 the one thing an append-only store cannot rewrite"
            ),
            ForgetError::MissingPayload { payload } => write!(
                f,
                "this store does not hold the content {payload}, and has no \
                 record of destroying it; there is nothing here to forget"
            ),
            ForgetError::MissingQuoted { document } => write!(
                f,
                "the span is quoted in {document}, which this store does not \
                 hold yet; forgetting preserves a document's shape, and the \
                 shape has not arrived"
            ),
            ForgetError::Materialise(error) => error.fmt(f),
            ForgetError::Merge(error) => error.fmt(f),
            ForgetError::Store(error) => error.fmt(f),
        }
    }
}

impl std::error::Error for ForgetError {}
