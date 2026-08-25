//! What `check` says, and what it refuses to make a fuss about.
//!
//! Decision 0006 splits the report in two. **Errors** mean the store
//! contradicts itself and cannot be trusted. **Notes** are observations that
//! never fail, because a store that is merely mid-sync, or tidy in a way the
//! default writer is not, is doing nothing wrong.
//!
//! The division matters more than the contents: a `check` that failed on
//! legitimate states would teach people to ignore it, and then it would not be
//! worth running in anger.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::fmt::Write as _;
use std::path::{Path, PathBuf};

use crate::core::{FileId, RevisionId};
use crate::format::{
    self, OperationDocument, ParseError, ResolutionDocument, RevisionDocument, digest,
};
use crate::fs::{Entry, Filesystem, read_to_string};
use crate::replay::ReplayError;

use super::{
    HEADER_FILE, Held, MalformedName, MaterialiseError, NAME_SUFFIX, Name, OPERATION_SUFFIX,
    OPERATION_SUFFIXES, OPERATIONS_DIR, REVISION_SUFFIX, REVISION_SUFFIXES, REVISIONS_DIR, claims,
    platform_name,
};

/// Whether a finding means the store is broken or merely worth mentioning.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Severity {
    /// The store contradicts itself.
    Error,
    /// An observation that never fails.
    Note,
}

/// One thing `check` found.
#[derive(Debug)]
#[non_exhaustive]
pub enum Finding {
    /// A revision document did not parse.
    Unparsable {
        /// The file it was read from.
        file: PathBuf,
        /// Why it was refused.
        error: ParseError,
    },
    /// No `historica` file, or one naming a format this reader lacks.
    UnreadableStore {
        /// What the header said, if it said anything.
        found: Option<String>,
    },
    /// A filename that claims a digest states the wrong one.
    FilenameLies {
        /// The offending file.
        file: PathBuf,
        /// The digest its name claims.
        claimed: RevisionId,
        /// The digest its bytes actually have.
        actual: RevisionId,
    },
    /// Two files hash alike and differ in bytes, which cannot happen.
    ImpossibleCollision {
        /// The digest both files produced.
        id: RevisionId,
        /// The files in question.
        files: Vec<PathBuf>,
    },
    /// A file of `skipped/` was not one rule, which would silently record
    /// what it names.
    MalformedSkipped {
        /// The file.
        file: PathBuf,
        /// Which line, and what was wanted there.
        error: crate::working::MalformedSkip,
    },
    /// A rule covers a file the tree already holds, so `record` refuses.
    ///
    /// Decision 0045: rules union and never conflict, which means a rule can
    /// arrive by `receive` without passing the refusal `skip` makes before
    /// writing one. Deleting the file that states it is the whole fix, so the
    /// finding names that file.
    RuleCoversTracked {
        /// The file of `skipped/` stating the rule.
        file: PathBuf,
        /// The rule, as its file states it.
        rule: String,
        /// A path it covers that the history holds.
        path: String,
    },
    /// Two files of `skipped/` state one rule.
    DuplicateRule {
        /// The rule both state.
        rule: String,
        /// The files stating it.
        files: Vec<PathBuf>,
    },
    /// A `skipped.txt` beside the store, which nothing reads.
    StaleSkipped {
        /// The file.
        file: PathBuf,
    },
    /// A file still stating `skip-suffix`, which decision 0051 retired.
    ///
    /// Worth more than "unknown key", which is all the loader can say, because
    /// there is an exact replacement and this can spell it.
    RetiredRule {
        /// The file.
        file: PathBuf,
        /// The line that says the same thing.
        replacement: String,
    },
    /// One path covered both privately and shared.
    ///
    /// Decision 0051: the two are separate rules, so a union takes both, so
    /// the path is named in an export and the private rule accomplished
    /// nothing. Privacy defeated by addition is the one contradiction this
    /// format resolves by naming rather than by taking both, and the fix is
    /// deleting whichever file the person did not mean.
    PrivateAndShared {
        /// The value both rules name.
        value: String,
        /// The file stating the private rule.
        private: PathBuf,
        /// The file stating the shared rule.
        shared: PathBuf,
    },
    /// A bookmark was not one valid line.
    MalformedBookmark {
        /// The bookmark file.
        file: PathBuf,
    },
    /// A file could not be read at all.
    Unreadable {
        /// The file.
        file: PathBuf,
        /// What the filesystem said.
        reason: String,
    },
    /// A `parent` digest naming no file in this store.
    MissingParent {
        /// The parent nothing here holds.
        parent: RevisionId,
        /// A revision that names it.
        named_by: RevisionId,
    },
    /// Work standing on a revision something has since superseded.
    ///
    /// Decision 0023, amended: supersession is a statement about one change's
    /// revisions and does not travel along parent edges, so a rewrite reaches
    /// what was rewritten and nothing built on it. `amend` refuses to make
    /// this state and `receive` delivers it anyway — one replica rewrote a
    /// revision, another built on it, and a union holds both. Nothing else
    /// here would say so: both lines are ordinary heads, and merging them
    /// would ask a person to resolve content that was never concurrent,
    /// because a rewrite mints its own items for lines its predecessor
    /// already minted.
    ///
    /// A note, because the store contradicts nothing — every document parses,
    /// hashes and replays. What it lacks is the rest of the rewrite.
    StandsOnSuperseded {
        /// The revision nothing supersedes, standing on one something does.
        revision: RevisionId,
        /// The parent that was withdrawn.
        superseded: RevisionId,
        /// What withdrew it, which is where the work belongs instead.
        successors: BTreeSet<RevisionId>,
    },
    /// A bookmark naming a change or revision this store does not hold.
    DanglingBookmark {
        /// The bookmark.
        name: String,
        /// What it points at.
        target: Name,
    },
    /// One revision stored under more than one filename.
    DuplicateContent {
        /// The revision.
        id: RevisionId,
        /// Every file holding it.
        files: Vec<PathBuf>,
    },
    /// A symbolic link where a document would be, which the walk never follows.
    Unfollowed {
        /// The link.
        file: PathBuf,
    },
    /// A file under `revisions/` or `operations/` that claimed to be neither.
    ForeignFile {
        /// The file.
        file: PathBuf,
    },
    /// An `edit` naming an operation document this store does not hold.
    MissingOperations {
        /// The document nothing here holds.
        document: RevisionId,
        /// A revision that names it.
        named_by: RevisionId,
    },
    /// A `text` or `bytes` header naming content this store does not hold.
    MissingPayload {
        /// The payload nothing here holds.
        payload: RevisionId,
        /// A revision that names it.
        named_by: RevisionId,
    },
    /// A file in `operations/` that no revision names as content.
    UnnamedPayload {
        /// The file.
        file: PathBuf,
    },
    /// A `text` payload holding bytes no operation document could quote.
    ///
    /// An error rather than a note: decision 0017 makes UTF-8 the format's own
    /// rule for a file of lines, because a later `edit` has to quote its
    /// items, so this is the store contradicting itself.
    PayloadNotText {
        /// The payload.
        payload: RevisionId,
        /// A revision that names it.
        named_by: RevisionId,
    },
    /// A revision that could not be applied to its parent's file set.
    TreeDisagrees {
        /// The revision that would not apply.
        revision: RevisionId,
        /// What went wrong, as the tree explains it.
        because: String,
    },
    /// An operation document that disagrees with the file it claims to edit.
    ///
    /// The error decision 0007 asked for by name: a `delete` whose recorded
    /// lines are not the parent's is the store contradicting itself, caught
    /// at the moment of replay rather than absorbed into a merge.
    ContentDisagrees {
        /// The revision naming the document.
        revision: RevisionId,
        /// The file it claims to edit.
        file: FileId,
        /// What went wrong, as the replayer explains it.
        because: String,
    },
    /// A document whose bytes were destroyed, with a forgetting document
    /// standing in for it.
    ///
    /// A note, per decision 0014: the destruction is a recorded fact carried
    /// out, and `check` can only do its accounting because the store says
    /// which documents are *forgotten* rather than *lost* or *corrupt*.
    Forgotten {
        /// The destroyed document.
        document: RevisionId,
        /// A revision that names it.
        named_by: RevisionId,
    },
    /// A document and a forgetting document naming it, both held.
    ///
    /// Decision 0013's deferred resurrection, arriving by sync: a pruned or
    /// forgotten file that returns is not an error, and the union rule means
    /// the redaction still wins.
    Resurrected {
        /// The document whose bytes are back.
        document: RevisionId,
    },
    /// A merge naming a resolution for a file its parents already agree about.
    ///
    /// Decision 0032: a resolution states what a merge decided between two
    /// different states, and where there was one state there was nothing to
    /// decide. A reader following the agreement and a reader following the
    /// resolution would get different files, which is the store contradicting
    /// itself.
    ResolvedWithoutDisagreement {
        /// The merge.
        revision: RevisionId,
        /// The file both parents leave identically.
        file: FileId,
    },
    /// A merge whose parents differ about a file, stating no resolution.
    ///
    /// A note rather than an error: this tool never writes one, but a store
    /// is a folder anyone may write, and a hand that omitted the resolution
    /// has understated rather than contradicted itself. What the omission
    /// costs is the thing decision 0032 bought — materialising this file
    /// past this merge needs a correct implementation of the merge
    /// algorithm rather than arithmetic.
    UnstatedMerge {
        /// The merge.
        revision: RevisionId,
        /// The file its parents disagree about.
        file: FileId,
    },
    /// A `keep` naming a document this store does not hold.
    ///
    /// A note on the same terms as a missing operation document: transport
    /// having more to deliver is ordinary, and a resolution is not
    /// self-contained prose — reading one means opening the documents it
    /// names.
    MissingReference {
        /// The document nothing here holds.
        document: RevisionId,
        /// The resolution that keeps items of it.
        named_by: RevisionId,
    },
    /// A document still quoting items another document says were destroyed.
    ///
    /// Mid-sync is a legitimate way to be in this state — a redaction that
    /// has not finished arriving — and decision 0006's division is not worth
    /// breaking for it.
    StillQuoted {
        /// The document still holding the bytes.
        document: RevisionId,
        /// The document whose destruction it undercuts.
        forgets: RevisionId,
    },
    /// A head whose history is not all here, so nothing can produce it.
    ///
    /// A note, because every reason for it is one: a missing parent, an
    /// undelivered operation document, a payload still in transit. What this
    /// adds to those is the consequence they leave a person to work out — that
    /// `files`, `cat`, and `update` cannot answer for this head until the rest
    /// arrives, and that the readable files are not yet the authority for
    /// anything at its tip.
    ///
    /// `check --complete` is the caller who wants this to fail: a sync that
    /// should have finished, a backup about to be trusted, a store about to be
    /// carried somewhere the other half of it is not.
    Incomplete {
        /// The head that cannot be produced.
        head: RevisionId,
        /// Every digest its history names and this store does not hold.
        missing: BTreeSet<RevisionId>,
    },
}

impl Finding {
    /// Whether this finding makes `check` fail.
    pub fn severity(&self) -> Severity {
        match self {
            Finding::Unparsable { .. }
            | Finding::UnreadableStore { .. }
            | Finding::FilenameLies { .. }
            | Finding::ImpossibleCollision { .. }
            | Finding::MalformedBookmark { .. }
            | Finding::Unreadable { .. }
            | Finding::TreeDisagrees { .. }
            | Finding::ContentDisagrees { .. }
            | Finding::PayloadNotText { .. }
            | Finding::ResolvedWithoutDisagreement { .. }
            | Finding::MalformedSkipped { .. }
            | Finding::RuleCoversTracked { .. }
            | Finding::StaleSkipped { .. }
            | Finding::RetiredRule { .. }
            | Finding::PrivateAndShared { .. } => Severity::Error,
            Finding::MissingParent { .. }
            | Finding::StandsOnSuperseded { .. }
            | Finding::DanglingBookmark { .. }
            | Finding::DuplicateContent { .. }
            | Finding::ForeignFile { .. }
            | Finding::Unfollowed { .. }
            | Finding::MissingOperations { .. }
            | Finding::MissingPayload { .. }
            | Finding::UnnamedPayload { .. }
            | Finding::Forgotten { .. }
            | Finding::Resurrected { .. }
            | Finding::UnstatedMerge { .. }
            | Finding::MissingReference { .. }
            | Finding::StillQuoted { .. }
            | Finding::DuplicateRule { .. }
            | Finding::Incomplete { .. } => Severity::Note,
        }
    }
}

impl fmt::Display for Finding {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Finding::Unparsable { file, error } => write!(f, "{}: {error}", file.display()),
            Finding::UnreadableStore { found: Some(found) } => write!(
                f,
                "this store says `{found}` and this reader reads `{}`",
                format::PREAMBLE
            ),
            Finding::UnreadableStore { found: None } => {
                write!(f, "no `{HEADER_FILE}` file, so this is not a store")
            }
            Finding::FilenameLies {
                file,
                claimed,
                actual,
            } => write!(
                f,
                "{} claims {} and hashes to {actual}; the name is a claim and it is false",
                file.display(),
                claimed.abbreviate(12)
            ),
            Finding::ImpossibleCollision { id, files } => write!(
                f,
                "{} files hash to {} with differing bytes, which cannot happen: {}",
                files.len(),
                id.abbreviate(12),
                display_files(files)
            ),
            Finding::MalformedBookmark { file } => {
                write!(f, "{}: {}", file.display(), MalformedName)
            }
            Finding::MalformedSkipped { file, error } => write!(
                f,
                "{}: {error}; a rule that does not read would take a file \
                 somebody asked it to leave",
                file.display()
            ),
            Finding::RuleCoversTracked { file, rule, path } => write!(
                f,
                "{} states `{rule}`, which covers `{path}` in this history; \
                 `record` refuses while it stands, and deleting that file is \
                 the fix — history holds what it holds",
                file.display()
            ),
            Finding::DuplicateRule { rule, files } => write!(
                f,
                "`{rule}` is stated twice, which means what stating it once \
                 means; either file may go:{}",
                display_files(files)
            ),
            Finding::StaleSkipped { file } => write!(
                f,
                "{} states nothing: rules are one to a file in `{}/`, and \
                 leaving this here says history skips what it does not",
                file.display(),
                crate::working::SKIPPED_DIR
            ),
            Finding::RetiredRule { file, replacement } => write!(
                f,
                "{} states `skip-suffix`, which is retired and no longer reads; \
                 `{replacement}` says the same thing, matched against a file's \
                 own name as the old key always was",
                file.display()
            ),
            Finding::PrivateAndShared {
                value,
                private,
                shared,
            } => write!(
                f,
                "`{value}` is covered privately by {} and shared by {}: rules \
                 union, so both stand, so the shared one names the path in \
                 every copy and the private one accomplishes nothing; delete \
                 whichever of the two you did not mean",
                private.display(),
                shared.display()
            ),
            Finding::Unreadable { file, reason } => write!(f, "{}: {reason}", file.display()),
            Finding::MissingParent { parent, named_by } => write!(
                f,
                "{} names parent {}, which is not here yet",
                named_by.abbreviate(12),
                parent.abbreviate(12)
            ),
            Finding::StandsOnSuperseded {
                revision,
                superseded,
                successors,
            } => write!(
                f,
                "{} stands on {}, which {} supersedes; it was authored before \
                 the rewrite. Run `historica carry` to repair automatically",
                revision.abbreviate(12),
                superseded.abbreviate(12),
                display_missing(successors)
            ),
            Finding::DanglingBookmark { name, target } => {
                write!(f, "`{name}` points at `{target}`, which is not here yet")
            }
            Finding::DuplicateContent { id, files } => write!(
                f,
                "{} is stored {} times: {}",
                id.abbreviate(12),
                files.len(),
                display_files(files)
            ),
            Finding::Unfollowed { file } => write!(
                f,
                "{} is a symbolic link, and a store reads the files it holds \
                 rather than the ones it points at",
                file.display()
            ),
            Finding::ForeignFile { file } => write!(
                f,
                "{} carries neither `{REVISION_SUFFIX}` nor `{NAME_SUFFIX}` \
                 where its directory wants one, so nothing reads it",
                file.display()
            ),
            Finding::MissingOperations { document, named_by } => write!(
                f,
                "{named_by} names the operation document {document}, \
                 which this store does not hold yet"
            ),
            Finding::MissingPayload { payload, named_by } => write!(
                f,
                "{} names the content {}, which is not here; it may not have \
                 arrived yet, or another writer may have overwritten it",
                named_by.abbreviate(12),
                payload.abbreviate(12)
            ),
            Finding::UnnamedPayload { file } => write!(
                f,
                "{} is not `{OPERATION_SUFFIX}` and no revision names it as content, \
                 so nothing reads it",
                file.display()
            ),
            Finding::PayloadNotText { payload, named_by } => write!(
                f,
                "{} names {} as text and it is not UTF-8, \
                 so no operation document could ever quote a line of it",
                named_by.abbreviate(12),
                payload.abbreviate(12)
            ),
            Finding::TreeDisagrees { revision, because } => {
                write!(f, "{revision}: {because}")
            }
            Finding::ContentDisagrees {
                revision,
                file,
                because,
            } => write!(f, "{revision}, file {file}: {because}"),
            Finding::Forgotten { document, named_by } => write!(
                f,
                "{} names {}, whose bytes were destroyed; a forgetting \
                 document stands in for it",
                named_by.abbreviate(12),
                document.abbreviate(12)
            ),
            Finding::Resurrected { document } => write!(
                f,
                "{} was forgotten and its bytes are here again, probably by \
                 sync; the redaction still holds, and `forget` run again \
                 destroys them again",
                document.abbreviate(12)
            ),
            Finding::ResolvedWithoutDisagreement { revision, file } => write!(
                f,
                "{revision} states a resolution for the file {file}, which both its parents \
                 leave exactly the same; a merge resolves where its parents differ, and \
                 where they agree the file is that agreed state"
            ),
            Finding::UnstatedMerge { revision, file } => write!(
                f,
                "{revision} is a merge whose parents differ about the file {file} and which \
                 states no resolution; reading that file past this revision needs the merge \
                 algorithm rather than arithmetic"
            ),
            Finding::MissingReference { document, named_by } => write!(
                f,
                "the resolution {named_by} keeps items of {document}, \
                 which this store does not hold yet"
            ),
            Finding::StillQuoted { document, forgets } => write!(
                f,
                "{} still quotes items {} says were destroyed; a redaction \
                 that has not finished arriving looks exactly like this",
                document.abbreviate(12),
                forgets.abbreviate(12)
            ),
            Finding::Incomplete { head, missing } => write!(
                f,
                "{} is a head this store cannot produce: its history names {}, \
                 which is not here",
                head.abbreviate(12),
                display_missing(missing)
            ),
        }
    }
}

/// The digests a head is waiting on, said without becoming a wall of hex.
///
/// One is the ordinary number — a store mid-sync is usually one document
/// behind — and a long list says the same thing as a short one plus a count.
fn display_missing(missing: &BTreeSet<RevisionId>) -> String {
    const SHOWN: usize = 3;
    let mut out = missing
        .iter()
        .take(SHOWN)
        .map(|id| id.abbreviate(12))
        .collect::<Vec<_>>()
        .join(", ");
    if missing.len() > SHOWN {
        let _ = write!(out, " and {} more", missing.len() - SHOWN);
    }
    out
}

fn display_files(files: &[PathBuf]) -> String {
    files
        .iter()
        .map(|file| file.display().to_string())
        .collect::<Vec<_>>()
        .join(", ")
}

/// Everything one pass over a store found.
#[derive(Debug, Default)]
pub struct Report {
    findings: Vec<Finding>,
}

impl Report {
    /// Every finding, errors first.
    pub fn findings(&self) -> &[Finding] {
        &self.findings
    }

    /// Findings that mean the store cannot be trusted.
    pub fn errors(&self) -> impl Iterator<Item = &Finding> {
        self.of(Severity::Error)
    }

    /// Findings that never fail.
    pub fn notes(&self) -> impl Iterator<Item = &Finding> {
        self.of(Severity::Note)
    }

    fn of(&self, severity: Severity) -> impl Iterator<Item = &Finding> {
        self.findings
            .iter()
            .filter(move |finding| finding.severity() == severity)
    }

    /// Whether the store can be trusted. Notes do not affect this.
    pub fn is_ok(&self) -> bool {
        self.errors().next().is_none()
    }

    /// Every head this store holds the history of but cannot produce.
    pub fn incomplete(&self) -> impl Iterator<Item = &Finding> {
        self.findings
            .iter()
            .filter(|finding| matches!(finding, Finding::Incomplete { .. }))
    }

    /// Whether every head here can be materialised from what is here.
    ///
    /// Separate from [`Report::is_ok`] on purpose. A store missing half its
    /// history contradicts nothing and is not broken — decision 0006 is right
    /// that transport having more to deliver is ordinary — but a caller who
    /// believes delivery has finished is asking a different question, and this
    /// is that question.
    pub fn is_complete(&self) -> bool {
        self.incomplete().next().is_none()
    }

    fn push(&mut self, finding: Finding) {
        self.findings.push(finding);
    }
}

/// A filename that claims to be a digest, if it does.
///
/// Decision 0020 gives a document a two-part suffix, which `file_stem` sees
/// only the last of — so a digest-named `<digest>.rev.txt` would come back as
/// `<digest>.rev`, parse as nothing, and quietly stop being checked. Every
/// accepted suffix is stripped instead.
fn claimed_digest(path: &Path) -> Option<RevisionId> {
    let name = path.file_name().and_then(|name| name.to_str())?;
    let stem = REVISION_SUFFIXES
        .iter()
        .chain(OPERATION_SUFFIXES.iter())
        .find_map(|suffix| name.strip_suffix(*suffix))
        .unwrap_or(name);
    stem.parse().ok()
}

/// Examine a store without loading it, reporting every fault at once.
pub(super) fn check<F: Filesystem + ?Sized>(files: &F, root: &Path) -> Report {
    let mut report = Report::default();

    match read_to_string(files, &root.join(HEADER_FILE)) {
        Ok(text) => {
            // Decision 0021: the first line is the format, and the rest is
            // the note a person reads.
            let line = text.lines().next().unwrap_or_default().to_owned();
            if line != format::PREAMBLE {
                report.push(Finding::UnreadableStore { found: Some(line) });
            }
        }
        Err(_) => report.push(Finding::UnreadableStore { found: None }),
    }

    let found = super::walk(files, root, REVISIONS_DIR).unwrap_or_default();
    for link in &found.links {
        report.push(Finding::Unfollowed { file: link.clone() });
    }

    let mut documents: BTreeMap<RevisionId, RevisionDocument> = BTreeMap::new();
    let mut files_by_digest: BTreeMap<RevisionId, Vec<PathBuf>> = BTreeMap::new();
    let mut bytes_by_digest: BTreeMap<RevisionId, Vec<u8>> = BTreeMap::new();

    for path in found.files {
        let name = path
            .file_name()
            .and_then(|n| n.to_str())
            .unwrap_or_default()
            .to_owned();

        // Decision 0022: a file the platform wrote into our folder is not ours
        // to have an opinion about, here as in `operations/`.
        if platform_name(&name) {
            continue;
        }
        if !claims(&path, &REVISION_SUFFIXES) {
            // Ignored without comment by the loader; a note here is that comment.
            report.push(Finding::ForeignFile { file: path.clone() });
            continue;
        }
        let bytes = match files.read(&path) {
            Ok(bytes) => bytes,
            Err(error) => {
                report.push(Finding::Unreadable {
                    file: path.clone(),
                    reason: error.to_string(),
                });
                continue;
            }
        };
        let id = digest(&bytes);

        if let Some(claimed) = claimed_digest(&path)
            && claimed != id
        {
            report.push(Finding::FilenameLies {
                file: path.clone(),
                claimed,
                actual: id,
            });
        }

        match bytes_by_digest.get(&id) {
            Some(existing) if existing != &bytes => {
                let mut files = files_by_digest.get(&id).cloned().unwrap_or_default();
                files.push(path.clone());
                report.push(Finding::ImpossibleCollision { id, files });
            }
            _ => {
                bytes_by_digest.insert(id, bytes.clone());
            }
        }
        files_by_digest.entry(id).or_default().push(path.clone());

        match RevisionDocument::parse(&bytes) {
            Ok(document) => {
                documents.insert(id, document);
            }
            Err(error) => report.push(Finding::Unparsable { file: path, error }),
        }
    }

    for (id, files) in &files_by_digest {
        if files.len() > 1 {
            report.push(Finding::DuplicateContent {
                id: *id,
                files: files.clone(),
            });
        }
    }

    // A missing parent means transport has more to deliver, which the core
    // already calls ordinary. A missing `supersedes` is not even that: the
    // successor carries the evidence precisely so the predecessor may be gone.
    for (id, document) in &documents {
        for parent in &document.parents {
            if !documents.contains_key(parent) {
                report.push(Finding::MissingParent {
                    parent: *parent,
                    named_by: *id,
                });
            }
        }
    }

    // What each withdrawn revision was withdrawn by. Built from the documents
    // that state it, so a supersession nobody here delivered is not one this
    // store knows about, and the loop below stays silent about it.
    let mut withdrawn: BTreeMap<RevisionId, BTreeSet<RevisionId>> = BTreeMap::new();
    for (id, document) in &documents {
        for predecessor in &document.supersedes {
            withdrawn.entry(*predecessor).or_default().insert(*id);
        }
    }

    // A revision that is itself superseded is passed over: a withdrawn
    // revision standing on a withdrawn revision is the trailing history a
    // finished rewrite leaves behind — the corpus's own amendment does
    // exactly that — and reporting it would make every rewrite a note.
    for (id, document) in &documents {
        if withdrawn.contains_key(id) {
            continue;
        }
        for parent in &document.parents {
            if let Some(successors) = withdrawn.get(parent) {
                report.push(Finding::StandsOnSuperseded {
                    revision: *id,
                    superseded: *parent,
                    successors: successors.clone(),
                });
            }
        }
    }

    let (operations, resolutions, payloads) = check_operations(files, root, &mut report);
    check_replay(
        files,
        &documents,
        &operations,
        &resolutions,
        &payloads,
        &mut report,
    );
    check_skipped(files, root, &mut report);

    check_resolutions(files, root, &documents, &mut report);
    check_names(files, root, &documents, &mut report);
    report.findings.sort_by_key(|finding| finding.severity());
    report
}

/// Decision 0032's obligation, held in both directions.
///
/// A merge revision must name a resolution for every file whose parents'
/// states differ, and may not name one anywhere else. Both halves are claims
/// about what a *reader* gets, so both are checked with the reader rather
/// than with a second copy of it: a store that will not open has already been
/// reported on line by line, and there is nothing here to add.
fn check_resolutions<F: Filesystem + ?Sized>(
    files: &F,
    root: &Path,
    documents: &BTreeMap<RevisionId, RevisionDocument>,
    report: &mut Report,
) {
    // Every finding below is stated about a revision with two parents, and
    // asking for them costs a second pass over `operations/` — decision 0036's
    // catalogue is refused here on purpose, so the pass is the directory
    // itself. A history with no merge in it has no obligation 0032 states, so
    // it is owed no reading to discover that.
    if documents
        .values()
        .all(|document| document.parents.len() < 2)
    {
        return;
    }
    // Decisions 0036 and 0058: `check` reads `revisions/` and catalogues
    // `operations/` itself, never by taking what `cache/` says. Everything
    // else this store answers is the arithmetic itself, and this is the one
    // command that exists to run it.
    let Ok(store) = super::Store::open_reading_everything_on(files, root) else {
        return;
    };
    // Opening no longer reads `operations/`, and this check is entirely about
    // what an `edit` line names there. A directory that will not parse has
    // already been reported file by file, on the same reasoning as above.
    if store.resolutions().is_err() {
        return;
    }

    // Decision 0032 defers binary at a merge: 0008 makes two concurrent
    // `bytes` a divergence and 0028 makes accepting one explicit, and a
    // payload needs no resolution grammar because a payload has no items.
    let whole: BTreeSet<FileId> = store
        .iter()
        .flat_map(|(_, document)| document.bytes.keys().copied())
        .collect();

    for (revision, document) in store.iter() {
        let parents: Vec<RevisionId> = document.parents.iter().copied().collect();
        if parents.len() < 2 {
            continue;
        }
        // Only files that exist here: content is a question about a file the
        // tree holds, and 0008 already decided which those are.
        let Ok(tree) = store.tree(revision) else {
            continue;
        };
        for (file, _) in tree.files() {
            if whole.contains(file) {
                continue;
            }
            let mut states = Vec::new();
            for parent in &parents {
                match store.replayed_content_of(parent, file) {
                    // A side whose history never mentions the file is not a
                    // side that disagrees about it.
                    Ok(None) => {}
                    Ok(Some(state)) => states.push(state),
                    // Anything undelivered is already a finding of its own.
                    Err(_) => {
                        states.clear();
                        break;
                    }
                }
            }
            let differ = states.windows(2).any(|pair| pair[0] != pair[1]);

            let resolves = document
                .edited
                .get(file)
                // Decision 0014: a resolution whose bytes were destroyed is
                // still the resolution this merge states, and the stand-in is
                // what a reader gets for it.
                .is_some_and(|named| matches!(store.effective_resolution(named), Ok(Some(_))));
            match (differ, resolves) {
                (false, true) => report.push(Finding::ResolvedWithoutDisagreement {
                    revision: *revision,
                    file: *file,
                }),
                (true, false) => report.push(Finding::UnstatedMerge {
                    revision: *revision,
                    file: *file,
                }),
                _ => {}
            }

            // Every reference the resolution makes, to a document and a range
            // that exist. Assembling it is what asks both questions at once,
            // and holds the `result` line 0031 makes it state.
            if !resolves {
                continue;
            }
            let named = document.edited[file];
            if let Err(error) = store.replayed_content_of(revision, file) {
                match error {
                    MaterialiseError::Content {
                        error: ReplayError::UnknownDocument { document },
                        ..
                    } => report.push(Finding::MissingReference {
                        document,
                        named_by: named,
                    }),
                    error => report.push(Finding::ContentDisagrees {
                        revision: *revision,
                        file: *file,
                        because: error.to_string(),
                    }),
                }
            }
        }
    }
}

/// Read `operations/` under the rules `revisions/` is read under.
///
/// Identity is content here too, so a document is keyed by its digest and its
/// filename is checked only where the name claims to be one. Decision 0017
/// puts two kinds of file here: only `*.ops` is an operation document, and
/// every other file is a payload, hashed and kept as bytes. This is the one
/// command that hashes every payload deliberately.
type Stored = (
    BTreeMap<RevisionId, OperationDocument>,
    BTreeMap<RevisionId, ResolutionDocument>,
    BTreeMap<RevisionId, PathBuf>,
);

fn check_operations<F: Filesystem + ?Sized>(files: &F, root: &Path, report: &mut Report) -> Stored {
    let found = super::walk(files, root, OPERATIONS_DIR).unwrap_or_default();
    for link in &found.links {
        report.push(Finding::Unfollowed { file: link.clone() });
    }

    let mut documents = BTreeMap::new();
    let mut resolutions = BTreeMap::new();
    let mut payloads: BTreeMap<RevisionId, PathBuf> = BTreeMap::new();
    let mut files_by_digest: BTreeMap<RevisionId, Vec<PathBuf>> = BTreeMap::new();

    for path in found.files {
        let name = path
            .file_name()
            .and_then(|n| n.to_str())
            .unwrap_or_default()
            .to_owned();

        // Decision 0022: a file the platform wrote into our folder is not
        // content and not a fault. Reporting it would put a note in every
        // store on a machine whose file browser has been near it.
        if platform_name(&name) {
            continue;
        }
        let is_document = claims(&path, &OPERATION_SUFFIXES);

        let bytes = match files.read(&path) {
            Ok(bytes) => bytes,
            Err(error) => {
                report.push(Finding::Unreadable {
                    file: path.clone(),
                    reason: error.to_string(),
                });
                continue;
            }
        };
        let id = digest(&bytes);
        if let Some(claimed) = claimed_digest(&path)
            && claimed != id
        {
            report.push(Finding::FilenameLies {
                file: path.clone(),
                claimed,
                actual: id,
            });
        }
        files_by_digest.entry(id).or_default().push(path.clone());

        if !is_document {
            // A payload has no format of its own, so there is nothing to parse
            // and nothing that can be malformed. Its only claim is its digest,
            // and the bytes are dropped here rather than held: a store with a
            // film in it must not be read into memory to be checked.
            payloads.insert(id, path);
            continue;
        }

        // Decision 0032: two content-document grammars share the suffix, and
        // the body says which strict parser the bytes are held to.
        if format::is_resolution(&bytes) {
            match ResolutionDocument::parse(&bytes) {
                Ok(document) => {
                    resolutions.insert(id, document);
                }
                Err(error) => report.push(Finding::Unparsable { file: path, error }),
            }
            continue;
        }

        match OperationDocument::parse(&bytes) {
            Ok(document) => {
                documents.insert(id, document);
            }
            Err(error) => report.push(Finding::Unparsable { file: path, error }),
        }
    }

    for (id, files) in &files_by_digest {
        if files.len() > 1 {
            report.push(Finding::DuplicateContent {
                id: *id,
                files: files.clone(),
            });
        }
    }
    (documents, resolutions, payloads)
}

/// Hold every revision to the tree and the files it claims to have edited.
///
/// This is what decision 0008 unblocked and 0007's merge completed: the walk
/// is over the whole ancestry of each head rather than a chain, so a
/// concurrent history is checked all the way through its merges. The tree
/// comes from [`crate::tree::merge`] and every file from [`crate::merge`],
/// which is the same machinery a person materialising the store would get.
fn check_replay<F: Filesystem + ?Sized>(
    files: &F,
    documents: &BTreeMap<RevisionId, RevisionDocument>,
    operations: &BTreeMap<RevisionId, OperationDocument>,
    resolutions: &BTreeMap<RevisionId, ResolutionDocument>,
    payloads: &BTreeMap<RevisionId, PathBuf>,
    report: &mut Report,
) {
    let mut parents: BTreeSet<RevisionId> = BTreeSet::new();
    for document in documents.values() {
        parents.extend(document.parents.iter().copied());
    }

    // What stands in for what, per decision 0014. A destroyed document with a
    // forgetting document naming it is *forgotten*, which is neither *lost*
    // nor *corrupt* — and the store saying which is what lets this report be
    // exact about the difference.
    let mut forgetting: BTreeMap<RevisionId, Vec<&OperationDocument>> = BTreeMap::new();
    for document in operations.values() {
        if let Some(target) = &document.forgets {
            forgetting.entry(*target).or_default().push(document);
        }
    }
    // The same, in the second grammar. A resolution's `insert` items are the
    // one thing a merge states that exists nowhere else, so decision 0014
    // reaches them too, and a stand-in for one is written as a resolution
    // because a stand-in has to have the shape of what it stands in for.
    let mut forgetting_resolutions: BTreeMap<RevisionId, Vec<&ResolutionDocument>> =
        BTreeMap::new();
    for document in resolutions.values() {
        if let Some(target) = &document.forgets {
            forgetting_resolutions
                .entry(*target)
                .or_default()
                .push(document);
        }
    }
    for target in forgetting.keys().chain(forgetting_resolutions.keys()) {
        if operations.contains_key(target)
            || resolutions.contains_key(target)
            || payloads.contains_key(target)
        {
            report.push(Finding::Resurrected { document: *target });
        }
    }

    // The content each revision names, and whether it is here — effectively,
    // redactions folded in. A `text` payload is held to one rule of its own:
    // it has to be UTF-8, because a later `edit` quotes its items into a
    // document that is. Keyed by revision *and* file: one revision creates as
    // many files as it likes, and each of them arrives with its own content.
    let mut held: BTreeMap<(RevisionId, FileId), Held> = BTreeMap::new();
    for (id, document) in documents {
        for (file, named) in &document.edited {
            // Decision 0032: an `edit` line names either grammar, and a
            // resolution states its file whole rather than as a delta. Its
            // redactions fold in exactly as an operation document's do.
            let standing_resolutions = forgetting_resolutions
                .get(named)
                .cloned()
                .unwrap_or_default();
            if resolutions.contains_key(named) || !standing_resolutions.is_empty() {
                match crate::format::stand_in_resolution(
                    resolutions.get(named),
                    &standing_resolutions,
                ) {
                    Some(effective) => {
                        if !resolutions.contains_key(named) {
                            report.push(Finding::Forgotten {
                                document: *named,
                                named_by: *id,
                            });
                        }
                        held.insert((*id, *file), Held::Resolution(*named, effective));
                    }
                    None => report.push(Finding::MissingOperations {
                        document: *named,
                        named_by: *id,
                    }),
                }
                continue;
            }
            let standing = forgetting.get(named).cloned().unwrap_or_default();
            match crate::format::stand_in(operations.get(named), &standing) {
                Some(effective) => {
                    if !operations.contains_key(named) {
                        report.push(Finding::Forgotten {
                            document: *named,
                            named_by: *id,
                        });
                    }
                    held.insert((*id, *file), Held::Operations(*named, effective));
                }
                None => report.push(Finding::MissingOperations {
                    document: *named,
                    named_by: *id,
                }),
            }
        }
        for named in document.bytes.values() {
            if !payloads.contains_key(named) {
                report.push(Finding::MissingPayload {
                    payload: *named,
                    named_by: *id,
                });
            }
        }
        for (file, named) in &document.text {
            let standing = forgetting.get(named).cloned().unwrap_or_default();
            let base = match payloads.get(named) {
                Some(path) => {
                    let bytes = match files.read(path) {
                        Ok(bytes) => bytes,
                        Err(error) => {
                            report.push(Finding::Unreadable {
                                file: path.clone(),
                                reason: error.to_string(),
                            });
                            continue;
                        }
                    };
                    match String::from_utf8(bytes) {
                        Ok(text) => crate::replay::creation(&text),
                        Err(_) => {
                            report.push(Finding::PayloadNotText {
                                payload: *named,
                                named_by: *id,
                            });
                            continue;
                        }
                    }
                }
                None if standing.is_empty() => {
                    report.push(Finding::MissingPayload {
                        payload: *named,
                        named_by: *id,
                    });
                    continue;
                }
                None => {
                    report.push(Finding::Forgotten {
                        document: *named,
                        named_by: *id,
                    });
                    None
                }
            };
            if let Some(effective) = crate::format::stand_in(base.as_ref(), &standing) {
                held.insert((*id, *file), Held::Operations(*named, effective));
            }
        }
    }

    // A payload no revision names. Reported for the reason `ForeignFile`
    // reported a stray document before decision 0017 made every other file in
    // `operations/` a payload: nothing reads it, and a person who put it there
    // meant something by it.
    let mut named: BTreeSet<RevisionId> = BTreeSet::new();
    for document in documents.values() {
        named.extend(document.text.values().copied());
        named.extend(document.bytes.values().copied());
    }
    for (payload, path) in payloads {
        if !named.contains(payload) {
            report.push(Finding::UnnamedPayload { file: path.clone() });
        }
    }

    let mut undercut: BTreeSet<(RevisionId, RevisionId)> = BTreeSet::new();
    for head in documents.keys().filter(|id| !parents.contains(id)) {
        let Some(reachable) = reachable(*head, documents) else {
            // A missing parent is already a note, and nothing here can decide
            // what is concurrent with what without the whole ancestry.
            continue;
        };

        match crate::tree::merge(reachable.iter().map(|(id, document)| crate::tree::Event {
            revision: *id,
            document,
        })) {
            Ok(_) => {}
            Err(error) => {
                report.push(Finding::TreeDisagrees {
                    revision: *head,
                    because: error.to_string(),
                });
                continue;
            }
        }

        let mut edited: BTreeSet<FileId> = BTreeSet::new();
        for (_, document) in &reachable {
            edited.extend(document.edited.keys().copied());
            edited.extend(document.text.keys().copied());
        }

        // Decision 0007: the walk is what concurrency costs. A Fugue replay
        // rebuilds the document's order once per event, so a history with no
        // merge in it pays a quadratic price for an answer arithmetic already
        // gives — and arithmetic is exactly what `replay` holds a chain to,
        // against the parent each document names. So a chain is replayed
        // forward instead, one document applied to the state the one before
        // it produced.
        //
        // Three conditions, and each is the walk saying something this cannot.
        // A redaction anywhere means `still_quoted` has a question, and it is
        // asked of the whole graph. A resolution states its file whole and is
        // not a delta to apply. And a chain with a document missing from it is
        // a chain whose arithmetic would fail for a reason already reported as
        // an absence, which would read as the store contradicting itself.
        if forgetting.is_empty()
            && let Some(chain) = chain(*head, documents)
            && chain.iter().all(|(id, document)| {
                document
                    .edited
                    .keys()
                    .chain(document.text.keys())
                    .all(|file| matches!(held.get(&(*id, *file)), Some(Held::Operations(..))))
            })
        {
            for file in &edited {
                let mut state = crate::replay::State::empty();
                for (id, _) in &chain {
                    let Some(Held::Operations(_, document)) = held.get(&(*id, *file)) else {
                        continue;
                    };
                    match state.apply(document) {
                        Ok(next) => state = next,
                        Err(error) => {
                            report.push(Finding::ContentDisagrees {
                                revision: *head,
                                file: *file,
                                because: error.to_string(),
                            });
                            break;
                        }
                    }
                }
            }
            continue;
        }

        for file in edited {
            let events: Vec<crate::merge::Event<'_>> = reachable
                .iter()
                .map(|(id, document)| {
                    let parents = document.parents.iter().copied().collect();
                    // Decision 0017: a creation stated whole replays as the
                    // document it is equivalent to, and decision 0014's
                    // redactions are already folded in — what is checked here
                    // is what a person materialising would get.
                    match held.get(&(*id, file)) {
                        Some(stated) => stated.event(*id, parents),
                        None => crate::merge::Event::nothing(*id, parents),
                    }
                })
                .collect();
            match crate::merge::quotes(events) {
                Err(error) => report.push(Finding::ContentDisagrees {
                    revision: *head,
                    file,
                    because: error.to_string(),
                }),
                Ok(quoted) => {
                    still_quoted(documents, &held, &file, &quoted, &mut undercut);
                }
            }
        }
    }
    for (document, forgets) in undercut {
        report.push(Finding::StillQuoted { document, forgets });
    }

    // Which digests something stands in for, in either grammar: what
    // completeness asks is whether a name can be answered at all, and a
    // forgotten document answers it (0014 keeps the shape).
    let standing: BTreeSet<RevisionId> = forgetting
        .keys()
        .chain(forgetting_resolutions.keys())
        .copied()
        .collect();
    check_completeness(
        documents,
        operations,
        resolutions,
        payloads,
        &standing,
        &forgetting_resolutions,
        report,
    );
}

/// Which heads this store can actually produce, and which it only describes.
///
/// Every missing piece is already a note of its own, and each says what is
/// absent. None says what that costs, and the cost is not proportional to the
/// count: one undelivered payload at the root of a history makes every file
/// downstream of it unreadable, while ten of them in a branch nothing stands
/// on cost nothing at all. The difference is reachability, so reachability is
/// what this reports.
///
/// Structural rather than replayed on purpose. A head is producible exactly
/// when its whole ancestry is here and every digest that ancestry names is
/// here; that is a walk of the graph, and it stays cheap on a store far too
/// large to materialise twice for the sake of a report.
fn check_completeness(
    documents: &BTreeMap<RevisionId, RevisionDocument>,
    operations: &BTreeMap<RevisionId, OperationDocument>,
    resolutions: &BTreeMap<RevisionId, ResolutionDocument>,
    payloads: &BTreeMap<RevisionId, PathBuf>,
    standing: &BTreeSet<RevisionId>,
    forgetting_resolutions: &BTreeMap<RevisionId, Vec<&ResolutionDocument>>,
    report: &mut Report,
) {
    // What one revision names and this store does not hold. A document that
    // has been forgotten is *here* for this purpose: decision 0014 destroys
    // the bytes and keeps the shape, so the file still materialises.
    let missing_from = |document: &RevisionDocument| {
        let mut missing = BTreeSet::new();
        let held = |named: &RevisionId| {
            operations.contains_key(named)
                || resolutions.contains_key(named)
                || payloads.contains_key(named)
                || standing.contains(named)
        };
        for named in document.edited.values() {
            if !held(named) {
                missing.insert(*named);
                continue;
            }
            // A resolution is not self-contained: it keeps runs of documents
            // it names, and a `keep` of something absent is a hole in the
            // file exactly as a missing operation document is.
            let stood_in_for = forgetting_resolutions
                .get(named)
                .and_then(|documents| documents.first().copied());
            if let Some(resolution) = resolutions.get(named).or(stood_in_for) {
                for piece in &resolution.pieces {
                    if let crate::format::Piece::Keep { document, .. } = piece
                        && !held(document)
                    {
                        missing.insert(*document);
                    }
                }
            }
        }
        for named in document.text.values().chain(document.bytes.values()) {
            if !held(named) {
                missing.insert(*named);
            }
        }
        missing
    };

    let mut parents: BTreeSet<RevisionId> = BTreeSet::new();
    for document in documents.values() {
        parents.extend(document.parents.iter().copied());
    }

    for head in documents.keys().filter(|id| !parents.contains(id)) {
        let mut missing: BTreeSet<RevisionId> = BTreeSet::new();
        let mut seen: BTreeSet<RevisionId> = BTreeSet::new();
        let mut stack = vec![*head];
        while let Some(id) = stack.pop() {
            if !seen.insert(id) {
                continue;
            }
            let Some(document) = documents.get(&id) else {
                missing.insert(id);
                continue;
            };
            missing.extend(missing_from(document));
            stack.extend(document.parents.iter().copied());
        }
        if !missing.is_empty() {
            report.push(Finding::Incomplete {
                head: *head,
                missing,
            });
        }
    }
}

/// Documents still holding bytes another document says were destroyed.
///
/// An item forgotten at one quote and legible at another is a redaction that
/// has not finished arriving: `forget` rewrites every document that quotes a
/// run, and sync delivers them one file at a time.
fn still_quoted(
    documents: &BTreeMap<RevisionId, RevisionDocument>,
    held: &BTreeMap<(RevisionId, FileId), Held>,
    file: &FileId,
    quoted: &[crate::merge::Quoted],
    undercut: &mut BTreeSet<(RevisionId, RevisionId)>,
) {
    let named_for = |revision: &RevisionId| {
        let document = documents.get(revision)?;
        document
            .edited
            .get(file)
            .or_else(|| document.text.get(file))
            .copied()
    };
    for item in quoted {
        let mut sites: Vec<(RevisionId, bool)> = Vec::new();
        if let Some(named) = named_for(&item.written_by) {
            sites.push((named, item.forgotten));
        }
        for (revision, operation, at) in &item.deletes {
            if let Some(named) = named_for(revision) {
                let forgotten = held
                    .get(&(*revision, *file))
                    .and_then(Held::operations)
                    .map(|document| document.operations[*operation].items[*at].forgotten)
                    .unwrap_or(false);
                sites.push((named, forgotten));
            }
        }
        let Some((forgets, _)) = sites.iter().find(|(_, forgotten)| *forgotten) else {
            continue;
        };
        let forgets = *forgets;
        for (document, forgotten) in sites {
            if !forgotten && document != forgets {
                undercut.insert((document, forgets));
            }
        }
    }
}

/// Every revision one head descends from, or `None` if one is undelivered.
/// A head's ancestry as a chain, oldest first, or nothing if it is not one.
///
/// Nothing when a revision on it has two parents — which is the state the
/// merge walk exists for — and nothing when a parent is missing, which is
/// already a note of its own and leaves no chain to replay.
fn chain(
    head: RevisionId,
    documents: &BTreeMap<RevisionId, RevisionDocument>,
) -> Option<Vec<(RevisionId, &RevisionDocument)>> {
    let mut chain = Vec::new();
    let mut at = Some(head);
    while let Some(id) = at {
        let document = documents.get(&id)?;
        if document.parents.len() > 1 {
            return None;
        }
        chain.push((id, document));
        at = document.parents.iter().next().copied();
        // A cycle cannot happen — a parent is named by digest and a digest
        // covers the parent line — but a store is a folder anyone may write,
        // and a walk that trusted that would hang rather than report.
        if chain.len() > documents.len() {
            return None;
        }
    }
    chain.reverse();
    Some(chain)
}

fn reachable(
    head: RevisionId,
    documents: &BTreeMap<RevisionId, RevisionDocument>,
) -> Option<Vec<(RevisionId, &RevisionDocument)>> {
    let mut seen: BTreeMap<RevisionId, &RevisionDocument> = BTreeMap::new();
    let mut queue = vec![head];
    while let Some(id) = queue.pop() {
        if seen.contains_key(&id) {
            continue;
        }
        let document = documents.get(&id)?;
        seen.insert(id, document);
        queue.extend(document.parents.iter().copied());
    }
    Some(seen.into_iter().collect())
}

/// Decision 0045's directory, read the way `check` reads everything: through.
///
/// Five things the loader cannot say. A file that is not one rule stops every
/// command, so `check` names it here rather than at the next `record`, and a
/// file still stating decision 0051's retired `skip-suffix` is named with the
/// `skip-name` line that replaces it. A rule stated twice is harmless and
/// means somebody's `receive` met a label two replicas spelled differently.
/// A rule covering a file the history holds is the one state a union can
/// arrive at that `skip` refuses to write: rules no longer conflict, so
/// nothing stops one reaching a store where it is not writable, and the fix is
/// to delete the file that states it. And one path covered both privately and
/// shared is decision 0051's one way the travel axis fails — privacy defeated
/// by addition, in the one container whose every other contradiction is
/// resolved by taking both.
fn check_skipped<F: Filesystem + ?Sized>(files: &F, root: &Path, report: &mut Report) {
    // The file this directory replaced. It is not read, and a store carrying
    // one is a store whose rules a reader cannot see.
    let stale = root.join("skipped.txt");
    if read_to_string(files, &stale).is_ok() {
        report.push(Finding::StaleSkipped { file: stale });
    }

    let found = super::walk(files, root, crate::working::SKIPPED_DIR).unwrap_or_default();
    let mut stated: Vec<(crate::working::Rule, PathBuf)> = Vec::new();
    for path in found.files {
        let name = path
            .file_name()
            .and_then(|name| name.to_str())
            .unwrap_or_default();
        // Decision 0022, in the directory that decision most expects Finder to
        // visit: a folder built to be opened is a folder that gets opened.
        if platform_name(name) {
            continue;
        }
        let text = match read_to_string(files, &path) {
            Ok(text) => text,
            Err(error) => {
                report.push(Finding::Unreadable {
                    file: path.clone(),
                    reason: error.to_string(),
                });
                continue;
            }
        };
        match crate::working::Skipped::rule_in(&text) {
            Ok(Some(rule)) => stated.push((rule, path)),
            // The note `init` writes, and any other prose somebody keeps here.
            Ok(None) => {}
            // Decision 0051's retired key first, because "unknown key" is the
            // true but useless half of what there is to say about it.
            Err(error) => match crate::working::Skipped::retired_in(&text) {
                Some(replacement) => report.push(Finding::RetiredRule {
                    file: path,
                    replacement,
                }),
                None => report.push(Finding::MalformedSkipped { file: path, error }),
            },
        }
    }

    let mut by_rule: BTreeMap<String, Vec<PathBuf>> = BTreeMap::new();
    for (rule, path) in &stated {
        by_rule
            .entry(rule.to_string())
            .or_default()
            .push(path.clone());
    }
    for (rule, files) in by_rule {
        if files.len() > 1 {
            report.push(Finding::DuplicateRule { rule, files });
        }
    }

    // Decision 0051's one way this fails: the same scope stated on both sides
    // of the travel axis. Scope equality is the whole of it — a shared rule
    // covering a private rule's path is not a leak, because what the copy
    // carries is the shared rule's own text, which names something else.
    for (rule, private_file) in &stated {
        if !rule.private {
            continue;
        }
        let twin = crate::working::Rule::shared(rule.scope.clone());
        if let Some((_, shared_file)) = stated.iter().find(|(had, _)| *had == twin) {
            report.push(Finding::PrivateAndShared {
                value: rule.scope.to_string(),
                private: private_file.clone(),
                shared: shared_file.clone(),
            });
        }
    }

    // Against every head, for `skip`'s own reason: a rule is a fact about the
    // repository, so a path any line of work holds is a path it cannot cover.
    let Ok(store) = super::Store::open_reading_everything_on(files, root) else {
        return;
    };
    let mut said: BTreeSet<String> = BTreeSet::new();
    for head in store.history().heads() {
        let Ok(tree) = store.tree(&head) else {
            continue;
        };
        for (_, path) in tree.files() {
            for (rule, file) in &stated {
                if rule.covers(path) && said.insert(rule.to_string()) {
                    report.push(Finding::RuleCoversTracked {
                        file: file.clone(),
                        rule: rule.to_string(),
                        path: path.to_owned(),
                    });
                }
            }
        }
    }
}

fn check_names<F: Filesystem + ?Sized>(
    files: &F,
    root: &Path,
    documents: &BTreeMap<RevisionId, RevisionDocument>,
    report: &mut Report,
) {
    let directory = root.join(super::NAMES_DIR);
    let Ok(entries) = files.entries(&directory) else {
        return;
    };
    // The trait promises no order, and a report two runs disagree about the
    // order of is a report nobody can diff.
    let mut entries: Vec<Entry> = entries;
    entries.sort();

    let changes: Vec<_> = documents.values().map(|document| document.change).collect();
    // Decision 0024: a `file` bookmark names an identifier, and what makes one
    // known is that some revision here says anything at all about it. `added`
    // alone would call a bookmark dangling in a store whose transport has
    // delivered the rename and not yet the creation.
    let identifiers: BTreeSet<FileId> = documents
        .values()
        .flat_map(|document| {
            document
                .added
                .keys()
                .chain(document.moved.keys())
                .chain(document.dropped.iter())
                .chain(document.edited.keys())
                .chain(document.text.keys())
                .chain(document.bytes.keys())
                .copied()
        })
        .collect();

    for Entry { path, kind } in entries {
        if !kind.is_file() {
            continue;
        }
        let Some(name) = path.file_name().and_then(|n| n.to_str()) else {
            continue;
        };
        if platform_name(name) {
            continue;
        }
        // Decision 0021: a bookmark is `<name>.txt`. Anything else in here is
        // a file nothing reads, which is the note `ForeignFile` is for.
        let Some(name) = name.strip_suffix(NAME_SUFFIX) else {
            report.push(Finding::ForeignFile { file: path.clone() });
            continue;
        };
        let text = match read_to_string(files, &path) {
            Ok(text) => text,
            Err(error) => {
                report.push(Finding::Unreadable {
                    file: path.clone(),
                    reason: error.to_string(),
                });
                continue;
            }
        };
        match Name::parse(&text) {
            Err(_) => report.push(Finding::MalformedBookmark { file: path.clone() }),
            Ok(target) => {
                let known = match target {
                    Name::Change(change) => changes.contains(&change),
                    Name::Revision(revision) => documents.contains_key(&revision),
                    Name::File(file) => identifiers.contains(&file),
                };
                if !known {
                    report.push(Finding::DanglingBookmark {
                        name: name.to_owned(),
                        target,
                    });
                }
            }
        }
    }
}
