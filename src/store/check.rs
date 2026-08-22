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
use std::path::{Path, PathBuf};

use crate::core::{FileId, RevisionId};
use crate::format::{OperationDocument, ParseError, RevisionDocument, Version, digest};
use crate::fs::{Entry, Filesystem, read_to_string};

use super::{
    HEADER_FILE, MalformedName, NAME_SUFFIX, Name, OPERATION_SUFFIX, OPERATION_SUFFIXES,
    OPERATIONS_DIR, REVISION_SUFFIX, REVISION_SUFFIXES, REVISIONS_DIR, claims, platform_name,
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
    /// No `historica` file, or one naming a version this reader lacks.
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
    /// `skipped.txt` was not rules, which would silently record what it names.
    MalformedSkipped {
        /// The file.
        file: PathBuf,
        /// Which line, and what was wanted there.
        error: crate::working::MalformedSkip,
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
    /// A filename a sync tool produced when it could not decide.
    SyncSuffixed {
        /// The file.
        file: PathBuf,
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
            | Finding::MalformedSkipped { .. } => Severity::Error,
            Finding::MissingParent { .. }
            | Finding::DanglingBookmark { .. }
            | Finding::DuplicateContent { .. }
            | Finding::SyncSuffixed { .. }
            | Finding::ForeignFile { .. }
            | Finding::Unfollowed { .. }
            | Finding::MissingOperations { .. }
            | Finding::MissingPayload { .. }
            | Finding::UnnamedPayload { .. }
            | Finding::Forgotten { .. }
            | Finding::Resurrected { .. }
            | Finding::StillQuoted { .. } => Severity::Note,
        }
    }
}

impl fmt::Display for Finding {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Finding::Unparsable { file, error } => write!(f, "{}: {error}", file.display()),
            Finding::UnreadableStore { found: Some(found) } => write!(
                f,
                "this store says `{found}` and this reader knows up to `{}`",
                Version::CURRENT
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
            Finding::Unreadable { file, reason } => write!(f, "{}: {reason}", file.display()),
            Finding::MissingParent { parent, named_by } => write!(
                f,
                "{} names parent {}, which is not here yet",
                named_by.abbreviate(12),
                parent.abbreviate(12)
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
            Finding::SyncSuffixed { file } => write!(
                f,
                "{} looks like a sync tool's conflicted copy; both files are legitimate revisions",
                file.display()
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
                "{} names the content {}, which is not here yet",
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
            Finding::StillQuoted { document, forgets } => write!(
                f,
                "{} still quotes items {} says were destroyed; a redaction \
                 that has not finished arriving looks exactly like this",
                document.abbreviate(12),
                forgets.abbreviate(12)
            ),
        }
    }
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

    fn push(&mut self, finding: Finding) {
        self.findings.push(finding);
    }
}

/// Filenames a sync tool writes when two replicas disagree.
///
/// Deliberately narrow: guessing more broadly would flag arranged names that
/// merely end in a number, and decision 0006 makes notes cheap only as long as
/// they are true.
fn sync_suffixed(name: &str) -> bool {
    let lower = name.to_ascii_lowercase();
    lower.contains("conflicted copy") || lower.contains(".sync-conflict")
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
            // Decision 0021: the first line is the version, and the rest is
            // the note a person reads.
            let line = text.lines().next().unwrap_or_default().to_owned();
            let known = [Version::V0, Version::V1, Version::V2]
                .iter()
                .any(|version| line == version.preamble());
            if !known {
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
        if sync_suffixed(&name) {
            report.push(Finding::SyncSuffixed { file: path.clone() });
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

    let (operations, payloads) = check_operations(files, root, &mut report);
    check_replay(files, &documents, &operations, &payloads, &mut report);
    if let Ok(text) = read_to_string(files, &root.join(crate::working::SKIPPED_FILE))
        && let Err(error) = crate::working::Skipped::parse(&text)
    {
        report.push(Finding::MalformedSkipped {
            file: root.join(crate::working::SKIPPED_FILE),
            error,
        });
    }

    check_names(files, root, &documents, &mut report);
    report.findings.sort_by_key(|finding| finding.severity());
    report
}

/// Read `operations/` under the rules `revisions/` is read under.
///
/// Identity is content here too, so a document is keyed by its digest and its
/// filename is checked only where the name claims to be one. Decision 0017
/// puts two kinds of file here: only `*.ops` is an operation document, and
/// every other file is a payload, hashed and kept as bytes. This is the one
/// command that hashes every payload deliberately.
type Held = (
    BTreeMap<RevisionId, OperationDocument>,
    BTreeMap<RevisionId, PathBuf>,
);

fn check_operations<F: Filesystem + ?Sized>(files: &F, root: &Path, report: &mut Report) -> Held {
    let found = super::walk(files, root, OPERATIONS_DIR).unwrap_or_default();
    for link in &found.links {
        report.push(Finding::Unfollowed { file: link.clone() });
    }

    let mut documents = BTreeMap::new();
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
        if is_document && sync_suffixed(&name) {
            report.push(Finding::SyncSuffixed { file: path.clone() });
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
        files_by_digest.entry(id).or_default().push(path.clone());

        if !is_document {
            // A payload has no format of its own, so there is nothing to parse
            // and nothing that can be malformed. Its only claim is its digest,
            // and the bytes are dropped here rather than held: a store with a
            // film in it must not be read into memory to be checked.
            payloads.insert(id, path);
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
    (documents, payloads)
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
    for target in forgetting.keys() {
        if operations.contains_key(target) || payloads.contains_key(target) {
            report.push(Finding::Resurrected { document: *target });
        }
    }

    // The content each revision names, and whether it is here — effectively,
    // redactions folded in. A `text` payload is held to one rule of its own:
    // it has to be UTF-8, because a later `edit` quotes its items into a
    // document that is. Keyed by revision *and* file: one revision creates as
    // many files as it likes, and each of them arrives with its own content.
    let mut held: BTreeMap<(RevisionId, FileId), OperationDocument> = BTreeMap::new();
    for (id, document) in documents {
        for (file, named) in &document.edited {
            let standing = forgetting.get(named).cloned().unwrap_or_default();
            match crate::format::stand_in(operations.get(named), &standing) {
                Some(effective) => {
                    if !operations.contains_key(named) {
                        report.push(Finding::Forgotten {
                            document: *named,
                            named_by: *id,
                        });
                    }
                    held.insert((*id, *file), effective);
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
                held.insert((*id, *file), effective);
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

        for file in edited {
            let events: Vec<crate::merge::Event<'_>> = reachable
                .iter()
                .map(|(id, document)| crate::merge::Event {
                    revision: *id,
                    parents: document.parents.iter().copied().collect(),
                    // Decision 0017: a creation stated whole replays as the
                    // document it is equivalent to, and decision 0014's
                    // redactions are already folded in — what is checked here
                    // is what a person materialising would get.
                    operations: held.get(&(*id, file)),
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
}

/// Documents still holding bytes another document says were destroyed.
///
/// An item forgotten at one quote and legible at another is a redaction that
/// has not finished arriving: `forget` rewrites every document that quotes a
/// run, and sync delivers them one file at a time.
fn still_quoted(
    documents: &BTreeMap<RevisionId, RevisionDocument>,
    held: &BTreeMap<(RevisionId, FileId), OperationDocument>,
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
