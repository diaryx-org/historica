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
use std::fs;
use std::path::{Path, PathBuf};

use crate::core::{FileId, RevisionId};
use crate::format::{OperationDocument, ParseError, RevisionDocument, digest};

use super::{
    HEADER_FILE, MalformedName, Name, OPERATION_EXT, OPERATIONS_DIR, PREAMBLE, REVISION_EXT,
    REVISIONS_DIR,
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
    /// `skipped` was not rules, which would silently record what it names.
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
            | Finding::MalformedSkipped { .. } => Severity::Error,
            Finding::MissingParent { .. }
            | Finding::DanglingBookmark { .. }
            | Finding::DuplicateContent { .. }
            | Finding::SyncSuffixed { .. }
            | Finding::ForeignFile { .. }
            | Finding::MissingOperations { .. } => Severity::Note,
        }
    }
}

impl fmt::Display for Finding {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Finding::Unparsable { file, error } => write!(f, "{}: {error}", file.display()),
            Finding::UnreadableStore { found: Some(found) } => write!(
                f,
                "this store says `{found}` and this reader knows `{PREAMBLE}`"
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
            Finding::ForeignFile { file } => write!(
                f,
                "{} carries neither `.{REVISION_EXT}` nor `.{OPERATION_EXT}`, \
                 so nothing reads it",
                file.display()
            ),
            Finding::MissingOperations { document, named_by } => write!(
                f,
                "{named_by} names the operation document {document}, \
                 which this store does not hold yet"
            ),
            Finding::TreeDisagrees { revision, because } => {
                write!(f, "{revision}: {because}")
            }
            Finding::ContentDisagrees {
                revision,
                file,
                because,
            } => write!(f, "{revision}, file {file}: {because}"),
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
fn claimed_digest(path: &Path) -> Option<RevisionId> {
    path.file_stem()
        .and_then(|stem| stem.to_str())
        .and_then(|stem| stem.parse().ok())
}

/// Examine a store without loading it, reporting every fault at once.
pub(super) fn check(root: &Path) -> Report {
    let mut report = Report::default();

    match fs::read_to_string(root.join(HEADER_FILE)) {
        Ok(text) => {
            let line = text.trim_end_matches('\n').to_owned();
            if line != PREAMBLE {
                report.push(Finding::UnreadableStore { found: Some(line) });
            }
        }
        Err(_) => report.push(Finding::UnreadableStore { found: None }),
    }

    let revisions = root.join(REVISIONS_DIR);
    let mut entries: Vec<PathBuf> = match fs::read_dir(&revisions) {
        Ok(entries) => entries.filter_map(Result::ok).map(|e| e.path()).collect(),
        Err(_) => Vec::new(),
    };
    entries.sort();

    let mut documents: BTreeMap<RevisionId, RevisionDocument> = BTreeMap::new();
    let mut files_by_digest: BTreeMap<RevisionId, Vec<PathBuf>> = BTreeMap::new();
    let mut bytes_by_digest: BTreeMap<RevisionId, Vec<u8>> = BTreeMap::new();

    for path in entries {
        if !path.is_file() {
            continue;
        }
        let name = path
            .file_name()
            .and_then(|n| n.to_str())
            .unwrap_or_default()
            .to_owned();

        if path.extension().is_none_or(|ext| ext != REVISION_EXT) {
            // Ignored without comment by the loader; a note here is that comment.
            report.push(Finding::ForeignFile { file: path.clone() });
            continue;
        }
        if sync_suffixed(&name) {
            report.push(Finding::SyncSuffixed { file: path.clone() });
        }

        let bytes = match fs::read(&path) {
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

    let operations = check_operations(root, &mut report);
    check_replay(&documents, &operations, &mut report);
    if let Ok(text) = fs::read_to_string(root.join(crate::working::SKIPPED_FILE))
        && let Err(error) = crate::working::Skipped::parse(&text)
    {
        report.push(Finding::MalformedSkipped {
            file: root.join(crate::working::SKIPPED_FILE),
            error,
        });
    }

    check_names(root, &documents, &mut report);
    report.findings.sort_by_key(|finding| finding.severity());
    report
}

/// Read `operations/` under the rules `revisions/` is read under.
///
/// Identity is content here too, so a document is keyed by its digest and its
/// filename is checked only where the name claims to be one.
fn check_operations(root: &Path, report: &mut Report) -> BTreeMap<RevisionId, OperationDocument> {
    let directory = root.join(OPERATIONS_DIR);
    let mut entries: Vec<PathBuf> = match fs::read_dir(&directory) {
        Ok(entries) => entries.filter_map(Result::ok).map(|e| e.path()).collect(),
        Err(_) => Vec::new(),
    };
    entries.sort();

    let mut documents = BTreeMap::new();
    let mut files_by_digest: BTreeMap<RevisionId, Vec<PathBuf>> = BTreeMap::new();

    for path in entries {
        if !path.is_file() {
            continue;
        }
        let name = path
            .file_name()
            .and_then(|n| n.to_str())
            .unwrap_or_default()
            .to_owned();

        if path.extension().is_none_or(|ext| ext != OPERATION_EXT) {
            report.push(Finding::ForeignFile { file: path.clone() });
            continue;
        }
        if sync_suffixed(&name) {
            report.push(Finding::SyncSuffixed { file: path.clone() });
        }

        let bytes = match fs::read(&path) {
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
    documents
}

/// Hold every revision to the tree and the files it claims to have edited.
///
/// This is what decision 0008 unblocked and 0007's merge completed: the walk
/// is over the whole ancestry of each head rather than a chain, so a
/// concurrent history is checked all the way through its merges. The tree
/// comes from [`crate::tree::merge`] and every file from [`crate::merge`],
/// which is the same machinery a person materialising the store would get.
fn check_replay(
    documents: &BTreeMap<RevisionId, RevisionDocument>,
    operations: &BTreeMap<RevisionId, OperationDocument>,
    report: &mut Report,
) {
    let mut parents: BTreeSet<RevisionId> = BTreeSet::new();
    for document in documents.values() {
        parents.extend(document.parents.iter().copied());
    }

    for (id, document) in documents {
        for named in document.edited.values() {
            if !operations.contains_key(named) {
                report.push(Finding::MissingOperations {
                    document: *named,
                    named_by: *id,
                });
            }
        }
    }

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
        }

        for file in edited {
            let events: Vec<crate::merge::Event<'_>> = reachable
                .iter()
                .map(|(id, document)| crate::merge::Event {
                    revision: *id,
                    parents: document.parents.iter().copied().collect(),
                    operations: document
                        .edited
                        .get(&file)
                        .and_then(|named| operations.get(named)),
                })
                .collect();
            if let Err(error) = crate::merge::merge(events) {
                report.push(Finding::ContentDisagrees {
                    revision: *head,
                    file,
                    because: error.to_string(),
                });
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

fn check_names(
    root: &Path,
    documents: &BTreeMap<RevisionId, RevisionDocument>,
    report: &mut Report,
) {
    let directory = root.join(super::NAMES_DIR);
    let Ok(entries) = fs::read_dir(&directory) else {
        return;
    };
    let mut paths: Vec<PathBuf> = entries.filter_map(Result::ok).map(|e| e.path()).collect();
    paths.sort();

    let changes: Vec<_> = documents.values().map(|document| document.change).collect();

    for path in paths {
        if !path.is_file() {
            continue;
        }
        let Some(name) = path.file_name().and_then(|n| n.to_str()) else {
            continue;
        };
        let text = match fs::read_to_string(&path) {
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
