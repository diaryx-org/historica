//! The folder beside the store, and what it does not take.
//!
//! Specified by `docs/decisions/0011-working-copy.md`. The working copy is the
//! directory holding `history/`, everything in it is tracked, and
//! `history/skipped/` names the exceptions. Nothing here is remembered between
//! commands: reading a working copy is a walk of the filesystem, every time.
//!
//! Decision 0043 leaves that sentence standing and makes it cheaper to keep.
//! [`Working::digest`] is what a comparison against the store actually asks
//! for, and `history/cache/working.txt` says what each path hashed to last
//! time — believed only where the directory still reports the size and the
//! modification time that digest was taken at, and only where that time is
//! strictly older than the catalogue's own. It is not an index and holds no
//! content: delete it and every command says exactly what it said before,
//! having read the folder, which is what it would have done anyway.

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::fmt;
use std::io;
use std::path::{Path, PathBuf};

use crate::core::RevisionId;
use crate::format::check_path;
use crate::fs::{Disk, Entry, Filesystem, Stamp, read_to_string};
use crate::store::STORE_DIR;

mod catalogue;

/// The directory in the store that says what history does not take.
///
/// Decision 0045: one rule to a file. What a single `skipped.txt` held was
/// always a set — [`Skipped::skips`] is `any(covers)`, so there is no order to
/// lose, a rule stated twice means what one means, and no rule can cancel
/// another because 0011 refused negation. Only the container was a sequence,
/// and a sequence is the thing two writers cannot both append to.
pub const SKIPPED_DIR: &str = "skipped";

/// What a rule file is called, after the label.
pub const RULE_SUFFIX: &str = ".txt";

/// The file `init` writes there: the grammar, and no rule.
///
/// It needs no special case in the reader. A file of comments states nothing,
/// which is exactly what decision 0027 asked the default to say.
pub const SKIPPED_NOTE_FILE: &str = "README.txt";

/// The name a directory rule takes inside the directory it names.
///
/// `skip target/` is `skipped/target/all.txt`, which parts it from
/// `skip target` at `skipped/target.txt` without either label having to spell
/// a trailing slash a filename cannot hold.
pub const UNDER_FILE: &str = "all.txt";

/// Label components longer than this are a name a filesystem may refuse.
///
/// Every filesystem in use allows 255 bytes; the margin is for the collision
/// suffix, and for the fact that a path component here is a path component
/// there.
const LABEL_BYTES: usize = 200;

/// What `history/skipped/` says.
///
/// Four keys on two axes, and the set closes there: decision 0049 makes what a
/// rule matches orthogonal to whether it travels, so `skip` and `skip-name`
/// each have a `private` spelling and no combination is missing. The matching
/// side stops at a path component — decision 0011 argues that the part people
/// get wrong about gitignore is never the pattern but which of five files won,
/// and 0045 found that precedence lived in the container. A star inside one
/// component introduces no order and no negation; a `/` inside a pattern would
/// introduce the whole dialect quarrel, so a value holds none.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Skipped {
    /// Each rule, with the file of `skipped/` that states it where one does.
    rules: Vec<(Rule, Option<String>)>,
}

/// One rule, which is one file of `history/skipped/`.
///
/// Public because writing the file is a thing a command does, and a rule that
/// renders itself is what keeps the writer from spelling a line the reader
/// would refuse.
///
/// Decision 0049: the travel axis is a second key rather than a bit on a rule,
/// because a bit is a second fact per rule and a second fact has to merge —
/// one rule held private on the laptop and shared on the desktop would leave
/// the union either leaking or holding a precedence rule, in the one container
/// 0045 spent a whole decision making order-free. The flag is part of the
/// rule's identity instead, so `skip x` and `private x` are two rules that
/// union like any other two, and both being present is a contradiction a
/// person wrote rather than an ambiguity a reader has to resolve.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Rule {
    /// What the rule matches.
    pub scope: Scope,
    /// Whether the rule's own text stays out of an export.
    pub private: bool,
}

/// What a rule matches, which is the grammar's two values times its two forms.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Scope {
    /// One exact path.
    Path(String),
    /// A directory and everything beneath it. Held without its trailing `/`.
    Under(String),
    /// A file's own name, at any depth.
    Name(Pattern),
    /// A directory's name at any depth, and everything beneath it.
    NameUnder(Pattern),
}

impl Rule {
    /// A rule whose text an export carries.
    pub fn shared(scope: Scope) -> Self {
        Self {
            scope,
            private: false,
        }
    }

    /// A rule that keeps a file out of history and its own text out of a copy.
    pub fn private(scope: Scope) -> Self {
        Self {
            scope,
            private: true,
        }
    }

    /// Whether `export` writes this rule into the copy.
    pub fn travels(&self) -> bool {
        !self.private
    }

    /// Read one stated rule.
    ///
    /// An unknown key is an error rather than something to ignore. Decision
    /// 0011: a reader that ignored a key it had not heard of would record
    /// files somebody asked it to keep out, into a history that is
    /// append-only, and refusing to record is the recoverable half of that.
    pub fn parse(line: &str) -> Result<Self, MalformedSkip> {
        Self::parse_at(line, 1)
    }

    /// The same, saying which line of its file the rule was on.
    fn parse_at(line: &str, at: usize) -> Result<Self, MalformedSkip> {
        let (key, value) = line.split_once(' ').ok_or(MalformedSkip {
            at,
            because: "a line is a key, a space, and a value",
        })?;
        if value.is_empty() || value != value.trim() {
            return Err(MalformedSkip {
                at,
                because: "a value is not empty and carries no leading or trailing space",
            });
        }
        let (private, matching) = match key {
            "skip" => (false, false),
            "private" => (true, false),
            "skip-name" => (false, true),
            "private-name" => (true, true),
            // Decision 0049 retires it: `skip-suffix .tmp` is `skip-name
            // *.tmp` with the meaning it always had, since the old rule was
            // already a match against the last component.
            "skip-suffix" => {
                return Err(MalformedSkip {
                    at,
                    because: "`skip-suffix` is retired: an ending is now \
                              `skip-name *` and the ending, matched against a \
                              file's own name",
                });
            }
            _ => {
                return Err(MalformedSkip {
                    at,
                    because: "the keys are `skip`, `skip-name`, `private` and \
                              `private-name`",
                });
            }
        };
        let under = value.ends_with('/');
        let value = match under {
            true => value.trim_end_matches('/'),
            false => value,
        };
        // The trailing slash is the whole of the parting, so a value that was
        // only slashes is a value that is now nothing.
        if value.is_empty() {
            return Err(MalformedSkip {
                at,
                because: "a value is not empty and carries no leading or trailing space",
            });
        }
        let scope = match (matching, under) {
            (false, false) => Scope::Path(crate::format::nfc(value).into_owned()),
            (false, true) => Scope::Under(crate::format::nfc(value).into_owned()),
            (true, false) => {
                Scope::Name(Pattern::parse(value).map_err(|because| MalformedSkip { at, because })?)
            }
            (true, true) => Scope::NameUnder(
                Pattern::parse(value).map_err(|because| MalformedSkip { at, because })?,
            ),
        };
        Ok(Rule { scope, private })
    }

    /// Where a writer files this rule, relative to `skipped/`.
    ///
    /// Decision 0045: the label is presentation and the content is the rule,
    /// which is 0003's sentence about every other file in the store. It has to
    /// be, because `skip docs/drafts/` holds a character no filename does — so
    /// the label mirrors the path into real directories instead, and the walk
    /// that reads them already recurses.
    ///
    /// A label the store cannot own falls back to the digest of the rule:
    /// 0018's collision suffix, arrived at from the rule alone rather than
    /// from what a directory already holds, so two replicas spelling one rule
    /// spell one filename. Decision 0049 adds two reasons to fall back — a
    /// pattern holding a `*`, which is a filename no Windows volume will carry
    /// and a shell will not leave alone, and the collision between a rule and
    /// its twin on the other axis, which `add_skipped` settles by writing the
    /// second under its digest.
    pub fn label(&self) -> String {
        let natural = match &self.scope {
            Scope::Path(path) => format!("{}{RULE_SUFFIX}", crate::naming::scrubbed(path)),
            Scope::Under(path) => format!("{}/{UNDER_FILE}", crate::naming::scrubbed(path)),
            Scope::Name(pattern) => {
                format!("name {}{RULE_SUFFIX}", crate::naming::scrubbed(&pattern.0))
            }
            Scope::NameUnder(pattern) => {
                format!("name {}/{UNDER_FILE}", crate::naming::scrubbed(&pattern.0))
            }
        };
        match self.spellable(&natural) {
            true => natural,
            false => self.digest_label(),
        }
    }

    /// The label a rule takes where the natural one is somebody else's.
    ///
    /// Derived from the rule and nothing else, so two replicas that both have
    /// to fall back fall back to one name. The rendered line carries the key,
    /// so a private rule and its shared twin derive two names.
    pub fn digest_label(&self) -> String {
        format!(
            "{}{RULE_SUFFIX}",
            crate::format::digest(self.to_string().as_bytes())
                .abbreviate(crate::naming::DIGEST_CHARS)
        )
    }

    /// Whether the natural label is one this directory can carry.
    ///
    /// Five ways it is not, and each would lose a rule silently rather than
    /// loudly: a name the reader skips as the platform's (0022), a name
    /// already meaning something else here, a component no filesystem will
    /// take, and — decision 0049 — a value holding a `*`, which is a character
    /// `naming::scrubbed` passes through untouched and no Windows volume will
    /// carry.
    fn spellable(&self, natural: &str) -> bool {
        let last = natural.rsplit('/').next().unwrap_or(natural);
        if crate::store::platform_name(last) || natural == SKIPPED_NOTE_FILE {
            return false;
        }
        if last == UNDER_FILE && !self.covers_everything_under() {
            return false;
        }
        if natural.contains('*') {
            return false;
        }
        natural
            .split('/')
            .all(|component| !component.is_empty() && component.len() <= LABEL_BYTES)
    }

    /// Whether this rule's scope is a directory and what hangs beneath it.
    fn covers_everything_under(&self) -> bool {
        matches!(self.scope, Scope::Under(_) | Scope::NameUnder(_))
    }

    /// Whether this rule covers a path.
    pub fn covers(&self, path: &str) -> bool {
        match &self.scope {
            Scope::Path(exact) => path == exact,
            Scope::Under(prefix) => path
                .strip_prefix(prefix.as_str())
                .is_some_and(|rest| rest.starts_with('/')),
            Scope::Name(pattern) => pattern.matches(last_component(path)),
            // Every component but the last, because a name-and-under rule
            // names a directory: `skip-name build/` does not cover a file
            // called `build`, exactly as `skip target/` does not.
            Scope::NameUnder(pattern) => {
                let mut components: Vec<&str> = path.split('/').collect();
                components.pop();
                components.iter().any(|name| pattern.matches(name))
            }
        }
    }
}

impl fmt::Display for Rule {
    /// The line the file holds, which [`Skipped::rule_in`] reads back.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let key = match (&self.scope, self.private) {
            (Scope::Path(_) | Scope::Under(_), false) => "skip",
            (Scope::Path(_) | Scope::Under(_), true) => "private",
            (Scope::Name(_) | Scope::NameUnder(_), false) => "skip-name",
            (Scope::Name(_) | Scope::NameUnder(_), true) => "private-name",
        };
        match &self.scope {
            Scope::Path(value) => write!(f, "{key} {value}"),
            Scope::Under(value) => write!(f, "{key} {value}/"),
            Scope::Name(pattern) => write!(f, "{key} {pattern}"),
            Scope::NameUnder(pattern) => write!(f, "{key} {pattern}/"),
        }
    }
}

impl fmt::Display for Scope {
    /// The value half of a rule's line, which is what a message about two
    /// rules covering one thing has to be able to name without the key.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Scope::Path(value) => f.write_str(value),
            Scope::Under(value) => write!(f, "{value}/"),
            Scope::Name(pattern) => write!(f, "{pattern}"),
            Scope::NameUnder(pattern) => write!(f, "{pattern}/"),
        }
    }
}

/// A value matched against one path component, in which `*` is the only
/// metacharacter.
///
/// Decision 0049: any run of characters, including an empty one and including
/// a leading dot, so `*.tmp` covers `.tmp` and `*` needs no companion rule for
/// dotfiles. No `?`, no character classes, no `**`, no negation, and no
/// escaping — a name that genuinely holds a star is spelled with `skip
/// <path>`, which is exact, so the pattern never has to express a literal one.
///
/// The value holds no `/`. Every dialect quarrel worth having is about
/// separators, and forbidding one stops all of them existing: what remains is
/// a matcher a stranger writes in ten lines and gets right, which is the
/// standard decision 0004 holds every other part of this format to.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pattern(String);

impl Pattern {
    /// Read a pattern, refusing the two values that are not one.
    ///
    /// A value holding a `/` is refused, naming `skip <path>` as what spells a
    /// path. A value that is only stars is refused because it says *the whole
    /// folder*, which is a request `skip` already refuses when it is spelled
    /// as the repository root, and rules exist to name the exceptions.
    pub fn parse(value: &str) -> Result<Self, &'static str> {
        if value.is_empty() {
            return Err("a pattern is not empty");
        }
        if value.contains('/') {
            return Err(
                "a pattern is one path component and holds no `/`: a path is \
                        spelled with `skip`",
            );
        }
        if value.chars().all(|character| character == '*') {
            return Err(
                "a pattern of nothing but `*` is the whole folder, which rules \
                        exist to name the exceptions to",
            );
        }
        Ok(Self(crate::format::nfc(value).into_owned()))
    }

    /// Whether this pattern matches one path component.
    ///
    /// Case-sensitive, as everything else here is. Leftmost-first for the
    /// runs between stars, which is exact rather than approximate: consuming a
    /// run as early as possible leaves the most for whatever follows it, so no
    /// backtracking can succeed where this fails.
    pub fn matches(&self, component: &str) -> bool {
        let mut runs = self.0.split('*');
        let first = runs.next().unwrap_or_default();
        let Some(mut rest) = component.strip_prefix(first) else {
            return false;
        };
        let runs: Vec<&str> = runs.collect();
        let Some((last, between)) = runs.split_last() else {
            // No star at all, so the pattern is the whole component.
            return rest.is_empty();
        };
        for run in between {
            match rest.find(run) {
                Some(at) => rest = &rest[at + run.len()..],
                None => return false,
            }
        }
        rest.len() >= last.len() && rest.ends_with(last)
    }

    /// The value as it was written, which [`Pattern::parse`] reads back.
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for Pattern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

/// A path's own name, which is what a `skip-name` rule is matched against.
fn last_component(path: &str) -> &str {
    path.rsplit('/').next().unwrap_or(path)
}

/// What `init` writes into `history/skipped/README.txt`.
///
/// Decision 0027: the file explains the rule syntax and states no rules.
/// Defaults belong to a host or project that knows what its files mean; the
/// history library does not silently leave anything out.
pub const SKIPPED_NOTE: &str = "\
# What recording does not take: one rule to a file, and this file states none.
# A rule is a key, a space, and a value. `skip <path>` names one file and
# `skip <path>/` everything under a directory; `skip-name <name>` matches a
# file's own name at any depth and `skip-name <name>/` a directory's, where
# `*` stands for any run of characters within the one name. A `#` line says
# nothing.
#
# `private` and `private-name` say the same things and are not written into an
# `export`, which is the only copy this design builds smaller than the store.
# A path covered both privately and shared is named in the copy anyway, and
# `check` reports it.
#
# The filename is a label for whoever opens this folder; the rule is what the
# file holds. Delete a file to drop its rule, and note that a store you receive
# from can hand it back, because a copy cannot tell a rule you deleted from a
# rule it has not seen yet.
";

impl Skipped {
    /// Skip nothing, which is what a store with an empty directory says.
    pub fn none() -> Self {
        Self::default()
    }

    /// Every rule these files state, with a rule stated twice counted once.
    ///
    /// The order is the order they were found in, which is the order the
    /// directory sorts — and it means nothing, because [`Skipped::skips`] asks
    /// every rule.
    pub fn from_rules(rules: impl IntoIterator<Item = Rule>) -> Self {
        Self::stated(rules.into_iter().map(|rule| (rule, None)))
    }

    /// The same, each rule with the file of `skipped/` that states it.
    ///
    /// The file is what deleting a rule means, so it is what a message about
    /// a rule has to be able to name.
    pub fn stated(rules: impl IntoIterator<Item = (Rule, Option<String>)>) -> Self {
        let mut held: Vec<(Rule, Option<String>)> = Vec::new();
        for (rule, file) in rules {
            if !held.iter().any(|(had, _)| *had == rule) {
                held.push((rule, file));
            }
        }
        Self { rules: held }
    }

    /// The rule one file states, or none where it states only comments.
    ///
    /// A file stating two rules is refused, and the error names the file
    /// rather than a line inside it — which is the better half of the trade
    /// decision 0045 makes, since the fix is now to split one file in two.
    pub fn rule_in(text: &str) -> Result<Option<Rule>, MalformedSkip> {
        let mut found: Option<Rule> = None;
        for (index, line) in text.lines().enumerate() {
            let at = index + 1;
            if line.is_empty() {
                continue;
            }
            // Decision 0022: a comment states nothing, so 0011's reason for
            // refusing an unknown key — that a reader which ignored one would
            // record files somebody asked it to keep out — does not reach it.
            if line.starts_with('#') {
                continue;
            }
            if found.is_some() {
                return Err(MalformedSkip {
                    at,
                    because: "a file states one rule, and this is a second",
                });
            }
            found = Some(Rule::parse_at(line, at)?);
        }
        Ok(found)
    }

    /// The spelling that replaces a retired key this file still states.
    ///
    /// Decision 0049 refuses `skip-suffix` by name, and the refusal is worth
    /// more than "unknown key" because there is an exact replacement and the
    /// reader can spell it. `check` reports it; the loader stops at it, as it
    /// stops at anything it cannot read.
    pub fn retired_in(text: &str) -> Option<String> {
        text.lines()
            .filter(|line| !line.is_empty() && !line.starts_with('#'))
            .find_map(|line| {
                let value = line.strip_prefix("skip-suffix ")?.trim();
                match value.is_empty() {
                    true => None,
                    false => Some(format!("skip-name *{value}")),
                }
            })
    }

    /// Whether history takes this path.
    pub fn skips(&self, path: &str) -> bool {
        self.rules.iter().any(|(rule, _)| rule.covers(path))
    }

    /// Whether a directory is skipped whole, so that walking it is pointless.
    ///
    /// Public because a path a person typed may name the directory rather than
    /// a file in it, and a command that could not tell "no such path" from
    /// "a rule keeps that path out" would say the wrong one of the two.
    pub fn skips_directory(&self, path: &str) -> bool {
        self.rules.iter().any(|(rule, _)| match &rule.scope {
            Scope::Under(prefix) | Scope::Path(prefix) => path == prefix,
            // Decision 0049: the directory's own name, which is what keeps
            // 0039 able to tell "no such path" from "a rule keeps that path
            // out" now that a rule can name a directory without spelling one.
            Scope::NameUnder(pattern) => pattern.matches(last_component(path)),
            Scope::Name(_) => false,
        })
    }

    /// Every rule, in the order the directory states them.
    pub fn rules(&self) -> impl Iterator<Item = &Rule> {
        self.rules.iter().map(|(rule, _)| rule)
    }

    /// Every rule with the file of `skipped/` that states it, where the rules
    /// were read from a store rather than assembled.
    pub fn stating(&self) -> impl Iterator<Item = (&Rule, Option<&str>)> {
        self.rules
            .iter()
            .map(|(rule, file)| (rule, file.as_deref()))
    }

    /// Every rule an `export` carries, in the order the directory states them.
    ///
    /// Decision 0049 supersedes the half of 0042 that named rules: a copy that
    /// silently dropped `skip target/` is a copy whose first `record` offers
    /// to record the recipient's build output, which is the failure 0011 wrote
    /// rules to prevent, arriving because the rules did not.
    pub fn travelling(&self) -> impl Iterator<Item = &Rule> {
        self.rules
            .iter()
            .map(|(rule, _)| rule)
            .filter(|rule| rule.travels())
    }

    /// How many rules an `export` holds back.
    pub fn withheld(&self) -> usize {
        self.rules.iter().filter(|(rule, _)| rule.private).count()
    }

    /// Which file of `skipped/` states this rule.
    pub fn file_of(&self, rule: &Rule) -> Option<&str> {
        self.rules
            .iter()
            .find(|(had, _)| had == rule)
            .and_then(|(_, file)| file.as_deref())
    }

    /// How many rules the directory states.
    pub fn len(&self) -> usize {
        self.rules.len()
    }

    /// Whether the directory states no rules.
    pub fn is_empty(&self) -> bool {
        self.rules.is_empty()
    }
}

/// A file of `history/skipped/` that was not one rule.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MalformedSkip {
    /// The line, counted from one.
    pub at: usize,
    /// What was wanted there.
    pub because: &'static str,
}

impl fmt::Display for MalformedSkip {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "line {}: {}", self.at, self.because)
    }
}

impl std::error::Error for MalformedSkip {}

/// The tracked files, by path, as the folder stands.
///
/// Holds the filesystem it was read from, so that [`Working::text`] and
/// [`Working::bytes`] read the same folder the walk saw. A working copy read
/// from one filesystem and read back through another would be describing a
/// folder it had never looked at — and because the filesystem is a type
/// parameter, [`crate::record::record`] can insist that a working copy and the
/// store it is recorded into are the same kind of folder.
#[derive(Debug, Clone)]
pub struct Working<F = Disk> {
    filesystem: F,
    /// The folder this is, which is also where `history/cache/` is found.
    root: PathBuf,
    files: BTreeMap<String, PathBuf>,
    /// Which tracked paths are links, and what each points at.
    ///
    /// Decision 0040: read during the walk, with the walk's own promise that
    /// nothing is followed. `None` against a path is the filesystem saying it
    /// cannot read the target — 0034's answer, doing 0034's work — and a
    /// recorder that gets it states nothing about that link.
    links: BTreeMap<String, Option<String>>,
    /// What the directory said about each tracked regular file, where it says
    /// anything at all.
    ///
    /// Decision 0043. Empty on a filesystem that reports no
    /// [`Stamp`](crate::fs::Stamp), which is the whole of what such a
    /// filesystem loses: every digest below is worked out by reading.
    stamps: BTreeMap<String, Stamp>,
    /// The digest of each tracked file, once anything has asked for it.
    ///
    /// Seeded from `history/cache/working.txt` with the entries the stamps
    /// above allow, and filled in by reading for everything else. Behind a
    /// cell because a working copy is read through a shared reference while it
    /// answers questions about itself — the same reason the store's own reads
    /// are.
    known: RefCell<Known>,
    refused: Vec<(String, String)>,
}

/// What this pass knows about the folder's content, and whether it learned any
/// of it the expensive way.
#[derive(Debug, Clone, Default)]
struct Known {
    digests: BTreeMap<String, RevisionId>,
    /// Whether anything here was worked out rather than taken from the
    /// catalogue. A folder nobody has touched learns nothing, and rewriting
    /// the file for it would be the whole catalogue's bytes for no change at
    /// all, on every command.
    learned: bool,
}

#[cfg(feature = "disk")]
impl Working<Disk> {
    /// Walk `root` on disk, taking every file the rules leave.
    pub fn read(root: &Path, skipped: &Skipped) -> Result<Self, WorkingError> {
        Self::read_on(Disk, root, skipped)
    }
}

impl<F: Filesystem> Working<F> {
    /// Walk `root` on `filesystem`, taking every file the rules leave.
    ///
    /// `history/` is never tracked and needs no rule. A name that is not UTF-8,
    /// or anything that is neither a regular file nor a link, is refused by
    /// name rather than skipped quietly: decision 0011 puts the difference
    /// between losing work and not at one error message.
    ///
    /// Decision 0040 takes symbolic links off that list. A link is a thing a
    /// folder holds, so the walk *reads* it — with
    /// [`Filesystem::link_target`], which follows nothing — and takes it as a
    /// tracked path whose content is a target rather than bytes.
    ///
    /// Decision 0015: the refusals are collected rather than raised one at a
    /// time, so that `status` can list a folder's whole set and a person can
    /// write the `skip` rules in one pass. `record` raises the collection,
    /// which is the same refusal on the same files. What still returns here is
    /// [`WorkingError::Io`] — a directory that cannot be read is not a fact
    /// about the folder, it is not knowing, and a walk that collected it would
    /// describe a folder while quietly missing part of it.
    pub fn read_on(filesystem: F, root: &Path, skipped: &Skipped) -> Result<Self, WorkingError> {
        let mut found = Found::default();
        walk(&filesystem, root, "", skipped, &mut found)?;
        // Decision 0043: what the last command hashed, kept only where the
        // directory still reports the size and the time it hashed it at. A
        // filesystem that reports neither hands back nothing here, and every
        // digest below is worked out by reading — which is what every command
        // did before this existed.
        let digests = catalogue::believed(&filesystem, &root.join(STORE_DIR), &found.stamps);
        Ok(Self {
            filesystem,
            root: root.to_path_buf(),
            files: found.files,
            links: found.links,
            stamps: found.stamps,
            known: RefCell::new(Known {
                digests,
                learned: false,
            }),
            refused: found.refused,
        })
    }

    /// The filesystem this working copy was read from.
    pub fn filesystem(&self) -> &F {
        &self.filesystem
    }

    /// Every path the walk would not take, with the short reason.
    pub fn refused(&self) -> &[(String, String)] {
        &self.refused
    }

    /// Every tracked path, in order, with where it is on disk.
    pub fn iter(&self) -> impl Iterator<Item = (&String, &PathBuf)> {
        self.files.iter()
    }

    /// Where one tracked path is on disk.
    pub fn get(&self, path: &str) -> Option<&PathBuf> {
        self.files.get(path)
    }

    /// Whether the folder holds this path.
    pub fn holds(&self, path: &str) -> bool {
        self.files.contains_key(path)
    }

    /// How many files are tracked.
    pub fn len(&self) -> usize {
        self.files.len()
    }

    /// Whether nothing is tracked.
    pub fn is_empty(&self) -> bool {
        self.files.is_empty()
    }

    /// One file's text, refused if it is not UTF-8.
    ///
    /// 0007's items are lines of text, so this is the boundary a file already
    /// recorded as lines is held to. A file nobody has recorded yet is offered
    /// to [`kind_of`] instead, which decides what kind it is rather than
    /// refusing it.
    pub fn text(&self, path: &str) -> Result<String, WorkingError> {
        let on_disk = self.regular(path)?;
        match read_to_string(&self.filesystem, on_disk) {
            Ok(text) => Ok(text),
            Err(error) if error.kind() == io::ErrorKind::InvalidData => {
                Err(WorkingError::NotText {
                    path: path.to_owned(),
                })
            }
            Err(error) => Err(WorkingError::io(on_disk, error)),
        }
    }

    /// One file's bytes, whatever they are.
    ///
    /// Decision 0017: a file that is not text is content that arrives whole
    /// rather than content this format cannot hold.
    pub fn bytes(&self, path: &str) -> Result<Vec<u8>, WorkingError> {
        let on_disk = self.regular(path)?;
        self.filesystem
            .read(on_disk)
            .map_err(|error| WorkingError::io(on_disk, error))
    }

    /// What one tracked file's bytes hash to.
    ///
    /// Decision 0043, and the question `status` and `record` ask before they
    /// ask for a file's content: identity comes from content, so *has this
    /// changed* is a comparison of digests, and the digest the store already
    /// states is on the other side of it.
    ///
    /// Answered from `history/cache/working.txt` where the directory says the
    /// file has not been written to since that digest was taken, and by
    /// reading the file otherwise — in pieces where the filesystem offers
    /// them, so a photograph costs a buffer rather than its own size. Which of
    /// the two happened changes how long this took and nothing else.
    pub fn digest(&self, path: &str) -> Result<RevisionId, WorkingError> {
        let on_disk = self.regular(path)?;
        if let Some(known) = self.known.borrow().digests.get(path).copied() {
            return Ok(known);
        }
        let digest = crate::fs::digest_of(&self.filesystem, on_disk)
            .map_err(|error| WorkingError::io(on_disk, error))?;
        let mut known = self.known.borrow_mut();
        known.digests.insert(path.to_owned(), digest);
        known.learned = true;
        Ok(digest)
    }

    /// One file's bytes, and the digest this read found them to have.
    ///
    /// Decision 0036's rule, applied one level up: *a lookup hashes what it
    /// reads before believing it*. The catalogue says where to look and never
    /// what is there, so whatever it said about this path, these bytes are
    /// what the path holds — and a catalogue that was wrong about a file is
    /// corrected by the read it caused rather than costing that read on every
    /// command afterwards.
    pub fn bytes_and_digest(&self, path: &str) -> Result<(Vec<u8>, RevisionId), WorkingError> {
        let bytes = self.bytes(path)?;
        let found = crate::format::digest(&bytes);
        self.correct(path, found);
        Ok((bytes, found))
    }

    /// One file's text, and the digest this read found its bytes to have.
    ///
    /// [`Working::bytes_and_digest`] for the files that are lines.
    pub fn text_and_digest(&self, path: &str) -> Result<(String, RevisionId), WorkingError> {
        let text = self.text(path)?;
        let found = crate::format::digest(text.as_bytes());
        self.correct(path, found);
        Ok((text, found))
    }

    /// Replace what is known about a path with what a read of it found.
    fn correct(&self, path: &str, found: RevisionId) {
        let mut known = self.known.borrow_mut();
        if known.digests.insert(path.to_owned(), found) != Some(found) {
            known.learned = true;
        }
    }

    /// Write down what this pass worked out, so the next one need not.
    ///
    /// Called once, by whatever has finished asking — the catalogue is
    /// rewritten whole, and a caller that wrote it after every question would
    /// be quadratic in the size of the folder. Nothing is reported: a folder
    /// on a read-only filesystem and a `cache/` somebody deleted mid-command
    /// are both conditions under which describing a folder must still succeed,
    /// and nothing was lost, because nothing here was information.
    ///
    /// A folder that learned nothing writes nothing, so a `status` on a folder
    /// nobody has touched leaves `cache/` exactly as it found it.
    pub fn remember(&self) {
        let known = self.known.borrow();
        if !known.learned || self.stamps.is_empty() {
            return;
        }
        catalogue::write(
            &self.filesystem,
            &self.root.join(STORE_DIR),
            &known.digests,
            &self.stamps,
        );
    }

    /// Whether one tracked file can be run, or `None` where this filesystem
    /// has no such bit.
    ///
    /// Decision 0034: `None` is not `false`. A recorder that cannot see the
    /// bit states nothing about it and leaves the recorded value standing,
    /// which is what stops two machines flipping it at each other.
    pub fn executable(&self, path: &str) -> Result<Option<bool>, WorkingError> {
        let on_disk = self.files.get(path).ok_or_else(|| WorkingError::Missing {
            path: path.to_owned(),
        })?;
        self.filesystem
            .executable(on_disk)
            .map_err(|error| WorkingError::io(on_disk, error))
    }

    /// Whether one tracked path is a symbolic link.
    pub fn is_link(&self, path: &str) -> bool {
        self.links.contains_key(path)
    }

    /// What one tracked link points at, as the folder spells it.
    ///
    /// `None` for a path that is not a link, and for a link on a filesystem
    /// that reports links and cannot read one — which a caller tells apart
    /// with [`Working::is_link`], and which decision 0040 makes the same
    /// answer either way: state nothing.
    pub fn link_target(&self, path: &str) -> Option<&str> {
        self.links.get(path)?.as_deref()
    }

    /// Every tracked link, with what it points at.
    pub fn links(&self) -> impl Iterator<Item = (&String, Option<&str>)> {
        self.links
            .iter()
            .map(|(path, target)| (path, target.as_deref()))
    }

    /// Where a tracked *regular* file is on disk.
    ///
    /// The one guard that keeps decision 0040's standing rule true by
    /// construction: a link is tracked now, and reading its path through
    /// `read` would open what it points at rather than the link. A caller that
    /// wants a link asks for its target.
    fn regular(&self, path: &str) -> Result<&PathBuf, WorkingError> {
        if self.links.contains_key(path) {
            return Err(WorkingError::IsALink {
                path: path.to_owned(),
            });
        }
        self.files.get(path).ok_or_else(|| WorkingError::Missing {
            path: path.to_owned(),
        })
    }
}

/// Which kind of file a person has just put in the folder.
///
/// Decision 0017 puts this rule in the tool rather than in the format: text is
/// valid UTF-8 with no NUL byte, and everything else is bytes. The format's
/// own rule is narrower — a `text` payload is valid UTF-8, because a later
/// `edit` has to quote its items — and NUL is the oldest and most reliable
/// signal that a person did not write this file as prose. A recorder is
/// allowed signals the format may not use.
///
/// Sniffed once, when a file is added, and never again: after that the kind
/// belongs to the file's identity and changing it is `drop` and `add`.
pub fn is_text(bytes: &[u8]) -> bool {
    !bytes.contains(&0) && std::str::from_utf8(bytes).is_ok()
}

/// What one walk of the folder turned up.
#[derive(Default)]
struct Found {
    files: BTreeMap<String, PathBuf>,
    links: BTreeMap<String, Option<String>>,
    stamps: BTreeMap<String, Stamp>,
    refused: Vec<(String, String)>,
}

/// One directory, then its subdirectories, in name order.
fn walk<F: Filesystem + ?Sized>(
    filesystem: &F,
    directory: &Path,
    prefix: &str,
    skipped: &Skipped,
    found: &mut Found,
) -> Result<(), WorkingError> {
    let mut entries = filesystem
        .entries(directory)
        .map_err(|error| WorkingError::io(directory, error))?;
    // The trait promises no order, and this walk's order is the order a
    // refusal list is printed in.
    entries.sort();

    for Entry {
        path: on_disk,
        kind,
    } in entries
    {
        let Some(name) = on_disk
            .file_name()
            .and_then(|name| name.to_str())
            .map(str::to_owned)
        else {
            // A name that cannot be spelled cannot be walked into either, so a
            // directory refused here is one refusal rather than one per file
            // beneath it.
            let path = on_disk.to_string_lossy().into_owned();
            let because = WorkingError::NotUtf8 { path: path.clone() }.because();
            found.refused.push((path, because));
            continue;
        };
        // Decision 0033: the store spells a path in normal form C, and this
        // is where a name the filesystem handed back decomposed becomes the
        // path it was recorded as. `on_disk` keeps the spelling the folder
        // actually uses, because that is what has to be opened.
        let name = crate::format::nfc(&name).into_owned();
        let path = if prefix.is_empty() {
            name
        } else {
            format!("{prefix}/{name}")
        };

        // The store is not tracked, and says so without a rule.
        if prefix.is_empty() && path == STORE_DIR {
            continue;
        }

        if kind.is_directory() {
            if !skipped.skips_directory(&path) {
                walk(filesystem, &on_disk, &path, skipped, found)?;
            }
            continue;
        }
        if skipped.skips(&path) {
            continue;
        }
        if !kind.is_file() && !kind.is_symlink() {
            let because = WorkingError::NotAFile { path: path.clone() }.because();
            found.refused.push((path, because));
            continue;
        }
        if let Err(unusable) = check_path(&path) {
            let because = WorkingError::Unusable {
                path: path.clone(),
                because: unusable.to_string(),
            }
            .because();
            found.refused.push((path, because));
            continue;
        }
        // Decision 0040: read here, once, with the walk — because this is
        // where the entry is known to be a link, and asking later would mean
        // asking a folder that has moved on. A filesystem that reports a link
        // and cannot say where it points answers `None`, and the recorder
        // leaves whatever is recorded standing.
        if kind.is_symlink() {
            let target = match filesystem.link_target(&on_disk) {
                Ok(target) => target,
                Err(error) if error.kind() == io::ErrorKind::InvalidData => {
                    let because = WorkingError::LinkNotUtf8 { path: path.clone() }.because();
                    found.refused.push((path, because));
                    continue;
                }
                Err(error) => return Err(WorkingError::io(&on_disk, error)),
            };
            found.links.insert(path.clone(), target);
        } else if let Ok(Some(stamp)) = filesystem.stamp(&on_disk) {
            // Decision 0043: taken here, with the walk, because this is where
            // the entry is known to be a regular file and because a stamp
            // taken later would be a stamp of a folder that has moved on.
            // A filesystem with no such thing to report, and a file that
            // vanished between the listing and the question, are the same
            // answer: nothing is remembered about it and the next command that
            // wants its digest reads it.
            found.stamps.insert(path.clone(), stamp);
        }
        found.files.insert(path, on_disk);
    }
    Ok(())
}

/// Why a working copy could not be read.
#[derive(Debug)]
#[non_exhaustive]
pub enum WorkingError {
    /// A filename whose bytes are not UTF-8, which 0008 refuses.
    NotUtf8 {
        /// The name, rendered as best it can be.
        path: String,
    },
    /// A path the format cannot hold, for a reason it can state.
    Unusable {
        /// The path.
        path: String,
        /// What is wrong with it.
        because: String,
    },
    /// A device, a socket, or anything else that is neither a file nor a link.
    NotAFile {
        /// The path.
        path: String,
    },
    /// A link whose target is not UTF-8, which this store cannot write down.
    LinkNotUtf8 {
        /// The path.
        path: String,
    },
    /// A link asked for as though it held bytes.
    ///
    /// Decision 0040's standing rule, made structural: reading a link's path
    /// would open what it points at, so nothing here does.
    IsALink {
        /// The path.
        path: String,
    },
    /// A file recorded as lines whose bytes are no longer UTF-8.
    NotText {
        /// The path.
        path: String,
    },
    /// A path asked for that the folder does not hold.
    Missing {
        /// The path.
        path: String,
    },
    /// The filesystem refused.
    Io {
        /// What was being read.
        path: PathBuf,
        /// The underlying failure.
        error: io::Error,
    },
}

impl WorkingError {
    fn io(path: impl AsRef<Path>, error: io::Error) -> Self {
        Self::Io {
            path: path.as_ref().to_path_buf(),
            error,
        }
    }

    /// The reason alone, for a list of refusals rather than a single failure.
    ///
    /// [`fmt::Display`] says the reason and then what to do about it, which is
    /// right when one file stops a command and repetitive when twelve are
    /// listed together. The caller listing them says the fix once.
    pub fn because(&self) -> String {
        match self {
            WorkingError::NotUtf8 { .. } => "not a name this format can hold".to_owned(),
            WorkingError::Unusable { because, .. } => because.clone(),
            WorkingError::NotAFile { .. } => "not a regular file".to_owned(),
            WorkingError::LinkNotUtf8 { .. } => {
                "a link pointing at a name that is not UTF-8".to_owned()
            }
            WorkingError::IsALink { .. } => {
                "a link, which holds a target rather than bytes".to_owned()
            }
            WorkingError::NotText { .. } => {
                "recorded as lines and no longer UTF-8 text; drop it and add it again".to_owned()
            }
            WorkingError::Missing { .. } => "not in the working copy".to_owned(),
            WorkingError::Io { error, .. } => error.to_string(),
        }
    }
}

impl fmt::Display for WorkingError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            WorkingError::NotUtf8 { path } => write!(
                f,
                "{path} is not a name this format can hold: a path is UTF-8; \
                 rename it, or `skip` it in `{STORE_DIR}/{SKIPPED_DIR}/`"
            ),
            WorkingError::Unusable { path, because } => write!(
                f,
                "`{path}` cannot be a path here: {because}; rename it, or `skip` \
                 it in `{STORE_DIR}/{SKIPPED_DIR}/`"
            ),
            WorkingError::NotAFile { path } => write!(
                f,
                "`{path}` is neither a regular file nor a link, and this format \
                 spells nothing else; `skip` it in `{STORE_DIR}/{SKIPPED_DIR}/`"
            ),
            WorkingError::LinkNotUtf8 { path } => write!(
                f,
                "`{path}` points at a name that is not UTF-8, and this store is \
                 UTF-8 text; point it somewhere spellable, or `skip` it in \
                 `{STORE_DIR}/{SKIPPED_DIR}/`"
            ),
            WorkingError::IsALink { path } => write!(
                f,
                "`{path}` is a link, which holds a target rather than bytes; \
                 nothing reads through a link, so ask it where it points"
            ),
            WorkingError::NotText { path } => write!(
                f,
                "`{path}` was recorded as lines and is no longer UTF-8 text; \
                 a file's kind is fixed when it is added, so this is a `drop` \
                 and an `add` rather than an edit"
            ),
            WorkingError::Missing { path } => {
                write!(f, "`{path}` is not in the working copy")
            }
            WorkingError::Io { path, error } => write!(f, "{}: {error}", path.display()),
        }
    }
}

impl std::error::Error for WorkingError {}

#[cfg(test)]
mod tests {
    use super::*;

    fn skipped(text: &str) -> Skipped {
        Skipped::from_rules(text.lines().filter(|line| !line.is_empty()).map(|line| {
            Skipped::rule_in(line)
                .expect("a rule the reader accepts")
                .expect("a line that states one")
        }))
    }

    #[test]
    fn a_path_rule_names_one_file_and_a_slash_names_a_directory() {
        let rules = skipped("skip target/\nskip .DS_Store\n");
        assert!(rules.skips("target/debug/notes.md"));
        assert!(!rules.skips("targets.md"));
        assert!(!rules.skips("target"), "the directory itself is not a file");
        assert!(rules.skips(".DS_Store"));
        assert!(!rules.skips("docs/.DS_Store"), "an exact path is exact");
    }

    #[test]
    fn a_name_rule_matches_a_files_own_name_at_any_depth() {
        let rules = skipped("skip-name *.tmp\n");
        assert!(rules.skips("docs/draft.tmp"));
        assert!(rules.skips("draft.tmp"));
        assert!(!rules.skips("docs.tmp/draft.md"));
        // Decision 0049: any run, including an empty one, so `*.tmp` is the
        // whole of what `skip-suffix .tmp` said and reaches `.tmp` besides.
        assert!(rules.skips("docs/.tmp"));
    }

    #[test]
    fn a_name_and_under_rule_matches_a_directorys_name() {
        let rules = skipped("skip-name node_modules/\n");
        assert!(rules.skips("app/node_modules/left-pad/index.js"));
        assert!(rules.skips("node_modules/x"));
        assert!(
            !rules.skips("node_modules"),
            "a directory rule does not cover a file of that name"
        );
        assert!(rules.skips_directory("app/node_modules"));
        assert!(!rules.skips_directory("app/node"));
    }

    #[test]
    fn a_star_stands_for_any_run_within_one_component() {
        let pattern = |value: &str| Pattern::parse(value).expect("a pattern");
        assert!(pattern("draft-*.md").matches("draft-two.md"));
        assert!(pattern("draft-*.md").matches("draft-.md"));
        assert!(!pattern("draft-*.md").matches("drafts.md"));
        assert!(pattern("~$*.docx").matches("~$report.docx"));
        assert!(
            pattern("*den").matches(".hidden"),
            "a run may begin with a dot, so dotfiles need no companion rule"
        );
        assert!(pattern("*.tmp").matches(".tmp"), "and may be empty");
        assert!(pattern("*a*ab").matches("aab"), "runs are found in order");
        assert!(!pattern("a*b").matches("ab/c"), "a component holds no `/`");
    }

    #[test]
    fn a_pattern_refuses_a_separator_and_refuses_being_only_stars() {
        assert!(Pattern::parse("docs/*.tmp").is_err());
        assert!(Pattern::parse("*").is_err());
        assert!(Pattern::parse("**").is_err());
        assert!(Pattern::parse("").is_err());
        assert!(Skipped::rule_in("skip-name */\n").is_err());
    }

    #[test]
    fn an_unknown_key_is_an_error_naming_the_line() {
        let refused = Skipped::rule_in("# a note\nignore secrets\n").expect_err("refused");
        assert_eq!(refused.at, 2);
        assert!(refused.to_string().contains("`skip-name`"));
        assert!(refused.to_string().contains("`private-name`"));
    }

    #[test]
    fn skip_suffix_is_refused_by_name_and_says_what_replaces_it() {
        let refused = Skipped::rule_in("skip-suffix .tmp\n").expect_err("refused");
        assert!(refused.to_string().contains("`skip-suffix` is retired"));
        assert_eq!(
            Skipped::retired_in("skip-suffix .tmp\n").as_deref(),
            Some("skip-name *.tmp")
        );
        assert_eq!(Skipped::retired_in("skip target/\n"), None);
    }

    #[test]
    fn a_line_that_is_not_a_rule_is_an_error() {
        assert!(Skipped::rule_in("skip\n").is_err());
        assert!(Skipped::rule_in("skip \n").is_err());
        assert!(Skipped::rule_in("skip  padded\n").is_err());
        assert!(Skipped::rule_in("skip /\n").is_err());
    }

    #[test]
    fn a_file_states_one_rule() {
        // Decision 0045: the second rule is refused where a line number used
        // to be reported, because the fix is now to split the file in two.
        let refused = Skipped::rule_in("skip target/\nskip-name *.tmp\n").expect_err("refused");
        assert_eq!(refused.at, 2);
        assert!(refused.to_string().contains("one rule"));
    }

    #[test]
    fn a_file_of_comments_states_nothing() {
        assert_eq!(Skipped::rule_in(SKIPPED_NOTE), Ok(None));
    }

    #[test]
    fn a_rule_stated_twice_is_stated_once() {
        let rules = skipped("skip target/\nskip target/\nskip-name *.tmp\n");
        assert_eq!(rules.len(), 2);
    }

    #[test]
    fn a_private_rule_and_its_shared_twin_are_two_rules() {
        // Decision 0049: the flag is part of the rule's identity, which is
        // what lets a union take both rather than tie-break between them.
        let rules = skipped("skip docs/\nprivate docs/\n");
        assert_eq!(rules.len(), 2);
        assert_eq!(rules.travelling().count(), 1);
        assert_eq!(rules.withheld(), 1);
        assert_ne!(
            Rule::shared(Scope::Under("docs".into())),
            Rule::private(Scope::Under("docs".into()))
        );
    }

    #[test]
    fn a_label_mirrors_the_path() {
        assert_eq!(
            Rule::shared(Scope::Path("docs/notes.md".into())).label(),
            "docs/notes.md.txt"
        );
        assert_eq!(
            Rule::shared(Scope::Under("target".into())).label(),
            "target/all.txt"
        );
        assert_eq!(
            Rule::shared(Scope::Name(Pattern::parse("notes.md").expect("a pattern"))).label(),
            "name notes.md.txt"
        );
        assert_eq!(
            Rule::shared(Scope::NameUnder(
                Pattern::parse("drafts").expect("a pattern")
            ))
            .label(),
            "name drafts/all.txt"
        );
        // The two rules that would otherwise want one name.
        assert_ne!(
            Rule::shared(Scope::Path("target".into())).label(),
            Rule::shared(Scope::Under("target".into())).label()
        );
    }

    #[test]
    fn a_label_the_store_cannot_own_is_the_rules_digest() {
        // A name the reader would skip as the platform's (0022), the name
        // `init` writes, the name a directory rule takes, and — decision
        // 0049 — a value holding a star.
        for rule in [
            Rule::shared(Scope::Path("._resources".into())),
            Rule::shared(Scope::Path("README".into())),
            Rule::shared(Scope::Path("docs/all".into())),
            Rule::shared(Scope::Name(Pattern::parse("*.tmp").expect("a pattern"))),
        ] {
            assert_eq!(rule.label(), rule.digest_label(), "{rule}");
        }
        // And the digest is the rule's, so two replicas agree on it.
        assert_eq!(
            Rule::shared(Scope::Path("._resources".into())).label(),
            Rule::shared(Scope::Path("._resources".into())).digest_label()
        );
        // A private rule and its shared twin derive two names, because the
        // rendered line carries the key.
        assert_ne!(
            Rule::shared(Scope::Path("._resources".into())).digest_label(),
            Rule::private(Scope::Path("._resources".into())).digest_label()
        );
    }

    #[test]
    fn a_label_is_read_back_as_the_rule_it_states() {
        for rule in [
            Rule::shared(Scope::Path("docs/notes.md".into())),
            Rule::shared(Scope::Under("target".into())),
            Rule::shared(Scope::Name(Pattern::parse("*.tmp").expect("a pattern"))),
            Rule::shared(Scope::NameUnder(
                Pattern::parse("node_modules").expect("a pattern"),
            )),
            Rule::private(Scope::Path("clients/acme".into())),
            Rule::private(Scope::Under("therapy".into())),
            Rule::private(Scope::Name(Pattern::parse("*.key").expect("a pattern"))),
            Rule::private(Scope::NameUnder(
                Pattern::parse("draft-*").expect("a pattern"),
            )),
            Rule::shared(Scope::Path("._resources".into())),
        ] {
            let stated = format!("{rule}\n");
            assert_eq!(Skipped::rule_in(&stated), Ok(Some(rule)));
        }
    }
}
