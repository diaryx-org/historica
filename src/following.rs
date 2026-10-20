//! A rule that follows what an identity's keys vouched for.
//!
//! Historica's decision 0086 has a copy choose its heads. A *tip* is a fact
//! about the store, and a *head* is a tip of the part of history the copy
//! follows. Which part that is, the embedder says with a rule asked of one
//! revision at a time:
//!
//! ```text
//! Fn(&RevisionId, &RevisionDocument) -> bool + Send + Sync
//! ```
//!
//! 0086 names this crate as where a forge's rule comes from: follow what a
//! maintainer's keys vouched for. [`Vouched`] is that rule. It accepts a
//! revision when a whole-revision claim over its digest verifies under one of
//! the keys it was given, and the key was not revoked when the claim says it
//! was made.
//!
//! # Plugging it in
//!
//! The rule is shaped like historica's `Accepts`, but this crate does not name
//! that type: it depends on historica by version, and the release it is
//! written against predates `Following`. Only [`RevisionId`] and
//! [`RevisionDocument`] cross the boundary, and both have been in every
//! release. A caller on a historica that has `Following` writes:
//!
//! ```text
//! let rule = Vouched::trusted(store.filesystem(), store.root())?;
//! let following = Following::Rule(Box::new(rule.into_rule()));
//! let heads = following.heads(&store);
//! ```
//!
//! # What it reads, and when
//!
//! Every claim is read and every signature checked once, when the rule is
//! made, and what is kept is the set of digests that passed. Asking about a
//! revision is then one lookup. A rule made before a claim arrived does not
//! know about it, which is also true of a [`crate::verify::Report`]: make the
//! rule again after `receive`.
//!
//! # What it accepts, and what it leaves to historica
//!
//! Only a claim over a whole revision (`claim-0`) is accepted. A claim over
//! one file (decision 0004) or over one document (decision 0006) vouches for
//! no revision, as [`crate::verify`] already says.
//!
//! The rule answers for the revision a claim names and for nothing else.
//! Following a revision follows everything it stands on, and historica makes
//! that true itself, so a claim over a head is enough to follow the whole
//! line behind it, as a claim over a head covers the history behind it.
//!
//! The rule never reports why it refused a claim. A claim that does not
//! parse, a signature that does not verify, a key it was not given: each is
//! simply not counted. [`crate::verify::verify`] is where those are reported.

use std::collections::{BTreeMap, BTreeSet};
use std::io;
use std::path::Path;

use historica::core::RevisionId;
use historica::format::{RevisionDocument, Timestamp};
use historica::fs::{Filesystem, read_to_string};

use crate::claim::{Claim, Key, Role, Scope};
use crate::layout::claims;
use crate::trust::{Entry, Trust, instant};
use crate::verify::{check_signature, look};

/// The revisions an identity's keys vouched for: a rule for historica's
/// `Following::Rule`.
///
/// An identity is the keys it was given, each with its history. Every key
/// counts as the identity, as every key on an account counts as the account:
/// a person with a key on each of three machines vouches with any of them.
/// Which keys belong together is the caller's to say. This crate never groups
/// entries by `who`, which is a label and not an identity.
#[derive(Debug, Clone, Default)]
pub struct Vouched {
    /// Each key, and the earliest moment it was revoked, if it was.
    keys: BTreeMap<Key, Option<Timestamp>>,
    /// Each revision a claim that counts names, and the roles it was claimed
    /// in.
    revisions: BTreeMap<RevisionId, BTreeSet<Role>>,
    /// The roles that count, or `None` for every role.
    roles: Option<BTreeSet<Role>>,
}

impl Vouched {
    /// A rule over these keys, which accepts nothing until claims are
    /// [admitted](Vouched::admit).
    ///
    /// A key given twice keeps the earlier revocation, and a revocation in
    /// either entry wins over none: removal has to win.
    pub fn new(keys: impl IntoIterator<Item = Entry>) -> Self {
        let mut held: BTreeMap<Key, Option<Timestamp>> = BTreeMap::new();
        for entry in keys {
            let revoked = entry.revoked;
            match held.get_mut(&entry.key) {
                None => {
                    held.insert(entry.key, revoked);
                }
                Some(earlier) => {
                    if let Some(revoked) = revoked
                        && earlier
                            .as_ref()
                            .is_none_or(|earlier| instant(&revoked) < instant(earlier))
                    {
                        *earlier = Some(revoked);
                    }
                }
            }
        }
        Self {
            keys: held,
            ..Self::default()
        }
    }

    /// Count only claims made in one of these roles.
    ///
    /// By default every role counts. A role is what a person says they were
    /// doing, and this crate keeps no vocabulary of roles ([`Role`]), so it
    /// has no standing to say which ones mean "this is my line". A caller that
    /// does narrows it here. A forge where a `reviewer` claim is an approval,
    /// and taking an offer is a separate act, follows `author` alone, so that
    /// approving a contributor's tip does not make it the maintainer's head.
    ///
    /// May be called before or after claims are admitted: roles are kept per
    /// revision and compared when the rule is asked.
    pub fn only(mut self, roles: impl IntoIterator<Item = Role>) -> Self {
        self.roles = Some(roles.into_iter().collect());
        self
    }

    /// Read the claims in a store's `claims/` directory, and keep those these
    /// keys vouched for.
    ///
    /// A store with no `claims/` directory is a store nobody has vouched for,
    /// and makes a rule that accepts nothing.
    pub fn read<F: Filesystem + ?Sized>(
        files: &F,
        root: &Path,
        keys: impl IntoIterator<Item = Entry>,
    ) -> io::Result<Self> {
        let mut rule = Self::new(keys);
        let (found, signatures, _, _) = look(files, &claims(root))?;
        for (name, path) in found {
            // A claim with no signature beside it vouches for nothing.
            let Some(signature) = signatures.get(name.as_str()) else {
                continue;
            };
            let bytes = files.read(&path)?;
            let signature = read_to_string(files, signature)?;
            rule.admit(&bytes, &signature);
        }
        Ok(rule)
    }

    /// Read the claims in a store's `claims/` directory, and keep those a key
    /// in its `trust/` directory vouched for.
    ///
    /// The rule decision 0086 names: every key this copy believes is taken to
    /// be one identity's. A trust file that is not an entry is skipped here,
    /// and [`crate::verify::verify`] reports it.
    pub fn trusted<F: Filesystem + ?Sized>(files: &F, root: &Path) -> io::Result<Self> {
        let policy = Trust::read(files, root)?;
        let keys: Vec<Entry> = policy.entries().map(|(_, entry)| entry.clone()).collect();
        Self::read(files, root, keys)
    }

    /// Take one claim and its signature, and say whether it counts.
    ///
    /// It counts when it parses as a whole-revision claim, names a key this
    /// rule was given, was made before that key was revoked, and its
    /// signature verifies under that key. `signature` is the text of the
    /// `.minisig` file. This is how a caller that does not hold the claims
    /// as files, such as a server reading them from a database, makes the
    /// rule.
    pub fn admit(&mut self, bytes: &[u8], signature: &str) -> bool {
        let Some(claim) = std::str::from_utf8(bytes)
            .ok()
            .and_then(|text| Claim::parse(text).ok())
        else {
            return false;
        };
        if claim.scope != Scope::Revision {
            return false;
        }
        let Some(revoked) = self.keys.get(&claim.key) else {
            return false;
        };
        if revoked
            .as_ref()
            .is_some_and(|revoked| instant(revoked) <= instant(&claim.when))
        {
            return false;
        }
        if check_signature(bytes, signature, &claim.key).is_err() {
            return false;
        }
        self.revisions
            .entry(claim.revision)
            .or_default()
            .insert(claim.role);
        true
    }

    /// Whether this rule follows a revision: a claim that counts names its
    /// digest, in a role that counts.
    ///
    /// The document is not read. A claim is over a digest, and the digest is
    /// the identity of the bytes, so `id` is the whole of the question. The
    /// parameter is there so the method has the shape of historica's
    /// `Accepts`.
    pub fn accepts(&self, id: &RevisionId, _document: &RevisionDocument) -> bool {
        self.vouches_for(id)
    }

    /// The same question, for a caller holding only the digest.
    pub fn vouches_for(&self, id: &RevisionId) -> bool {
        self.revisions.get(id).is_some_and(|roles| {
            self.roles
                .as_ref()
                .is_none_or(|only| !roles.is_disjoint(only))
        })
    }

    /// Every revision this rule follows directly, in no particular order of
    /// history.
    pub fn revisions(&self) -> impl Iterator<Item = &RevisionId> {
        self.revisions
            .keys()
            .filter(|revision| self.vouches_for(revision))
    }

    /// The rule as a closure, for historica's `Following::Rule`:
    /// `Following::Rule(Box::new(rule.into_rule()))`.
    pub fn into_rule(
        self,
    ) -> impl Fn(&RevisionId, &RevisionDocument) -> bool + Send + Sync + 'static {
        move |id, document| self.accepts(id, document)
    }
}
