//! The rule a copy follows when it follows what an identity's keys vouched for.
//!
//! Historica's decision 0086 asks a rule one question of one revision. These
//! tests ask it of real revisions, with claims signed by real keys, and damage
//! the claims on purpose: the rule's worth is what it refuses.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};

use historica::core::RevisionId;
use historica::format::{RevisionDocument, Timestamp};
use historica::record::{Clock, Kinds, Platform, Recording, Restriction, record};
use historica::store::Store;
use historica::working::Working;
use historica_minisign::claim::{Claim, Key, Scope};
use historica_minisign::sign::SecretKey;
use historica_minisign::trust::Entry;
use historica_minisign::verify::Finding;
use historica_minisign::{Vouched, key, naming, sign, trust, verify};

const PASSWORD: &str = "not a secret";

fn scratch(test: &str) -> PathBuf {
    let path = Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("following-{test}"));
    let _ = fs::remove_dir_all(&path);
    fs::create_dir_all(&path).expect("a scratch directory");
    path
}

/// A store of `revisions` revisions over one file, each descending from the
/// last, and their digests in the order they were recorded.
fn store_of(directory: &Path, revisions: usize) -> (Store, Vec<RevisionId>) {
    let folder = directory.join("work");
    fs::create_dir_all(&folder).expect("a folder");
    let mut store = Store::init(folder.join("history")).expect("a store");
    let mut ids = Vec::new();

    for step in 0..revisions {
        fs::write(folder.join("notes.txt"), format!("line {step}\n")).expect("a file");
        let working = Working::read(&folder, store.skipped()).expect("the folder");
        let recording = Recording {
            parents: store.history().childless().into_iter().collect(),
            author: "Adam Harris <adam@example.com>".to_owned(),
            when: Platform.now().expect("a clock"),
            message: format!("step {step}"),
            moves: Vec::new(),
            at: Vec::new(),
            accepted: BTreeSet::new(),
            only: Restriction::Everything,
            kinds: Kinds::default(),
            extensions: BTreeMap::new(),
        };
        record(&mut store, &working, &recording, &mut Platform).expect("a revision");
        let head = verify::current_heads(&store)
            .into_iter()
            .next()
            .expect("a head");
        ids.push(head);
    }
    (store, ids)
}

/// A key pair under `directory/name`, unlocked.
fn keys(directory: &Path, name: &str) -> (SecretKey, Key) {
    let home = directory.join(name);
    let generated = key::generate(&home, Some(PASSWORD.to_owned())).expect("a key pair");
    let secret = key::load(&generated.secret, Some(PASSWORD.to_owned())).expect("the key back");
    (secret, generated.key)
}

fn at(text: &str) -> Timestamp {
    text.parse().expect("a timestamp")
}

/// A claim over `revision` by `key`, said to be made at `when`, as its bytes
/// and its signature by `secret`.
fn claim(
    revision: RevisionId,
    role: &str,
    key: &Key,
    when: &str,
    secret: &SecretKey,
) -> (Vec<u8>, String) {
    let claim = Claim {
        revision,
        scope: Scope::Revision,
        role: role.parse().expect("a role"),
        key: key.clone(),
        when: at(when),
    };
    let bytes = claim.render().into_bytes();
    let signature = sign::signature(secret, &bytes, "a.claim.txt").expect("a signature");
    (bytes, signature)
}

fn document(store: &Store, id: &RevisionId) -> RevisionDocument {
    store
        .get(id)
        .expect("the store reads")
        .expect("the revision")
        .clone()
}

fn entry(key: &Key) -> Entry {
    Entry::new(key.clone(), "Adam Harris <adam@example.com>")
}

fn revoked(key: &Key, when: &str) -> Entry {
    Entry {
        revoked: Some(at(when)),
        ..entry(key)
    }
}

#[test]
fn a_claim_by_a_given_key_is_accepted() {
    let directory = scratch("accepted");
    let (store, ids) = store_of(&directory, 2);
    let (secret, key) = keys(&directory, "laptop");

    let mut rule = Vouched::new([entry(&key)]);
    let (bytes, signature) = claim(ids[1], "author", &key, "2026-10-01T09:00:00-06:00", &secret);
    assert!(rule.admit(&bytes, &signature));

    assert!(rule.accepts(&ids[1], &document(&store, &ids[1])));
    // The rule answers for what a claim names. Following what that stands on
    // is historica's to do.
    assert!(!rule.accepts(&ids[0], &document(&store, &ids[0])));
}

#[test]
fn a_claim_by_a_key_it_was_not_given_is_refused() {
    let directory = scratch("untrusted");
    let (store, ids) = store_of(&directory, 1);
    let (_, mine) = keys(&directory, "mine");
    let (theirs, their_key) = keys(&directory, "theirs");

    let mut rule = Vouched::new([entry(&mine)]);
    let (bytes, signature) = claim(
        ids[0],
        "author",
        &their_key,
        "2026-10-01T09:00:00-06:00",
        &theirs,
    );
    assert!(!rule.admit(&bytes, &signature));
    assert!(!rule.accepts(&ids[0], &document(&store, &ids[0])));
}

#[test]
fn a_claim_before_revocation_counts_and_one_at_or_after_it_does_not() {
    let directory = scratch("revoked");
    let (store, ids) = store_of(&directory, 3);
    let (secret, key) = keys(&directory, "lost");

    let mut rule = Vouched::new([revoked(&key, "2026-10-19T08:30:00-06:00")]);
    let before = claim(ids[0], "author", &key, "2026-10-19T08:29:59-06:00", &secret);
    let exactly = claim(ids[1], "author", &key, "2026-10-19T08:30:00-06:00", &secret);
    // The same instant as the revocation, in another offset.
    let after = claim(ids[2], "author", &key, "2026-10-19T14:30:01+00:00", &secret);
    assert!(rule.admit(&before.0, &before.1));
    assert!(!rule.admit(&exactly.0, &exactly.1));
    assert!(!rule.admit(&after.0, &after.1));

    assert!(rule.accepts(&ids[0], &document(&store, &ids[0])));
    assert!(!rule.accepts(&ids[1], &document(&store, &ids[1])));
    assert!(!rule.accepts(&ids[2], &document(&store, &ids[2])));
}

#[test]
fn a_revocation_in_either_of_two_entries_for_one_key_wins() {
    let directory = scratch("revoked-twice");
    let (_, ids) = store_of(&directory, 1);
    let (secret, key) = keys(&directory, "lost");

    let mut rule = Vouched::new([
        entry(&key),
        revoked(&key, "2026-10-19T08:30:00-06:00"),
        revoked(&key, "2026-12-01T00:00:00+00:00"),
    ]);
    let late = claim(ids[0], "author", &key, "2026-11-01T00:00:00+00:00", &secret);
    assert!(!rule.admit(&late.0, &late.1));
}

#[test]
fn a_claim_over_another_digest_does_not_vouch_for_this_one() {
    let directory = scratch("other-digest");
    let (store, ids) = store_of(&directory, 2);
    let (secret, key) = keys(&directory, "laptop");

    let mut rule = Vouched::new([entry(&key)]);
    let (bytes, signature) = claim(ids[0], "author", &key, "2026-10-01T09:00:00-06:00", &secret);
    assert!(rule.admit(&bytes, &signature));
    assert!(!rule.accepts(&ids[1], &document(&store, &ids[1])));

    // And a claim edited to name the other digest no longer verifies.
    let edited = String::from_utf8(bytes)
        .expect("text")
        .replace(&ids[0].to_string(), &ids[1].to_string());
    let mut rule = Vouched::new([entry(&key)]);
    assert!(!rule.admit(edited.as_bytes(), &signature));
    assert!(!rule.accepts(&ids[1], &document(&store, &ids[1])));
}

#[test]
fn a_tampered_signature_is_refused() {
    let directory = scratch("tampered");
    let (store, ids) = store_of(&directory, 1);
    let (secret, key) = keys(&directory, "laptop");
    let (other, _) = keys(&directory, "other");

    let mut rule = Vouched::new([entry(&key)]);
    let (bytes, signature) = claim(ids[0], "author", &key, "2026-10-01T09:00:00-06:00", &secret);

    // A signature by another key over the same bytes.
    let forged = sign::signature(&other, &bytes, "a.claim.txt").expect("a signature");
    assert!(!rule.admit(&bytes, &forged));

    // The right signature with one character in the middle of it changed:
    // the signature itself, past minisign's algorithm and key ID.
    let mut lines: Vec<String> = signature.lines().map(str::to_owned).collect();
    let line = &mut lines[1];
    let flipped = if line.as_bytes()[40] == b'A' {
        "B"
    } else {
        "A"
    };
    line.replace_range(40..41, flipped);
    assert!(!rule.admit(&bytes, &(lines.join("\n") + "\n")));
    // And the untouched one still counts, so it was the change that failed.
    let mut fresh = Vouched::new([entry(&key)]);
    assert!(fresh.admit(&bytes, &signature));

    // No signature at all.
    assert!(!rule.admit(&bytes, ""));

    assert!(!rule.accepts(&ids[0], &document(&store, &ids[0])));
}

#[test]
fn any_of_an_identitys_keys_vouches_for_it() {
    let directory = scratch("several-keys");
    let (_, ids) = store_of(&directory, 3);
    let (laptop, laptop_key) = keys(&directory, "laptop");
    let (phone, phone_key) = keys(&directory, "phone");

    let mut rule = Vouched::new([
        revoked(&laptop_key, "2026-10-19T08:30:00-06:00"),
        entry(&phone_key),
    ]);
    let by_laptop = claim(
        ids[0],
        "author",
        &laptop_key,
        "2026-09-01T09:00:00-06:00",
        &laptop,
    );
    let by_phone = claim(
        ids[1],
        "author",
        &phone_key,
        "2026-10-20T09:00:00-06:00",
        &phone,
    );
    // The laptop was lost: what it signs now does not count, and the phone is
    // unaffected.
    let late = claim(
        ids[2],
        "author",
        &laptop_key,
        "2026-10-20T09:00:00-06:00",
        &laptop,
    );
    assert!(rule.admit(&by_laptop.0, &by_laptop.1));
    assert!(rule.admit(&by_phone.0, &by_phone.1));
    assert!(!rule.admit(&late.0, &late.1));

    let followed: BTreeSet<&RevisionId> = rule.revisions().collect();
    assert_eq!(followed, BTreeSet::from([&ids[0], &ids[1]]));
}

#[test]
fn a_rule_can_count_some_roles_only() {
    let directory = scratch("roles");
    let (store, ids) = store_of(&directory, 2);
    let (secret, key) = keys(&directory, "laptop");

    let mut rule = Vouched::new([entry(&key)]);
    let authored = claim(ids[0], "author", &key, "2026-10-01T09:00:00-06:00", &secret);
    let reviewed = claim(
        ids[1],
        "reviewer",
        &key,
        "2026-10-01T09:00:00-06:00",
        &secret,
    );
    assert!(rule.admit(&authored.0, &authored.1));
    assert!(rule.admit(&reviewed.0, &reviewed.1));
    assert!(rule.accepts(&ids[1], &document(&store, &ids[1])));

    // Approving a tip is not taking it, where the caller says so.
    let rule = rule.only(["author".parse().expect("a role")]);
    assert!(rule.accepts(&ids[0], &document(&store, &ids[0])));
    assert!(!rule.accepts(&ids[1], &document(&store, &ids[1])));
}

/// The shape historica's `Accepts` has, so a caller on a historica with
/// `Following` boxes it as it is.
#[test]
fn the_rule_is_shaped_like_historicas_accepts() {
    type Accepts = dyn Fn(&RevisionId, &RevisionDocument) -> bool + Send + Sync;

    let directory = scratch("shape");
    let (store, ids) = store_of(&directory, 1);
    let (secret, key) = keys(&directory, "laptop");
    let mut rule = Vouched::new([entry(&key)]);
    let (bytes, signature) = claim(ids[0], "author", &key, "2026-10-01T09:00:00-06:00", &secret);
    rule.admit(&bytes, &signature);

    let boxed: Box<Accepts> = Box::new(rule.into_rule());
    let handed = std::thread::spawn(move || boxed)
        .join()
        .expect("sent and back");
    assert!(handed(&ids[0], &document(&store, &ids[0])));
}

/// End to end, from the files: claims signed and filed by `sign`, keys in
/// `trust/`, one of them revoked, and `verify` agreeing with the rule.
#[test]
fn a_rule_read_from_a_store_follows_what_trust_believes() {
    let directory = scratch("from-files");
    let (store, ids) = store_of(&directory, 2);
    let (laptop, laptop_key) = keys(&directory, "laptop");
    let (phone, phone_key) = keys(&directory, "phone");

    for (label, key) in [("laptop", &laptop_key), ("phone", &phone_key)] {
        trust::add(store.filesystem(), store.root(), label, &entry(key)).expect("the policy");
    }

    let write = |revision: RevisionId, key: &Key, secret: &SecretKey, when: &str| {
        let claim = Claim {
            revision,
            scope: Scope::Revision,
            role: "author".parse().expect("a role"),
            key: key.clone(),
            when: at(when),
        };
        let stem = naming::stem_for(
            &claim.digest(),
            &claim,
            store.documents().expect("the documents"),
            std::iter::empty::<(&RevisionId, &Claim)>(),
        );
        sign::write(store.filesystem(), store.root(), &claim, &stem, secret).expect("written");
    };
    write(ids[0], &phone_key, &phone, "2026-10-01T09:00:00-06:00");
    write(ids[1], &laptop_key, &laptop, "2026-10-20T09:00:00-06:00");

    let rule = Vouched::trusted(store.filesystem(), store.root()).expect("the rule");
    assert!(rule.vouches_for(&ids[0]));
    assert!(rule.vouches_for(&ids[1]));

    trust::revoke(
        store.filesystem(),
        store.root(),
        "laptop",
        &at("2026-10-19T08:30:00-06:00"),
    )
    .expect("revoked");
    let rule = Vouched::trusted(store.filesystem(), store.root()).expect("the rule");
    assert!(rule.vouches_for(&ids[0]));
    assert!(!rule.vouches_for(&ids[1]));

    let store = Store::open(store.root()).expect("the store again");
    let report = verify::verify(&store).expect("a report");
    assert!(report.ok(), "{:?}", report.findings().collect::<Vec<_>>());
    assert!(
        report
            .notes()
            .any(|finding| matches!(finding, Finding::Revoked { .. })),
        "{:?}",
        report.findings().collect::<Vec<_>>()
    );
    // The phone's claim over the first revision is all that counts, and the
    // second revision is the head nobody now vouches for.
    assert!(report.vouches_for(&ids[0]));
    assert!(!report.vouches_for(&ids[1]));
}
