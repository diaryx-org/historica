//! The git facts historica has no word for, carried across as headers.
//!
//! Decision 0004 makes a commit a function of the revision it came from, and
//! measured the set that does not hold: a committer distinct from the author,
//! and a signature. Decision 0012 found a third, the order of a merge's
//! parents. All three are in the commit's own bytes, so a revision that cannot
//! state them cannot be written back as the commit it came from.
//!
//! Historica's decision 0065 has the door and its 0070 opened it: a key with a
//! dot in it is another tool's vocabulary, parsed, hashed with everything else,
//! never interpreted, and carried across an amendment. So the fact lives in the
//! revision's own bytes, the revision's identity covers it, and a rewrite does
//! not silently drop what made the commit what it was.
//!
//! The keys are `git.`-qualified for the tool that owns them, which is this
//! one.

use historica::core::{ChangeId, RevisionId};

use crate::stream::{Person, quote, unquote};

/// The committer, where the commit named one other than its author.
///
/// The whole line git writes, since every part of it is in the commit's bytes:
/// `Name <email> 1767348245 -0700`.
pub const COMMITTER: &str = "git.committer";

/// The signature, exactly as the stream carried it.
pub const SIGNATURE: &str = "git.signature";

/// What `gpgsig` said the signature was: `sha1 openpgp`.
///
/// Its own key rather than a prefix on the signature, because it is a different
/// fact — what the bytes are — and joining two facts in one value would need a
/// grammar to take them apart again.
pub const SIGNATURE_KIND: &str = "git.signature-kind";

/// A merge's parents in the order git named them, by change.
///
/// Historica keeps `parent` lines sorted by digest, and git's first parent is
/// the line the merge was made on, so the order is a fact of its own. By change
/// rather than by digest, because a change survives the amendment or the carry
/// that gives a parent a new digest. Decision 0012.
pub const PARENTS: &str = "git.parents";

/// Change IDs as one header value, single-spaced.
///
/// A change ID is letters only, so the value needs no quoting and is the same
/// bytes every time.
pub fn spell_parents(changes: &[ChangeId]) -> String {
    changes
        .iter()
        .map(ChangeId::to_string)
        .collect::<Vec<_>>()
        .join(" ")
}

/// The same list, read back. `None` where a word is not a change ID.
pub fn read_parents(value: &str) -> Option<Vec<ChangeId>> {
    value.split(' ').map(|word| word.parse().ok()).collect()
}

/// A revision's parents in the order `stated` gives their changes.
///
/// `None` unless `stated` names each parent's change exactly once and nothing
/// else. A rewrite that took a parent away or brought one in leaves a header
/// that describes a different merge, and putting part of it to use would be a
/// guess.
pub fn in_stated_order(
    parents: &[(RevisionId, ChangeId)],
    stated: &[ChangeId],
) -> Option<Vec<RevisionId>> {
    if stated.len() != parents.len() {
        return None;
    }
    let mut ordered = Vec::with_capacity(parents.len());
    for change in stated {
        let mut matching = parents.iter().filter(|(_, of)| of == change);
        let (revision, _) = matching.next()?;
        if matching.next().is_some() || ordered.contains(revision) {
            return None;
        }
        ordered.push(*revision);
    }
    Some(ordered)
}

/// Bytes as a header value: raw where they can be read, quoted where they
/// cannot.
///
/// Historica's rule for any header value is one line, no control characters,
/// and no leading or trailing space. A committer satisfies it as it stands and
/// stays readable; a signature is an armoured block with newlines in it and
/// does not. So the one escaping rule this crate already has — the stream's
/// own, in [`crate::stream::quote`] — does the second case, which means the
/// escape a person meets in a revision document is the escape they already met
/// in the stream.
pub fn spell(bytes: &[u8]) -> String {
    let plain = quote(bytes, false);
    // `quote` lets a space travel raw, and a value historica takes may not
    // begin or end with one. Quoting spaces too is the fallback, and it is only
    // ever reached by a name somebody padded.
    let spelled = match plain.first() == Some(&b' ') || plain.last() == Some(&b' ') {
        true => quote(bytes, true),
        false => plain,
    };
    String::from_utf8_lossy(&spelled).into_owned()
}

/// The bytes a header value spells, whichever way [`spell`] wrote it.
pub fn read(value: &str) -> Option<Vec<u8>> {
    match value.as_bytes().first() {
        Some(b'"') => unquote(value.as_bytes()).ok().map(|(bytes, _)| bytes),
        _ => Some(value.as_bytes().to_vec()),
    }
}

/// A person and a time, as the one line git writes them on.
pub fn spell_person(person: &Person) -> String {
    let mut line = person.name.clone();
    line.extend_from_slice(b" <");
    line.extend_from_slice(&person.email);
    line.extend_from_slice(b"> ");
    line.extend_from_slice(person.seconds.to_string().as_bytes());
    line.push(b' ');
    line.extend_from_slice(offset(person.offset_minutes).as_bytes());
    spell(&line)
}

/// The same line, read back.
///
/// `None` where the value is not one, which is a header somebody else wrote
/// under a key this tool owns — reported rather than guessed at.
pub fn read_person(value: &str) -> Option<Person> {
    let text = read(value)?;
    let close = text.iter().rposition(|&byte| byte == b'>')?;
    let open = text[..close].iter().rposition(|&byte| byte == b'<')?;
    let name = text[..open]
        .iter()
        .rev()
        .skip_while(|byte| **byte == b' ')
        .copied()
        .collect::<Vec<_>>()
        .into_iter()
        .rev()
        .collect::<Vec<u8>>();
    let email = text[open + 1..close].to_vec();

    let when = String::from_utf8_lossy(text.get(close + 1..)?).into_owned();
    let when = when.trim();
    let (seconds, offset) = when.split_once(' ')?;
    let seconds: i64 = seconds.trim().parse().ok()?;

    let offset = offset.trim();
    if offset.len() != 5 {
        return None;
    }
    let sign = match offset.as_bytes()[0] {
        b'-' => -1,
        b'+' => 1,
        _ => return None,
    };
    let hours: i32 = offset[1..3].parse().ok()?;
    let minutes: i32 = offset[3..5].parse().ok()?;

    Some(Person {
        name,
        email,
        seconds,
        offset_minutes: sign * (hours * 60 + minutes),
    })
}

/// Minutes east of UTC, as git's `+HHMM`.
pub fn offset(minutes: i32) -> String {
    let sign = if minutes < 0 { '-' } else { '+' };
    let minutes = minutes.abs();
    format!("{sign}{:02}{:02}", minutes / 60, minutes % 60)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn person() -> Person {
        Person {
            name: b"Ada Lovelace".to_vec(),
            email: b"ada@example.com".to_vec(),
            seconds: 1767348245,
            offset_minutes: -420,
        }
    }

    #[test]
    fn a_committer_stays_readable() {
        assert_eq!(
            spell_person(&person()),
            "Ada Lovelace <ada@example.com> 1767348245 -0700"
        );
        assert_eq!(read_person(&spell_person(&person())), Some(person()));
    }

    #[test]
    fn a_signature_survives_its_newlines() {
        let armour = b"-----BEGIN PGP SIGNATURE-----\n\nabc/+=\n-----END PGP SIGNATURE-----";
        let spelled = spell(armour);
        assert!(!spelled.contains('\n'), "a header is one line: {spelled}");
        assert!(
            spelled.starts_with("\"-----BEGIN PGP SIGNATURE-----"),
            "what it is should still be legible: {spelled}"
        );
        assert_eq!(read(&spelled).as_deref(), Some(&armour[..]));
    }

    /// Every byte, as a value: what `spell` writes is what `read` reads, it is
    /// a header historica takes, and two runs agree about it.
    ///
    /// The last of those three is the one that is load-bearing somewhere else.
    /// A header value is in the revision's canonical bytes, so the spelling has
    /// to be a *function* of the signature rather than a choice about it: two
    /// runs of `import` over one commit that spelled it two ways would write two
    /// revision IDs, and the reproducibility decision 0003 exists for would fail
    /// only when somebody re-imported, which is the worst time to find out.
    ///
    /// It is a pure function today and the point is to keep it one. In
    /// particular `spell` ends in `String::from_utf8_lossy`, which is only
    /// lossless because `quote` escapes every byte outside printable ASCII —
    /// an invariant worth asserting rather than reasoning about once.
    #[test]
    fn every_byte_spells_and_reads_back_the_same_way_twice() {
        let mut values: Vec<Vec<u8>> = Vec::new();
        for byte in 0u8..=255 {
            // Alone, at the front, at the back, and in the middle, so that the
            // leading- and trailing-space fallback is reached by the byte that
            // needs it rather than only by the case that was thought of.
            values.push(vec![byte]);
            values.push(vec![byte, b'a']);
            values.push(vec![b'a', byte]);
            values.push(vec![b'a', byte, b'b']);
        }
        values.push(Vec::new());
        values.push(b"-----BEGIN PGP SIGNATURE-----\n\nabc/+=\n-----END-----".to_vec());
        values.push(
            "Ada \u{fffd} Lovelace <ada@example.com> 1 +0000"
                .as_bytes()
                .to_vec(),
        );
        values.push(vec![0xff, 0xfe, 0xfd]);

        for value in values {
            let spelled = spell(&value);
            assert_eq!(
                spelled,
                spell(&value),
                "two spellings of {value:?} disagreed"
            );
            assert!(
                spelled.is_ascii(),
                "{value:?} spelled as something `from_utf8_lossy` could damage: {spelled}"
            );
            assert_eq!(
                read(&spelled).as_deref(),
                Some(&value[..]),
                "{value:?} did not read back from {spelled}"
            );
            historica::format::check_extension(SIGNATURE, &spelled).unwrap_or_else(|because| {
                panic!("{value:?} spelled as `{spelled}`, which historica refused: {because:?}")
            });
        }
    }

    /// The same, for the one value that is parsed rather than only carried.
    #[test]
    fn a_committer_reads_back_however_it_was_written() {
        let awkward = [
            &b"Ada"[..],
            b"",
            b"  leading",
            b"Quote\" Name",
            b"Back\\slash",
            b"Caf\xc3\xa9",
            b"Name <with> angles",
        ];
        for name in awkward {
            for offset_minutes in [0, -420, 330] {
                let person = Person {
                    name: name.to_vec(),
                    email: b"ada@example.com".to_vec(),
                    seconds: 1767348245,
                    offset_minutes,
                };
                let spelled = spell_person(&person);
                assert_eq!(spelled, spell_person(&person), "two spellings disagreed");
                historica::format::check_extension(COMMITTER, &spelled)
                    .unwrap_or_else(|because| panic!("`{spelled}` refused: {because:?}"));
                assert_eq!(
                    read_person(&spelled),
                    Some(person),
                    "did not read back from `{spelled}`"
                );
            }
        }
    }

    /// A name ending in a space comes back without it, because `Name <email>`
    /// cannot hold one.
    ///
    /// Not a loss this crate chose. The separator before the address is a
    /// space, so a trailing space in a name is a space git's own reader cannot
    /// tell from the separator — `stream::read`'s `person` trims for exactly
    /// this reason, and git normalises such a name away before a commit object
    /// ever holds one.
    ///
    /// Nor is it a loss at all, in the end: historica cannot hold that person
    /// either. Its `split_header` refuses a value with leading or trailing
    /// space outright, on decision 0002's rule that a value must survive a
    /// round trip, so `author Adam ` is not a line this format would parse or
    /// write. One end trims and the other refuses, by different mechanisms and
    /// for different reasons, and the set of people neither can represent is
    /// the same set. So the trim discards nothing that could have come from
    /// either side.
    ///
    /// Asserted rather than left to be discovered, so that the one input
    /// `spell_person` does not round-trip is a stated rule instead of a
    /// surprise.
    #[test]
    fn a_name_ending_in_a_space_loses_it_as_it_would_in_git() {
        let padded = Person {
            name: b"  padded  ".to_vec(),
            email: b"ada@example.com".to_vec(),
            seconds: 1767348245,
            offset_minutes: 0,
        };
        let read = read_person(&spell_person(&padded)).expect("it still reads");
        assert_eq!(read.name, b"  padded", "the trailing space is what goes");
        assert_eq!(read.email, padded.email);
        assert_eq!(read.seconds, padded.seconds);
    }

    fn change(byte: u8) -> ChangeId {
        ChangeId::from_bytes([byte; historica::core::CHANGE_ID_LEN])
    }

    fn revision(byte: u8) -> RevisionId {
        historica::format::digest(&[byte])
    }

    #[test]
    fn a_merges_parents_read_back_in_the_order_they_were_spelled() {
        let changes = [change(9), change(1), change(5)];
        let spelled = spell_parents(&changes);
        assert_eq!(read_parents(&spelled).as_deref(), Some(&changes[..]));
        assert_eq!(read_parents("not a change"), None);
        assert_eq!(read_parents(""), None);
    }

    /// The order a header gives is used only where it describes this merge:
    /// every parent's change named once, and nothing else.
    #[test]
    fn a_stated_order_is_used_only_where_it_names_every_parent_once() {
        let parents = [(revision(1), change(1)), (revision(2), change(2))];
        assert_eq!(
            in_stated_order(&parents, &[change(2), change(1)]),
            Some(vec![revision(2), revision(1)])
        );
        // A parent a rewrite took away, or brought in.
        assert_eq!(in_stated_order(&parents, &[change(2)]), None);
        assert_eq!(in_stated_order(&parents, &[change(2), change(3)]), None);
        assert_eq!(
            in_stated_order(&parents, &[change(2), change(1), change(3)]),
            None
        );
        // One change named twice, which leaves the other parent unplaced.
        assert_eq!(in_stated_order(&parents, &[change(2), change(2)]), None);
        // Two parents that are versions of one change, which a change ID
        // cannot tell apart.
        let divergent = [(revision(1), change(1)), (revision(2), change(1))];
        assert_eq!(in_stated_order(&divergent, &[change(1), change(1)]), None);
    }

    /// What historica will accept, checked here rather than discovered by a
    /// `record` that refuses halfway through a conversion.
    #[test]
    fn what_is_spelled_is_a_header_historica_takes() {
        let armour = b"-----BEGIN PGP SIGNATURE-----\n\nabc\n-----END-----";
        for (key, value) in [
            (COMMITTER, spell_person(&person())),
            (SIGNATURE, spell(armour)),
            (SIGNATURE_KIND, spell(b"sha1 openpgp")),
            // A name somebody padded, which is the case `spell` falls back for.
            (COMMITTER, spell(b"  padded  ")),
            (PARENTS, spell_parents(&[change(9), change(1), change(5)])),
        ] {
            historica::format::check_extension(key, &value)
                .unwrap_or_else(|because| panic!("`{key}` = `{value}` refused: {because:?}"));
        }
    }
}
