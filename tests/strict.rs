//! The strict parsers, held to their contracts by bytes nobody wrote.
//!
//! Decision 0004 gives every hashed document one promise with two halves: a
//! parser accepts exactly what a writer would emit, and every refusal names
//! the line and the fix. The corpus states that promise one file at a time,
//! and each file is a claim somebody thought to make. What is here asks the
//! same question of inputs nobody thought of — the corpus mutated a line, a
//! byte, a token at a time — and holds each answer to the half that applies:
//! an accepted document writes back as the bytes it was read from, and a
//! refused one says something, about a line the file has.
//!
//! Not every grammar here is hashed, and the properties follow what each one
//! is. A listing (decisions 0048, 0052, 0056, 0080) is refetchable and reads
//! an unknown kind as a line to discard, so it promises a value rather than
//! bytes: what it read, written and read again, is what it read. A bookmark
//! (0006, 0062) and a skip rule (0045, 0051) are named by their path rather
//! than by a digest, so a second spelling cannot mint a second identity and
//! the promise is the same one. The private grammars of the cache are tested
//! where they live, beside the modules that keep them `pub(super)`.
//!
//! Each target is an ordinary `#[test]`. Under `cargo test` bolero runs it
//! on random input for about a second and prints `BOLERO_RANDOM_SEED` on
//! failure, which reproduces it; `cargo xtask soak` runs every target
//! longer, and `cargo xtask fuzz <name>` runs one coverage-guided, under
//! libFuzzer on nightly.
//!
//! Random bytes rarely get past a preamble, so the input is read as a script
//! rather than as a document: the first byte chooses between taking the rest
//! as the document whole and mutating a seed, and in the second case the
//! bytes after it pick the seed and then the edits. A guided fuzzer learns
//! the script as readily as it would learn the format, and a random one
//! starts every run from a file the parser accepts.

use std::fs;
use std::path::{Path, PathBuf};
use std::sync::OnceLock;

use historica::format::{
    self, ForgottenPayload, OperationDocument, ParseError, ParseErrorKind, ResolutionDocument,
    RevisionDocument,
};
use historica::record::identity::Identities;
use historica::store::{Bookmark, Manifest, Name, Offer, Page, Tip};
use historica::working::{Rule, Skipped};

const DIGEST: &str = "1e4e224e93380a25d4cd1be85d35db37f4064be4388822eba250894c6d6daa0d";
const CHANGE: &str = "qpvuntsmwlrkzxonmvtplsyq";

/// What a mutation may insert, taken from what the grammars in `src/format`,
/// `src/store/offer.rs`, `src/store/mod.rs` and `src/working` spell, and the
/// edges of each rule they enforce.
const TOKENS: &[&str] = &[
    "historica",
    "historica-",
    "historica-v0",
    "change ",
    "parent ",
    "supersedes ",
    "author ",
    "when ",
    "revised-by ",
    "revised ",
    "add ",
    "move ",
    "mode ",
    "drop ",
    "edit ",
    "text ",
    "bytes ",
    "link ",
    "file:",
    "plain",
    "executable",
    "x.y ",
    "a..b ",
    "forgets ",
    "result ",
    "length ",
    "keep ",
    "insert",
    "insert ",
    "delete ",
    "+",
    "-",
    "\\ no newline",
    "\\ forgotten",
    "\r",
    "\n",
    "\n\n",
    " ",
    "  ",
    "\t",
    "0",
    "1",
    "01",
    "18446744073709551616",
    DIGEST,
    CHANGE,
    "kkkkkkkkkkkkkkkkkkkkkkkk",
    "zzzzzzzzzzzzzzzzzzzzzzzz",
    "\u{feff}",
    "2025-08-19T00:47:11-06:00",
    "2024-02-29T23:59:59+00:00",
    "-00:00",
    "Z",
    "/",
    "..",
    "e\u{301}",
    "\u{85}",
    "historica-offer-1",
    "historica-offer-2",
    "historica-offer-page-1",
    "head ",
    "page ",
    "gone ",
    "revision ",
    "operation ",
    "payload ",
    "rule ",
    "reserved ",
    "name ",
    "private",
    "skip ",
    "skip-name ",
    "private-name ",
    "skip-suffix ",
    "*",
    "#",
    "under ",
    "~/",
];

/// Every file of `tests/corpus`, read once.
struct Corpus {
    /// Files a revision parser reads, valid and invalid.
    revisions: Vec<Vec<u8>>,
    /// Files in `operations/`'s three grammars, valid and invalid.
    bodies: Vec<Vec<u8>>,
    /// Everything, for splicing a line of one file into another.
    all: Vec<Vec<u8>>,
}

fn corpus() -> &'static Corpus {
    static CORPUS: OnceLock<Corpus> = OnceLock::new();
    CORPUS.get_or_init(|| {
        let mut paths = Vec::new();
        collect(
            &Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/corpus"),
            &mut paths,
        );
        paths.sort();
        let mut corpus = Corpus {
            revisions: Vec::new(),
            bodies: Vec::new(),
            all: Vec::new(),
        };
        for path in paths {
            let name = path.to_string_lossy();
            let bytes = fs::read(&path).expect("a corpus file is readable");
            // The suffix is the claim, as decision 0003 has it: `.rev` is
            // what `revisions/` reads and `.ops` what `operations/` reads.
            if name.contains(".rev") {
                corpus.revisions.push(bytes.clone());
            } else if name.contains(".ops") {
                corpus.bodies.push(bytes.clone());
            }
            corpus.all.push(bytes);
        }
        // A writer's output for the one grammar the corpus states only once.
        let payload =
            ForgottenPayload::parse(format!("historica\nforgets {DIGEST}\nlength 0\n").as_bytes())
                .expect("a forgotten payload");
        corpus.bodies.push(payload.write());
        corpus
    })
}

/// The body seeds `Store` would send to one grammar, so that each target
/// starts from its own files rather than mostly from its neighbours'.
fn bodies_sent_to(grammar: usize) -> Vec<Vec<u8>> {
    corpus()
        .bodies
        .iter()
        .filter(|bytes| sent_to(bytes) == grammar)
        .cloned()
        .collect()
}

/// Which grammar `Store` reads bytes in `operations/` with: a forgotten
/// payload, a resolution, or an operation document.
fn sent_to(bytes: &[u8]) -> usize {
    if format::is_forgotten_payload(bytes) {
        0
    } else if format::is_resolution(bytes) {
        1
    } else {
        2
    }
}

fn collect(directory: &Path, into: &mut Vec<PathBuf>) {
    for entry in fs::read_dir(directory).expect("a corpus directory") {
        let path = entry.expect("an entry").path();
        if path.is_dir() {
            collect(&path, into);
        } else if path.file_name().is_some_and(|name| name != "MANIFEST") {
            into.push(path);
        }
    }
}

/// Bytes read one at a time, and zero once there are none.
struct Script<'a>(&'a [u8]);

impl Script<'_> {
    fn byte(&mut self) -> Option<u8> {
        let (&first, rest) = self.0.split_first()?;
        self.0 = rest;
        Some(first)
    }

    /// A position below `bound`, from two bytes.
    fn below(&mut self, bound: usize) -> usize {
        let wide =
            usize::from(self.byte().unwrap_or(0)) << 8 | usize::from(self.byte().unwrap_or(0));
        wide % bound.max(1)
    }
}

/// The document an input describes: itself, or a seed after its edits.
fn document(input: &[u8], seeds: &[Vec<u8>]) -> Vec<u8> {
    let Some((&mode, rest)) = input.split_first() else {
        return Vec::new();
    };
    if mode % 8 == 0 || seeds.is_empty() {
        return rest.to_vec();
    }
    let mut script = Script(rest);
    let mut document = seeds[script.below(seeds.len())].clone();
    // A few edits rather than as many as the input is long: a random input
    // runs to kilobytes, and a seed edited a thousand times is noise again.
    for _ in 0..=script.byte().unwrap_or(0) % 8 {
        let Some(edit) = script.byte() else { break };
        mutate(&mut document, edit, &mut script);
    }
    document
}

/// One edit. Bytes for the faults a parser checks per character, lines for
/// the ones it checks per line, and tokens for the ones it checks per word.
fn mutate(document: &mut Vec<u8>, edit: u8, script: &mut Script) {
    let mut lines: Vec<Vec<u8>> = document
        .split_inclusive(|byte| *byte == b'\n')
        .map(<[u8]>::to_vec)
        .collect();
    let at = script.below(document.len() + 1);
    match edit % 10 {
        0 if !document.is_empty() => {
            let at = at.min(document.len() - 1);
            document[at] ^= 1 << (script.byte().unwrap_or(0) % 8);
        }
        1 => document.insert(at, script.byte().unwrap_or(0)),
        2 if at < document.len() => {
            document.remove(at);
        }
        3 if !document.is_empty() => document.truncate(at),
        4 if !lines.is_empty() => {
            lines.remove(script.below(lines.len()));
            *document = lines.concat();
        }
        5 if !lines.is_empty() => {
            let line = lines[script.below(lines.len())].clone();
            lines.insert(script.below(lines.len() + 1), line);
            *document = lines.concat();
        }
        6 if !lines.is_empty() => {
            let (one, other) = (script.below(lines.len()), script.below(lines.len()));
            lines.swap(one, other);
            *document = lines.concat();
        }
        7 => {
            let all = &corpus().all;
            let from: Vec<&[u8]> = all[script.below(all.len())]
                .split_inclusive(|byte| *byte == b'\n')
                .collect();
            if !from.is_empty() {
                let line = from[script.below(from.len())].to_vec();
                lines.insert(script.below(lines.len() + 1), line);
                *document = lines.concat();
            }
        }
        8 => {
            let token = TOKENS[script.below(TOKENS.len())].as_bytes();
            document.splice(at..at, token.iter().copied());
        }
        9 => {
            // A token in place of the same number of bytes, which is how a
            // digest becomes a change ID without the line moving.
            let token = TOKENS[script.below(TOKENS.len())].as_bytes();
            let end = (at + token.len()).min(document.len());
            document.splice(at..end, token.iter().copied());
        }
        _ => {}
    }
}

/// Lines as decision 0004's errors count them: an unterminated last line is
/// a line.
fn lines_in(bytes: &[u8]) -> usize {
    let breaks = bytes.iter().filter(|byte| **byte == b'\n').count();
    breaks + usize::from(!bytes.ends_with(b"\n") && !bytes.is_empty())
}

/// Decision 0004, both halves, for one grammar and one input.
fn holds_to_its_writer<T: PartialEq + std::fmt::Debug>(
    bytes: &[u8],
    parsed: Result<T, ParseError>,
    write: impl Fn(&T) -> Vec<u8>,
) -> Option<T> {
    match parsed {
        Ok(document) => {
            assert_eq!(
                write(&document),
                bytes,
                "accepted, and written back as other bytes: {:?}",
                String::from_utf8_lossy(bytes)
            );
            Some(document)
        }
        Err(error) => {
            assert!(!error.to_string().is_empty(), "a refusal that says nothing");
            assert!(
                error.line <= lines_in(bytes) + 1,
                "a refusal naming line {} of a file of {}: {error}",
                error.line,
                lines_in(bytes)
            );
            None
        }
    }
}

/// Decision 0004 for the revision document, and decision 0061 for the two
/// readings of one: the cheaper one refuses every shape the whole one does,
/// agrees with it about every fact a revision holds, and is outrun by it only
/// on what a value means.
#[test]
fn a_revision_document_is_read_as_written() {
    let seeds = &corpus().revisions;
    bolero::check!().for_each(|input: &[u8]| {
        let bytes = document(input, seeds);
        let whole = RevisionDocument::parse(&bytes);
        let revision = format::revision(&bytes);
        match (&whole, &revision) {
            (Ok(document), Ok(revision)) => assert_eq!(*revision, document.to_revision()),
            (Ok(_), Err(error)) => {
                panic!("the whole reading accepted what the cheap one refused: {error}")
            }
            (Err(error), Ok(_)) => assert!(
                about_a_value(&error.kind),
                "the cheap reading accepted a shape the whole one refused: {error}"
            ),
            (Err(_), Err(_)) => {}
        }
        holds_to_its_writer(&bytes, whole, RevisionDocument::write);
    });
}

/// What decision 0061 lets the whole reading refuse after the cheap one
/// accepted: what a value means, or two tree facts contradicting each other.
fn about_a_value(kind: &ParseErrorKind) -> bool {
    match kind {
        ParseErrorKind::MalformedDigest { key, .. } => matches!(*key, "edit" | "text" | "bytes"),
        ParseErrorKind::MalformedTimestamp { .. }
        | ParseErrorKind::MalformedPath { .. }
        | ParseErrorKind::MalformedFileId { .. }
        | ParseErrorKind::MalformedFileEntry { .. }
        | ParseErrorKind::MalformedSize { .. }
        | ParseErrorKind::UnknownMode { .. }
        | ParseErrorKind::FileStatedTwice { .. }
        | ParseErrorKind::ContradictoryFileFacts { .. }
        | ParseErrorKind::TextWithoutAdd { .. } => true,
        _ => false,
    }
}

#[test]
fn an_operation_document_is_read_as_written() {
    let seeds = &bodies_sent_to(2);
    bolero::check!().for_each(|input: &[u8]| {
        let bytes = document(input, seeds);
        holds_to_its_writer(
            &bytes,
            OperationDocument::parse(&bytes),
            OperationDocument::write,
        );
    });
}

#[test]
fn a_resolution_is_read_as_written() {
    let seeds = &bodies_sent_to(1);
    bolero::check!().for_each(|input: &[u8]| {
        let bytes = document(input, seeds);
        holds_to_its_writer(
            &bytes,
            ResolutionDocument::parse(&bytes),
            ResolutionDocument::write,
        );
    });
}

#[test]
fn a_forgotten_payload_is_read_as_written() {
    let seeds = &bodies_sent_to(0);
    bolero::check!().for_each(|input: &[u8]| {
        let bytes = document(input, seeds);
        holds_to_its_writer(
            &bytes,
            ForgottenPayload::parse(&bytes),
            ForgottenPayload::write,
        );
    });
}

/// Decisions 0032 and 0066 put three grammars in one directory under one
/// suffix and let the file say which it is written in: `is_forgotten_payload`
/// first, then `is_resolution`, and an operation document otherwise, which
/// is the order `Store` and the catalogue ask in. So no bytes are two
/// documents, and bytes that are one are sent to the parser that accepts
/// them.
#[test]
fn the_three_bodies_never_read_one_file() {
    let seeds = &corpus().bodies;
    bolero::check!().for_each(|input: &[u8]| {
        let bytes = document(input, seeds);
        let accepted = [
            ForgottenPayload::parse(&bytes).is_ok(),
            ResolutionDocument::parse(&bytes).is_ok(),
            OperationDocument::parse(&bytes).is_ok(),
        ];
        let sent = sent_to(&bytes);
        assert!(
            accepted.iter().filter(|ok| **ok).count() <= 1,
            "two grammars accept {:?}",
            String::from_utf8_lossy(&bytes)
        );
        if let Some(grammar) = accepted.iter().position(|ok| *ok) {
            assert_eq!(
                grammar,
                sent,
                "accepted by one grammar and sent to another: {:?}",
                String::from_utf8_lossy(&bytes)
            );
        }
    });
}

/// Seeds for the grammars no corpus states, in every spelling each has.
fn listings() -> Vec<Vec<u8>> {
    let entries = format!(
        "payload {DIGEST} - store/history/operations/photo.png\n\
         operation {DIGEST} {DIGEST} store/history/operations/a b.ops.txt\n\
         revision {DIGEST} - store/history/revisions/2026-08/start.rev.txt\n\
         rule {DIGEST} - store/history/skipped/target/all.txt\n\
         reserved {DIGEST} - store/history/x.tool/state\n\
         name {DIGEST} - store/history/names/main.txt\n\
         later {DIGEST} - store/history/somewhere\n"
    );
    [
        format!("historica-offer-1\nhead {DIGEST}\n{entries}"),
        format!("historica-offer-2\nhead {DIGEST}\npage {DIGEST} pages/one two.txt\n"),
        format!(
            "historica-offer-page-1\n{entries}gone {}",
            entries.lines().next().unwrap_or_default()
        ),
    ]
    .map(String::into_bytes)
    .into()
}

/// A listing promises its value, not its bytes. Decision 0048 makes it a
/// rendering nobody hashes, decision 0056 has a reader discard a line of a
/// kind it does not know, and `\r\n` reads as `\n` — so the bytes it is read
/// from need not be the bytes it writes, and what it writes reads back as
/// itself.
#[test]
fn a_listing_reads_back_as_itself() {
    let seeds = listings();
    bolero::check!().for_each(|input: &[u8]| {
        let bytes = document(input, &seeds);
        let text = String::from_utf8_lossy(&bytes);
        // The one shape that does not hold yet, which the ignored test below
        // pins: docs/tasks/a-listing-ending-in-a-carriage-return.md.
        if text.ends_with('\r') {
            return;
        }
        match Offer::parse(&text) {
            Ok(offer) => assert_eq!(Offer::parse(&offer.to_string()), Ok(offer)),
            Err(error) => assert!(!error.to_string().is_empty()),
        }
        match Tip::parse(&text) {
            Ok(tip) => assert_eq!(Tip::parse(&tip.to_string()), Ok(tip)),
            Err(error) => assert!(!error.to_string().is_empty()),
        }
        match Page::parse(&text) {
            Ok(page) => assert_eq!(Page::parse(&page.to_string()), Ok(page)),
            Err(error) => assert!(!error.to_string().is_empty()),
        }
        match Manifest::parse(&text) {
            Ok(Manifest::Whole(offer)) => assert_eq!(
                Manifest::parse(&offer.to_string()),
                Ok(Manifest::Whole(offer))
            ),
            Ok(Manifest::Paged(tip)) => {
                assert_eq!(Manifest::parse(&tip.to_string()), Ok(Manifest::Paged(tip)))
            }
            Ok(_) => {}
            Err(error) => assert!(!error.to_string().is_empty()),
        }
    });
}

/// The shape the target above skips: a carriage return ending the last,
/// unterminated line, which reads into the path and writes back as a line
/// ending.
#[test]
#[ignore = "docs/tasks/a-listing-ending-in-a-carriage-return.md"]
fn a_listing_ending_in_a_carriage_return_reads_back_as_itself() {
    let tip = Tip::parse(&format!("historica-offer-2\npage {DIGEST} p\r")).expect("a tip");
    assert_eq!(Tip::parse(&tip.to_string()), Ok(tip));
    let offer =
        Offer::parse(&format!("historica-offer-1\nrevision {DIGEST} - p\r")).expect("an offer");
    assert_eq!(Offer::parse(&offer.to_string()), Ok(offer));
}

/// Decision 0062, and `Name::parse`'s own words: a bookmark is not named by
/// its bytes, so a second spelling cannot mint a second identity and the
/// promise is the value.
#[test]
fn a_bookmark_reads_back_as_itself() {
    let seeds: Vec<Vec<u8>> = [
        format!("change {CHANGE}\n"),
        format!("revision {DIGEST}\nprivate\n"),
        format!("file {CHANGE}"),
    ]
    .map(String::into_bytes)
    .into();
    bolero::check!().for_each(|input: &[u8]| {
        let text = String::from_utf8_lossy(&document(input, &seeds)).into_owned();
        if let Ok(bookmark) = Bookmark::parse(&text) {
            assert_eq!(Bookmark::parse(&bookmark.write()), Ok(bookmark));
        }
        if let Ok(name) = Name::parse(&text) {
            assert_eq!(Name::parse(&name.to_string()), Ok(name));
        }
    });
}

/// Decisions 0045 and 0051: a rule is the one line its file holds, and
/// `Store::add_skipped` writes it as that line and a newline. What a reader
/// took from a file is what it writes, and what that writes reads back as
/// the same rule — whose label a writer can always compute.
#[test]
fn a_skip_rule_reads_back_as_itself() {
    let seeds: Vec<Vec<u8>> = [
        "skip docs/drafts/\n",
        "private-name *.key\n",
        "# a comment\n\nskip-name build/\n",
        "skip a name with spaces.md\n",
        "skip-suffix .tmp\n",
    ]
    .map(|seed| seed.as_bytes().to_vec())
    .into();
    bolero::check!().for_each(|input: &[u8]| {
        let text = String::from_utf8_lossy(&document(input, &seeds)).into_owned();
        if let Ok(Some(rule)) = Skipped::rule_in(&text) {
            assert_eq!(
                Skipped::rule_in(&format!("{rule}\n")),
                Ok(Some(rule.clone()))
            );
            assert_eq!(Rule::parse(&rule.to_string()), Ok(rule.clone()));
            let _ = (rule.label(), rule.digest_label());
        }
        let _ = Skipped::retired_in(&text);
    });
}

/// Decision 0010's identity file has no writer, so all it can promise is to
/// answer: a person's configuration either reads or says which line did not.
#[test]
fn an_identity_file_always_answers() {
    let seeds: Vec<Vec<u8>> = [
        "author Adam Harris <adam@example.com>\n\nunder ~/work/\nauthor Adam at work\n",
        "under /\nauthor root\n",
    ]
    .map(|seed| seed.as_bytes().to_vec())
    .into();
    bolero::check!().for_each(|input: &[u8]| {
        let text = String::from_utf8_lossy(&document(input, &seeds)).into_owned();
        match Identities::parse(&text) {
            Ok(identities) => {
                let _ = identities.author_for(Path::new("/home/someone/work/journal"));
            }
            Err(error) => assert!(!error.to_string().is_empty()),
        }
    });
}
