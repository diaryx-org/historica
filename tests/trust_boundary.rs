//! What the Verus proofs take on trust, which in this crate is nothing.
//!
//! A proof rests on whatever Verus is told without checking it: a body it
//! does not verify, a specification assumed of a function it cannot see, an
//! assumed fact, an admitted goal. Decision 0076 keeps all of that out of the
//! library's source, so that what the proofs rest on is Verus, Z3 and the
//! specifications `vstd` gives the standard library — and nothing written
//! here. When a proof does need one, it goes in one file, that file is named
//! in [`TRUSTED`], and reviewing it is reviewing everything the proofs rest
//! on.

use std::path::Path;

/// What asks Verus to take something on faith.
const TRUST: &[&str] = &[
    "external_body",
    "assume_specification",
    "external_fn_specification",
    "external_type_specification",
    "assume(",
    "admit(",
];

/// The files allowed to, from the crate root. None yet.
const TRUSTED: &[&str] = &[];

fn visit(directory: &Path, root: &Path, found: &mut Vec<String>) {
    for entry in std::fs::read_dir(directory).unwrap() {
        let path = entry.unwrap().path();
        if path.is_dir() {
            visit(&path, root, found);
            continue;
        }
        if path.extension().is_none_or(|extension| extension != "rs") {
            continue;
        }
        let relative = path
            .strip_prefix(root)
            .unwrap()
            .to_string_lossy()
            .replace('\\', "/");
        if TRUSTED.contains(&relative.as_str()) {
            continue;
        }
        let text = std::fs::read_to_string(&path).unwrap();
        for (at, line) in text.lines().enumerate() {
            if TRUST.iter().any(|trust| line.contains(trust)) {
                found.push(format!("{relative}:{}: {}", at + 1, line.trim()));
            }
        }
    }
}

#[test]
fn the_proofs_take_nothing_in_the_library_on_trust() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut found = Vec::new();
    visit(&root.join("src"), root, &mut found);
    assert!(
        found.is_empty(),
        "the library asks Verus to take something on trust outside {TRUSTED:?}:\n{}",
        found.join("\n")
    );
}
