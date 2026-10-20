//! What a glob rule covers: decision 0087 executed.
//!
//! `tests/corpus/skipped/cases.txt` is each glob with the paths it covers and
//! the paths it leaves, and every verdict in it is git's: `against-git.sh`
//! writes each rule as the `.gitignore` meaning the same and asks
//! `git check-ignore`. This test holds historica's matcher to the same
//! verdicts, so the two agree by way of a file anybody can read.
//!
//! `invalid/` holds rule files that must be refused, one per reason, and the
//! filename is the reason.

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

use historica::core::RevisionId;
use historica::format::digest;
use historica::working::{Rule, Skipped};

fn corpus() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/corpus/skipped")
}

fn manifest() -> BTreeMap<String, RevisionId> {
    let text = fs::read_to_string(corpus().join("MANIFEST")).expect("MANIFEST is readable");
    text.lines()
        .filter(|line| !line.trim().is_empty())
        .map(|line| {
            let (digest, name) = line.split_once("  ").expect("`<digest>  <name>` per line");
            (
                name.to_owned(),
                digest.parse().expect("a digest in the manifest"),
            )
        })
        .collect()
}

fn read(name: &str) -> String {
    fs::read_to_string(corpus().join(name)).unwrap_or_else(|_| panic!("{name} is readable"))
}

/// One case: the rule's text, and each path with whether it is covered.
struct Case {
    rule: String,
    paths: Vec<(bool, String)>,
}

fn cases() -> Vec<Case> {
    let mut found = Vec::new();
    let mut rule: Vec<&str> = Vec::new();
    let mut paths = Vec::new();
    let text = read("cases.txt");
    for line in text.lines().chain([""]) {
        if line.starts_with('#') {
            continue;
        }
        if line.is_empty() {
            if !rule.is_empty() {
                found.push(Case {
                    rule: rule.join("\n"),
                    paths: std::mem::take(&mut paths),
                });
                rule.clear();
            }
            continue;
        }
        match (line.strip_prefix("+ "), line.strip_prefix("- ")) {
            (Some(path), _) => paths.push((true, path.to_owned())),
            (_, Some(path)) => paths.push((false, path.to_owned())),
            _ => rule.push(line),
        }
    }
    found
}

#[test]
fn the_manifest_describes_the_corpus_on_disk() {
    for (name, expected) in manifest() {
        assert_eq!(
            digest(read(&name).as_bytes()),
            expected,
            "{name} has drifted"
        );
    }
}

#[test]
fn every_glob_covers_what_git_ignores_and_nothing_else() {
    let cases = cases();
    assert!(cases.len() > 20, "the corpus was read");
    for case in cases {
        let rule = Rule::parse(&case.rule).unwrap_or_else(|error| panic!("{}: {error}", case.rule));
        assert_eq!(rule.to_string(), case.rule, "a case is spelled canonically");
        let rules = Skipped::from_rules([rule]);
        for (covered, path) in &case.paths {
            assert_eq!(rules.skips(path), *covered, "`{}` and `{path}`", case.rule);
        }
    }
}

#[test]
fn every_invalid_rule_is_refused() {
    let invalid: Vec<String> = manifest()
        .into_keys()
        .filter(|name| name.starts_with("invalid/"))
        .collect();
    assert!(invalid.len() > 15, "the corpus was read");
    for name in invalid {
        assert!(
            Skipped::rule_in(&read(&name)).is_err(),
            "{name} was accepted"
        );
    }
}
