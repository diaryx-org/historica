//! What git ignores, said as historica's skip rules.
//!
//! Decision 0011. A colocated directory is one folder with two readers, and
//! historica does not read git's ignore files. Without this, the first
//! `record` after a `cargo build` takes `target/`, and one after a `.env` is
//! written takes the secret — into a history that is append-only.
//!
//! Only the part of git's dialect that historica's rules can say exactly is
//! carried. A rule that skipped more than git ignores would keep a file out of
//! history that git would commit, which is the quiet loss 0001 is about; a rule
//! that skipped less would be no rule at all. Everything else is reported, by
//! file and line, for `historica skip` to say by hand.

use std::fs;
use std::io;
use std::path::Path;

use historica::working::{Pattern, Rule, Scope};

/// One of git's ignore files, and whether a rule taken from it travels.
pub struct Source {
    /// Where the file is, as a person would name it in a note.
    pub name: String,
    /// What it says.
    pub text: String,
    /// A tracked `.gitignore` is the project's, so its rules are shared. The
    /// repository's `info/exclude` and a person's global excludes file are
    /// facts about one machine, so theirs are private, as 0008's `.git` rules
    /// are.
    pub shared: bool,
}

impl Source {
    /// The file at `path`, or nothing where there is none.
    pub fn read(path: &Path, name: String, shared: bool) -> io::Result<Option<Self>> {
        match fs::read_to_string(path) {
            Ok(text) => Ok(Some(Self { name, text, shared })),
            Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(None),
            Err(error) => Err(error),
        }
    }
}

/// What the ignore files came to.
#[derive(Debug, Default)]
pub struct Translated {
    /// The rules that say exactly what a line says.
    pub rules: Vec<Rule>,
    /// Each line that did not become a rule, and why, as `<file>:<line>`.
    pub left: Vec<(String, &'static str)>,
}

/// Translate `sources`, given lowest precedence first.
///
/// git reads the global file, then `info/exclude`, then `.gitignore`, and a
/// later `!` re-includes what any earlier line ignored. historica has no
/// negation, so a line that some later `!` could override is not carried.
/// Nested `.gitignore` files are named in `nested`: a pattern in one applies
/// only below its own directory, which no rule's scope can say for a name, so
/// none of their lines is carried, and a `!` in one could override any line
/// above it.
///
/// `tracked` is every file git tracks. A rule covering one of them is dropped:
/// git keeps a tracked file whatever its ignore files say, and a rule that
/// skipped it would record its deletion.
pub fn translate(sources: &[Source], nested: &[Source], tracked: &[String]) -> Translated {
    let mut translated = Translated::default();
    let lines: Vec<(&Source, usize, &str)> = sources
        .iter()
        .flat_map(|source| {
            source
                .text
                .lines()
                .enumerate()
                .map(move |(index, line)| (source, index + 1, line))
        })
        .collect();
    let negated_after = |at: usize| {
        lines[at + 1..]
            .iter()
            .any(|(_, _, line)| line.starts_with('!'))
            || nested
                .iter()
                .any(|source| source.text.lines().any(|line| line.starts_with('!')))
    };

    for (at, (source, number, line)) in lines.iter().enumerate() {
        let place = format!("{}:{number}", source.name);
        let scopes = match scopes(line) {
            Line::Nothing => continue,
            Line::Negation => {
                translated.left.push((
                    place,
                    "a `!` re-includes, and historica's rules only keep out",
                ));
                continue;
            }
            Line::Unsaid(because) => {
                translated.left.push((place, because));
                continue;
            }
            Line::Scopes(scopes) => scopes,
        };
        if negated_after(at) {
            translated.left.push((
                place,
                "a later `!` may re-include part of it, and a rule would keep that part out",
            ));
            continue;
        }
        let rules: Vec<Rule> = scopes
            .into_iter()
            .map(|scope| match source.shared {
                true => Rule::shared(scope),
                false => Rule::private(scope),
            })
            .collect();
        if tracked
            .iter()
            .any(|path| rules.iter().any(|rule| rule.covers(path)))
        {
            translated.left.push((
                place,
                "it covers a file git tracks, and a rule would record that file's deletion",
            ));
            continue;
        }
        for rule in rules {
            if !translated.rules.contains(&rule) {
                translated.rules.push(rule);
            }
        }
    }

    for source in nested {
        for (index, line) in source.text.lines().enumerate() {
            if matches!(scopes(line), Line::Nothing) {
                continue;
            }
            translated.left.push((
                format!("{}:{}", source.name, index + 1),
                "a nested `.gitignore` applies below its own directory, and a rule by \
                 name applies everywhere",
            ));
        }
    }
    translated
}

/// What one line of an ignore file says.
enum Line {
    /// A blank line or a comment.
    Nothing,
    /// A `!` line.
    Negation,
    /// A pattern no rule says exactly.
    Unsaid(&'static str),
    /// The scopes that together say exactly what the line says.
    Scopes(Vec<Scope>),
}

fn scopes(line: &str) -> Line {
    if line.contains('\\') {
        return Line::Unsaid("an escape is git's spelling, and historica has none");
    }
    // git drops trailing spaces that are not escaped, and there are none.
    let line = line.trim_end_matches(' ');
    if line.is_empty() || line.starts_with('#') {
        return Line::Nothing;
    }
    if line.starts_with('!') {
        return Line::Negation;
    }
    if line.contains(['?', '[', ']']) {
        return Line::Unsaid("historica's patterns have `*` and no other wildcard");
    }

    let (mut pattern, mut directory) = match line.strip_suffix('/') {
        Some(stripped) => (stripped, true),
        None => (line, false),
    };
    // `**/name` is `name` at any depth, which is what an unanchored name
    // already is; `path/**` is everything beneath `path`.
    if let Some(rest) = pattern.strip_prefix("**/") {
        pattern = rest;
        if pattern.contains('/') {
            return Line::Unsaid("`**` between directories has no rule that says it");
        }
    }
    // A slash anywhere but the end anchors the pattern to the root, and the
    // one before a trailing `/**` is such a slash.
    let anchored = pattern.contains('/');
    if let Some(rest) = pattern.strip_suffix("/**") {
        pattern = rest;
        directory = true;
    }
    if pattern.contains("**") {
        return Line::Unsaid("`**` between directories has no rule that says it");
    }

    if anchored {
        let path = pattern.trim_start_matches('/');
        if path.is_empty() {
            return Line::Unsaid("it names the whole folder");
        }
        if path.contains('*') {
            return Line::Unsaid("a wildcard in a path has no rule that says it");
        }
        let under = Scope::Under(path.to_owned());
        return Line::Scopes(match directory {
            true => vec![under],
            false => vec![Scope::Path(path.to_owned()), under],
        });
    }
    let Ok(name) = Pattern::parse(pattern) else {
        return Line::Unsaid("historica refuses it as a name");
    };
    Line::Scopes(match directory {
        true => vec![Scope::NameUnder(name)],
        false => vec![Scope::Name(name.clone()), Scope::NameUnder(name)],
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn source(text: &str, shared: bool) -> Source {
        Source {
            name: ".gitignore".to_owned(),
            text: text.to_owned(),
            shared,
        }
    }

    fn said(text: &str) -> Vec<String> {
        translate(&[source(text, true)], &[], &[])
            .rules
            .iter()
            .map(ToString::to_string)
            .collect()
    }

    #[test]
    fn each_form_git_and_historica_share_is_carried() {
        assert_eq!(said("/target"), ["skip target", "skip target/"]);
        assert_eq!(said("target/"), ["skip-name target/"]);
        assert_eq!(said(".env"), ["skip-name .env", "skip-name .env/"]);
        assert_eq!(said("*.log"), ["skip-name *.log", "skip-name *.log/"]);
        assert_eq!(said("**/node_modules/"), ["skip-name node_modules/"]);
        assert_eq!(said("build/**"), ["skip build/"]);
        assert_eq!(said("docs/out"), ["skip docs/out", "skip docs/out/"]);
        assert_eq!(said("# a comment\n\n"), Vec::<String>::new());
    }

    #[test]
    fn what_historica_cannot_say_is_left_and_said() {
        for line in [
            "file?.txt",
            "[ab].c",
            "a/**/b",
            "src/*.rs",
            "\\#hash",
            "!keep",
        ] {
            let translated = translate(&[source(line, true)], &[], &[]);
            assert!(translated.rules.is_empty(), "{line} became a rule");
            assert_eq!(translated.left.len(), 1, "{line} was not said");
        }
    }

    #[test]
    fn a_line_a_later_negation_could_override_is_left() {
        let translated = translate(
            &[
                source("*.log\n", false),
                source("/target\n!keep.log\n", true),
            ],
            &[],
            &[],
        );
        assert!(translated.rules.is_empty());
        assert_eq!(translated.left.len(), 3);

        let after = translate(&[source("!keep.log\n/target\n", true)], &[], &[]);
        assert_eq!(after.rules.len(), 2);
    }

    #[test]
    fn a_rule_covering_a_tracked_file_is_left() {
        let tracked = ["logs/kept.log".to_owned()];
        let translated = translate(&[source("*.log\n/target\n", true)], &[], &tracked);
        let rules: Vec<String> = translated.rules.iter().map(ToString::to_string).collect();
        assert_eq!(rules, ["skip target", "skip target/"]);
        assert_eq!(translated.left[0].0, ".gitignore:1");
    }

    #[test]
    fn a_private_source_makes_private_rules() {
        let rules = translate(&[source(".DS_Store", false)], &[], &[]).rules;
        assert!(rules.iter().all(|rule| !rule.travels()));
    }

    #[test]
    fn a_nested_file_is_said_and_its_negation_stops_the_rest() {
        let nested = Source {
            name: "sub/.gitignore".to_owned(),
            text: "out\n!keep\n".to_owned(),
            shared: true,
        };
        let translated = translate(&[source("/target", true)], &[nested], &[]);
        assert!(translated.rules.is_empty());
        assert_eq!(translated.left.len(), 3);
    }
}
