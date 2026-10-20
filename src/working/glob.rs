//! Decision 0087's pattern: one gitignore pattern, anchored at the root.
//!
//! The meaning is git's `wildmatch` with pathname matching, applied to a
//! pattern that is always matched against the whole path. The spelling is
//! narrower than git's, so that one meaning has one spelling: no leading `/`,
//! no `**` inside a part, no two `**` in a row, `[!` and never `[^`, and a
//! `\` only where something needs escaping. `tests/corpus/skipped/` is the
//! specification executed, and its verdicts are git's.

use std::fmt;

/// One pattern, as a `skip-glob`, `private-glob` or `except` line holds it,
/// without the trailing `/` that says it names a directory.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GlobPattern {
    /// The value as it was written, which [`GlobPattern::parse`] reads back.
    source: String,
    /// The value split on `/`.
    parts: Vec<Part>,
}

/// One `/`-separated part of a pattern.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Part {
    /// `**`: any number of directories, or as the last part, anything beneath.
    Any,
    /// Anything else, matched against one path component.
    Name(Vec<Token>),
}

/// One unit of a part.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Token {
    /// One character, written as itself or escaped.
    Char(char),
    /// `*`: any run of characters within the component.
    Star,
    /// `?`: one character.
    One,
    /// `[...]`: one character from a set, or with `!`, one not in it.
    Set { negated: bool, items: Vec<Item> },
}

/// What a set holds.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Item {
    Char(char),
    Range(char, char),
    Class(Class),
}

/// A POSIX class, which git reads in the C locale: ASCII only.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Class {
    Alnum,
    Alpha,
    Blank,
    Cntrl,
    Digit,
    Graph,
    Lower,
    Print,
    Punct,
    Space,
    Upper,
    Xdigit,
}

impl Class {
    fn named(name: &str) -> Option<Self> {
        Some(match name {
            "alnum" => Class::Alnum,
            "alpha" => Class::Alpha,
            "blank" => Class::Blank,
            "cntrl" => Class::Cntrl,
            "digit" => Class::Digit,
            "graph" => Class::Graph,
            "lower" => Class::Lower,
            "print" => Class::Print,
            "punct" => Class::Punct,
            "space" => Class::Space,
            "upper" => Class::Upper,
            "xdigit" => Class::Xdigit,
            _ => return None,
        })
    }

    fn holds(self, character: char) -> bool {
        match self {
            Class::Alnum => character.is_ascii_alphanumeric(),
            Class::Alpha => character.is_ascii_alphabetic(),
            Class::Blank => matches!(character, ' ' | '\t'),
            Class::Cntrl => character.is_ascii_control(),
            Class::Digit => character.is_ascii_digit(),
            Class::Graph => character.is_ascii_graphic(),
            Class::Lower => character.is_ascii_lowercase(),
            Class::Print => character.is_ascii_graphic() || character == ' ',
            Class::Punct => character.is_ascii_punctuation(),
            Class::Space => matches!(character, ' ' | '\t' | '\n' | '\r'),
            Class::Upper => character.is_ascii_uppercase(),
            Class::Xdigit => character.is_ascii_hexdigit(),
        }
    }
}

impl GlobPattern {
    /// Read a pattern, refusing every second spelling of a meaning and every
    /// pattern that could match nothing.
    pub fn parse(value: &str) -> Result<Self, &'static str> {
        if value.is_empty() {
            return Err("a glob is not empty");
        }
        if value.starts_with('/') {
            return Err("a glob is anchored at the root already, so a leading `/` \
                        says nothing: `src/x`, not `/src/x`");
        }
        if value.starts_with(char::is_whitespace) {
            return Err("a glob starts with no space, and a leading space in a \
                        name is spelled `\\ `");
        }
        if value.ends_with(char::is_whitespace) && !escapes_last(value) {
            return Err("a glob ends with no space, and a trailing space in a \
                        name is spelled `\\ `");
        }
        let mut parts = Vec::new();
        for text in value.split('/') {
            if text.is_empty() {
                return Err("a glob has no empty part, and `//` matches nothing");
            }
            if text == "." || text == ".." {
                return Err("a glob has no `.` or `..` part, and a path holds none");
            }
            if text == "**" {
                if parts.last() == Some(&Part::Any) {
                    return Err("two `**` in a row say what one says");
                }
                parts.push(Part::Any);
                continue;
            }
            parts.push(Part::Name(tokens(text)?));
        }
        Ok(Self {
            source: value.to_owned(),
            parts,
        })
    }

    /// The value as it was written.
    pub fn as_str(&self) -> &str {
        &self.source
    }

    /// Whether this pattern matches a path, given as its components.
    pub fn matches(&self, components: &[&str]) -> bool {
        parts_match(&self.parts, components)
    }

    /// Whether every part is `*` or `**` and one is `**`: a pattern that,
    /// standing alone, covers every file or every directory.
    pub(crate) fn is_everything(&self) -> bool {
        self.parts.contains(&Part::Any)
            && self.parts.iter().all(|part| match part {
                Part::Any => true,
                Part::Name(tokens) => tokens.iter().all(|token| *token == Token::Star),
            })
    }

    /// Whether the value holds anything but literal characters and `/`.
    pub(crate) fn is_literal(&self) -> bool {
        !self.source.contains(['*', '?', '[', '\\'])
    }
}

impl fmt::Display for GlobPattern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.source)
    }
}

/// A glob rule's value: its pattern, and the exceptions that narrow it.
///
/// Decision 0087: the order of `except` lines means nothing, so they are held
/// sorted and once each, and two replicas that state one rule spell one file.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Glob {
    pattern: GlobPattern,
    except: Vec<GlobPattern>,
}

impl Glob {
    /// A pattern with its exceptions, refusing one that covers everything.
    pub fn new(pattern: GlobPattern, mut except: Vec<GlobPattern>) -> Result<Self, &'static str> {
        except.sort_by(|one, other| one.source.cmp(&other.source));
        except.dedup();
        if except.is_empty() && pattern.is_everything() {
            return Err("a glob of nothing but `*` and `**` covers everything, and \
                        rules exist to name the exceptions to it");
        }
        Ok(Self { pattern, except })
    }

    /// What the rule matches.
    pub fn pattern(&self) -> &GlobPattern {
        &self.pattern
    }

    /// What narrows it, sorted.
    pub fn except(&self) -> &[GlobPattern] {
        &self.except
    }

    /// Whether the pattern matches these components and no exception does.
    pub fn admits(&self, components: &[&str]) -> bool {
        self.pattern.matches(components)
            && !self.except.iter().any(|except| except.matches(components))
    }
}

/// Whether the last character of `value` is escaped, which takes an odd run
/// of `\` before it.
fn escapes_last(value: &str) -> bool {
    let mut characters = value.chars().rev();
    characters.next();
    characters
        .take_while(|character| *character == '\\')
        .count()
        % 2
        == 1
}

/// One part's tokens.
fn tokens(text: &str) -> Result<Vec<Token>, &'static str> {
    let characters: Vec<char> = text.chars().collect();
    let mut found = Vec::new();
    let mut at = 0;
    while at < characters.len() {
        match characters[at] {
            '\\' => {
                let escaped = characters
                    .get(at + 1)
                    .copied()
                    .ok_or("a `\\` escapes the character after it, and there is none")?;
                if !matches!(escaped, '*' | '?' | '[' | '\\' | ' ') {
                    return Err("a `\\` escapes only `*`, `?`, `[`, `\\` and a space; \
                                anything else means itself unescaped");
                }
                found.push(Token::Char(escaped));
                at += 2;
            }
            '*' => {
                if characters.get(at + 1) == Some(&'*') {
                    return Err("`**` is a whole part or nothing, and `a**b` is `a*b`");
                }
                found.push(Token::Star);
                at += 1;
            }
            '?' => {
                found.push(Token::One);
                at += 1;
            }
            '[' => {
                let (set, after) = set(&characters, at + 1)?;
                found.push(set);
                at = after;
            }
            character => {
                found.push(Token::Char(character));
                at += 1;
            }
        }
    }
    Ok(found)
}

/// A set whose `[` is just before `start`, and where the part resumes.
fn set(characters: &[char], start: usize) -> Result<(Token, usize), &'static str> {
    const UNCLOSED: &str = "a `[` opens a set that `]` closes, and a literal one is `\\[`";
    let mut at = start;
    let negated = characters.get(at) == Some(&'!');
    if negated {
        at += 1;
    }
    if characters.get(at) == Some(&'^') {
        return Err("a set is negated with `!`, as `[!a]`, and `[^a]` spells it twice");
    }
    let mut items = Vec::new();
    let mut first = true;
    loop {
        let character = *characters.get(at).ok_or(UNCLOSED)?;
        if character == ']' && !first {
            return Ok((Token::Set { negated, items }, at + 1));
        }
        first = false;
        if character == '\\' {
            return Err("a set holds no `\\`: `]` first and `-` first or last mean \
                        themselves");
        }
        if character == '[' && characters.get(at + 1) == Some(&':') {
            let name_start = at + 2;
            let close = (name_start..characters.len().saturating_sub(1))
                .find(|&end| characters[end] == ':' && characters[end + 1] == ']')
                .ok_or("a class is spelled `[:name:]`")?;
            let name: String = characters[name_start..close].iter().collect();
            let class = Class::named(&name).ok_or(
                "the classes are alnum, alpha, blank, cntrl, digit, graph, lower, \
                 print, punct, space, upper and xdigit",
            )?;
            items.push(Item::Class(class));
            at = close + 2;
            continue;
        }
        let end = characters.get(at + 2).copied();
        if characters.get(at + 1) == Some(&'-') && end.is_some_and(|end| end != ']') {
            let end = end.unwrap_or(character);
            if end == '\\' {
                return Err("a set holds no `\\`: `]` first and `-` first or last mean \
                            themselves");
            }
            if end < character {
                return Err("a range runs upward, and one that runs down matches nothing");
            }
            items.push(Item::Range(character, end));
            at += 3;
            continue;
        }
        items.push(Item::Char(character));
        at += 1;
    }
}

/// Whether `parts` match exactly the components of `path`.
///
/// A `**` as the last part takes one component or more, which is git's
/// `a/**` covering what is in `a` and not `a`; anywhere else it takes any
/// number, including none.
fn parts_match(parts: &[Part], path: &[&str]) -> bool {
    match parts.split_first() {
        None => path.is_empty(),
        Some((Part::Any, [])) => !path.is_empty(),
        Some((Part::Any, rest)) => (0..=path.len()).any(|skip| parts_match(rest, &path[skip..])),
        Some((Part::Name(tokens), rest)) => path
            .split_first()
            .is_some_and(|(first, tail)| name_matches(tokens, first) && parts_match(rest, tail)),
    }
}

/// Whether one part matches one component.
///
/// A star takes as little as it can and gives back one character at a time,
/// which is exact for a pattern whose only repetition is a star: the last
/// star reached is the only one any later failure needs to retry.
fn name_matches(tokens: &[Token], component: &str) -> bool {
    let characters: Vec<char> = component.chars().collect();
    let (mut token, mut at) = (0, 0);
    let mut retry: Option<(usize, usize)> = None;
    while at < characters.len() {
        match tokens.get(token) {
            Some(Token::Star) => {
                retry = Some((token, at));
                token += 1;
            }
            Some(single) if one_matches(single, characters[at]) => {
                token += 1;
                at += 1;
            }
            _ => match retry {
                Some((star, from)) => {
                    token = star + 1;
                    at = from + 1;
                    retry = Some((star, from + 1));
                }
                None => return false,
            },
        }
    }
    tokens[token..].iter().all(|rest| *rest == Token::Star)
}

/// Whether a token that is not a star matches one character.
fn one_matches(token: &Token, character: char) -> bool {
    match token {
        Token::Char(expected) => *expected == character,
        Token::One => true,
        Token::Star => false,
        Token::Set { negated, items } => {
            let held = items.iter().any(|item| match item {
                Item::Char(expected) => *expected == character,
                Item::Range(low, high) => (*low..=*high).contains(&character),
                Item::Class(class) => class.holds(character),
            });
            held != *negated
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn matches(pattern: &str, path: &str) -> bool {
        let components: Vec<&str> = path.split('/').collect();
        GlobPattern::parse(pattern)
            .expect("a pattern")
            .matches(&components)
    }

    #[test]
    fn a_part_matches_one_component() {
        assert!(matches("src/*.rs", "src/main.rs"));
        assert!(!matches("src/*.rs", "src/a/main.rs"));
        assert!(matches("*.tmp", ".tmp"), "a star takes a leading dot");
        assert!(matches("a?c", "abc"));
        assert!(!matches("a?c", "ac"));
        assert!(matches("*a*b*c", "xaybzc"));
        assert!(!matches("*a*b*c", "xaybz"));
    }

    #[test]
    fn a_double_star_is_any_number_of_directories() {
        assert!(matches("**/b", "b"));
        assert!(matches("**/b", "x/y/b"));
        assert!(matches("a/**/b", "a/b"));
        assert!(matches("a/**/b", "a/x/y/b"));
        assert!(matches("a/**", "a/x"));
        assert!(matches("a/**", "a/x/y"));
        assert!(!matches("a/**", "a"), "a trailing `**` is what is beneath");
    }

    #[test]
    fn a_set_is_one_character() {
        assert!(matches("[a-c]x", "bx"));
        assert!(!matches("[a-c]x", "dx"));
        assert!(matches("[!a-c]x", "dx"));
        assert!(matches("[]a]", "]"));
        assert!(matches("[a-]", "-"));
        assert!(matches("[[:digit:]]x", "1x"));
        assert!(!matches("[[:digit:]]x", "ax"));
    }

    #[test]
    fn an_escape_means_the_character() {
        assert!(matches("\\*", "*"));
        assert!(!matches("\\*", "a"));
        assert!(matches("trail\\ ", "trail "));
    }

    #[test]
    fn a_second_spelling_is_refused() {
        for refused in [
            "/a",
            "a//b",
            "a/./b",
            "a/../b",
            "a**b",
            "**/**/a",
            "[^a]",
            "\\#a",
            "[a",
            "[\\]]",
            "[z-a]",
            "[[:word:]]",
            "a ",
            " a",
            "a\\",
        ] {
            assert!(GlobPattern::parse(refused).is_err(), "{refused}");
        }
    }
}
