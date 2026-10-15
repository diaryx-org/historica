//! The one place this crate parses a document.
//!
//! A remark is content — a text file with a metadata block and a body. This
//! module finds the block: it detects the archetype (`---` YAML frontmatter,
//! `+++` TOML, a fenced block), resolves the format its content is written
//! in, and hands the block to `fig` to read, with the prose on either side of
//! it as the body.
//!
//! Finding the block was fig's own job until fig 6 took embedding out of fig
//! (fig's `docs/migrating-to-6.md`, "Embedding has left fig"); its successor,
//! twig's `twig::meta`, reads Markdown frontmatter and endmatter and nothing
//! else. So the rules here are fig 5's `Embed::detect` and `Embed::extract`,
//! kept as they were, so that every document that read as a remark before
//! still does: the archetypes on the first line, then a trailing
//! ```` ```endmatter ```` block, then an HTML data island anywhere in the page.
//!
//! Which format a store's documents use is not this crate's to decide, so
//! nothing here names one: [`split`] reads whichever it finds. What it will
//! not do is guess at a file with no block at all — that is a document with
//! no metadata, which is a document that is not a remark, and it comes back
//! as `None` rather than as an error.
//!
//! A caller that has already parsed its own documents never reaches this
//! module. It implements [`Fields`](crate::Fields) over its own value tree
//! and calls [`Reader::read`](crate::Reader::read), and this file is dead
//! code to it — which is the point of the seam being a trait.

use crate::error::Result;

/// A document's metadata block and its body, or `None` when it has no block.
///
/// The body is the host text outside the block: the prose under
/// frontmatter, the prose above endmatter. It is owned rather than borrowed
/// because a mid-document block has host text on *both* sides of it, and a
/// remark's body is all of it.
pub fn split(text: &str) -> Result<Option<(fig::Value, String)>> {
    let Some(block) = locate(text) else {
        // No block, or an opening delimiter with nothing closing it. The open
        // alone is enough to recognise one; a caller asking for remarks in a
        // chain of a thousand documents should not have the whole answer
        // refused because one of them has a stray `---` in it.
        return Ok(None);
    };
    let format = match block.inner {
        Inner::Yaml => fig_yaml::format()?,
        Inner::Json => fig_json::format()?,
        Inner::Toml => fig_toml::format()?,
        // fig's authoring dialect is recognised, as it always was, and not
        // read: this crate does not link the language.
        Inner::Figl => return Err(fig::Error::UnsupportedFormat.into()),
    };
    let meta = fig::Document::parse(text[block.content.clone()].as_bytes(), format)?;
    let before = &text[..block.open_start];
    let after = &text[block.close_end..];
    let body = match before.is_empty() {
        true => after.to_string(),
        false => format!("{before}{after}"),
    };
    Ok(Some((meta.to_value()?, body)))
}

/// The four languages a block can be written in. Three are read; see
/// [`split`] for the fourth.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Inner {
    Yaml,
    Json,
    Toml,
    Figl,
}

/// How a block closes, which is what its open line decides.
#[derive(Debug, Clone, Copy)]
enum Close {
    /// The line, trailing space trimmed, is one of these. Leading space
    /// counts: a Markdown fence sits at column 0.
    WholeLine(&'static [&'static str]),
    /// The line, trimmed on both sides, is one of these: a close tag may be
    /// indented inside the page it sits in.
    Trimmed(&'static [&'static str]),
}

/// A block that opens and closes: where its open line starts, the content
/// between its fences, and where its close line ends.
struct Block {
    inner: Inner,
    open_start: usize,
    content: std::ops::Range<usize>,
    close_end: usize,
}

const BOM: &str = "\u{feff}";

/// The first block in `text`, as fig 5 found it: a block opening on the
/// first line (after a byte-order mark), else a trailing ```` ```endmatter ````
/// block, else an HTML `<script>` or `<code>` island on a line of its own.
/// `None` for no open, or for an open with no close after it.
fn locate(text: &str) -> Option<Block> {
    let start = if text.starts_with(BOM) { BOM.len() } else { 0 };
    let (open, inner, close) = detect(text, start)?;
    let mut at = open.end;
    while at < text.len() {
        let end = line_end(text, at);
        let line = text[at..end].trim_end_matches(['\r', '\n']);
        let closes = match close {
            Close::WholeLine(tokens) => tokens.contains(&line.trim_end_matches(HSPACE)),
            Close::Trimmed(tokens) => tokens.contains(&line.trim_matches(HSPACE)),
        };
        if closes {
            return Some(Block {
                inner,
                open_start: open.start,
                content: open.end..at,
                close_end: end,
            });
        }
        at = end;
    }
    None
}

/// The open line of the block `text` has, its language, and how it closes.
fn detect(text: &str, start: usize) -> Option<(std::ops::Range<usize>, Inner, Close)> {
    const DASHES: Close = Close::WholeLine(&["---", "..."]);
    const FENCE: Close = Close::WholeLine(&["```"]);

    let first = start..line_end(text, start);
    let line = trimmed(&text[first.clone()]);
    if let Some(inner) = fenced_open(line) {
        return Some((first, inner, FENCE));
    }
    if let Some(inner) = frontmatter_open(line) {
        return Some((first, inner, DASHES));
    }
    match line {
        ";;;" => return Some((first, Inner::Json, Close::WholeLine(&[";;;"]))),
        "+++" => return Some((first, Inner::Toml, Close::WholeLine(&["+++"]))),
        _ => {}
    }

    let mut at = start;
    while at < text.len() {
        let end = line_end(text, at);
        let line = text[at..end].trim_end_matches(['\r', '\n']);
        if line.trim_end_matches(HSPACE) == "```endmatter" {
            return Some((at..end, Inner::Yaml, FENCE));
        }
        at = end;
    }
    let mut at = start;
    while at < text.len() {
        let end = line_end(text, at);
        let line = trimmed(&text[at..end]);
        if let Some(inner) = script_open(line) {
            return Some((at..end, inner, Close::Trimmed(&["</script>"])));
        }
        if let Some(inner) = code_open(line) {
            return Some((
                at..end,
                inner,
                Close::Trimmed(&["</code></pre>", "</code>"]),
            ));
        }
        at = end;
    }
    None
}

const HSPACE: [char; 2] = [' ', '\t'];

/// Where the line starting at `from` ends: past its newline, or at the end.
fn line_end(text: &str, from: usize) -> usize {
    text[from..]
        .find('\n')
        .map_or(text.len(), |nl| from + nl + 1)
}

/// A line without its line ending or the space around it.
fn trimmed(line: &str) -> &str {
    line.trim_end_matches(['\r', '\n']).trim_matches(HSPACE)
}

/// The first space-separated word: a fence's info string may say more after
/// its language.
fn first_token(s: &str) -> &str {
    let s = s.trim_matches(HSPACE);
    s.split(HSPACE).next().unwrap_or(s)
}

/// A fence tag or `---` tag's language; `None` for one that is not a config
/// language, so a ```` ```python ```` sample is prose and not a block.
fn from_tag(tag: &str) -> Option<Inner> {
    let is = |name: &str| tag.eq_ignore_ascii_case(name);
    match () {
        _ if is("yaml") || is("yml") => Some(Inner::Yaml),
        _ if is("json") => Some(Inner::Json),
        _ if is("toml") => Some(Inner::Toml),
        _ if is("fig") || is("figl") => Some(Inner::Figl),
        _ => None,
    }
}

/// A `<script type>`'s language.
fn from_mime(mime: &str) -> Option<Inner> {
    let is = |name: &str| mime.eq_ignore_ascii_case(name);
    match () {
        _ if is("application/yaml") || is("application/x-yaml") || is("text/yaml") => {
            Some(Inner::Yaml)
        }
        _ if is("application/json") || is("application/ld+json") => Some(Inner::Json),
        _ if is("application/toml") => Some(Inner::Toml),
        _ if is("application/figl") || is("application/fig") => Some(Inner::Figl),
        _ => None,
    }
}

/// ```` ```<lang> ````. A bare ```` ``` ```` closes and never opens.
fn fenced_open(line: &str) -> Option<Inner> {
    let tag = line.strip_prefix("```")?.trim_matches(HSPACE);
    if tag.is_empty() {
        return None;
    }
    from_tag(first_token(tag))
}

/// A bare `---`, which is YAML, or `---<lang>`.
fn frontmatter_open(line: &str) -> Option<Inner> {
    let rest = line.strip_prefix("---")?.trim_matches(HSPACE);
    if rest.is_empty() {
        return Some(Inner::Yaml);
    }
    from_tag(first_token(rest))
}

/// The attributes of an open tag `<name …>` that is the whole line, or
/// `None`. The name compares as HTML compares it, ignoring case, and must end
/// there: `<scripts>` is not `<script>`.
fn open_tag<'a>(line: &'a str, name: &str) -> Option<&'a str> {
    let head = line.get(..name.len())?;
    if !head.eq_ignore_ascii_case(name) {
        return None;
    }
    let rest = &line[name.len()..];
    if !rest.starts_with([' ', '\t', '>']) {
        return None;
    }
    let gt = rest.find('>')?;
    (gt == rest.len() - 1).then(|| &rest[..gt])
}

/// `<script type="…">` on a line of its own, typed as a config language.
fn script_open(line: &str) -> Option<Inner> {
    from_mime(attribute(open_tag(line, "<script")?, "type")?)
}

/// `<code class="language-…">`, perhaps after `<pre>` on the same line.
fn code_open(line: &str) -> Option<Inner> {
    let mut line = line;
    if line
        .get(..4)
        .is_some_and(|head| head.eq_ignore_ascii_case("<pre"))
    {
        if !line[4..].starts_with([' ', '\t', '>']) {
            return None;
        }
        let gt = line.find('>')?;
        line = line[gt + 1..].trim_start_matches(HSPACE);
    }
    let class = attribute(open_tag(line, "<code")?, "class")?;
    class
        .split(HSPACE)
        .filter_map(|word| {
            word.strip_prefix("language-")
                .or_else(|| word.strip_prefix("lang-"))
        })
        .find_map(from_tag)
}

/// The value of attribute `name` in an open tag's attributes: quoted either
/// way or not at all, in any order, its name compared without case.
fn attribute<'a>(attrs: &'a str, name: &str) -> Option<&'a str> {
    let bytes = attrs.as_bytes();
    let space = |i: usize| bytes[i] == b' ' || bytes[i] == b'\t';
    let mut i = 0;
    while i < bytes.len() {
        while i < bytes.len() && space(i) {
            i += 1;
        }
        if i >= bytes.len() {
            break;
        }
        let name_start = i;
        while i < bytes.len() && bytes[i] != b'=' && !space(i) {
            i += 1;
        }
        let attr = &attrs[name_start..i];
        while i < bytes.len() && space(i) {
            i += 1;
        }
        let mut value = "";
        if i < bytes.len() && bytes[i] == b'=' {
            i += 1;
            while i < bytes.len() && space(i) {
                i += 1;
            }
            if i < bytes.len() && (bytes[i] == b'"' || bytes[i] == b'\'') {
                let quote = bytes[i];
                i += 1;
                let start = i;
                while i < bytes.len() && bytes[i] != quote {
                    i += 1;
                }
                value = &attrs[start..i];
                if i < bytes.len() {
                    i += 1;
                }
            } else {
                let start = i;
                while i < bytes.len() && !space(i) {
                    i += 1;
                }
                value = &attrs[start..i];
            }
        }
        if attr.eq_ignore_ascii_case(name) {
            return Some(value);
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::split;

    /// The block's `target`, and the body, for a document that has a block.
    fn read(text: &str) -> Option<(String, String)> {
        let (meta, body) = split(text).unwrap()?;
        let target = meta.get("target").and_then(fig::Value::as_str).unwrap();
        Some((target.to_string(), body))
    }

    fn reads(text: &str, body: &str) {
        assert_eq!(read(text), Some(("t".into(), body.into())), "{text:?}");
    }

    #[test]
    fn every_archetype_fig_5_read_still_reads() {
        reads("---\ntarget: t\n---\nbody\n", "body\n");
        reads("---\ntarget: t\n...\nbody\n", "body\n");
        reads("---yaml\ntarget: t\n---\n", "");
        reads("---json\n{\"target\": \"t\"}\n---\n", "");
        reads("---toml\ntarget = \"t\"\n---\n", "");
        reads("+++\ntarget = \"t\"\n+++\nbody", "body");
        reads(";;;\n{\"target\": \"t\"}\n;;;\n", "");
        reads("```yml title\ntarget: t\n```\nbody\n", "body\n");
        reads("```TOML\ntarget = \"t\"\n```\n", "");
        reads("body\n\n```endmatter\ntarget: t\n```\n", "body\n\n");
        reads(
            "<head>\n  <script type='application/ld+json'>\n{\"target\": \"t\"}\n  </script>\n</head>\n",
            "<head>\n</head>\n",
        );
        reads(
            "<pre><code class=\"hl language-yaml\">\ntarget: t\n</code></pre>\n",
            "",
        );
        reads("\u{feff}---\r\ntarget: t\r\n---\r\nbody", "\u{feff}body");
    }

    #[test]
    fn what_is_not_a_block_is_none() {
        assert_eq!(read("just prose\n"), None);
        assert_eq!(read("---\ntarget: t\n"), None, "never closed");
        assert_eq!(read("```python\ntarget = 't'\n```\n"), None);
        assert_eq!(
            read("<scripts type=\"application/json\">\n{}\n</scripts>\n"),
            None
        );
        assert_eq!(
            read("text\n---\ntarget: t\n---\n"),
            None,
            "not on the first line"
        );
        assert_eq!(
            read(" ---\ntarget: t\n ---\n"),
            None,
            "an indented fence closes nothing"
        );
    }

    #[test]
    fn figl_is_found_and_not_read() {
        assert!(split("```fig\ntarget = t\n```\n").is_err());
    }
}
