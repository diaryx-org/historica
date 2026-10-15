//! The remark itself — *a reader's mark on somebody else's document.*
//!
//! The model is the W3C Web Annotation Data Model's, because that is where
//! the experience of anchoring a remark to text that may later change was
//! paid for: a **target** (what is annotated), a **selector** (which part —
//! the quoted text with a little of what surrounds it), a **motivation**
//! (why), a **body** (what the reader said), and a **state** (which version
//! of the target the reader was looking at).
//!
//! Its serialisation is not borrowed. JSON-LD nesting is the wrong shape for
//! a metadata block a person edits, so a remark is an ordinary document whose
//! metadata is flat and typed:
//!
//! ```yaml
//! target: ark:12345/dxk7f2q9wl/bcdfgr   # the annotated document, durably
//! at: 3f9ce1                            # the revision the reader saw
//! exact: "we had no idea the lake would freeze"
//! prefix: "That winter "
//! suffix: " and Dad laughed"
//! motivation: questioning
//! color: yellow
//! ```
//!
//! and whose body is the remark. A highlight is a remark with no body.
//!
//! # Why the fields are quoted and the format is fig's
//!
//! `exact`, `prefix`, `suffix` and `replacement` are verbatim slices of
//! somebody's prose. Their edge whitespace is the point — the prefix above
//! ends in a space, the suffix begins with one — and a format that trimmed
//! them would produce an anchor that silently stops matching, in the one piece
//! of machinery whose whole job is surviving an edit. They may also contain
//! newlines. So the carrying format has to quote, and fig's quoted scalars
//! are that rule already written and already tested; inventing a line grammar
//! here would mean inventing an escape rule beside it.
//!
//! # Editing
//!
//! `editing` is the one motivation that proposes a change rather than saying
//! something about the passage — the Web Annotation model's own term for a
//! reader requesting an edit to the target. It is a patch, and it is shaped
//! like one:
//!
//! ```yaml
//! target: ark:12345/dxk7f2q9wl/bcdfgr
//! at: 3f9ce1                            # the base — required, for an edit
//! exact: "the red bouy"                 # what to replace
//! prefix: "rowed out past "
//! suffix: " before"
//! motivation: editing
//! replacement: "the red buoy"           # what to replace it with
//! ```
//!
//! The replacement lives in the metadata, quoted, for the reason the selector
//! does: it is prose whose edge whitespace and newlines are the proposal. The
//! body stays what it is everywhere else — what the reader said, here about
//! *why* — and may be empty. An empty `replacement` is a deletion; an
//! insertion quotes the neighbouring text and gives it back with the new
//! words inside it, so there is no second selector kind to anchor.
//!
//! Three things every other motivation may leave out are required of an
//! edit, and a document that calls itself one without them is
//! [`Error::Unreadable`]: the base revision, because a patch without a base
//! is a guess; a selector, because this crate does not define a whole-document
//! patch; and the replacement itself. The converse holds too — a
//! `replacement` on a comment is a document that says two things about
//! itself.
//!
//! [`apply`] is the pure half of taking one: anchor the selector in a text
//! and splice the replacement in, reporting the anchor so the caller can see
//! whether it was certain. Whether a given anchor is certain *enough* — and
//! whether the person proposing it may have it applied without a hand — are
//! policies, and they belong to whoever holds the store.
//!
//! # Why the target is opaque
//!
//! A remark's target is by design in *another* store than the one the remark
//! lives in — the author's, of which the reader holds a fetched copy and
//! never the original. What identity means across that gap is the caller's
//! question, not this crate's: a Diaryx vault names documents by ARK, a
//! static site by URL, a corpus by DOI. So a target is a string here, and
//! what counts as one is a [`TargetCheck`] the caller hands to a [`Reader`].
//!
//! # Anchoring
//!
//! [`anchor`] is the Web Annotation `TextQuoteSelector` rule: find the quoted
//! text, prefer the occurrence its context agrees with, and say how sure that
//! was. Whether the items the reader quoted still *exist* at head, and where
//! they moved to, is the layer above this one ([`crate::layer`]) and needs
//! the store; this function needs only the text.

use crate::error::{Error, Result};

/// The metadata keys a remark is written with.
pub const TARGET_FIELD: &str = "target";
pub const AT_FIELD: &str = "at";
pub const EXACT_FIELD: &str = "exact";
pub const PREFIX_FIELD: &str = "prefix";
pub const SUFFIX_FIELD: &str = "suffix";
pub const MOTIVATION_FIELD: &str = "motivation";
pub const COLOR_FIELD: &str = "color";
/// What an `editing` remark proposes in the quoted passage's place. Present
/// on an edit and on nothing else; empty for a deletion.
pub const REPLACEMENT_FIELD: &str = "replacement";

/// Every field a remark declares, in the order they are written.
pub const FIELDS: &[&str] = &[
    TARGET_FIELD,
    AT_FIELD,
    EXACT_FIELD,
    PREFIX_FIELD,
    SUFFIX_FIELD,
    MOTIVATION_FIELD,
    COLOR_FIELD,
    REPLACEMENT_FIELD,
];

/// Two more Web Annotation properties, written by a store that takes a copy
/// of somebody else's remark rather than by the remark's own author.
///
/// `via` is the remark's identity in the chain that first wrote it — what
/// lets a copy be recognised as a copy, so it is taken once and so its author
/// sees one mark instead of two when it comes back to them. `creator` is who
/// wrote it, as the copying side knows them.
///
/// This crate reads both off a fetched document and writes neither: deciding
/// to take a copy is a policy, and a policy belongs to whoever holds the
/// store.
pub const VIA_FIELD: &str = "via";
pub const CREATOR_FIELD: &str = "creator";

// ---------------------------------------------------------------------------
// Reading a metadata block this crate did not parse
// ---------------------------------------------------------------------------

/// A parsed metadata block, whoever parsed it.
///
/// The crate reads fig, and [`fig::Value`] implements this. It is a trait
/// rather than a concrete type because the callers this is written for
/// already have the document parsed — a workspace engine with its own value
/// tree, an editor with its own frontmatter reader — and making them
/// round-trip through a second parser to be told what they already know would
/// be a cost with nothing on the other side of it.
pub trait Fields {
    /// One field, as a string. `None` for a field that is absent or is not a
    /// string, which this crate treats alike: a `motivation` that is a
    /// number is a field it has no reading for either way.
    fn text(&self, key: &str) -> Option<&str>;

    /// One field that is a term or a list of terms, in the order written —
    /// how `audience` and its kind are spelled. A scalar string is a
    /// one-element list; anything else is empty.
    fn terms(&self, key: &str) -> Vec<&str>;
}

impl Fields for fig::Value {
    fn text(&self, key: &str) -> Option<&str> {
        self.get(key).and_then(fig::Value::as_str)
    }

    fn terms(&self, key: &str) -> Vec<&str> {
        match self.get(key) {
            Some(fig::Value::Seq(items)) => items.iter().filter_map(fig::Value::as_str).collect(),
            Some(value) => value.as_str().into_iter().collect(),
            None => Vec::new(),
        }
    }
}

// ---------------------------------------------------------------------------
// What counts as a target
// ---------------------------------------------------------------------------

/// Whether a string can be a remark's target.
///
/// `Err(why)` refuses it, and `why` is what the reader is told — so the
/// caller that knows what a target *is* is also the one that says what was
/// wrong with this one.
pub trait TargetCheck {
    fn check(&self, target: &str) -> std::result::Result<(), String>;
}

/// Any non-empty string. What a caller with no identity scheme of its own
/// gets, and what [`Reader::new`] uses.
///
/// Empty is still refused: a remark whose target is the empty string is
/// pointing at nothing, and every caller agrees about that one.
#[derive(Debug, Clone, Copy, Default)]
pub struct AnyTarget;

impl TargetCheck for AnyTarget {
    fn check(&self, target: &str) -> std::result::Result<(), String> {
        match target.trim().is_empty() {
            true => Err("a remark's target cannot be empty".to_string()),
            false => Ok(()),
        }
    }
}

impl<F> TargetCheck for F
where
    F: Fn(&str) -> std::result::Result<(), String>,
{
    fn check(&self, target: &str) -> std::result::Result<(), String> {
        self(target)
    }
}

// ---------------------------------------------------------------------------
// The model
// ---------------------------------------------------------------------------

/// Why a remark was made — the Web Annotation motivations a reader of
/// somebody's writing actually has, and no more.
///
/// A closed set. An unknown motivation is an unknown intent, and a reader
/// that guessed at one would be putting words in the writer's mouth; so a
/// document naming one this does not know is [`Error::Unreadable`] rather
/// than a remark with a shrug in it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Motivation {
    /// Marking a passage, with nothing to say about it yet.
    Highlighting,
    /// Saying something about a passage.
    Commenting,
    /// Asking something about a passage.
    Questioning,
    /// Judging whether a passage holds up — the Web Annotation model's term
    /// for "a review or assessment". The term covers praise as well as
    /// critique; a store that has another channel for one of them may narrow
    /// it by convention.
    Assessing,
    /// Answering another remark — whose document is then the target.
    Replying,
    /// Keeping a place.
    Bookmarking,
    /// Proposing a change to a passage: the quoted text, and what should
    /// stand in its place. The one motivation that is a patch — see the
    /// module note on what it requires.
    Editing,
}

impl Motivation {
    /// Every motivation, in the order a picker offers them.
    pub const ALL: [Motivation; 7] = [
        Motivation::Highlighting,
        Motivation::Commenting,
        Motivation::Questioning,
        Motivation::Assessing,
        Motivation::Replying,
        Motivation::Bookmarking,
        Motivation::Editing,
    ];

    /// The Web Annotation spelling, which is what the field carries.
    pub fn as_str(self) -> &'static str {
        match self {
            Motivation::Highlighting => "highlighting",
            Motivation::Commenting => "commenting",
            Motivation::Questioning => "questioning",
            Motivation::Assessing => "assessing",
            Motivation::Replying => "replying",
            Motivation::Bookmarking => "bookmarking",
            Motivation::Editing => "editing",
        }
    }

    /// The motivation a word names, or `None`.
    pub fn parse(word: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|m| m.as_str() == word.trim())
    }

    /// The closed vocabulary's terms — what a store that validates its own
    /// fields declares the `motivation` field as.
    pub fn terms() -> Vec<String> {
        Self::ALL.iter().map(|m| m.as_str().to_string()).collect()
    }
}

impl std::fmt::Display for Motivation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}

/// Which part of the target a remark is about: the quoted text, with a little
/// of what came before and after it, so the quote can be found again when it
/// has moved and told apart when it recurs.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Selector {
    /// The text itself, verbatim.
    pub exact: String,
    /// What immediately preceded it, if any was recorded.
    pub prefix: Option<String>,
    /// What immediately followed it, likewise.
    pub suffix: Option<String>,
}

impl Selector {
    /// A selector over `exact` with no context recorded.
    pub fn quoting(exact: impl Into<String>) -> Self {
        Self {
            exact: exact.into(),
            prefix: None,
            suffix: None,
        }
    }

    /// The same, with the text on either side.
    pub fn in_context(
        exact: impl Into<String>,
        prefix: impl Into<String>,
        suffix: impl Into<String>,
    ) -> Self {
        Self {
            exact: exact.into(),
            prefix: Some(prefix.into()),
            suffix: Some(suffix.into()),
        }
    }
}

/// One remark, as read from or written to a document.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Annotation {
    /// The annotated document's identity, in whatever scheme the caller
    /// names documents by. See the module note on why this is a string.
    pub target: String,
    /// The revision of the target the reader was looking at, when known —
    /// a historica revision digest of the copy they hold.
    pub at: Option<String>,
    /// Which part of the target, or `None` for the whole document.
    pub selector: Option<Selector>,
    pub motivation: Motivation,
    /// A rendering hint for a highlight, uninterpreted here.
    pub color: Option<String>,
    /// What the reader said. Empty for a highlight.
    pub body: String,
    /// What an edit proposes in the quoted passage's place — `Some("")` is
    /// a deletion. `Some` exactly when the motivation is
    /// [`Motivation::Editing`]; see [`check`](Self::check).
    pub replacement: Option<String>,
}

impl Annotation {
    /// A remark on the whole of `target`.
    pub fn new(target: impl Into<String>, motivation: Motivation) -> Self {
        Self {
            target: target.into(),
            at: None,
            selector: None,
            motivation,
            color: None,
            body: String::new(),
            replacement: None,
        }
    }

    /// A proposed change to `target` as it stood at revision `at`: the
    /// passage `selector` quotes, replaced by `replacement`. The body is
    /// left for the reader to say why.
    pub fn edit(
        target: impl Into<String>,
        at: impl Into<String>,
        selector: Selector,
        replacement: impl Into<String>,
    ) -> Self {
        Self {
            target: target.into(),
            at: Some(at.into()),
            selector: Some(selector),
            motivation: Motivation::Editing,
            color: None,
            body: String::new(),
            replacement: Some(replacement.into()),
        }
    }

    /// Whether this remark says one thing about itself.
    ///
    /// An edit needs a base revision, a selector with something in it, and a
    /// replacement; anything else must not carry a replacement. [`Reader`]
    /// refuses a document that fails this, and a writer building one by hand
    /// can ask before writing it.
    pub fn check(&self) -> Result<()> {
        let editing = self.motivation == Motivation::Editing;
        let quoted = self.selector.as_ref().is_some_and(|s| !s.exact.is_empty());
        match (
            editing,
            self.at.is_some(),
            quoted,
            self.replacement.is_some(),
        ) {
            (true, true, true, true) | (false, _, _, false) => Ok(()),
            (true, false, _, _) => Err(Error::Unreadable(
                "an edit names no `at` — a patch needs the revision it was made against".into(),
            )),
            (true, _, false, _) => Err(Error::Unreadable(
                "an edit quotes nothing — a patch needs the passage it replaces".into(),
            )),
            (true, _, _, false) => Err(Error::Unreadable(
                "an edit has no `replacement` — a patch needs what goes in the passage's place"
                    .into(),
            )),
            (false, _, _, true) => Err(Error::Unreadable(format!(
                "a `replacement` on a remark whose motivation is {} — only an edit carries one",
                self.motivation
            ))),
        }
    }

    /// The metadata this remark is written with, in [`FIELDS`] order.
    ///
    /// Pairs rather than a map of somebody's `Value` type, because the two
    /// kinds of caller want different maps out of it and neither wants a
    /// conversion: a store with its own value tree builds its own, and
    /// [`render`](Self::render) builds fig's.
    ///
    /// Absent halves are absent keys, not empty ones — a suffix that was
    /// never recorded and a suffix that is the empty string are different
    /// facts about what the reader saw.
    pub fn fields(&self) -> Vec<(&'static str, String)> {
        let mut out = Vec::with_capacity(FIELDS.len());
        let mut put = |key: &'static str, value: Option<&str>| {
            if let Some(value) = value {
                out.push((key, value.to_string()));
            }
        };
        put(TARGET_FIELD, Some(&self.target));
        put(AT_FIELD, self.at.as_deref());
        if let Some(selector) = &self.selector {
            put(EXACT_FIELD, Some(&selector.exact));
            put(PREFIX_FIELD, selector.prefix.as_deref());
            put(SUFFIX_FIELD, selector.suffix.as_deref());
        }
        put(MOTIVATION_FIELD, Some(self.motivation.as_str()));
        put(COLOR_FIELD, self.color.as_deref());
        put(REPLACEMENT_FIELD, self.replacement.as_deref());
        out
    }

    /// The whole document: this remark's metadata as a fig frontmatter
    /// block, then the body.
    ///
    /// What a caller with no document format of its own writes. A caller that
    /// has one — a workspace engine, a static site generator — takes
    /// [`fields`](Self::fields) and writes its own, which is the case this
    /// crate expects more of.
    ///
    /// The inverse of [`Reader::document`] in every field but the body's
    /// surrounding whitespace: this writes the blank line that separates a
    /// frontmatter block from the prose under it, as markdown is written, and
    /// reading gives that line back. Neither side trims — a body is somebody's
    /// prose, and a reader that decided which of its whitespace counted would
    /// be editing it.
    pub fn render(&self) -> Result<String> {
        let map = fig::Value::Map(
            self.fields()
                .into_iter()
                .map(|(key, value)| (fig::Value::Str(key.to_string()), fig::Value::Str(value)))
                .collect(),
        );
        let meta = map.serialize(fig_yaml::format()?)?;
        let mut text = String::from("---\n");
        text.push_str(meta.trim_end());
        text.push_str("\n---\n");
        if !self.body.trim().is_empty() {
            text.push('\n');
            text.push_str(self.body.trim_end());
            text.push('\n');
        }
        Ok(text)
    }
}

// ---------------------------------------------------------------------------
// Reading
// ---------------------------------------------------------------------------

/// Reads remarks, under one caller's idea of what a target is.
///
/// The target check travels with the reader rather than being handed to every
/// call, because it is a fact about the caller and not about the document: a
/// Diaryx vault refuses a target that is not an ARK everywhere, or nowhere.
#[derive(Debug, Clone, Default)]
pub struct Reader<C = AnyTarget> {
    targets: C,
}

impl Reader<AnyTarget> {
    /// A reader that accepts any non-empty target.
    pub fn new() -> Self {
        Self { targets: AnyTarget }
    }
}

impl<C: TargetCheck> Reader<C> {
    /// A reader that accepts the targets `targets` accepts.
    pub fn with_targets(targets: C) -> Self {
        Self { targets }
    }

    /// Whether `target` is one this reader would accept.
    pub fn check_target(&self, target: &str) -> Result<()> {
        self.targets.check(target.trim()).map_err(Error::Unreadable)
    }

    /// Read a remark out of a document's metadata and body.
    ///
    /// `Ok(None)` for a document that declares no `target` — an ordinary
    /// document, and the answer for most of what a chain holds. `Err` for one
    /// that declares a target and cannot be a remark of it: those two are
    /// different because the first says nothing went wrong and the second
    /// says something did.
    pub fn read(&self, fields: &impl Fields, body: &str) -> Result<Option<Annotation>> {
        let Some(target) = fields.text(TARGET_FIELD) else {
            return Ok(None);
        };
        self.check_target(target)?;
        let motivation = match fields.text(MOTIVATION_FIELD) {
            Some(word) => Motivation::parse(word)
                .ok_or_else(|| Error::Unreadable(format!("unknown motivation {word:?}")))?,
            // A remark without a stated reason is a comment; a mark without
            // one is a highlight.
            None if body.trim().is_empty() => Motivation::Highlighting,
            None => Motivation::Commenting,
        };
        let owned = |key: &str| fields.text(key).map(str::to_string);
        let selector = owned(EXACT_FIELD).map(|exact| Selector {
            exact,
            prefix: owned(PREFIX_FIELD),
            suffix: owned(SUFFIX_FIELD),
        });
        let annotation = Annotation {
            target: target.to_string(),
            at: owned(AT_FIELD),
            selector,
            motivation,
            color: owned(COLOR_FIELD),
            body: body.to_string(),
            replacement: owned(REPLACEMENT_FIELD),
        };
        annotation.check()?;
        Ok(Some(annotation))
    }

    /// [`read`](Self::read), for a whole document this crate parses itself —
    /// the inverse of [`Annotation::render`].
    ///
    /// `Ok(None)` for text with no metadata block at all, as well as for one
    /// whose block declares no target: a document that is not a remark is not
    /// a remark for either reason.
    pub fn document(&self, text: &str) -> Result<Option<Annotation>> {
        let Some((meta, body)) = crate::document::split(text)? else {
            return Ok(None);
        };
        self.read(&meta, &body)
    }
}

// ---------------------------------------------------------------------------
// Anchoring
// ---------------------------------------------------------------------------

/// Where a selector's quote was found in a text, and how sure the finding is.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Anchor {
    /// Byte offset where the quote starts.
    pub start: usize,
    /// Byte offset just past the quote's end.
    pub end: usize,
    /// Whether the recorded prefix and suffix both agreed with what surrounds
    /// the quote here. `false` is a quote found in changed surroundings — or
    /// one of several occurrences, with nothing to choose between them.
    pub certain: bool,
}

/// Find a selector's quote in `text` — the Web Annotation `TextQuoteSelector`
/// rule: every occurrence of `exact` is a candidate; the one whose context
/// matches the recorded prefix and suffix wins; failing that, the one
/// matching either; failing that, the first. `None` when the quote is not in
/// the text at all, which is a remark orphaned by an edit.
pub fn anchor(selector: &Selector, text: &str) -> Option<Anchor> {
    if selector.exact.is_empty() {
        return None;
    }
    let mut best: Option<(u8, usize)> = None;
    let mut from = 0;
    while let Some(found) = text[from..].find(&selector.exact) {
        let start = from + found;
        let end = start + selector.exact.len();
        let before = selector
            .prefix
            .as_deref()
            .map(|p| text[..start].ends_with(p));
        let after = selector
            .suffix
            .as_deref()
            .map(|s| text[end..].starts_with(s));
        // Two points for context that was recorded and agrees, none for
        // context that was recorded and disagrees, one for context that was
        // never recorded — so an unrecorded side neither helps nor hurts.
        let score = [before, after]
            .into_iter()
            .map(|side| match side {
                Some(true) => 2,
                Some(false) => 0,
                None => 1,
            })
            .sum::<u8>();
        if best.is_none_or(|(held, _)| score > held) {
            best = Some((score, start));
        }
        // On by one character, not one byte: a quote that opens with an
        // em dash or a curly quote starts on a three-byte character, and a
        // byte into it is not a place a `&str` can be sliced.
        from = start + selector.exact.chars().next().map_or(1, char::len_utf8);
        if from >= text.len() {
            break;
        }
    }
    let (score, start) = best?;
    let occurrences = text.matches(&selector.exact).count();
    Some(Anchor {
        start,
        end: start + selector.exact.len(),
        certain: score == 4 || (occurrences == 1 && score >= 2),
    })
}

// ---------------------------------------------------------------------------
// Applying an edit
// ---------------------------------------------------------------------------

/// An edit, applied to a text: the text as it would read, and where in the
/// old text the quoted passage was found.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Applied {
    /// The text with the replacement in the passage's place.
    pub text: String,
    /// Where the passage was in the text it was applied to, and whether the
    /// finding was certain. An uncertain anchor is a replacement that landed
    /// somewhere the reader may not have meant; what to do with one is the
    /// caller's policy.
    pub anchor: Anchor,
}

/// Apply an `editing` remark to `text`.
///
/// Anchors the selector by [`anchor`]'s rule and splices the replacement in
/// where it landed. `Ok(None)` when the quoted passage is not in the text at
/// all — an orphaned edit, with nothing to apply it to. `Err` when `edit` is
/// not an edit, which is a caller's mistake rather than a fact about the text.
///
/// Pure: the text is a string and the result is a string. Whether the
/// revision being edited is the one the edit was made against, and whether it
/// may be applied without a hand, are decided by whoever holds the store.
pub fn apply(edit: &Annotation, text: &str) -> Result<Option<Applied>> {
    edit.check()?;
    let (Some(selector), Some(replacement)) = (&edit.selector, &edit.replacement) else {
        return Err(Error::Unreadable(format!(
            "cannot apply a remark whose motivation is {} — only an edit proposes a change",
            edit.motivation
        )));
    };
    let Some(found) = anchor(selector, text) else {
        return Ok(None);
    };
    let mut out = String::with_capacity(text.len() + replacement.len());
    out.push_str(&text[..found.start]);
    out.push_str(replacement);
    out.push_str(&text[found.end..]);
    Ok(Some(Applied {
        text: out,
        anchor: found,
    }))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn selector(exact: &str, prefix: Option<&str>, suffix: Option<&str>) -> Selector {
        Selector {
            exact: exact.into(),
            prefix: prefix.map(str::to_string),
            suffix: suffix.map(str::to_string),
        }
    }

    fn meta(pairs: &[(&str, &str)]) -> fig::Value {
        fig::Value::Map(
            pairs
                .iter()
                .map(|(k, v)| {
                    (
                        fig::Value::Str(k.to_string()),
                        fig::Value::Str(v.to_string()),
                    )
                })
                .collect(),
        )
    }

    #[test]
    fn a_quote_is_found_where_its_context_agrees() {
        let text = "the lake froze. the lake thawed. the lake froze again.";
        let sel = selector("the lake", Some("thawed. "), Some(" froze again"));
        let found = anchor(&sel, text).unwrap();
        assert_eq!(&text[found.start..found.end], "the lake");
        assert_eq!(found.start, text.rfind("the lake").unwrap());
        assert!(found.certain);
    }

    #[test]
    fn changed_surroundings_still_find_a_unique_quote_but_say_so() {
        let text = "We had no idea the lake would freeze that year.";
        let sel = selector(
            "the lake would freeze",
            Some("That winter "),
            Some(" and Dad laughed"),
        );
        let found = anchor(&sel, text).unwrap();
        assert_eq!(&text[found.start..found.end], "the lake would freeze");
        assert!(!found.certain, "the context the reader saw is gone");
    }

    #[test]
    fn a_recurring_quote_with_no_context_to_choose_by_is_uncertain() {
        let text = "again and again and again";
        let found = anchor(&selector("again", None, None), text).unwrap();
        assert_eq!(found.start, 0);
        assert!(!found.certain);
        let alone = anchor(&selector("and again and", None, None), text).unwrap();
        assert!(alone.certain, "unique, and no context recorded to disagree");
    }

    #[test]
    fn a_quote_opening_on_a_multibyte_character_is_found() {
        // Stepping past a candidate by one byte lands inside the em dash,
        // and slicing there is a panic rather than a miss.
        let text = "so — apple, then — apple again";
        let found = anchor(&selector("— apple", Some("then "), Some(" again")), text).unwrap();
        assert_eq!(&text[found.start..found.end], "— apple");
        assert_eq!(found.start, "so — apple, then ".len());
        assert!(found.certain);
    }

    #[test]
    fn a_quote_that_is_gone_is_orphaned() {
        assert_eq!(anchor(&selector("gone", None, None), "nothing here"), None);
        assert_eq!(anchor(&selector("", None, None), "nothing here"), None);
    }

    #[test]
    fn a_remark_round_trips_through_its_metadata() {
        let mut note = Annotation::new("doc:1", Motivation::Questioning);
        note.at = Some("3f9c".into());
        note.selector = Some(selector("freeze", Some("would "), None));
        note.color = Some("yellow".into());
        note.body = "Which lake?".into();

        let fields = note.fields();
        assert!(
            !fields.iter().any(|(key, _)| *key == SUFFIX_FIELD),
            "absent halves are absent keys"
        );
        let pairs: Vec<(&str, &str)> = fields.iter().map(|(k, v)| (*k, v.as_str())).collect();
        let back = Reader::new()
            .read(&meta(&pairs), &note.body)
            .unwrap()
            .unwrap();
        assert_eq!(back, note);
    }

    /// Every motivation is read back as the one that was written — the
    /// closed set is closed in both directions.
    #[test]
    fn every_motivation_round_trips_through_a_document() {
        for motivation in Motivation::ALL {
            let mut note = Annotation::new("doc:1", motivation);
            note.at = Some("3f9c".into());
            note.selector = Some(selector("freeze", None, None));
            note.body = "Does it?".into();
            if motivation == Motivation::Editing {
                note.replacement = Some("thaw".into());
            }
            let back = Reader::new()
                .document(&note.render().unwrap())
                .unwrap()
                .unwrap();
            assert_eq!(back.motivation, motivation);
            assert_eq!(Motivation::parse(motivation.as_str()), Some(motivation));
        }
        assert_eq!(Motivation::parse("assessing"), Some(Motivation::Assessing));
    }

    /// The property that decided the serialisation. `prefix` ends in a space
    /// and `suffix` begins with one, and an anchor whose context lost its
    /// edge whitespace stops matching — silently, in the one piece of
    /// machinery whose whole job is surviving an edit.
    #[test]
    fn a_selectors_edge_whitespace_and_newlines_survive_the_document() {
        let text = "That winter we had no idea the lake would freeze and Dad laughed";
        let mut note = Annotation::new("doc:1", Motivation::Commenting);
        note.selector = Some(selector(
            "we had no idea\nthe lake would freeze",
            Some("That winter "),
            Some(" and Dad laughed"),
        ));
        note.body = "Which lake?".into();

        let mut back = Reader::new()
            .document(&note.render().unwrap())
            .unwrap()
            .unwrap();
        let sel = back.selector.as_ref().unwrap();
        assert_eq!(sel.prefix.as_deref(), Some("That winter "));
        assert_eq!(sel.suffix.as_deref(), Some(" and Dad laughed"));
        assert!(sel.exact.contains('\n'));

        // Everything but the blank line `render` writes between the block and
        // the prose, which reading gives back because neither side trims.
        assert_eq!(back.body.trim(), note.body);
        back.body = note.body.clone();
        assert_eq!(back, note);

        // And the anchor those bytes exist for still lands, on the text as
        // the reader saw it with the newline flattened out of it.
        let flat = Selector {
            exact: sel.exact.replace('\n', " "),
            prefix: sel.prefix.clone(),
            suffix: sel.suffix.clone(),
        };
        let found = anchor(&flat, text).unwrap();
        assert!(found.certain, "both sides of the recorded context agree");
        assert_eq!(&text[found.start..found.end], flat.exact);
    }

    #[test]
    fn an_ordinary_document_is_not_a_remark() {
        let plain = meta(&[("title", "Kin")]);
        assert_eq!(Reader::new().read(&plain, "").unwrap(), None);
        assert_eq!(Reader::new().document("just prose\n").unwrap(), None);
    }

    #[test]
    fn a_motivation_left_unsaid_is_read_off_the_body() {
        let bare = meta(&[(TARGET_FIELD, "doc:1")]);
        let read = |body| Reader::new().read(&bare, body).unwrap().unwrap().motivation;
        assert_eq!(read(""), Motivation::Highlighting);
        assert_eq!(read("hm"), Motivation::Commenting);
    }

    #[test]
    fn a_motivation_this_does_not_know_is_refused() {
        let odd = meta(&[(TARGET_FIELD, "doc:1"), (MOTIVATION_FIELD, "vibing")]);
        assert!(matches!(
            Reader::new().read(&odd, "").unwrap_err(),
            Error::Unreadable(_)
        ));
    }

    /// The caller's own idea of a target, and its own account of what was
    /// wrong with one. An empty target is refused even by [`AnyTarget`].
    #[test]
    fn the_caller_says_what_a_target_is() {
        let arks = Reader::with_targets(|target: &str| match target.starts_with("ark:") {
            true => Ok(()),
            false => Err(format!("{target:?} is not an ARK")),
        });
        let good = meta(&[(TARGET_FIELD, "ark:12345/dxk7f2q9wl/bcdfgr")]);
        assert!(arks.read(&good, "").unwrap().is_some());

        let bad = meta(&[(TARGET_FIELD, "notes/kin.md")]);
        let Err(Error::Unreadable(why)) = arks.read(&bad, "") else {
            panic!("a target this reader does not accept is not a remark");
        };
        assert!(why.contains("is not an ARK"), "{why}");

        // And the same document is an ordinary remark to a reader that has
        // no scheme of its own — which is the point of the check travelling
        // with the reader.
        assert!(Reader::new().read(&bad, "").unwrap().is_some());
        assert!(matches!(
            Reader::new()
                .read(&meta(&[(TARGET_FIELD, "  ")]), "")
                .unwrap_err(),
            Error::Unreadable(_)
        ));
    }

    /// A term list and a bare scalar are the same shape to a reader of it,
    /// which is how `audience` and its kind are written in the wild.
    #[test]
    fn a_field_that_is_a_term_or_a_list_of_them_reads_as_a_list() {
        let one = fig::Value::Map(vec![(
            fig::Value::Str("audience".into()),
            fig::Value::Str("grandma".into()),
        )]);
        let many = fig::Value::Map(vec![(
            fig::Value::Str("audience".into()),
            fig::Value::Seq(vec![
                fig::Value::Str("grandma".into()),
                fig::Value::Str("mom".into()),
            ]),
        )]);
        assert_eq!(one.terms("audience"), vec!["grandma"]);
        assert_eq!(many.terms("audience"), vec!["grandma", "mom"]);
        assert!(one.terms("nobody").is_empty());
    }

    // -- editing ----------------------------------------------------------

    fn edit(exact: &str, prefix: &str, suffix: &str, replacement: &str) -> Annotation {
        Annotation::edit(
            "doc:1",
            "3f9c",
            Selector::in_context(exact, prefix, suffix),
            replacement,
        )
    }

    /// The replacement is metadata, quoted, for the reason the selector is:
    /// its edge whitespace and newlines are the proposal, and a body would
    /// have lost them to the blank line `render` writes.
    #[test]
    fn an_edit_round_trips_with_its_replacement_intact() {
        let mut fix = edit(
            "the red bouy",
            "rowed out past ",
            " before",
            "the red buoy ",
        );
        fix.body = "typo".into();
        let back = Reader::new()
            .document(&fix.render().unwrap())
            .unwrap()
            .unwrap();
        assert_eq!(back.motivation, Motivation::Editing);
        assert_eq!(back.replacement.as_deref(), Some("the red buoy "));
        assert_eq!(back.body.trim(), "typo");

        // A deletion is an empty replacement, and empty is not absent.
        let cut = edit("the red bouy ", "rowed out past ", "before", "");
        let fields = cut.fields();
        assert_eq!(
            fields.iter().find(|(k, _)| *k == REPLACEMENT_FIELD),
            Some(&(REPLACEMENT_FIELD, String::new()))
        );
        let back = Reader::new()
            .document(&cut.render().unwrap())
            .unwrap()
            .unwrap();
        assert_eq!(back.replacement.as_deref(), Some(""));
    }

    #[test]
    fn an_edit_applies_where_its_quote_is_found() {
        let text = "We rowed out past the red bouy before dark.";
        let fix = edit("the red bouy", "rowed out past ", " before", "the red buoy");
        let done = apply(&fix, text).unwrap().unwrap();
        assert_eq!(done.text, "We rowed out past the red buoy before dark.");
        assert!(done.anchor.certain);
        assert_eq!(&text[done.anchor.start..done.anchor.end], "the red bouy");

        // Deletion and insertion are the same operation with a different
        // replacement: nothing, or the quote given back with more in it.
        let cut = edit(" before dark", "bouy", ".", "");
        assert_eq!(
            apply(&cut, text).unwrap().unwrap().text,
            "We rowed out past the red bouy."
        );
        let add = edit("before dark", "bouy ", ".", "before dark, laughing");
        assert_eq!(
            apply(&add, text).unwrap().unwrap().text,
            "We rowed out past the red bouy before dark, laughing."
        );
    }

    /// The text moved on since the edit was made. The quote is still there,
    /// so the edit still lands — but the anchor says the surroundings the
    /// reader saw are gone, and that is the caller's cue to ask a person.
    #[test]
    fn an_edit_against_changed_text_lands_but_says_so() {
        let text = "Later we rowed to the red bouy and back.";
        let fix = edit("the red bouy", "rowed out past ", " before", "the red buoy");
        let done = apply(&fix, text).unwrap().unwrap();
        assert_eq!(done.text, "Later we rowed to the red buoy and back.");
        assert!(!done.anchor.certain);
    }

    #[test]
    fn an_edit_whose_quote_is_gone_is_orphaned() {
        let fix = edit("the red bouy", "past ", " before", "the red buoy");
        assert_eq!(apply(&fix, "We stayed ashore.").unwrap(), None);
    }

    #[test]
    fn only_an_edit_can_be_applied() {
        let mut note = Annotation::new("doc:1", Motivation::Commenting);
        note.selector = Some(Selector::quoting("bouy"));
        assert!(matches!(
            apply(&note, "the bouy").unwrap_err(),
            Error::Unreadable(_)
        ));
    }

    /// An edit says one thing about itself, or it is not read. Each of the
    /// three halves a patch needs is checked, and so is the converse.
    #[test]
    fn an_edit_missing_a_half_is_refused_and_so_is_a_comment_with_one() {
        let whole = edit("bouy", "", "", "buoy");
        assert!(whole.check().is_ok());

        let mut no_base = whole.clone();
        no_base.at = None;
        assert!(no_base.check().unwrap_err().to_string().contains("`at`"));

        let mut no_quote = whole.clone();
        no_quote.selector = None;
        assert!(
            no_quote
                .check()
                .unwrap_err()
                .to_string()
                .contains("quotes nothing")
        );
        no_quote.selector = Some(Selector::quoting(""));
        assert!(no_quote.check().is_err());

        let mut no_replacement = whole.clone();
        no_replacement.replacement = None;
        assert!(
            no_replacement
                .check()
                .unwrap_err()
                .to_string()
                .contains("`replacement`")
        );

        let mut comment = whole.clone();
        comment.motivation = Motivation::Commenting;
        assert!(
            comment
                .check()
                .unwrap_err()
                .to_string()
                .contains("commenting")
        );

        // And the reader enforces the same rule on a document it did not
        // write: a comment carrying a replacement is not a remark.
        let odd = meta(&[
            (TARGET_FIELD, "doc:1"),
            (MOTIVATION_FIELD, "commenting"),
            (REPLACEMENT_FIELD, "buoy"),
        ]);
        assert!(matches!(
            Reader::new().read(&odd, "").unwrap_err(),
            Error::Unreadable(_)
        ));
        let half = meta(&[
            (TARGET_FIELD, "doc:1"),
            (MOTIVATION_FIELD, "editing"),
            (EXACT_FIELD, "bouy"),
            (REPLACEMENT_FIELD, "buoy"),
        ]);
        assert!(matches!(
            Reader::new().read(&half, "").unwrap_err(),
            Error::Unreadable(_)
        ));
    }
}
