# The Rust tool's words for a document it refuses: `ParseErrorKind`'s
# `Display`, one def per kind, and `ParseError`'s, which puts the line in
# front. Every parser here refuses in these words, so `check`, `log`,
# `cat` and every other command say of a document that does not parse what
# the Rust tool says.

import Base
import ./text.bend as T

def PREAMBLE() -> String:
  "historica"

def NO_NEWLINE() -> String:
  "\\ no newline"

# `ParseError`: the line in front, where the fault has one.
def at(+line: Nat, +kind: String) -> String:
  "line " ++ Nat.show(line) ++ ": " ++ kind

def empty() -> String:
  "a Historica document is never empty; it opens with `historica`"

def not_utf8() -> String:
  "a Historica document is UTF-8; re-save this file as UTF-8"

def byte_order_mark() -> String:
  "a byte order mark is part of the digest; delete the first three bytes"

def carriage_return() -> String:
  "carriage returns change a revision's identity; save this file with LF endings"

def unterminated() -> String:
  "every line the parser reads ends with a newline; add one"

def missing_preamble() -> String:
  "a Historica document opens with `historica`; add it as the first line"

def pre_release(+found: String) -> Bool:
  Bool.or(Bool.or(Bool.or(String.eq(found, "v0"), String.eq(found, "v1")), Bool.or(String.eq(found, "v2"), String.eq(found, "v3"))), Bool.or(String.eq(found, "v4"), String.eq(found, "v5")))

def unknown_version(+found: String) -> String:
  Bool.pick(String, pre_release(found),
    "this document is `historica-" ++ found ++ "`, a pre-1.0 format this release no longer reads; a 0.x Historica still reads it",
    "this document is `historica-" ++ found ++ "` and this reader reads `historica`; upgrade Historica rather than trusting what it would leave out")

def empty_keep() -> String:
  "a `keep` that keeps nothing states nothing; delete the line"

def adjacent_keeps() -> String:
  "two `keep`s of one document whose ranges meet are one `keep`; join them, so that one byte sequence spells this resolution"

def adjacent_inserts() -> String:
  "two `insert`s that meet are one `insert`; join them, so that one byte sequence spells this resolution"

def insert_with_position(+found: String) -> String:
  "a resolution's `insert` takes no position — the pieces are the file, in order — and `insert " ++ found ++ "` states one; delete the number"

def result_of_forgetting() -> String:
  "a forgetting document states no result: a digest of the destroyed state would confirm a guess at what was destroyed; delete the line"

def forgotten_payload_with_body() -> String:
  "a payload has no items, so the document standing in for a forgotten one is `forgets` and `length` and nothing else; delete the blank line and everything under it"

def malformed_key(+key: String) -> String:
  "`" ++ key ++ "` is not a key: keys are lowercase letters and hyphens, and a dot separates a tool's name from what it named, as in `diaryx.review-url`"

def unknown_header(+key: String) -> String:
  "`" ++ key ++ "` is not a header this format knows; spell it `<tool>." ++ key ++ "` if a reader may ignore it, or upgrade Historica if not"

def unknown_mode(+found: String) -> String:
  "`" ++ found ++ "` is not a mode; a file is `plain` or `executable`, and decision 0034 carries no other bit"

def empty_value() -> String:
  "a header with no value is an absent fact spelled ambiguously; delete the line or give it a value"

def padded_value() -> String:
  "a value has no leading or trailing space; trim it"

def control_character() -> String:
  "a value holds no control characters; remove it"

def keys_out_of_order(+key: String, +after: String) -> String:
  "`" ++ key ++ "` comes before `" ++ after ++ "` in the fixed key order; move the line up"

def repeated_key_out_of_order(+key: String) -> String:
  "repeated `" ++ key ++ "` lines are sorted; move this one above the line before it"

def duplicate_fact(+key: String) -> String:
  "this `" ++ key ++ "` line states a fact already stated; delete it"

def repeated_header(+key: String) -> String:
  "`" ++ key ++ "` appears once in a revision; delete the second line"

def missing_header(+key: String) -> String:
  Bool.pick(String, String.eq(key, "result"),
    "a content document states the digest of the file it produces; add the `result` line — `shasum -a 256` on that file prints it",
    "a revision states `" ++ key ++ "`; add the line")

def malformed_change_id(+found: String) -> String:
  "`" ++ found ++ "` is not a change ID: 24 characters of `k` to `z`, an alphabet no digest can be mistaken for; copy the change ID this work already has, or mint a new one"

def malformed_digest(+key: String, +found: String) -> String:
  Bool.pick(String, Bool.or(String.eq(key, "text"), String.eq(key, "bytes")),
    "`" ++ key ++ "` names content by digest, and `" ++ found ++ "` is not 64 lowercase hexadecimal characters; `shasum -a 256` on the file you mean prints the right one",
    "`" ++ key ++ "` names a revision by digest, and `" ++ found ++ "` is not 64 lowercase hexadecimal characters; `shasum -a 256` on the revision you mean prints the right one")

def malformed_timestamp(+found: String, +because: String) -> String:
  "`" ++ found ++ "` is not a timestamp (" ++ because ++ "); write `YYYY-MM-DDThh:mm:ss±hh:mm`"

def rewrite_without_supersedes(+key: String) -> String:
  "`" ++ key ++ "` describes a rewrite, and this revision supersedes nothing; delete the line"

def redundant_revised_by() -> String:
  "`revised-by` repeats the author, which is a second spelling of one fact; delete the line"

def empty_body_after_separator() -> String:
  "an empty message is spelled with no blank line at all; delete the blank line"

def text_without_add(+file: String) -> String:
  "`text` states the lines a file is created with, and this revision does not add the file " ++ file ++ "; write `edit` against the file as it stands, or `add` it here"

def malformed_file_entry(+key: String) -> String:
  Bool.pick(String, String.eq(key, "edit"),
    "`edit` names a file and the digest of its operation document; write both, separated by one space",
    Bool.pick(String, Bool.or(String.eq(key, "text"), String.eq(key, "bytes")),
      "`" ++ key ++ "` names a file and the digest of its content; write both, separated by one space",
      "`" ++ key ++ "` names a file and a path; write both, separated by one space"))

def malformed_file_id(+found: String) -> String:
  "`" ++ found ++ "` is not a file ID: 24 characters of `k` to `z`, the same alphabet a change ID uses and no digest can be mistaken for; copy the ID this file already has, or mint a new one"

def malformed_path(+found: String, +because: String) -> String:
  "`" ++ found ++ "` is not a path (" ++ because ++ "); write components separated by `/`, relative to the repository root"

def file_stated_twice(+key: String, +file: String) -> String:
  "two `" ++ key ++ "` lines name the file " ++ file ++ ", which states one fact twice; delete one of them"

def contradictory(+first: String, +second: String, +file: String) -> String:
  "the file " ++ file ++ " is named by both `" ++ first ++ "` and `" ++ second ++ "` in one revision, and they cannot both hold; keep the one that says what happened"

def missing_separator() -> String:
  "an operation document is a preamble, a blank line, and operations; add the blank line"

def no_operations() -> String:
  "a revision that changes nothing about a file names no operation document; write what this one did, or delete the file and the line that names it"

def unknown_operation(+found: String) -> String:
  "`" ++ found ++ "` is not an operation; write `delete P N`, `insert P`, `-item`, `+item`, or `\\ no newline`"

def malformed_delete() -> String:
  "`delete` takes a position and a count, as in `delete 3 1`; write both, separated by one space"

def malformed_insert() -> String:
  "`insert` takes one position, as in `insert 4`; the items follow on their own lines"

def malformed_number(+found: String) -> String:
  "`" ++ found ++ "` is not a position: decimal digits, no sign, and no leading zero, counted from zero into the parent; write it plainly"

def empty_delete() -> String:
  "a `delete` removes at least one item, and one that removes none is an absent fact spelled out loud; delete the line"

def empty_insert() -> String:
  "an `insert` adds at least one item; add a `+` line, or delete the `insert`"

def delete_count_disagrees(+stated: Nat, +found: Nat) -> String:
  "this `delete` states " ++ Nat.show(stated) ++ " items and " ++ Nat.show(found) ++ " follow it; the `-` lines are what a reader checks the count against, so make them agree"

def content_without_operation(+prefix: Char) -> String:
  "a `" ++ String.from_list([prefix]) ++ "` line is content and belongs to the operation above it, and there is none; add the `delete` or `insert` line"

def operations_out_of_order(+position: Nat, +after: Nat) -> String:
  "operations are written in ascending position order, and " ++ Nat.show(position) ++ " follows " ++ Nat.show(after) ++ "; move this operation up"

def overlapping(+position: Nat) -> String:
  "operations describe separate regions of the parent, and this one starts at " ++ Nat.show(position) ++ ", inside the region above it; merge the two, or move this one past the end of that region"

def adjacent_deletes(+at: Nat, +total: Nat) -> String:
  "these two `delete` lines remove one unbroken run, which is one fact; write them as `delete " ++ Nat.show(at) ++ " " ++ Nat.show(total) ++ "`"

def delete_after_insert(+position: Nat) -> String:
  "at position " ++ Nat.show(position) ++ " a `delete` is written before an `insert`, the way every diff spells a replacement; move the `delete` and its `-` lines up"

def inserts_at_one_position(+position: Nat) -> String:
  "two `insert` lines at position " ++ Nat.show(position) ++ " are one insert; merge their `+` lines into the first"

def carriage_return_in_operation() -> String:
  "a carriage return in the format's own line changes this document's identity; delete it — a `-` or `+` line may hold one, because that is content"

def no_newline_without_item() -> String:
  "`\\ no newline` describes the line above it, and there is none; delete it"

def no_newline_not_last(+prefix: Char) -> String:
  "`\\ no newline` marks a file's last line, and `" ++ String.from_list([prefix]) ++ "` lines come after this one; move it under the last of them, or delete it"

# `number`: decimal digits, no sign, no leading zero.
def number(+s: String) -> Maybe<&2, Nat>:
  T.number(s)

# The first line's checks, which every document shares: a byte order mark,
# then the preamble, then its newline.
def bom(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      Char.is_eq(c, '\u{FEFF}')

def preamble.found(+line: String, prefixed: Maybe<&2, String>) -> String:
  match prefixed:
    case None{}:
      missing_preamble()
    case Some{+v}:
      unknown_version(v)

# `check_preamble`, as a refusal or none.
def preamble(+line: String, terminated: Bool) -> Maybe<&2, String>:
  Bool.pick(Maybe<&2, String>, T.same(line, "historica"),
    Bool.pick(Maybe<&2, String>, terminated, None{}, Some{at(1n, unterminated())}),
    Some{at(1n, preamble.found(line, T.strip_prefix(line, "historica-")))})
