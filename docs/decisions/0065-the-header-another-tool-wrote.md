# 0065 — The header another tool wrote

0002 gave the format an escape hatch and 0004 defended it:

> An unknown header whose key begins with `x-` is advisory and may be ignored.
> An unknown header without that prefix is a hard error.

The defence was against RFC 6648, which deprecated `X-` because experimental
names become load-bearing and then cannot be migrated. 0004 answered that a
format whose reader's vocabulary only grows can never retire a spelling of
anything, `x-` or not, so the prefix costs nothing immutability was not
already charging. That answer still holds, and it answers a question nobody
asks first.

The question asked first is what the `x` is. A person reading
`x-diaryx-review-url` in a revision cannot tell from the line what the prefix
does, and the format gives them no way to guess: `x-` is the one abbreviation
in a grammar that spells out `supersedes`, `revised-by`, `historica`, and
`executable`. Everywhere else, reading the file is how you learn what it says.

Replacing the prefix with a word does not fix it, because every available word
attaches to the wrong thing. `advisory-review-url` reads as an advisory review
URL — the adjective lands on the fact, not on the header's standing — and
`note-`, `extra-`, and `optional-` all fail the same way. The mark is not a
qualifier on what was named. It is a statement about whose vocabulary the key
is drawn from, and a word in front of a key cannot say that.

## What is actually load-bearing

Not the prefix. The two tiers.

A reader that meets a key it does not know has exactly two things it can do,
and the file has to say which is right. Ignoring what it does not understand
means rendering a signed revision as unsigned, which 0002 called being
confidently wrong. Refusing everything it does not understand means no tool
can annotate anything, ever.

0047 made that division carry more weight than it did when 0004 wrote it down.
The numbered preamble is gone, so there is no version to gate a grammar change
on: "an unknown header is already refused by 0004's strictness, so a document
using a header this reader lacks fails closed, named, at the line that uses
it." The refusal is the whole forward-compatibility mechanism now. Whatever
marks the ignorable half has to keep being unmistakable; it does not have to
be a prefix.

## The decision

- **A key with a dot in it is some other tool's, and a key without one is this
  format's.** `diaryx.review-url` is a header historica ignores and hashes;
  `review-url` is a header historica does not define and refuses by name. The
  dot is the mark, in the place the prefix was, saying the one thing the
  prefix could not say by being read.

- **No key this format defines will ever hold a dot.** That is the promise the
  rule rests on, and it is cheap to keep: every key in the grammar today is
  letters and hyphens, and the split is by character class rather than by a
  reserved name, so neither half can grow into the other by accident.

- **A key is lowercase letters, hyphens, and dots, and a dot separates
  something on both sides.** `.a`, `a.`, and `a..b` name no tool and are not
  keys. This makes the tool boundary the parser's business, which 0004 could
  only recommend: `x-<tool>-<fact>` was convention because a hyphen cannot
  say where the tool's name ends, and `<tool>.<fact>` is checked because a dot
  can.

- **What historica does with such a header is unchanged.** It parses, it
  hashes like every other byte, it sorts last and against its own kind by
  whole key, it survives an amendment (0023) because a writer that cannot read
  a header must not drop it, and it is never interpreted. A reader that does
  not understand one renders without it and is not wrong to.

- **Graduation is unchanged.** When an advisory fact becomes standard it gets
  a dotless key, writers stop emitting the dotted one, and readers accept the
  dotted one for as long as the format exists.

- **`x-` is not reserved, and nothing is grandfathered.** `x-review-url` is
  now an unknown dotless header, refused at its line with the fix in the
  message. Nothing has been published under any spelling of this format
  (0047), so this costs a re-record in this repository's own fixtures and
  nothing anywhere else. After a first release it would cost two names for one
  fact, which is the RFC 6648 failure arriving by the door 0004 shut.

## Rejected alternatives

**Keeping `x-`.** The status quo, and the objection to it is not the one 0004
answered. Permanence is priced in; legibility is not, and a mark that must be
looked up is a mark that will be guessed at instead.

**A word — `advisory-`, `note-`, `ext-`.** Above: the word binds to the fact
rather than to the header, so `advisory-review-url` asks the reader what an
advisory review URL is. A mark that reads as part of the name is worse than
one that reads as punctuation.

**A registry in the store of the keys this store recognises.** Attractive
because it answers the newcomer's question with a list, and wrong here for
four reasons. A `.rev` file travels alone — by `cp -r` (0029), in an
assembled copy (0042), out of a stranger's URL (0048) — so parseability would
become a property of where the file is rather than of what it says, and the
same bytes would be a revision in one store and not in another. The file
would be mutable shared state that two replicas can disagree about, wanting
the merge policy `names/` still does not have (0053). `check` would need an
opinion about it. And a tool could grant itself recognition by writing to it.
0053 refused the same manifest for directories, where the file at least does
not travel.

**A registry in historica, with unregistered keys ignorable.** The fatal
version, because it looks like it works. A registry is a property of a reader
at a version, and the reader this rule exists for is the old one — the one
that meets a header historica gained after it shipped. That key is absent
from its registry by construction, so "not in the registry" would mean
"ignore a future `signed-by`". This is ignoring what you do not understand,
with a table in front of it. What a registry can honestly be is what
`format.txt` already is: the list of keys this format defines, which answers
what historica knows and says nothing about what it does not.

**A colon, or another separator.** A colon invites reading `diaryx:` as a key
and the rest as its value, which is exactly the misreading to avoid in a
format whose key and value are separated by a space. The dot is the idiom a
reader already has for a name qualified by whose it is.

**Validating the tool's name against a list of known tools.** The registry
again, one level down, with the same defect: the list is a property of the
reader, and the tool that matters is the one written after it shipped.

## Consequences

- The key alphabet gains `.`, and `MalformedKey` now also covers a dot with
  nothing on one side of it. `UnknownHeader`'s message names the new fix,
  `<tool>.<key>`.
- `RevisionDocument::extensions` keeps its type and changes what can appear
  in it, so the implementing commit carries a `Behavioural-change:` trailer: a
  document holding `x-review-url` parsed before and is refused now, and one
  holding `diaryx.review-url` is refused before and parses now.
- `format.txt` states the rule where the header table ends, in the terms a
  person reading a file will meet it: the dot is what says the header is
  somebody else's.
- The corpus is re-spelled — `05-amended` carries `diaryx.review-url`, and
  the invalid fixture is an unknown header with no dot in it — so their
  digests and `06-rebased`'s parent line move with them.
- `check` gains nothing. Which vocabulary a key is drawn from is a question
  the parser answers, and a store that parses has already answered it.

## Deferred

**A tool's own header in an operation or resolution document.** Only revision
documents have the rank, because only they have ever been asked for one. The
rule established here is what such a request would be answered with, and the
question it would have to settle first is what a header means on a document
whose whole content is a replayable operation.

**Attribution built on the dot.** The tool's name is now machine-visible, so
`log` or `show` could group or name the tool that wrote a header rather than
printing the key whole. Nobody has asked, 0037 is suspicious of a second
answer to a question one document already answers, and the fields decided in
0064 do not include headers at all.
