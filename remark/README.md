# historica-remark

Reader's remarks on a [Historica](https://github.com/diaryx-org/historica)
chain, and the layer that carries them back.

```toml
[dependencies]
historica-remark = "0.1"
```

Two halves, and you may want either alone.

**The remark** is the [W3C Web Annotation Data
Model](https://www.w3.org/TR/annotation-model/), flattened into a metadata
block: a target, a selector quoting the passage with a little of its context,
a motivation, a body, and the revision the reader was looking at. `anchor`
finds the quoted passage again in text that has since changed, and says how
sure it is. One motivation, `editing`, is a patch rather than a note — the
quoted passage and what should stand in its place — and `apply` is the pure
half of taking one; whether it lands without a hand is the store's policy.
Another, `offering`, is a forge's pull request: it names a fork's `offer.txt`
and the revision in it offered, and its body is the description. It is an
extension of the model, a narrower kind of `editing`.

A `replying` remark may also close or reopen the thread it answers, and add or
remove labels. `thread::fold` turns a thread into its state, given whose
replies count: the owner or the root's writer sets the status, the latest such
reply winning, and only the owner labels. It needs nothing but the remarks.

**The layer** is the transport. A layer is a companion chain — somebody else's
single-writer history, fetched into a directory beside your own, kept current
by fetching again, and carried onward when your own history leaves.

## The loop

```
  author ──── publishes ────▶ reader
                                │ remarks, in a chain of their own
  author ◀─── publishes ────────┘
    │ keeps that chain as a layer, and carries it
    └──────── publishes ────▶ every other reader
```

Nothing about the mechanism knows which direction it is running in. The reader
who remarks on the author's letters does exactly what the author did — writes,
snapshots, publishes — and the author receives it the same way the reader
received the letters. "Comment access" is not a permission anywhere in this;
it is the machinery run the other way.

And a remark reaching a third reader is still its author's. It travels as
their own chain, digest-verified end to end, with their own signed claims
carried alongside — so the store in the middle is a courier rather than a
witness. That is the property the whole shape is for, and it is why a layer is
a chain and not a pile of copied documents.

## Reading

```rust
use historica_remark::{Reader, layer::Layers};

let layers = Layers::at("vault/history/remarks");
let reader = Reader::new();

for name in layers.names()? {
    let layer = layers.layer(&name)?;
    let who = layers.sender(&name);
    for remark in layer.remarks(&reader, &who, None)? {
        println!("{who} on {}: {}", remark.annotation.target, remark.annotation.body);
    }
}
# Ok::<(), historica_remark::Error>(())
```

## Writing

A remark is content, and content is the caller's. This crate does not record,
snapshot or publish — Historica does that, and a caller that keeps documents
already has its own way of writing one. So the writing side here is
`Annotation::fields`, which hands back the metadata in order for a caller to
write with its own document machinery, and `Annotation::render` for a caller
that has none:

```yaml
---
target: ark:12345/dxk7f2q9wl/bcdfgr   # the annotated document, durably
at: 3f9ce1                            # the revision the reader saw
exact: "we had no idea the lake would freeze"
prefix: "That winter "
suffix: " and Dad laughed"
motivation: questioning
---

Which lake?
```

A highlight is a remark with no body. An offer, and a reply that closes a
thread, look like this:

```yaml
---
target: 7c1e                          # the project: its root revision
motivation: offering
fork: https://hub.example/ada/historica/offer.txt
tip: 9b04                             # the revision offered
---

Freeze the lake earlier.
```

```yaml
---
target: ada/remarks/lake-question     # the remark it answers
motivation: replying
thread: closed
label: [answered, docs]
unlabel: [triage]
---

Fixed by Ada's offer.
```

A reply's labels are lists, so a caller writing with its own machinery takes
them from `Annotation::lists` beside `fields`.

### Why the fields are quoted, and why the format is fig's

`exact`, `prefix` and `suffix` are verbatim slices of somebody else's prose.
Their edge whitespace is the point — the prefix above ends in a space, the
suffix begins with one — and a format that trimmed them would produce an
anchor that silently stops matching, in the one piece of machinery whose whole
job is surviving an edit. They may also contain newlines. So the carrying
format has to quote, and [fig](https://github.com/diaryx-org/fig)'s quoted
scalars are that rule already written and already tested.

Which format your documents use is not this crate's to decide: it reads
whichever of YAML, JSON or TOML frontmatter it finds. And a caller that has
already parsed its own documents never reaches that code at all — it
implements the `Fields` trait over its own value tree, which is one method,
and hands the crate what it already knows.

### Why the target is opaque

A remark's target is by design in *another* store than the one the remark
lives in — the author's, of which the reader holds a fetched copy and never
the original. What identity means across that gap is yours, not this crate's:
a Diaryx vault names documents by ARK, a static site by URL, a corpus by DOI.
So a target is a string, and what counts as one is a `TargetCheck` you hand to
a `Reader`, which also says what was wrong with one it refuses.

## What travels

Nothing this crate arranges. Historica carries a reserved directory by its
class (its decision 0053), and its registry says `claims/` travels and
`trust/` does not — so the signed claims that vouch for a chain
([historica-minisign](../minisign)) are
in the offer as `reserved` entries, named by the digest of their bytes like
everything else, and a fetch verifies them like everything else.

That is worth stating because the obvious alternative is wrong. A tool could
carry claims *beside* the offer, in an index of its own. It would work, and
every byte of it would arrive unverified — the offer is what names a file by
its digest, so a file the offer does not list is a file nothing checks.

And `trust/` staying home is not an omission. A claim arriving says *here is a
fact*, which commits the receiving copy to nothing; an opinion about a key
arriving would say *believe more*, and a copy seeded with a stranger's key
verifies the stranger's history. Believing a key is a person on that machine
deciding, and nothing else.

## Suppression

The keeper's one editorial power, and deliberately small: a suppressed path is
left out of what you show, and it lifts again as easily as it was laid on.
Nothing was destroyed, so nothing has to be fetched back.

It does not reach into the chain. The keeper is not the writer and cannot
redact a chain they do not own; the writer's own forgetting is the only thing
that destroys — and that arrives here on the next fetch, as the destruction of
what it forgot, without anybody on this side being asked.

## Features

`default-features = false` leaves the annotation model and `fig`: no
historica, no store, no filesystem. What a renderer, a viewer or an importer
takes.

- `layer` *(default)* — the transport. Everything that touches a store.

## Development

This crate lives in the [historica](https://github.com/diaryx-org/historica)
repository, under `remark/`, as a member of its Cargo workspace; it moved there
from its own repository with its history. It depends on historica, and on
historica-minisign for one test, by path and by version.

CI is historica's: `ship ci` at the repository root runs every job in order,
and the workflow runs nothing else; `ship ci --list` lists them, from its
`.config/ship.figl`. The `remark-model-only` job is the build with no default
features. See [ship](https://github.com/diaryx-org/ship).

## License

MIT or Apache-2.0, at your option.
