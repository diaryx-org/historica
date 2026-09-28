# 0079 — A reader looks where `forget` files

[0003](0003-store.md) and [0014](0014-forgetting.md) let a store be synced by
anything that copies files, and 0014 says a redaction survives it:

> a redaction that could be undone by transport is not one

A sync that copies and deletes nothing brings a forgetting document in beside
the original it forgets. [0049](0049-what-a-lookup-does-not-prove.md) let a
reader take the catalogue its cache holds as it stands, with this reasoning:

> **Holding the bytes is the answer to whether they were redacted.** 0014
> destroys the original when a forgetting document is complied with —
> `forget` deletes it, `receive` complies before it writes.

A sync is where that reasoning fails. The sync complies with nothing, so the
original stays and the stand-in arrives beside it. 0049 names the state that
leaves, `Resurrected`, and hands it to `check`. It does not say what readers
show in the meantime. They showed the original. A reader in a store nobody
writes to, or one whose new documents are all found where their revision
files them ([0041](0041-where-a-revision-is-filed.md)), never walks
`operations/` and never read the stand-in. `cat` printed the forgotten line
until an `offer`, a digest the catalogue could not place, or a deleted cache
made the store read the directory.

For a payload, a walk did not help either. [0066](0066-forgetting-a-payload.md)'s
stand-in was consulted only when the bytes were missing, so bytes a sync
brought back were printed, laid in the folder by `update` and exported,
whatever the catalogue knew.

## Where the stand-ins are

`forget` files an operation document's stand-in and a resolution's at the
top of `operations/`, under their own digest. It files a payload's stand-in
beside the destroyed payload, under the payload's name with `.ops.txt` after
it, and at the top under its digest if that name is taken. `receive` and
`fetch` file what they bring by digest, at the top. A sync copies paths, so on
the receiving side each lands where the writer put it.

## The decision

- **A reader lists the top of `operations/` before it believes a held
  catalogue.** It lists names, not contents, and only that one directory, not
  the walk. A document there whose name is a digest is looked up in the
  catalogue by that digest. If the catalogue places it at that path, nothing
  is read. If not, the file is read, hashed and parsed, as the pass reads any
  path it cannot account for. If it forgets something, the states the cache
  kept are cleared, and the catalogue is written back naming it, in the
  pass's order, so the next reader does not read it again.

- **A payload read looks beside the payload.** Once the bytes are found and
  hashed, the store checks whether anything it already knows of forgets them,
  and then looks at the payload's path with `.ops.txt` after it. A file there
  is read, hashed and parsed before it is believed, as 0036 requires of any
  claim that a document forgets something.

- **A payload's stand-in beats the payload, as an operation document's does.**
  0014's union rule already makes a held redaction win over a held original
  for lines. For a payload the stand-in forgets everything, so a payload that
  something here forgets is one this store does not hand over.
  `Store::payload_file` and `Store::payload` answer `None` for it, and every
  reader then tells a person what became of it, as 0066 has them tell a
  person about bytes that are gone.

- **A miss proves nothing.** Nothing at the top that the catalogue does not
  place, or nothing beside a payload, means the store's writers put nothing
  there. It does not mean nothing forgets the bytes, and no reader treats it
  as an absence, so none walks the directory over it. Holding the bytes is
  still 0049's answer to every question these looks do not ask.

## Why this is not 0036's shortcut

0036 refused the name-to-digest shortcut:

> The obvious cheap trick is to notice that a digest-named store can find a
> digest by its filename. 0019 makes the default store readably-named, so the
> trick does not apply to the stores people actually have — and it would make
> `arrange` a performance cliff.

Neither reason applies here. These looks do not find a digest by its name.
They look at the paths where the store's own writers file a stand-in, and
those are the same in every layout, readably-named or not. A digest a name
spells is only what the catalogue is asked about. A file is believed for what
its bytes hash to. And if `arrange` moves a stand-in, a look finds nothing
there, which costs nothing and leaves the reader where it was before this
decision. That is a window, not a cliff.

Nothing a look finds is believed further than 0036 believes a pass. A file at
the top that is not what its name says is read for what it is. A file beside
a payload that does not parse, or forgets something else, is not a stand-in.

## What this does not change

- **A stand-in filed anywhere else keeps the window.** A stand-in moved by
  hand, or filed by `arrange` under a revision's folder, and then synced
  beside an original, is still read only by a pass. `check` still reports the
  original as `Resurrected`, and its note now says readers apply what
  `forget` filed.
- **A name that is not a digest is not looked at**, at the top or anywhere
  else. The top of a default store holds month directories and the documents
  filed by digest. A store whose writer filed everything by a readable name at
  the top reads none of it here.
- **`check` is unchanged.** It reads every file and takes no cached answer.
- **The resurrected bytes stay.** A reader does not destroy them: a reader
  writes nothing to the store. `forget` run again, or a `receive`, destroys
  them, as 0014 says.

## Consequences

- `Store::catalogue` reads the top of `operations/` wherever it takes a
  catalogue from the cache. That is one `entries` call a command, on the first
  question about content. 0077 counted the walk as one per revision
  directory. On `cargo xtask bench`'s store (30 files, 121 revisions), a
  cached `cat` went from 7.9 to 8.4 ms and `status` from 9.9 to 10.4 ms,
  which is within run-to-run noise (`log`, which never reaches the look,
  moved by as much).
- A payload read looks for one path beside the payload. That is one `look`,
  paid on every payload read, and a read and a parse only where something is
  there.
- `Store::payload_file`, `Store::payload`, `Store::payload_in_pieces` and
  `Store::copy_payload_to` answer as though the bytes were absent where a held
  stand-in forgets them. `cat` reports the payload forgotten, `update` refuses
  to lay it in the folder, and `export` leaves it out of a copy. Before, each
  used the bytes. `Store::payloads`, which says what the directory holds, is
  unchanged: `receive` and `forget` need it to find what to destroy.
- 0049's rule about held originals is amended to name the sync case and this
  decision.
