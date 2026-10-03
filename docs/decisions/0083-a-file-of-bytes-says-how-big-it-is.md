# 0083 — A file of bytes says how big it is

[0017](0017-content-that-arrives-whole.md) spelled a file of bytes as
`bytes <file> <digest>`, and [0067](0067-content-that-arrives-whole-is-named-not-carried.md)
made that line the whole of what a revision says about one: the payload is
named, never carried. Everything the format knows about a photograph is its
digest, and everything else is asked of the bytes.

That was enough while every store held every payload it named. The proposal
*Bytes held elsewhere* ended that: a copy fetched with `--no-bytes`, or one
that has evicted since, holds the history of a photograph without the
photograph, and the history is all it has to answer from. It can say which
payload a file holds, and it can say whether it changed. It cannot say how
big it is, and that is the question such a copy is asked next — by a person
deciding whether to fetch it now, by a progress bar fetching a hundred of
them, by a tool comparing its own record of a file against the one a server
publishes. `diff` already prints a length for a file of bytes, by asking the
store's copy of the payload, and prints nothing for one held elsewhere.

The proposal said a size would need a new grammar, and that choosing what to
leave behind by size was a caller's policy. Both are still true. This decides
the grammar and none of the policy.

## The decision

- **A `bytes` line may state its payload's size, as a third word.**
  `bytes <file> <digest> <size>`: the number of bytes the payload holds, in
  decimal, with no sign, no separator and no leading zero — the one spelling
  a writer produces, so that `write(parse(bytes)) == bytes` holds for the
  line as it holds for every other. `wc -c` checks it, as `shasum -a 256`
  checks the digest beside it.

- **`record` always states it.** The size is counted in the same pass that
  takes the digest — the sniff of a file being added, the re-read of one that
  changed — so the two numbers describe the same bytes. A stat taken beside
  the read could describe a file written between the two. A file being added
  under a stated `bytes` kind is read rather than taken from the working
  catalogue's digest for the same reason: a digest without its size is half of
  what the line is about to say, and a file nobody has recorded is almost
  never catalogued anyway.

- **A line without one is still a line.** Every `bytes` line written before
  this decision is two words long, and reads, writes back and builds a tree
  exactly as before. The tree's entry says it does not know the size — and so
  does an entry whose payload is contested, since 0008 picks no payload there
  to have a size. Nothing guesses one.

- **The tree carries it.** `tree::Entry::size` is the size the line stating
  the entry's payload stated, replaced by the next `bytes` line for the file,
  including with nothing when that line states none.

- **A squash restates it, and an amendment keeps it.** A squash states a
  file's payload from the tip's tree (0082), and states the size the tip's
  tree has — none, where the line that brought the payload had none. A
  reword and a carry restate their predecessor's lines, sizes included.

- **`check` holds a size to the bytes.** Where the store holds a payload a
  `bytes` line names, it has just read and hashed it, and a stated size that
  is not its length is an error, `SizeLies`, as a filename that lies about its
  digest is. Where the store does not hold it there is nothing to count, and
  the line is what the copy goes on.

## Who can still read

0047 retired the version number, and with it any way for a revision to say
*a newer Historica wrote this*: an unknown spelling is refused at the line
that uses it, and that refusal is the whole of the mechanism. A reader
released before this decision meets `bytes <file> <digest> <size>`, reads the
last two words as a digest, and refuses the document as `MalformedDigest` on
that line. It fails closed, which is what 0047 promised, but a store recorded
by this release cannot be read by the last one — and a replica syncing
revisions between devices stops at the first one recorded on an upgraded
device until every device is upgraded.

That is the price, and it is paid now because the alternatives cost more:

- **A dotted header** (0065) would be ignored by the old reader and need no
  upgrade, but a key with a dot in it is some other tool's, and no key this
  format defines may hold one. The size is this format's own fact about its
  own line.
- **A line of its own**, `size <file> <n>`, is refused by an old reader too,
  as a header it does not define, so it buys no compatibility. It does cost a
  second line that can disagree with the first: a size for a file the
  revision states no payload for.
- **Asking whoever holds the bytes** — a server's listing, a peer — works
  only where there is someone to ask, and is a different answer for every
  transport.

## What this does not change

- **What a store leaves behind.** `fetch --no-bytes` still leaves every file
  of bytes and nothing else. A size makes a policy by size possible for a
  caller; this decision does not adopt one.
- **`forget`'s refusal of bytes it does not hold.** The forgetting document's
  `length` is measured from the bytes being destroyed (0066), and a stated
  size is a claim about them rather than the bytes. Whether a stand-in may
  take its length from a line is a separate decision.
- **The offer and page grammars.** A listing still names payloads by digest
  alone. A fetcher wanting sizes reads the revisions it fetched.
