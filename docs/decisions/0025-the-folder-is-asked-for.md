# 0025 — The folder is asked for

0003 makes the store a directory, and everything since has agreed with it.
0016 arranges that directory so a person can read it. 0018 files a path as a
path, with real directories for real components. 0011 puts the working copy
next to it. Every one of those is a decision about *a folder*, and every one of
them is right.

None of them is a decision about `std::fs`.

The library had been reaching for `std::fs` anyway, in six modules, because it
was the folder that was to hand. This document separates the two: the format's
claim on a folder, which stands, from the assumption that the folder is the one
the operating system is offering this process, which was never argued for.

## The decision

- **The library reaches the folder through `historica::fs::Filesystem`**, an
  object-safe trait of eight methods.
- **`Store<F = Disk>` and `Working<F = Disk>` carry it as a type parameter.**
  The bound lives on the `impl` blocks, never on the struct.
- **`historica::fs::Disk` is that trait over `std::fs`**, and is what the
  `disk` feature adds. The feature is on by default.
- **The short constructors stay, and are `Disk`.** `Store::open(root)`,
  `Store::init`, `Store::check`, `Store::discover`, `Working::read` and
  `record::author_for` live on `impl Store<Disk>` under
  `#[cfg(feature = "disk")]`.
- **The CLI is `std::fs` throughout**, deliberately. `src/cli/` and
  `src/main.rs` call it directly and the binary declares
  `required-features = ["disk"]`. A command-line program is the one caller that
  always knows it is talking to a real filesystem.
- **A path is still `std::path::Path`, and an error is still
  `std::io::Error`.** Two error kinds carry meaning: `NotFound` and
  `AlreadyExists`.

## Why a type parameter, and not a trait object

This was written the other way first — `Arc<dyn Filesystem>`, one line in each
struct, no generics anywhere — and the reason that is wrong is not performance.
A virtual call is nothing against a read and a SHA-256.

It is that **a boxed trait object has to demand capabilities of every
implementation in order to have them itself.** `Store` derives `Debug` and is
`Send`. For `Store` holding an `Arc<dyn Filesystem>` to keep either, the trait
must require `Debug + Send + Sync` of everyone who implements it, forever,
whether the store they make ever crosses a thread or not.

Now look at who this abstraction exists for. A host holding its documents
through a document provider — a Swift object behind an FFI pointer, a `JsValue`
on a single-threaded `wasm32-unknown-unknown` target. **Neither of those is
`Send`.** Under the boxed version they cannot implement the trait at all
without writing `unsafe impl Send + Sync` on a wrapper — which is sound on a
single-threaded target and is still unsafe code this crate would be requiring
of a host in order to let it in, from a library that is `#![forbid(unsafe_code)]`
about its own.

A type parameter makes the derived implementations conditional instead. The
trait requires nothing:

```rust
pub trait Filesystem { /* eight methods */ }

#[derive(Debug, Clone)]
pub struct Store<F = Disk> { files: F, /* … */ }
```

`Store<Disk>` is `Debug`, `Clone` and `Send`, exactly as before.
`Store<SomethingAwkward>` is whatever that thing is. Nobody is asked to promise
anything about a handle they did not choose the shape of.
`tests/filesystem.rs` drives a store over a filesystem that is none of the
three, holding an `Rc` and a `Cell`, and the test beside it asserts that the
disk store still has all of them.

### Dynamic dispatch is still available

It is a choice rather than the architecture. A smart pointer to a filesystem is
a filesystem — `&T`, `Box<T>`, `Rc<T>` and `Arc<T>` all forward — so
`Store<Arc<dyn Filesystem>>` is the store that decided at run time, spelled in
the type by the one caller who wanted it. The in-memory test uses
`Store<Arc<Memory>>` for exactly this reason.

### It costs less at the call sites than it looks

Three mechanisms carry it, and between them the diff outside the library's own
type declarations is nearly empty:

- **The default type parameter applies in argument position.** Every CLI
  signature that says `&Store` still means `&Store<Disk>`. None of them
  changed.
- **`Store::open(root)` still infers**, because `open` lives on
  `impl Store<Disk>` and is the only `open` there is. This is the mechanism
  `HashMap::new` uses.
- **The internal helpers take `F: Filesystem + ?Sized`**, so `walk`,
  `write_once` and `check` accept a `&Disk` and a `&dyn Filesystem` alike.

Of 289 tests, exactly one file needed editing when the parameter was
introduced, and only to name `Store<Arc<Memory>>` in two helper signatures.

### What it costs

**Monomorphisation.** `check` and the store's read path are compiled once per
filesystem. In practice that is one or two.

**`impl<F: Filesystem> Store<F>` on five impl blocks**, which is more to read
than `impl Store`. This is a real cost in a codebase that weights readable
source heavily, and it is the one argument the trait object wins on.

**`Disk` names a type even when it cannot be one.** The default parameter has
to resolve without the feature, so `pub struct Disk;` is unconditional and
`impl Filesystem for Disk` is what `disk` adds. A `--no-default-features` build
that says `Store` rather than `Store<MyFilesystem>` is told
``Disk doesn't satisfy `Disk: Filesystem` ``, which is the right sentence.

**A pairing that is now enforced.** `record<F>(&mut Store<F>, &Working<F>, …)`
insists the store and the working copy are the same kind of folder. This was
not previously checkable, and 0011 — the working copy is the folder next to the
store — is why it should be.

## What the trait is, and what it is not

Eight methods: `read`, `write`, `create_new`, `create_directory`, `entries`,
`look`, `remove_file`, `remove_directory`. Four things are deliberately absent.

**No `rename`.** Nothing in the library renames anything, and that is 0019's
doing rather than an oversight: *a writer names the file it is creating rather
than renaming it afterwards*. The one command that renames is `arrange`, which
is a CLI command on `std::fs` — see the open question below, which is live.

**No `canonicalize`, and therefore no `Store::discover` off disk.** Discovery
walks up from a canonicalised path looking for a `historica.txt`. "Resolve this
path against the process's current directory and the symbolic links along it"
is a question about the machine the program is running on, not about the
folder — and a host that supplies its own filesystem already knows where its
store is. `discover` stays, on `Disk` only.

**No `read_to_string`.** Decoding is not a filesystem's business. The
UTF-8-or-`InvalidData` rule `std::fs::read_to_string` has lives in
`historica::fs::read_to_string` instead, as a free function over `read`, so
every caller gets the error kind it had and no implementation has to know the
rule exists.

**No metadata beyond a `Kind`.** Not size, not mtime, not permissions. Identity
comes from content (0003), so nothing here has ever asked a file how big or how
old it is, and a trait that offered it would invite a future reader to depend
on something two replicas can disagree about.

Two things the trait does insist on, both because the format already did:

**`create_new` is one operation.** This is the whole of the format's
concurrency story. A store is append-only and a document is named by the digest
of its own bytes, so two writers producing one revision produce one file and
neither has to win — but only if the create and the test-for-existence cannot
be split. An implementation that checks and then writes has a window, and what
fits in the window is a half-written document under a name that promises its
digest.

**Nothing follows a symbolic link.** `entries` and `look` report
`Kind::Symlink` and stop. 0016 established this for the store walk and 0011 for
the working copy; putting it in the trait is what makes an unbounded walk safe,
since a tree of real directories cannot contain itself.

And one thing it refuses to promise: **directory order**. `entries` may return
anything in any order, and the library sorts what it needs sorted, because two
replicas loading one store must agree and a `readdir` order is not something
either of them chose. The in-memory filesystem in `tests/filesystem.rs` returns
its entries reversed on purpose, so that a sort dropped anywhere in the library
fails a test rather than a sync.

## Why paths are not abstracted

`std::path::Path` stays, and this is the part most likely to look like a
half-measure. It is not one. 0018's whole argument was that a path is a path
and the filesystem already has a separator — a store's names *are* paths, and a
type that made them opaque would be reintroducing the fraction slash with more
ceremony. An implementation backed by something that is not a filesystem is
free to treat a `Path` as an opaque key: this crate only ever splits one into
components and joins them back.

The practical half of the answer is that `std::path` is not `std::fs`. A target
that lacks the second still has the first, so nothing is bought by replacing
it, and the cost of replacing it would be every signature in the crate.

## Consequences

- `historica::store::walk` takes the filesystem first. It is public, and this
  is a breaking change to it; `arrange` is the only caller in the tree.
- `Store::check` becomes `Store::check_on` off disk, and `check` threads the
  filesystem through `check_operations`, `check_replay` and `check_names`.
- `record::author_for` is `disk`-only; `record::author_for_on` takes a
  filesystem. `identity_path` is untouched and ungated, because it reads the
  environment and not the folder — which directory an operating system keeps
  configuration in is a question about the process.
- `Working` is no longer `Default`. It holds a filesystem, and there is no
  default one to hold when `disk` is off. Nothing constructed one.
- `Store::filesystem()` and `Working::filesystem()` hand back `&F`.
- The `bare` CI job builds the library with `--no-default-features` and greps
  `src/` for `std::fs`, skipping `src/cli/`, `src/main.rs` and `src/fs.rs`. The
  build is the real check; the grep is what turns a slip into a message naming
  the line rather than an error about a missing feature.

## Rejected alternatives

**`Arc<dyn Filesystem>`.** Argued above, at length, because it was written that
way first. Smaller source, and it taxes the exact hosts this exists for.

**Keeping the trait object but dropping only `Debug`**, with a hand-written
`Debug` for `Store` and `Working`. Removes one of the three constraints and
leaves the two that matter.

**A borrowed `Store<'a>` holding `&'a dyn Filesystem`.** No allocation and no
supertraits either, and it puts a lifetime on the handle type a host wants to
keep in a struct beside the filesystem it borrows from. Self-referential by
construction.

**Passing the filesystem to every method instead of holding one.** `Store` is a
handle, not a value: it inserts, sets bookmarks, prunes and forgets. And it
caches — the payload index maps digests to paths on one particular filesystem,
so a later call with a different one would silently read a stale index. Holding
it makes that unrepresentable, which is the argument 0003 makes about digests
and filenames, in a different place.

**`no_std`.** A much larger change nobody has asked for, and one that would
have to give up `std::io::Error`, `std::path` and `String::from_utf8`'s error
type on the way. `std` without a usable `std::fs` is the configuration that
actually exists.

**A `historica::Error` in place of `std::io::Error`.** Every implementation
translates into it and every one of this crate's error variants translates back
out, so that two `ErrorKind`s could be spelled differently.

**Leaving `check` on disk only.** Tempting, since `check` is a command. But
`check` is the one thing that reads a store *without trusting it*, which is
exactly what a host receiving a synced folder wants, and it would be a strange
library that could write a store it could not then examine.

**Abstracting the clock and the entropy source in the same change.**
`record::Platform` already isolates both behind `Clock` and `Entropy`, which is
the same seam arrived at earlier for the same reason. Nothing more is owed.

## Open questions

1. **Whether `arrange` should move into the library.** Live, and leaning yes:
   the core offering is readability, and `arrange` is the command that makes a
   folder readable — so a host syncing a store wants the arranged names for the
   same reason a person does. It is the only thing `rename` is wanted for, and
   it is already shaped like `prunable`/`prune` and `forget_plan`/`forget`,
   with `operation_names` sitting in `src/cli/` doing pure library work today.
2. **Whether the trait should offer a bulk or streaming read**, since `check`
   hashes every payload one `read` at a time. On disk this is right. Over a
   network-backed provider it may be a round trip per photograph.
3. **Whether `write` should be atomic** — write-and-rename rather than
   truncate-and-write. It touches only the four mutable files a store has, and
   0003 already calls those its entire conflict surface, so the exposure is a
   half-written bookmark. Worth doing; not worth doing in the change that only
   moves where the calls are made.
