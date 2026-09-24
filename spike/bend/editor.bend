# A message from the editor a person has already chosen: the Rust tool's
# `from_an_editor`, for a `record` or an `abandon` given no `-m`.
#
# `$VISUAL` where it is set, `$EDITOR` where it is not, and neither where
# the one that is set is empty: that is a usage error, as the Rust tool
# makes it. The editor is run on `historica-message` in the temporary
# directory — `$TMPDIR`, or `/tmp` — written empty first: decision 0011
# refuses to interpret a body 0002 promises never to interpret, so there is
# no template and nothing is stripped. It runs in the directory `-C`
# names, with this process's standard streams; an editor that ends with
# any code but `0` stopped without saving. What the file holds after is the
# message, and the file goes.

import Base
import ./store.bend as Store
import ./identity.bend as Identity

# Why no message came back, and what the process exits with.
type Stop is Data:
  Stop{code: U32, why: String}

def nonempty(+v: String) -> Maybe<&2, String>:
  Bool.pick(Maybe<&2, String>, String.is_empty(v), None{}, Some{v})

# `$VISUAL`, or `$EDITOR` where `$VISUAL` is not set at all; empty is none.
def chosen(visual: Result<&1, &1, U32 & String, String>, editor: Result<&1, &1, U32 & String, String>) -> Maybe<&2, String>:
  match visual editor:
    case Done{+v} _:
      nonempty(v)
    case Fail{e} Done{+v}:
      nonempty(v)
    case Fail{e} Fail{f}:
      None{}

# `std::env::temp_dir()` and the file in it.
def scratch(tmp: Result<&1, &1, U32 & String, String>) -> String:
  match tmp:
    case Done{+t}:
      Identity.joined(t, "historica-message")
    case Fail{e}:
      "/tmp/historica-message"

# How the editor ended: saved, or why not.
def ended(+editor: String, r: Result<&1, &1, U32 & String, String>) -> Result<&2, &2, Stop, Unit>:
  match r:
    case Fail{Tuple{code, msg}}:
      Fail{Stop{1, editor ++ ": " ++ msg}}
    case Done{+answer}:
      Bool.pick(Result<&2, &2, Stop, Unit>, String.eq(answer, "0"), Done{Unit{}}, Fail{Stop{1, "the editor stopped without saving"}})

def read.back(+file: String, r: Result<&1, &1, U32 & String, File>) -> IO(Result<&2, &2, Stop, String>):
  match r:
    case Fail{Tuple{+code, msg}}:
      IO.pure(Result<&2, &2, Stop, String>, Fail{Stop{1, file ++ ": " ++ Store.os_error(code, msg)}})
    case Done{f}:
      do IO<Result<&2, &2, Stop, String>>:
        File.close(f)
        text : String <- Store.read_text(file)
        gone : Result<&1, &1, U32 & String, String> <- Store.removed(Identity.parent(file) ++ "\n" ++ file)
        return Done{text}

def saved(+file: String, r: Result<&2, &2, Stop, Unit>) -> IO(Result<&2, &2, Stop, String>):
  match r:
    case Fail{s}:
      IO.pure(Result<&2, &2, Stop, String>, Fail{s})
    case Done{u}:
      do IO<Result<&2, &2, Stop, String>>:
        opened : Result<&1, &1, U32 & String, File> <- File.open(file, "r")
        read.back(file, opened)

def edited(+file: String, +editor: String, w: Result<&1, &1, U32 & String, String>) -> IO(Result<&2, &2, Stop, String>):
  match w:
    case Fail{Tuple{code, msg}}:
      IO.pure(Result<&2, &2, Stop, String>, Fail{Stop{1, msg}})
    case Done{x}:
      do IO<Result<&2, &2, Stop, String>>:
        here : String <- Store.from()
        r : Result<&1, &1, U32 & String, String> <- Store.ran(here, editor, [file])
        saved(file, ended(editor, r))

def chosen.run(e: Maybe<&2, String>, +file: String) -> IO(Result<&2, &2, Stop, String>):
  match e:
    case None{}:
      IO.pure(Result<&2, &2, Stop, String>, Fail{Stop{2, "no $VISUAL or $EDITOR here; say what this records with -m"}})
    case Some{+editor}:
      do IO<Result<&2, &2, Stop, String>>:
        w : Result<&1, &1, U32 & String, String> <- Store.written(file ++ "\n")
        edited(file, editor, w)

def message() -> IO(Result<&2, &2, Stop, String>):
  do IO<Result<&2, &2, Stop, String>>:
    visual : Result<&1, &1, U32 & String, String> <- IO.get_env("VISUAL")
    editor : Result<&1, &1, U32 & String, String> <- IO.get_env("EDITOR")
    tmp : Result<&1, &1, U32 & String, String> <- IO.get_env("TMPDIR")
    chosen.run(chosen(visual, editor), scratch(tmp))
