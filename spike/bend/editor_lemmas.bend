# The editor a message comes from is the one the Rust tool's
# `from_an_editor` asks for — `$VISUAL`, `$EDITOR` where `$VISUAL` is not
# set at all, an empty one being none — and what it leaves is read back
# only where it exited 0.
import Base
import ./editor.bend as Editor

# What an environment variable says: its value where it is set, empty or
# not.
def set(r: Result<&1, &1, U32 & String, String>) -> Maybe<&2, String>:
  match r:
    case Done{v}:
      Some{v}
    case Fail{e}:
      None{}

# A value kept only where it is not empty, as Rust's `filter` keeps it.
def unless_empty(m: Maybe<&2, String>) -> Maybe<&2, String>:
  match m:
    case None{}:
      None{}
    case Some{+v}:
      Bool.pick(Maybe<&2, String>, String.is_empty(v), None{}, Some{v})

def chosen_done(+v: String, editor: Result<&1, &1, U32 & String, String>) -> {Editor.chosen(Done{v}, editor) == unless_empty(Maybe.or(&2, String, Some{v}, set(editor))) : Maybe<&2, String>}:
  match editor:
    case Done{x}:
      {==}
    case Fail{f}:
      {==}

# `var_os("VISUAL").or_else(|| var_os("EDITOR")).filter(|e| !e.is_empty())`.
def chooses(visual: Result<&1, &1, U32 & String, String>, editor: Result<&1, &1, U32 & String, String>) -> {Editor.chosen(visual, editor) == unless_empty(Maybe.or(&2, String, set(visual), set(editor))) : Maybe<&2, String>}:
  match visual:
    case Done{+v}:
      chosen_done(v, editor)
    case Fail{e}:
      match editor:
        case Done{x}:
          {==}
        case Fail{f}:
          {==}

# Any exit but 0 stops with the editor unsaved, and reads nothing.
def unsaved(+file: String, +editor: String, +a: String, h: {String.eq(a, "0") == False{} : Bool}, read: String -> IO(Result<&2, &2, Editor.Stop, String>)) -> {Editor.saved.with(file, Editor.ended(editor, Done{a}), read) == IO.pure(Result<&2, &2, Editor.Stop, String>, Fail{Editor.Stop{1, "the editor stopped without saving"}}) : IO(Result<&2, &2, Editor.Stop, String>)}:
  %Equal.sym(Bool, String.eq(a, "0"), False{}, h) : {Editor.saved.with(file, Bool.pick(Result<&2, &2, Editor.Stop, Unit>, _, Done{Unit{}}, Fail{Editor.Stop{1, "the editor stopped without saving"}}), read) == IO.pure(Result<&2, &2, Editor.Stop, String>, Fail{Editor.Stop{1, "the editor stopped without saving"}}) : IO(Result<&2, &2, Editor.Stop, String>)}
  {==}

# The temporary directory, as `std::env::temp_dir` reads it: `$TMPDIR`,
# or `/tmp` where it is not set.
def tmpdir(r: Result<&1, &1, U32 & String, String>) -> String:
  match r:
    case Done{t}:
      t
    case Fail{e}:
      "/tmp"

# A temporary directory spelled as a directory is: not empty, and with no
# trailing `/`.
def tmp_ok(r: Result<&1, &1, U32 & String, String>) -> Bool:
  match r:
    case Done{+t}:
      Bool.and(Bool.not(String.is_empty(t)), Bool.not(String.ends_with(t, "/")))
    case Fail{e}:
      True{}
