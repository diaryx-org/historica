"""Write `notes.bend`: the four texts `init` writes, as the Rust tool writes them,
and the usage text `historica help` prints.

They are prose, not grammar, and the Rust tool keeps them in its source, so
the port takes them from the bytes a Rust `init` lays down and the text its
`help` prints rather than restating them by hand. `check.py` holds `init` and
`help` to the Rust tool byte for byte, so a text that drifted from the crate
fails there; run this to take it up again:

    python3 notes.py
"""
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
NOTES = [
    ("HEADER_NOTE", "historica.txt", "What `historica.txt` holds: the format line, the blank line reserved\n# under it, and the note to whoever opens the folder."),
    ("SKIPPED_NOTE", "skipped/README.txt", "`skipped/README.txt`: the rule syntax, explained, and no rule stated."),
    ("FORMAT_NOTE", "format.txt", "`format.txt`: every grammar in the store, for a reader with no Historica."),
    ("CACHE_NOTE", "cache/README.txt", "`cache/README.txt`: that everything beside it may be deleted."),
]
USAGE = "What `historica help` prints, and a usage error after its message: the\n# text of the default build, which has `fetch` and decision 0072's dispatch,\n# without the newline it ends with."


def literal(line):
    return '"' + line.replace("\\", "\\\\").replace('"', '\\"').replace("\t", "\\t") + '"'


def main():
    rust = shutil.which("historica") or sys.exit("the Rust `historica` is required on PATH")
    with tempfile.TemporaryDirectory() as directory:
        subprocess.run([rust, "init"], cwd=directory, check=True, capture_output=True)
        store = Path(directory) / "history"
        out = [
            "# The texts `init` writes, taken from what the Rust tool's `init` lays",
            "# down by `notes.py`, which says how to take them up again. Nothing reads",
            "# them: they are for a person who opens the folder. And the usage text,",
            "# taken from what the Rust tool's `help` prints.",
            "",
            "import Base",
        ]
        for name, path, about in NOTES:
            text = (store / path).read_text()
            assert text.endswith("\n"), path
            lines = text[:-1].split("\n")
            out += ["", f"# {about}", f"def {name}() -> String:", "  String.join(["]
            out += [f"    {literal(line)}," for line in lines[:-1]]
            out += [f"    {literal(lines[-1])}", '  ], "\\n") ++ "\\n"']
        # The usage, less the newline it ends with: `help` prints it with
        # one, and a usage error after its own message, where the halt that
        # ends the program adds one.
        usage = subprocess.run([rust, "help"], check=True, capture_output=True, text=True).stdout
        assert usage.endswith("\n")
        lines = usage[:-1].split("\n")
        out += ["", f"# {USAGE}", "def USAGE() -> String:", "  String.join(["]
        out += [f"    {literal(line)}," for line in lines[:-1]]
        out += [f"    {literal(lines[-1])}", '  ], "\\n")']
        (ROOT / "notes.bend").write_text("\n".join(out) + "\n")


if __name__ == "__main__":
    main()
