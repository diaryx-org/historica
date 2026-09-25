#!/usr/bin/env python3
"""Check proofs, run JS/native corpora, ensure replay mutations are rejected,
and hold the store commands to the Rust tool's output.

The stages are independent and run at once; `check.py <stage>...` runs only
those named, for iterating on one: store, corpora, similar, proof, mutations.

The corpora and the store commands run on the JS build alone unless given
`--native`, which builds and runs each natively as well: emitting and
compiling `main.bend`'s C takes minutes the JS build does not.

`--stores=a,b` holds only the stores named to the Rust tool, and leaves the
corpus of `opdiff` fixtures out, for iterating on one command's store.
"""
from concurrent.futures import ThreadPoolExecutor
import time
from pathlib import Path
import hashlib
import itertools
import os
import random
import re
import shutil
import stat
import subprocess
import sys
import tempfile
import threading

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parent.parent
CORPUS = REPO / "tests" / "corpus"
# A Nix profile (or another package manager) can update while a gate runs.
# Resolve once so the printed version identifies every check in this run.
BEND = shutil.which("bend")
if BEND is None:
    raise SystemExit("bend is required on PATH")
BEND = str(Path(BEND).resolve())

# Bend's checker and `cc` each take about two cores; more of them at once than
# the machine holds only slows every one, until the proofs run into timeouts.
SLOTS = threading.BoundedSemaphore(max(1, (os.cpu_count() or 2) // 2))
NATIVE = "--native" in sys.argv[1:]
ONLY = next((a.split("=", 1)[1].split(",") for a in sys.argv[1:] if a.startswith("--stores=")), None)


def run(*args, cwd=ROOT, timeout=120):
    print("+", " ".join(map(str, args)), flush=True)
    with SLOTS:
        subprocess.run(args, cwd=cwd, check=True, timeout=timeout)


def capture(*args, cwd, env=None):
    """A command's stdout, stderr and exit code, for comparing two tools."""
    done = subprocess.run(args, cwd=cwd, env=env, capture_output=True, timeout=120)
    return done.stdout, done.stderr, done.returncode


def parallel(jobs, workers=os.cpu_count()):
    """Run each job at once, and raise the first failure after all finish."""
    with ThreadPoolExecutor(max(1, min(workers, len(jobs)))) as pool:
        futures = [pool.submit(job) for job in jobs]
    failures = [f.exception() for f in futures if f.exception() is not None]
    for failure in failures[1:]:
        print("also failed:", failure, flush=True)
    if failures:
        raise failures[0]
    return [f.result() for f in futures]


def check_proof(temporary):
    run(BEND, "PROOF.bend")


# How much of what the tool runs a law reaches (`reach.py`): a report, not a
# gate, so that the number is in front of whoever runs the check.
def check_reach(temporary):
    run(sys.executable, "reach.py")


def check_corpora(temporary):
    def suite(name):
        def job():
            run(BEND, f"{name}.bend")
            if NATIVE:
                executable = temporary / name
                run(BEND, f"{name}.bend", "-o", str(executable), timeout=600)
                run(str(executable))
        return job

    parallel([suite(name) for name in ("corpus_ops", "corpus_rev", "corpus_tree", "replay_tests")])


def timed(name, stage, temporary):
    def job():
        started = time.monotonic()
        try:
            stage(temporary)
        except BaseException as failure:
            print(f"FAILED {name} after {time.monotonic() - started:.0f}s", flush=True)
            # A `sys.exit` in a thread is a failure to report, not an exit.
            raise RuntimeError(f"{name}: {failure}") from failure
        print(f"done  {name} in {time.monotonic() - started:.0f}s", flush=True)
    return job


def main():
    # The longest first, so that it takes the first slots.
    stages = {
        "store": check_store,
        "corpora": check_corpora,
        "similar": check_similar,
        "proof": check_proof,
        "mutations": check_mutations,
        "reach": check_reach,
    }
    asked = [a for a in sys.argv[1:] if a != "--native" and not a.startswith("--stores=")] or list(stages)
    unknown = [name for name in asked if name not in stages]
    if unknown:
        raise SystemExit(f"unknown stage {', '.join(unknown)}; the stages are {', '.join(stages)}")
    run(BEND, "version")
    started = time.monotonic()
    with tempfile.TemporaryDirectory(prefix="historica-bend-") as directory:
        temporary = Path(directory)
        try:
            parallel([timed(name, stages[name], temporary) for name in asked])
        except RuntimeError as failure:
            raise SystemExit(str(failure))
    print(f"all of {', '.join(asked)} in {time.monotonic() - started:.0f}s")


# The diff
# --------

# `similar.bend` is `similar`'s Histogram diff, held to the crate itself on
# cases drawn to reach each of its paths: small edits over few distinct
# lines, runs where every shared line is common (the Myers fallback, with its
# heuristics and its exact small-side search), and long sides that share
# almost nothing (the preflights). Bend prints the operations before the
# `Replace` hook groups them, and the grouping is applied here. A case
# marked `M:` asks both for Myers instead, which `diff` draws a changed
# line's emphasis with.
def similar_cases(rng):
    kind = rng.random()
    if kind < 0.5:
        alpha = rng.randint(1, 8)
        old = [str(rng.randint(0, alpha)) for _ in range(rng.randint(0, 30))]
        new = list(old)
        for _ in range(rng.randint(0, 8)):
            r = rng.random()
            if r < 0.4 and new:
                del new[rng.randrange(len(new))]
            elif r < 0.8:
                new.insert(rng.randint(0, len(new)), str(rng.randint(0, alpha + 3)))
            elif new:
                new[rng.randrange(len(new))] = str(rng.randint(0, alpha))
        return old, new
    if kind < 0.8:
        old = [rng.choice(["x", "x", "x", "y", str(rng.randint(0, 50))]) for _ in range(rng.randint(60, 300))]
        new = [rng.choice(["x", "x", "y", "z", str(rng.randint(0, 50))]) for _ in range(rng.randint(60, 300))]
        return old, new
    n, m = rng.randint(512, 1200), rng.randint(512, 1200)
    old = [f"a{rng.randint(0, 5000)}" for _ in range(n)]
    new = [f"b{rng.randint(0, 5000)}" for _ in range(m)]
    for _ in range(rng.choice([1, 3, 20, 80])):
        old[rng.randint(10, n - 10)] = "x"
        new[rng.randint(10, m - 10)] = "x"
    for _ in range(rng.choice([0, 1, 5, 30])):
        shared = f"c{rng.randint(0, 40)}"
        old[rng.randint(10, n - 10)] = shared
        new[rng.randint(10, m - 10)] = shared
    return old, new


def replaced(line):
    """The `Replace` hook: each run between shared runs as one operation."""
    out, eq, dl, ins = [], None, None, None

    def flush():
        nonlocal dl, ins
        if dl and ins:
            out.append(f"R{dl[0]},{dl[1]},{ins[1]},{ins[2]}")
        elif dl:
            out.append(f"D{dl[0]},{dl[1]},{dl[2]}")
        elif ins:
            out.append(f"I{ins[0]},{ins[1]},{ins[2]}")
        dl = ins = None

    for token in line.split():
        a, b, c = map(int, token[1:].split(","))
        if token[0] == "E":
            flush()
            eq = [eq[0], eq[1], eq[2] + c] if eq else [a, b, c]
            continue
        if eq:
            out.append(f"E{eq[0]},{eq[1]},{eq[2]}")
            eq = None
        if token[0] == "D":
            dl = [dl[0], dl[1] + b, dl[2]] if dl else [a, b, c]
        else:
            ins = [ins[0], ins[1], ins[2] + c] if ins else [a, b, c]
    if eq:
        out.append(f"E{eq[0]},{eq[1]},{eq[2]}")
    flush()
    return " ".join(out)


def check_similar(temporary):
    run("cargo", "build", "-q", "--release", "--example", "similar_ops", cwd=ROOT / "ffi", timeout=600)
    source = temporary / "similar.c"
    native = temporary / "similar"
    run(BEND, "similar.bend", "-o", str(source), timeout=600)
    run(os.environ.get("CC", "cc"), "-O2", "-w", "-o", str(native), str(source), "-lm", "-lpthread", timeout=900)
    rng = random.Random(20260922)
    cases = [similar_cases(rng) for _ in range(1500)]
    # A third again for Myers alone, which `diff` draws a line's emphasis with.
    cases += [(["M:"] + old, new) for old, new in (similar_cases(rng) for _ in range(500))]
    text = "".join(" ".join(old).replace("M: ", "M:", 1) + "|" + " ".join(new) + "\n" for old, new in cases)
    (temporary / "cases.txt").write_text(text)
    reference = ROOT / "ffi" / "target" / "release" / "examples" / "similar_ops"
    expected = subprocess.run([str(reference)], input=text, capture_output=True, text=True, check=True).stdout.splitlines()
    got = subprocess.run([str(native), str(temporary / "cases.txt")], capture_output=True, text=True, check=True).stdout.splitlines()
    unfit = [i for i, line in enumerate(got) if "UNFIT" in line]
    if unfit:
        sys.exit(f"{len(unfit)} of {len(cases)} cases found moves the check in `Sim.diff` refuses, first {text.splitlines()[unfit[0]][:200]}")
    differ = [i for i, want in enumerate(expected) if i >= len(got) or replaced(got[i]) != want]
    for i in differ[:3]:
        print(f"DIFF similar case {i}:\n  {text.splitlines()[i][:200]}\n  want {expected[i][:200]}\n  got  {replaced(got[i])[:200] if i < len(got) else ''}")
    if differ or len(got) != len(cases):
        sys.exit(f"{len(differ)} of {len(cases)} diffs differ from `similar`")
    print(f"similar: {len(cases)} cases, as the crate draws them")


# The store commands
# ------------------

# `main.bend`'s `log`, `files`, `cat` and `show` are held to the Rust tool,
# byte for byte, on stores assembled from the corpora: each corpus's
# `revisions/` and `operations/` under a `history/` with the header file the
# tool looks for. What is compared is the `.js` build, which runs the
# adapter's JS twins, and with `--native` the native binary too, linked
# against the Rust archive in `ffi/` — so a twin that drifts from its C side
# fails a `--native` run.
#
# One command per corpus is a target the Rust tool resolves; the rest are
# refusals, whose text is compared too — a usage error to the end of its
# message, since the Rust tool prints its whole usage after it. `record`
# and `name` run each tool on a copy of the store of its own, and what the
# folder and `names/` hold after is compared too: `--move` renames before
# anything is read, and `name` writes and deletes bookmarks — or, for
# `init`, the whole of what is there.
# What both writers are told, so that a record is the same bytes from
# either: the moment, the seed every identifier is drawn from, and who.
# The Rust side is `historica-pinned`, the test build of the same command
# line; a command led by a dict runs with those variables changed.
PINS = {
    "HISTORICA_AUTHOR": "Check <check@example.com>",
    "HISTORICA_PINNED_NOW": "2026-03-04T09:10:11+02:00",
    "HISTORICA_PINNED_SEED": "check.py",
    # No editor: a command wanting a message it was not given refuses the
    # same way on every machine, whatever this one's environment says.
    "VISUAL": "",
    "EDITOR": "",
}

# The commands that supersede, which write the store as `record` does.
REWRITES = ("amend", "abandon", "carry")

STORES = {
    "tree": [
        ["log"],
        ["log", "kxry"],
        ["files", "head"],
        ["files", "qpvu"],
        ["cat", "head", "docs/README.md"],
        ["cat", "kxry", "README.md"],
        ["cat", "head", "entry.md"],
        ["show", "head"],
        ["show", "mzvw", "docs/README.md"],
        ["show", "zzzz"],
        ["show", "nope"],
        ["status"],
        ["status", "--onto", "kxry"],
        ["record", "-n"],
        ["record", "-n", "--onto", "kxry", "docs"],
    ],
    "revisions": [["log"], ["log", "kxryzmor"], ["show", "head"], ["status"], ["record", "-n"]],
    "merged": [["log"], ["files", "head"], ["status"]],
    "links": [
        ["log"],
        ["files", "head"],
        ["files", "kxry"],
        ["cat", "head", "current"],
        ["cat", "kxry", "current"],
        ["cat", "mzvw", "2026/08.md"],
        ["cat", "head", "2026/08.md"],
        ["diff", "head"],
        ["diff", "kxry"],
        ["blame", "head", "current"],
        ["diff"],
        ["status"],
        ["status", "--onto", "kxry"],
        ["record", "-n"],
        ["record", "-n", "--onto", "kxry", "current"],
    ],
    "modes": [["log"], ["files", "head"], ["diff", "head"], ["blame", "head", "run.sh"], ["diff"], ["status"], ["record", "-n"]],
    "whole": [
        ["log"], ["files", "head"], ["cat", "head", "notes/2026-08-20.md"],
        ["diff", "head"], ["blame", "head", "notes/photo.png"], ["blame", "head", "notes/2026-08-20.md"],
        # An assembled store has no folder beside it, so everything is gone.
        ["diff"], ["blame", "notes/2026-08-20.md"], ["status"], ["record", "-n"], ["record", "-n", "notes/photo.png"],
    ],
    # Recorded here by the Rust tool rather than taken from a corpus: the
    # widest path holds characters outside ASCII, which the Rust tool
    # measures in bytes and pads in characters.
    "unicode": [["files", "head"], ["cat", "head", "café/naïve résumé.md"]],
    # Bookmarks, pointed by the Rust tool's own `name`: a change, a pin, a
    # file, a private one, one called `head` — which wins over the word —
    # and two written by hand that point at nothing here.
    "names": [
        ["names"],
        ["files", "main"],
        ["cat", "head", "notes.md"],
        ["cat", "main", "notes.md"],
        ["cat", "main", "file:nb"],
        ["cat", "first", "file:nb"],
        ["cat", "main", "path:notes.md"],
        ["cat", "main", "file:main"],
        ["cat", "main", "file:zz"],
        ["show", "main", "file:nb"],
        ["log", "first"],
        ["files", "nb"],
        ["files", "x/pin"],
        ["files", "gone"],
        # A bookmark written: to a change, pinned to a revision, to a file
        # by path, `path:` or `file:`; moved, keeping its axis or changing
        # it; nested; and deleted, tidying what it leaves empty. And what
        # each refuses, with `--fields`' header where a statement was asked.
        ["name", "new", "first"],
        ["name", "new", "first", "--revision"],
        ["name", "new", "--revision", "first", "--change"],
        ["name", "new", "head", "notes.md"],
        ["name", "new", "first", "path:notes.md"],
        ["name", "new", "first", "file:nb"],
        ["name", "new", "main"],
        ["name", "main", "first"],
        ["name", "main", "first", "--private"],
        ["name", "feature/x", "first"],
        ["name", "feature/x", "first", "--shared"],
        ["name", "feature/y", "first", "--private", "--shared"],
        ["name", "deep/er/z", "first", "--private"],
        ["name", "x", "first"],
        ["name", "x/pin/deeper", "first"],
        ["name", "head", "main"],
        ["name", "--fields", "new", "first"],
        ["name", "new", "first", "--fields", "--revision"],
        ["name", "--fields", "new", "nosuch"],
        ["name", "--fields", "new", ""],
        ["name", "--fields", "new", "first", "file:"],
        ["name", "--fields", "new", "first", "nope.md"],
        ["name", "--fields", "k" * 24, "first"],
        ["name", "new", "nosuch"],
        ["name", "new", "gone"],
        ["name", "new", "first", "nope.md"],
        ["name", "new", "first", "file:zz"],
        ["name", "new", "nb"],
        ["name", "new", "first", "notes.md", "--revision"],
        ["name"],
        ["name", "new"],
        ["name", "a", "b", "c", "d"],
        ["name", "a\\b", "first"],
        ["name", "", "first"],
        ["name", "/abs", "first"],
        ["name", "../up", "first"],
        ["name", "a//b", "first"],
        ["name", " lead", "first"],
        ["name", "dir/", "first"],
        ["name", "bell\x07", "first"],
        ["name", "k" * 24, "first"],
        ["name", "--delete", "main"],
        ["name", "--delete", "x/pin"],
        ["name", "--delete", "feature/x"],
        ["name", "--delete", "gone"],
        ["name", "--delete", "nope"],
        ["name", "--delete", " lead"],
        ["name", "--delete"],
        ["name", "--delete", "a", "b"],
        ["name", "--delete", "main", "--private"],
        ["name", "--delete", "main", "--fields"],
        ["name", "--fields", "--delete", "nope"],
        ["name", "--fields", "--delete"],
    ],
    # The same, with a bookmark file that is not one: every command refuses.
    "badname": [["names"], ["log"], ["files", "main"], ["name", "new", "head"], ["name", "--fields", "new", "head"], ["name", "--delete", "main"],
                ["record", "--fields", "-m", "x"], ["amend", "--fields", "-m", "y"], ["abandon", "head", "--fields", "-m", "z"], ["carry", "--fields"]],
    # Two authors, a rename, and a line of work beside the main one, for
    # `log`'s filters, ranges and `--fields`.
    "log": [
        ["log"],
        ["log", "--limit", "2", "tip"],
        ["log", "tip", "--limit", "0"],
        ["log", "--author", "Bob"],
        ["log", "--grep", "other", "--author", "Ada", "--limit", "1"],
        ["log", "--since", "2000-01-01", "--until", "2000-12-31"],
        ["log", "--since", "2024-02-29T00:00:00+00:00"],
        ["log", "base..tip"],
        ["log", "tip..base"],
        ["log", "tip..tip"],
        ["log", "--fields"],
        ["log", "--fields", "tip", "--limit", "2"],
        ["record", "-n"],
        ["record", "-n", "--onto", "tip"],
        ["record", "-n", "--onto", "tip", "--merge", "base"],
        ["log", "tip", "--path", "renamed.md"],
        ["log", "base", "--path", "notes.md"],
        ["log", "--path", "renamed.md"],
        ["log", "tip", "--path", "nope.md"],
        ["log", "base..zzzz"],
        # `diff` and `blame`, which the rename and the second author are for.
        ["diff", "tip"],
        ["diff", "tip", "--onto", "base"],
        ["diff", "base", "--onto", "tip"],
        ["diff", "tip", "renamed.md"],
        ["diff", "tip", "--color", "never"],
        ["diff", "tip", "--color", "always"],
        ["diff", "tip", "--onto", "base", "--color=always"],
        ["diff", "tip", "nope.md"],
        ["blame", "tip", "renamed.md"],
        ["blame", "tip", "renamed.md", "--lines", "2..3"],
        ["blame", "tip", "renamed.md", "--lines", "9"],
        ["blame", "base", "notes.md"],
        # Two heads: the folder has no one position to be compared with.
        ["diff"],
        ["blame", "renamed.md"],
        ["diff", "--onto", "tip"],
        ["blame", "renamed.md", "--lines", "1..1"],
        ["status"],
        ["status", "--onto", "tip"],
        ["status", "--onto", "base"],
        ["status", "--onto", "zzzz"],
        ["status", "--onto", "base", "--onto", "tip"],
    ],
    # The folder against the position: an edit, a file gone, files new —
    # text and bytes — a file of bytes changed, a mode, links retargeted,
    # made and removed, a file become a link, and rules skipping a path, a
    # directory, a name and a directory's name, filed flat and in folders.
    "folder": [
        ["diff"],
        ["diff", "notes.md"],
        ["diff", "path:notes.md"],
        ["diff", "file:nb"],
        ["diff", "gone.md"],
        ["diff", "nope.md"],
        ["diff", "--onto", "first"],
        ["diff", "--onto", "first", "notes.md"],
        ["diff", "--color", "never"],
        ["diff", "--color", "always"],
        ["diff", "--color", "auto"],
        ["blame", "notes.md"],
        ["blame", "file:nb"],
        ["blame", "path:notes.md", "--lines", "2..3"],
        ["blame", "new.md"],
        ["blame", "kept.md"],
        ["blame", "gone.md"],
        ["blame", "photo.bin"],
        ["blame", "data.bin"],
        ["blame", "current"],
        ["blame", "build/out.md"],
        ["blame", "deep/scratch.tmp"],
        ["blame", "nope.md"],
        ["blame", "file:zz"],
        ["status"],
        ["status", "--onto", "first"],
        # What recording would state, and each thing it refuses before
        # it looks: a path nothing answers to, one a rule keeps out, a kind
        # stated too late or for a path not looked at or not there, and
        # bytes that are not lines; and renames, done in the folder first.
        ["record", "--dry-run"],
        ["record", "-n", "--onto", "first"],
        ["record", "-n", "notes.md"],
        ["record", "-n", "deep", "notes.md/"],
        ["record", "-n", "current", "gone.md", "run.sh"],
        ["record", "-n", "build/out.md"],
        ["record", "-n", "build", "logs", "secret.md"],
        ["record", "-n", "nope.md", "gone/"],
        ["record", "-n", "nope.md", "build/out.md"],
        ["record", "-n", "--lines", "photo.bin"],
        ["record", "-n", "--bytes", "new.md", "--lines", "photo.bin"],
        ["record", "-n", "--bytes", "notes.md"],
        ["record", "-n", "--lines", "data.bin"],
        ["record", "-n", "--bytes", "current"],
        ["record", "-n", "notes.md", "--bytes", "new.md"],
        ["record", "-n", "--lines", "gone.md"],
        ["record", "-n", "--move", "notes.md=moved/notes.md"],
        ["record", "-n", "--move", "gone.md=new.md"],
        ["record", "-n", "--move", "kept.md=secret.md"],
        ["record", "-n", "--move", "kept.md=build/kept.md"],
        ["record", "-n", "--move", "kept.md=k.md", "--move", "k.md=l.md"],
        ["record", "-n", "--move", "kept.md=k.md", "--move", "kept.md=l.md"],
        ["record", "-n", "--move", "nope.md=new.md"],
        ["record", "-n", "--move", "notes.md=a/"],
        ["record", "-n", "--move", "notes.md=a//b.md"],
        ["record", "-n", "--move", "notes.md= lead.md"],
        ["record", "-n", "notes.md", "--move", "notes.md=n.md"],
        ["record", "-n", "notes.md", "n.md", "--move", "notes.md=n.md"],
        ["record", "-n", "--at", "nb=elsewhere.md"],
        ["record", "-n", "--at", "first=x.md"],
        ["record", "-n", "--at", "zz=x.md"],
        ["record", "-n", "--at", "nb"],
        ["record", "-n", "--accept", "data.bin"],
        ["record", "-n", "--accept", "data.bin", "--accept", "photo.bin"],
        ["record", "-n", "--merge", "first"],
        ["record", "-n", "--merge", "first", "notes.md"],
        ["record", "-n", "--fields"],
        ["record", "-n", "-m"],
        ["record", "-n", "--frobnicate"],
        ["record", "-n", ""],
        ["record", "-n", "//"],
        ["record", "-n", "--bytes", "a", "--lines", "b", "--bytes", "b"],
        ["record", "-n", "-m", "a message", "--message", "another"],
    ],
    # Recording, written: the store's own words and every byte it filed,
    # against the Rust tool's with the same clock and the same minting. Each
    # kind of file arriving, edited, going, renamed, run and pointed at; a
    # name another revision already has, and a summary the filesystem will
    # not take whole; the bookmarks that follow; content the store already
    # holds; and what is refused before anything is written.
    "recording": [
        ["record", "-m", "second"],
        ["record", "-m", "second", "--fields"],
        ["record", "--fields", "-m", "the first"],
        ["record", "-m", "the first"],
        ["record", "-m", "", "notes.md"],
        ["record", "-m", "...", "notes.md"],
        ["record", "-m", "Fix: the parser? <yes> \"quoted\" | piped *star*, and on until it is cut\nand a second line", "notes.md"],
        ["record", "-m", "moved", "--move", "old.md=moved.md"],
        ["record", "-m", "moved", "old.md", "moved.md", "--move", "old.md=moved.md"],
        ["record", "-m", "kinds", "new.md", "blob.bin", "--bytes", "new.md", "--lines", "blob.bin"],
        ["record", "-m", "twins", "twin-a.md", "twin-b.md", "copy.md", "odd.ops.txt"],
        ["record", "-m", "links", "to-new", "new.md", "abs-link", "to-notes", "going.md"],
        ["record", "-m", "runs", "run.sh", "tool.sh", "empty.md", "sub"],
        ["record", "-m", "on the first", "--onto", "first"],
        ["record", "-m", "nothing", "unchanged.md"],
        ["record", "-m", "nothing", "unchanged.md", "--fields"],
        [{"HISTORICA_PINNED_NOW": "2026-03-03T23:59:59-01:00"}, "record", "-m", "late"],
        [{"HISTORICA_PINNED_NOW": "2026-03-04T05:06:07+00:00"}, "record", "-m", "at once", "notes.md"],
        [{"HISTORICA_AUTHOR": " Spaced <s@example.com>"}, "record", "-m", "who"],
        [{"HISTORICA_AUTHOR": " Spaced <s@example.com>"}, "record", "-m", "who", "--fields"],
        ["record", "-m", "not here", "nope.md"],
    ],
    # Rewriting, written: `abandon`, `amend` and `carry` against the pinned
    # build, every byte they file compared. A run abandoned and one revision
    # alone; a reword above a stack, and an amendment the folder speaks for;
    # a move onto another line, restating what the rewrite moved beneath it,
    # and each refusal in the order the Rust tool meets it.
    "rewriting": [
        ["abandon"],
        ["abandon", "a", "b"],
        ["abandon", "--bogus"],
        ["abandon", "-m"],
        ["abandon", "-n", "--fields", "top"],
        ["abandon", "nope"],
        ["abandon", "-n", "top"],
        ["abandon", "-n", "base"],
        ["abandon", "-n", "tip"],
        ["abandon", "-n", "base", "--only"],
        ["abandon", "-n", "top", "--only"],
        ["abandon", "top", "-m", "gone"],
        ["abandon", "top", "-m", "gone", "--fields"],
        ["abandon", "top", "-m", " "],
        ["abandon", "top"],
        ["abandon", "tip", "-m", "why"],
        ["abandon", "base", "-m", "forked"],
        ["abandon", "top", "--only", "-m", "not that"],
        ["abandon", "top", "--only", "-m", "not that", "--fields"],
        ["abandon", "bottom", "--only", "-m", "contested"],
        ["abandon", "base", "--only", "-m", "lost"],
        ["abandon", "middle", "-m", "the side goes"],
        ["amend"],
        ["amend", "a", "b"],
        ["amend", "--only"],
        ["amend", "-n", "--fields"],
        ["amend", "nope"],
        ["amend", "top", "-m", "top, reworded"],
        ["amend", "top", "-m", "top, reworded", "--fields"],
        ["amend", "-n", "top", "-m", "top, reworded"],
        ["amend", "top"],
        ["amend", "top", "-m", "top"],
        ["amend", "top", "--move", "f.md=x.md", "-m", "x"],
        ["amend", "base", "-m", "a new base"],
        ["amend", "-n", "tip"],
        ["amend", "tip"],
        ["amend", "tip", "--fields"],
        ["amend", "tip", "-m", "tip, again"],
        ["amend", "tip", "--move", "extra.md=more.md"],
        ["amend", "tip", "--move", "g.md=h.md", "-m", "moved"],
        ["amend", "tip", "--move", "nope.md=x.md"],
        [{"HISTORICA_AUTHOR": "Other <o@example.com>"}, "amend", "tip", "-m", "by another"],
        ["amend", "middle", "-m", "middle"],
        ["carry"],
        ["carry", "-n"],
        ["carry", "--fields"],
        ["carry", "a", "b"],
        ["carry", "--only"],
        ["carry", "-n", "--fields"],
        ["carry", "--onto", "base"],
        ["carry", "top"],
        ["carry", "top", "--onto", "middle"],
        ["carry", "-n", "top", "--onto", "middle"],
        ["carry", "top", "--onto", "middle", "--fields"],
        ["carry", "bottom", "--onto", "middle"],
        ["carry", "tip", "--onto", "middle"],
        ["carry", "middle", "--onto", "top"],
        ["carry", "middle", "--onto", "tip"],
        ["carry", "tip", "--onto", "bottom"],
        ["carry", "top", "--onto", "tip"],
        ["carry", "base", "--onto", "tip"],
        ["carry", "top", "--onto", "side"],
        ["carry", "side", "--onto", "nope"],
    ],
    # A rewrite that arrived without its carries: the repair, swept, named,
    # and planned; and what already rewritten refuses.
    "stranded": [
        ["carry", "-n"],
        ["carry"],
        ["carry", "--fields"],
        ["carry", "bottom"],
        ["carry", "tip"],
        ["carry", "top"],
        ["carry", "-n", "side", "--onto", "tip"],
        ["amend", "top", "-m", "again"],
        ["abandon", "top", "-m", "again"],
        ["status"],
        ["log"],
    ],
    # `init`, where there is nothing yet: here, in a directory named — `.`,
    # nothing, nested, with a slash — made with its parents; refused beside a
    # second argument, and where a store is already. And every command that
    # needs a store, finding none.
    "bare": [
        ["init"],
        ["init", "."],
        ["init", ""],
        ["init", "sub"],
        ["init", "sub/deeper/"],
        ["init", "sub/./deeper/.."],
        ["init", "a", "b"],
        ["status"],
        ["name", "x", "head"],
        ["record", "-n"],
        ["skip"], ["skip", "x"], ["skip", "--bogus"],
        # No statement where no store is found: the Rust tool leaves before
        # it considers one, for the four commands it finds the store for
        # before reading their words — and not for `name`, which finds it
        # after.
        ["record", "--fields", "-m", "x"], ["amend", "--fields"], ["abandon", "x", "--fields"], ["carry", "--fields"],
        ["name", "--fields", "x", "head"], ["-C", "nowhere", "record", "--fields"], ["-C", "nowhere", "name", "--fields", "x", "head"],
        # `check` where there is no store: none found, a directory named
        # that holds none, a file named, and a path not there.
        ["check", "."], ["check", "notes.md"], ["check", "nowhere"], ["check", "nowhere/history"], ["-C", "nowhere", "check"],
    ],
    # The command line before any command: the usage and the version, what
    # is not an option, `-C` in its every position — the last counting, a
    # directory below the store, one that is not there, `init` making one —
    # and decision 0072's dispatch to `historica-<word>` on `PATH`: run in
    # `-C`'s directory with its own code, killed, not runnable, not there,
    # and a word never looked for. And the commands that count their words
    # after opening the store.
    "shell": [
        ["help"], ["-h"], ["--help"], [], ["-V"], ["--version"], ["-C", "sub", "--version"],
        ["-x"], ["-C"], ["-C", "sub", "-q", "log"], ["bogus"], ["a/b"], ["x-"], ["-x-"],
        ["-C", "sub", "log", "--limit", "1"],
        ["-C", "nowhere", "-C", "sub", "status"],
        ["-C", "sub", "-C", "nowhere", "status"],
        ["-C", "nowhere", "log"],
        ["-C", "", "log"],
        ["-C", "sub/", "record", "-n"],
        ["-C", "sub", "init"],
        ["-C", ".", "init"],
        ["-C", "fresh/deeper", "init", "there"],
        ["-C", "sub", "name", "sub-name", "head"],
        [{"PATH": "{temporary}/bin:{path}"}, "hello", "a", "b c", ""],
        [{"PATH": "{temporary}/bin:{path}"}, "-C", "sub", "hello", "--fields"],
        [{"PATH": "{temporary}/bin:{path}"}, "-C", "nowhere", "hello"],
        [{"PATH": "{temporary}/bin:{path}"}, "quiet"],
        [{"PATH": "{temporary}/bin:{path}"}, "killed"],
        [{"PATH": "{temporary}/bin:{path}"}, "unrunnable"],
        [{"PATH": "{temporary}/bin:{path}"}, "hello.sh"],
        ["show"], ["show", "head", "notes.md", "x"], ["files"], ["files", "head", "x"],
        ["cat"], ["cat", "head"], ["cat", "head", "notes.md", "x"], ["names", "x"],
        # The directory `check` is given: the store's, its `history`, one
        # below it, by an absolute path, and a second one.
        ["check", "."], ["check", "history"], ["check", "history/"], ["check", "./history/."], ["check", "sub"], ["check", "{copy}"],
        ["check", "{copy}/history"], ["-C", "sub", "check"], ["-C", "sub", "check", ".."], ["check", ".", "--complete"],
        ["check", "--bogus"], ["check", ".", "sub"], ["check", "--complete", "--complete"],
    ],
    # Opening a store, where there is only a `history` directory, or one
    # whose header names a format or a layout this reader lacks: every
    # command that opens it is refused, a writing one asked for `--fields`
    # with its statement first — and the nearest `history` stops the walk.
    "headless": [
        ["log"], ["status"], ["names"], ["show", "head"], ["files", "head"], ["cat", "head", "a.md"],
        ["diff"], ["blame", "a.md"], ["record", "-n"], ["record", "--bogus"], ["record", "-m", "x"],
        ["record", "--fields", "-m", "x"], ["amend", "--fields"], ["abandon", "x", "--fields"],
        ["carry", "--fields"], ["name", "x", "head"], ["name", "--fields", "x", "head"],
        ["name", "--delete", "x", "--fields"], ["names", "x"], ["show"],
        ["-C", "old", "log"], ["-C", "future", "log"], ["-C", "layout", "log"], ["-C", "layout", "record", "--fields", "-m", "x"],
        ["-C", "noted", "log"], ["-C", "crlf", "log"], ["-C", "bare", "log"],
        ["-C", "future/deeper", "status"],
        ["skip"], ["skip", "x"], ["-C", "layout", "skip"],
        ["init"],
        # `check` describes what the others refuse, found the laxer way.
        *(["check", name] for name in ("old", "future", "layout", "noted", "crlf", "bare", "old/history", "future/deeper")),
        ["-C", "old", "check"], ["-C", "future/deeper", "check"], ["check", "old", "future"], ["check", "--complete", "layout"],
    ],
    # Who records. `identity` writing the file where the environment says
    # it goes — under `$XDG_CONFIG_HOME`, under `$HOME/.config`, nowhere —
    # and refusing to rewrite one; and every writing command, with
    # `$HISTORICA_AUTHOR` empty, reading it: a default, the deepest `under`
    # holding the repository, none for it, no file at all, and each way a
    # file is not blocks of keys and values.
    "identity": [
        ["identity"], ["identity", "a", "b"],
        ["identity", "New Person <n@example.com>"],
        ["identity", " spaced and\ttabbed "],
        [{"XDG_CONFIG_HOME": "{copy}/history/configs/default"}, "identity", "X <x@example.com>"],
        [{"XDG_CONFIG_HOME": ""}, "identity", "Home <h@example.com>"],
        [{"XDG_CONFIG_HOME": "{copy}/history/configs/"}, "identity", "Slash <s@example.com>"],
        [{"XDG_CONFIG_HOME": None, "HOME": None, "USERPROFILE": None}, "identity", "Nobody <n@example.com>"],
        [{"XDG_CONFIG_HOME": None, "HOME": None, "USERPROFILE": "{copy}/history/profile"}, "identity", "Profile <p@example.com>"],
        [{"XDG_CONFIG_HOME": "{copy}/notes.md"}, "identity", "Blocked <b@example.com>"],
        [{"HISTORICA_AUTHOR": ""}, "record", "-m", "who"],
        [{"HISTORICA_AUTHOR": ""}, "record", "-m", "who", "--fields"],
        [{"HISTORICA_AUTHOR": None}, "record", "-m", "who"],
        [{"HISTORICA_AUTHOR": "", "XDG_CONFIG_HOME": None, "HOME": None, "USERPROFILE": None}, "record", "-m", "who"],
        *([{"HISTORICA_AUTHOR": "", "XDG_CONFIG_HOME": "{copy}/history/configs/" + case}, "record", "-m", "who"]
          for case in ("default", "under", "nodefault", "twodefaults", "badkey", "nospace", "spaced", "undertwice",
                       "underlate", "authortwice", "noauthor", "sameunder", "empty", "comment", "crlf")),
        [{"HISTORICA_AUTHOR": "", "XDG_CONFIG_HOME": "{copy}/history/configs/under", "HOME": "{copy}"}, "record", "-m", "who"],
        [{"HISTORICA_AUTHOR": "", "XDG_CONFIG_HOME": "{copy}/history/configs/under", "HOME": "{copy}/sub"}, "record", "-m", "who"],
        [{"HISTORICA_AUTHOR": "", "XDG_CONFIG_HOME": "{copy}/history/configs/under", "HOME": None}, "record", "-m", "who"],
        [{"HISTORICA_AUTHOR": "", "XDG_CONFIG_HOME": "", "HOME": "{copy}/history/homes/one"}, "record", "-m", "who"],
        [{"HISTORICA_AUTHOR": "", "XDG_CONFIG_HOME": "{copy}/history/configs/default"}, "record", "-m", "who", "--fields"],
        [{"HISTORICA_AUTHOR": "", "XDG_CONFIG_HOME": "{copy}/history/configs/badkey"}, "record", "-m", "who", "--fields"],
        [{"HISTORICA_AUTHOR": "", "XDG_CONFIG_HOME": "{copy}/history/configs/default"}, "amend", "-m", "reworded"],
        [{"HISTORICA_AUTHOR": "", "XDG_CONFIG_HOME": "{copy}/history/configs/default"}, "abandon", "head", "-m", "gone"],
        [{"HISTORICA_AUTHOR": "", "XDG_CONFIG_HOME": "{copy}/history/configs/nodefault"}, "abandon", "head", "-m", "gone", "--fields"],
        [{"HISTORICA_AUTHOR": "", "XDG_CONFIG_HOME": "{copy}/history/configs/default"}, "carry", "head", "--onto", "first"],
        [{"HISTORICA_AUTHOR": ""}, "record", "-n"],
    ],
    # A message from an editor, where `record` and `abandon` are given no
    # `-m`: `$VISUAL` before `$EDITOR`, an empty one being none; the file
    # it is handed, empty, in `$TMPDIR`; the editor run in `-C`'s
    # directory, with the streams this process has; and an editor that
    # writes nothing, that fails, that takes the file away, that is not
    # there — each refused as the Rust tool refuses it, a statement owed
    # first where `--fields` asked for one.
    "editing": [
        [{"VISUAL": None, "EDITOR": "{temporary}/editors/writes"}, "record"],
        [{"VISUAL": "{temporary}/editors/writes", "EDITOR": "{temporary}/editors/fails"}, "record"],
        [{"VISUAL": "", "EDITOR": "{temporary}/editors/writes"}, "record"],
        [{"VISUAL": None, "EDITOR": ""}, "record"],
        [{"VISUAL": None, "EDITOR": None}, "record", "--fields"],
        [{"VISUAL": None, "EDITOR": "{temporary}/editors/writes"}, "record", "--fields"],
        [{"VISUAL": None, "EDITOR": "{temporary}/editors/nothing"}, "record"],
        [{"VISUAL": None, "EDITOR": "{temporary}/editors/fails"}, "record"],
        [{"VISUAL": None, "EDITOR": "{temporary}/editors/fails"}, "record", "--fields"],
        [{"VISUAL": None, "EDITOR": "{temporary}/editors/removes"}, "record"],
        [{"VISUAL": None, "EDITOR": "{temporary}/editors/killed"}, "record"],
        [{"VISUAL": None, "EDITOR": "no-such-editor"}, "record"],
        [{"VISUAL": None, "EDITOR": "{temporary}/editors/where"}, "-C", "sub", "record"],
        [{"VISUAL": None, "EDITOR": "{temporary}/editors/where", "TMPDIR": ""}, "record"],
        [{"VISUAL": None, "EDITOR": "{temporary}/editors/writes"}, "record", "-n"],
        [{"VISUAL": None, "EDITOR": "{temporary}/editors/writes"}, "abandon", "head"],
        [{"VISUAL": None, "EDITOR": "{temporary}/editors/fails"}, "abandon", "head", "--fields"],
        [{"VISUAL": None, "EDITOR": "{temporary}/editors/writes"}, "amend"],
    ],
    # `skip`: the rules listed — by path component, each rule once, the
    # platform's files and a file of comments passed over — and written, a
    # path relative to the repository whatever `-C` says, a directory as
    # one, through a link as where it leads, under a label or, where that
    # cannot be a file or is another's, under the rule's digest; and every
    # refusal: a path outside, the repository itself, space and line
    # breaks, a name that is a path or only `*`, the retired flag, and a
    # rule covering what some head holds.
    "skipping": [
        ["skip"], ["skip", "build"], ["skip", "build/"], ["skip", "--private", "out"], ["skip", "out", "--private"],
        ["skip", "--name", "*.o"], ["skip", "--name", "target/"], ["skip", "--name", "x//"], ["skip", "--name", "README.txt"],
        ["skip", "--name", ".DS_Store"], ["skip", "notes.md"], ["skip", "notes.md", "docs"], ["skip", "branch.md"],
        ["skip", "docs"], ["skip", "linkdocs"], ["skip", "--name", "*.md"], ["skip", "/etc"], ["skip", "."], ["skip", ""],
        ["skip", " x"], ["skip", "a\nb"], ["skip", "a\tb"], ["skip", "--name", "a\nb"], ["skip", "--suffix", ".o"],
        ["skip", "--bogus"], ["skip", "/etc", "--bogus"], ["skip", "--bogus", "/etc"], ["skip", "--name"],
        ["skip", "--name", "a/b"], ["skip", "--name", "**"], ["skip", "--name", ""], ["skip", "x", "x"],
        ["skip", "../outside"], ["skip", "build/../zz"], ["skip", "README"], ["skip", "all", "x/all"],
        ["skip", "{copy}/new.o"], ["skip", "{copy}"], ["-C", "docs", "skip", "x"], ["-C", "docs", "skip"],
        ["skip", "tmp", "--name", "*.tmp", "--private", "buildfile"], ["skip", "--name", "*.tmp"],
    ],
    # A rule file stating two rules: the store will not open.
    # And each writing command asked for `--fields`: the statement, then
    # the refusal (decision 0074).
    "badskip": [["diff"], ["blame", "notes.md"], ["log"], ["files", "head"], ["cat", "head", "kept.md"], ["show", "head"], ["names"], ["status"], ["record", "-n"], ["skip"], ["skip", "x"],
                ["record", "--fields", "-m", "x"], ["amend", "--fields", "-m", "y"], ["abandon", "head", "--fields", "-m", "z"], ["carry", "--fields"], ["name", "--fields", "x", "head"]],
    # Nothing recorded yet: every file is the folder's own.
    "fresh": [
        ["diff"], ["blame", "a.md"], ["blame", "file:a"], ["diff", "file:a"], ["status"],
        ["record", "--dry-run"], ["record", "-n", "a.md"], ["record", "-n", "--lines", "b.bin"],
        ["record", "-n", "--bytes", "a.md", "--lines", "a.md"], ["record", "-n", "--onto", "head"],
        ["record", "-n", "--move", "a.md=c.md"],
        ["record", "-m", "a root"],
        ["record", "-m", "a root", "--fields"],
        ["record", "-m", "a root", "b.bin"],
        ["record", "-m", "a root", "--bytes", "a.md"],
        ["name", "x", "head"],
        ["name", "--fields", "x", "head"],
        ["init"],
        ["init", "."],
        ["init", "history"],
    ],
    # A file recorded as lines that is no longer text.
    "notext": [["diff"], ["diff", "kept.md"], ["blame", "notes.md"], ["status"], ["record", "-n"], ["record", "-n", "kept.md"]],
    # What `status` says of a folder: files moved with `mv`, of lines and of
    # bytes, one to one and not; empty files, which match nothing; links
    # spelled differently to the same file, pointing at an arrival, at a
    # file going, at an absolute path, and at `file:`; names the format
    # cannot hold, a target that is not UTF-8, and a pipe.
    # And a file added empty, which every reader takes as no lines at all.
    "surveyed": [
        ["status"], ["status", "--onto", "first"], ["diff"], ["diff", "first"], ["cat", "first", "empty.md"], ["blame", "first", "empty.md"],
        # Everything the folder cannot take stops a record, unless the
        # record is not looking at it.
        ["record", "-n"],
        ["record", "-n", "ref", "ref2", "abs", "to-arrival", "renamed.md"],
        ["record", "-n", "bad-link"],
        ["record", "-n", "sub", "run-new.sh", "empty.md", "fresh-empty.md"],
        ["record", "-n", "a.md", "renamed.md", "--move", "a.md=renamed.md"],
        ["record", "-n", "b.bin", "moved.bin", "to-bin", "--move", "b.bin=moved.bin"],
        ["record", "-n", "target.md"],
    ],
    # A rule skipping a file the position holds: `status` refuses.
    "skipheld": [["status"], ["diff"], ["record", "-n"], ["record", "-n", "kept.md"]],
    # Two lines of work from one base, being joined: a file both moved, bytes
    # both changed, a file one dropped and the other edited, a link each
    # pointed elsewhere, a mode one changed, and a file both edited — which
    # the folder resolves, so a merge owes it — beside one both left alone.
    "joining": [
        ["record", "-n", "--onto", "left", "--merge", "right"],
        ["record", "-n", "--merge", "right"],
        ["record", "-n", "--merge", "right", "a.md"],
        ["record", "-n", "--onto", "left", "a.md"],
        ["record", "-n", "--onto", "right"],
        ["status", "--onto", "left", "--merge", "right"],
        ["status", "--merge", "left", "--merge", "right"],
        ["status", "--merge", "right", "--onto", "left"],
        ["status", "--merge", "right"],
        ["status", "--onto", "left", "--merge", "left"],
        ["status", "--onto", "left"],
        ["status", "--onto", "right"],
        ["status", "--merge", "base", "--merge", "left"],
    ],

    # Two lines of work that each added a file at one path, and each wrote
    # different bytes to one file: a merge of them has to say where each
    # goes and which bytes it keeps. And a link to a file the folder no
    # longer holds, for a record that is not looking at the link.
    "claimed": [
        ["record", "-n", "--onto", "left", "--merge", "right"],
        ["record", "-n", "--onto", "left", "--merge", "right", "--at", "lx=x.md"],
        ["record", "-n", "--onto", "left", "--merge", "right", "--at", "lx=x.md", "--at", "rx=x-right.md"],
        ["record", "-n", "--onto", "left", "--merge", "right", "--at", "lx=x.md", "--at", "rx=x-right.md", "--accept", "c.bin"],
        ["record", "-n", "--onto", "left", "--merge", "right", "--at", "lx=x.md", "--at", "rx=x-right.md", "--accept", "c.bin", "--accept", "a.md"],
        ["record", "-n", "--onto", "left", "--merge", "right", "--at", "lx=x.md", "--at", "rx=x-right.md", "--accept", "a.md", "--accept", "t.md"],
        ["record", "-n", "--onto", "left", "--merge", "right", "--move", "x.md=y.md"],
        ["record", "-n", "--onto", "left", "--at", "rx=x.md"],
        ["record", "-n", "--onto", "left", "--at", "left=x.md"],
        ["record", "-n", "--onto", "left", "t.md"],
        ["record", "-n", "--onto", "left", "t.md", "lnk"],
        ["record", "-n", "--onto", "left", "--move", "t.md=u.md"],
        ["record", "-n"],
        ["status", "--onto", "left", "--merge", "right"],
    ],
    # Two merges the Rust tool resolved, the first by hand: resolutions that
    # keep a payload's lines, an operation document's inserts and an earlier
    # resolution's, and insert their own — and a merge written here for each
    # way a resolution can fail to assemble or to parse.
    "merge": [
        *(["cat", target, path] for target in ("left", "m1", "after", "m2") for path in ("f.md", "h.md")),
        *(["cat", target, "f.md"] for target in ("unknown", "range", "result", "notlast", "adjacent", "positioned")),
        ["diff", "m1"],
        ["diff", "m1", "--onto", "left"],
        ["diff", "m2", "--onto", "x", "f.md"],
        *(["blame", target, path] for target in ("m1", "m2") for path in ("f.md", "h.md")),
    ],
    # Merges that state no resolution, written by hand as the Rust tool
    # never would: where decision 0032's rule stops, and the file is what
    # `merge.bend`'s proven walk reads. Two branches edit apart, and one
    # deletes beside the other's insert; two insert at one place, so the
    # digests break the tie; a third merge joins all three; and `after` is
    # recorded on top of one, so its edit counts into the walked file; and
    # a merge joining a resolution with an edit concurrent with it.
    "walked": [
        *(["cat", target, path] for target in ("joined", "tops", "all", "after") for path in ("f.md", "g.md")),
        *(["blame", target, path] for target in ("joined", "tops", "all", "after") for path in ("f.md", "g.md")),
        ["diff", "joined", "--onto", "left"],
        ["diff", "joined", "--onto", "right"],
        ["diff", "after"],
        ["diff", "after", "g.md"],
        *(["cat", target, path] for target in ("resolved", "crossed") for path in ("f.md", "g.md")),
        *(["blame", target, path] for target in ("resolved", "side", "crossed") for path in ("f.md", "g.md")),
        ["diff", "crossed", "--onto", "side"],
        ["status", "--onto", "after", "--merge", "crossed"],
        ["status", "--merge", "tops", "--merge", "all"],
    ],
    # What `check` exists to find, each store built by the Rust tool and then
    # damaged: files nothing reads, a revision stored twice and under a
    # digest it does not hash to, a parent that never arrived; documents
    # and payloads gone, and a payload's bytes replaced; a line forgotten and
    # a document written by hand against a view its author did not have;
    # and a corpus's forgotten payload beside the forgetting documents that
    # do not parse.
    "damaged": [],
    "gutted": [],
    "tampered": [],
    "forgotten": [],
}

# Every store checked, and asked whether it is complete.
for commands in STORES.values():
    commands += [["check"], ["check", "--complete"]]


def join(history, name, parents, change):
    """A merge of `parents` that says nothing about any file.

    Its parents disagree about every file both edited, so the file there is
    the walk's. Pinned by a bookmark, as `craft`'s merges are.
    """
    digest = lambda data: hashlib.sha256(data).hexdigest()
    named = {n.stem: n.read_text().split()[1] for n in (history / "names").glob("*.txt")}
    text = (
        f"historica\nchange {change}\n"
        + "".join(f"parent {p}\n" for p in sorted(named[p] for p in parents))
        + "author Check <check@example.com>\nwhen 2026-09-23T12:00:00+00:00\n\n"
        + f"joined {' and '.join(parents)}, resolving nothing"
    )
    (history / "revisions" / "crafted").mkdir(exist_ok=True)
    (history / "revisions" / "crafted" / f"{name}.rev.txt").write_text(text)
    (history / "names" / f"{name}.txt").write_text(f"revision {digest(text.encode())}\n")


def craft(history):
    """Merges like `m1`, each naming a resolution of `f.md` broken one way.

    Written by hand, as the Rust tool never would: a revision is its bytes'
    digest, so each is a new revision beside `m1`, pinned by a bookmark.
    """
    digest = lambda data: hashlib.sha256(data).hexdigest()
    m1 = (history / "names" / "m1.txt").read_text().split()[1]
    revision = next(p for p in history.glob("revisions/**/*.rev.txt") if digest(p.read_bytes()) == m1)
    text = revision.read_text()
    documents = {digest(p.read_bytes()): p for p in history.glob("operations/**/*") if p.is_file()}
    file, named = next(
        (f, d) for f, d in re.findall(r"^edit (\S+) ([0-9a-f]{64})$", text, re.M) if b"+BOTH" in documents[d].read_bytes()
    )
    resolution = documents[named].read_text()
    kept = re.search(r"^keep (\S+) 0 1$", resolution, re.M).group(1)
    broken = {
        "unknown": resolution.replace(f"keep {kept} 0 1", "keep " + "a" * 64 + " 0 1", 1),
        "range": resolution.replace(" 2 2\n", " 2 9\n"),
        "result": re.sub(r"^result \S+", "result " + "b" * 64, resolution, flags=re.M),
        "notlast": resolution.replace("+BOTH\n", "+BOTH\n\\ no newline\n"),
        "adjacent": resolution.replace("+BOTH\n", "+BOTH\ninsert\n+MORE\n"),
        "positioned": resolution.replace("insert\n", "insert 1\n"),
    }
    (history / "operations" / "crafted").mkdir()
    (history / "revisions" / "crafted").mkdir()
    for name, body in broken.items():
        (history / "operations" / "crafted" / f"{name}.ops.txt").write_text(body)
        stated = text.replace(f"edit {file} {named}", f"edit {file} {digest(body.encode())}")
        stated = stated.replace("resolved by hand", f"crafted: {name}")
        (history / "revisions" / "crafted" / f"{name}.rev.txt").write_text(stated)
        (history / "names" / f"{name}.txt").write_text(f"revision {digest(stated.encode())}\n")


def record(temporary, rust, corpus, pinned=None):
    store = temporary / f"store-{corpus}"
    home = temporary / f"home-{corpus}"
    env = {**os.environ, "HOME": str(home), "XDG_CONFIG_HOME": str(home / ".config")}

    def historica(*command):
        subprocess.run([rust, *command], cwd=store, env=env, check=True, capture_output=True, timeout=120)

    store.mkdir(parents=True)
    if corpus == "bare":
        # No store at all: a folder with a file in it, and a file where a
        # directory would have to be made.
        (store / "notes.md").write_text("notes\n")
        (store / "taken").write_text("a file\n")
        return store
    if corpus == "headless":
        # A `history` directory and nothing in it; and beside it stores
        # whose header this reader does not read, each a store in every
        # other respect.
        (store / "history").mkdir()
        (store / "a.md").write_text("a\n")
        for name, header in (("old", "historica-v3\n"), ("future", "historica-v9\n\nnote\n"), ("layout", "historica\nuses: something\n"),
                             ("noted", "historica\n\nuses: nothing, a note\n"), ("crlf", "historica\r\n\r\n"), ("bare", "historica")):
            subprocess.run([rust, "init", name], cwd=store, env=env, check=True, capture_output=True, timeout=120)
            (store / name / "history" / "historica.txt").write_text(header)
            (store / name / "deeper").mkdir()
        return store
    historica("init", ".")
    historica("identity", "Check <check@example.com>")
    if corpus == "unicode":
        (store / "café").mkdir()
        (store / "café" / "naïve résumé.md").write_text("an accent\n")
        (store / "notes.md").write_text("plain\n")
        historica("record", "-m", "one")
    elif corpus == "merge":
        pinned = {}

        def rec(name, *command):
            done = subprocess.run([rust, "record", *command], cwd=store, env=env, check=True, capture_output=True, text=True, timeout=120)
            digest = re.search(r"^recorded [a-z]+ as ([0-9a-f]+)", done.stdout, re.M).group(1)
            historica("name", name, digest, "--revision")

        def write(**files):
            for path, text in files.items():
                (store / f"{path}.md").write_text(text)

        write(f="a\nb\nc\nd", h="one\n")
        rec("base", "-m", "base")
        write(f="a\nLEFT\nc\nd", h="one\nleft h\n")
        rec("left", "-m", "left")
        write(f="a\nRIGHT\nc\nd", h="one\nright h\n")
        rec("right", "--onto", "base", "-m", "right")
        write(f="a\nBOTH\nc\nd", h="one\nleft h\nright h\n")
        rec("m1", "--merge", "left", "--merge", "right", "-m", "resolved by hand")
        write(f="a\nBOTH\nc\nd\ne\n")
        rec("after", "-m", "after the merge")
        write(f="a\nBOTH\nc\nd\ne\nx\n")
        rec("x", "-m", "x")
        write(f="z\na\nBOTH\nc\nd\ne\n")
        rec("z", "--onto", "after", "-m", "z")
        write(f="z\na\nBOTH\nc\nd\ne\nx\n")
        rec("m2", "--merge", "x", "--merge", "z", "-m", "second merge")
        craft(store / "history")
    elif corpus == "walked":
        def rec(name, *command):
            done = subprocess.run([rust, "record", *command], cwd=store, env=env, check=True, capture_output=True, text=True, timeout=120)
            digest = re.search(r"^recorded [a-z]+ as ([0-9a-f]+)", done.stdout, re.M).group(1)
            historica("name", name, digest, "--revision")

        def write(**files):
            for path, text in files.items():
                (store / f"{path}.md").write_text(text)

        write(f="a\nb\nc\nd\n", g="one\n")
        rec("base", "-m", "base")
        write(f="top\na\nc\nd\n", g="one\nleft g\n")
        rec("left", "-m", "left")
        write(f="a\nb\nB2\nc\nd\nbottom\n", g="one\nright g\n")
        rec("right", "--onto", "base", "-m", "right")
        write(f="also top\na\nb\nc\nd\n", g="one\n")
        rec("third", "--onto", "base", "-m", "third")
        join(store / "history", "joined", ("left", "right"), "k" * 24)
        join(store / "history", "tops", ("left", "third"), "l" * 24)
        join(store / "history", "all", ("joined", "third"), "m" * 24)
        write(f="top\na\nB2\nc\nd\nbottom\nafter\n", g="one\nleft g\nright g\n")
        rec("after", "--onto", "joined", "-m", "after")
        # A merge the Rust tool resolves, and an edit concurrent with it of a
        # line it kept: joined, the walk crosses the resolution, and the
        # edit lands on the kept element, since it kept its name.
        write(f="top\na\nc\nd\nbottom\nresolved\n", g="one\nleft g\nright g\n")
        rec("resolved", "--merge", "left", "--merge", "right", "-m", "resolved")
        write(f="top\na\nC\nd\n", g="one\nleft g\nside g\n")
        rec("side", "--onto", "left", "-m", "side")
        join(store / "history", "crossed", ("resolved", "side"), "p" * 24)
    elif corpus == "log":
        (store / "notes.md").write_text("one\n")
        historica("record", "-m", "first: notes")
        (store / "notes.md").write_text("one\ntwo\n")
        (store / "other.md").write_text("x\n")
        historica("record", "-m", "second, with other")
        env["HISTORICA_AUTHOR"] = "Bob <bob@example.com>"
        (store / "notes.md").rename(store / "renamed.md")
        historica("record", "--move", "notes.md=renamed.md", "-m", "rename notes")
        historica("name", "base", "head", "--revision")
        (store / "renamed.md").write_text("one\ntwo\nthree\n")
        historica("record", "-m", "third by bob")
        del env["HISTORICA_AUTHOR"]
        (store / "other.md").write_text("x\ny\n")
        historica("record", "-m", "other again")
        historica("name", "tip", "head", "--revision")
        (store / "side.md").write_text("side\n")
        historica("record", "--onto", "base", "-m", "a side line")
    elif corpus in ("folder", "badskip", "notext"):
        (store / "notes.md").write_text("one\ntwo\nthree\nfour\n")
        (store / "kept.md").write_text("kept\n")
        (store / "gone.md").write_text("going\n")
        (store / "data.bin").write_bytes(b"\x00\x01bytes")
        (store / "run.sh").write_text("#!/bin/sh\n")
        (store / "target.md").write_text("pointed at\n")
        os.symlink("target.md", store / "current")
        os.symlink("kept.md", store / "was-link")
        os.symlink("gone.md", store / "removed-link")
        historica("record", "-m", "one")
        historica("name", "first", "head", "--revision")
        (store / "notes.md").write_text("one\n2\nthree\nfour\nfive\n")
        historica("record", "-m", "two")
        historica("name", "nb", "head", "notes.md")
        historica("skip", "build/")
        historica("skip", "--name", "*.tmp")
        historica("skip", "--private", "secret.md")
        historica("skip", "--name", "cache/")
        # A rule filed in a folder of its own, and a note stating none.
        (store / "history" / "skipped" / "grouped").mkdir()
        (store / "history" / "skipped" / "grouped" / "logs.txt").write_text("# the logs\n\nskip logs/\n")
        (store / "history" / "skipped" / "grouped" / ".DS_Store").write_bytes(b"\x00")
        (store / "notes.md").write_text("zero\none\ntwo, then — café\nthree\nfour v2\nfive\nsix\n")
        (store / "gone.md").unlink()
        (store / "new.md").write_text("brand\nnew\n")
        (store / "photo.bin").write_bytes(b"\x89PNG\x00\x00")
        (store / "data.bin").write_bytes(b"\x00\x02more bytes")
        (store / "run.sh").chmod(0o755)
        os.remove(store / "current")
        os.symlink("new.md", store / "current")
        os.remove(store / "was-link")
        (store / "was-link").write_text("now a file\n")
        os.remove(store / "removed-link")
        os.symlink("kept.md", store / "new-link")
        for skipped in ("build/out.md", "deep/scratch.tmp", "secret.md", "a/cache/x.md", "logs/today.md"):
            (store / skipped).parent.mkdir(parents=True, exist_ok=True)
            (store / skipped).write_text("not taken\n")
        (store / "deep" / "kept.txt").write_text("taken\n")
        (store / "cache").write_text("a file, which a directory's name does not cover\n")
        if corpus == "badskip":
            (store / "history" / "skipped" / "two.txt").write_text("skip a\nskip b\n")
        if corpus == "notext":
            (store / "notes.md").write_bytes(b"one\n\xff\xfe\n")
    elif corpus == "surveyed":
        (store / "a.md").write_text("alpha\nbeta\n")
        (store / "b.bin").write_bytes(b"\x00bin")
        (store / "twin1.md").write_text("same\n")
        (store / "twin2.md").write_text("same\n")
        (store / "empty.md").write_text("")
        (store / "edited.md").write_text("one\n")
        (store / "target.md").write_text("pointed at\n")
        (store / "sub").mkdir()
        (store / "sub" / "deep.md").write_text("deep\n")
        os.symlink("target.md", store / "ref")
        os.symlink("sub/deep.md", store / "ref2")
        os.symlink("/etc/hosts", store / "abs")
        os.symlink("b.bin", store / "to-bin")
        historica("record", "-m", "one")
        historica("name", "first", "head", "--revision")
        (store / "edited.md").write_text("one\ntwo\n")
        (store / "a.md").write_text("alpha\nbeta\ngamma\n")
        historica("record", "-m", "two")
        os.rename(store / "a.md", store / "renamed.md")
        os.rename(store / "b.bin", store / "moved.bin")
        (store / "twin1.md").unlink()
        (store / "twin2.md").unlink()
        (store / "twin-new.md").write_text("same\n")
        (store / "empty.md").unlink()
        (store / "fresh-empty.md").write_text("")
        (store / "edited.md").write_text("one\ntwo\nthree\n")
        os.remove(store / "ref")
        os.symlink("./target.md", store / "ref")
        os.remove(store / "ref2")
        os.symlink("sub/../sub/deep.md", store / "ref2")
        os.remove(store / "abs")
        os.symlink("/etc/passwd", store / "abs")
        os.symlink("renamed.md", store / "to-arrival")
        os.symlink("file:x", store / "bad-link")
        os.symlink(b"\xff", os.fsencode(store / "unreadable-link"))
        (store / "trailing .md").write_text("a space at the end\n")
        (store / "bell\x07.md").write_text("a control character\n")
        (store / "d ").mkdir()
        (store / "d " / "x.md").write_text("a space inside\n")
        os.mkfifo(store / "pipe")
        (store / "run-new.sh").write_text("#!/bin/sh\n")
        (store / "run-new.sh").chmod(0o755)
        (store / "sub" / "deep.md").chmod(0o755)
    elif corpus == "joining":
        (store / "a.md").write_text("one\ntwo\n")
        (store / "b.md").write_text("bee\n")
        (store / "c.bin").write_bytes(b"\x00base")
        (store / "run.sh").write_text("#!/bin/sh\n")
        (store / "gone.md").write_text("going\n")
        (store / "same.md").write_text("same\n")
        (store / "empty-me.md").write_text("both\n")
        os.symlink("a.md", store / "lnk")
        historica("record", "-m", "base")
        historica("name", "base", "head", "--revision")
        (store / "a.md").write_text("one\ntwo\nleft\n")
        (store / "empty-me.md").write_text("both\nleft\n")
        (store / "b.md").rename(store / "b-left.md")
        (store / "c.bin").write_bytes(b"\x00left")
        (store / "run.sh").chmod(0o755)
        (store / "gone.md").unlink()
        os.remove(store / "lnk")
        os.symlink("same.md", store / "lnk")
        historica("record", "--move", "b.md=b-left.md", "-m", "left")
        historica("name", "left", "head", "--revision")
        (store / "a.md").write_text("right\none\ntwo\n")
        (store / "empty-me.md").write_text("right\nboth\n")
        (store / "b-left.md").rename(store / "b-right.md")
        (store / "c.bin").write_bytes(b"\x00right")
        (store / "run.sh").chmod(0o644)
        (store / "gone.md").write_text("going\nstill\n")
        os.remove(store / "lnk")
        os.symlink("b-right.md", store / "lnk")
        historica("record", "--onto", "base", "--move", "b.md=b-right.md", "-m", "right")
        fields = subprocess.run([rust, "log", "--fields"], cwd=store, env=env, check=True, capture_output=True, text=True).stdout
        left = (store / "history" / "names" / "left.txt").read_text().split()[1]
        right = next(line.split()[0] for line in fields.splitlines()[1:] if "head" in line.split()[3] and line.split()[0] != left)
        historica("name", "right", right, "--revision")
        (store / "a.md").write_text("right\none\ntwo\nleft\n")
        (store / "empty-me.md").write_text("")
        (store / "new.md").write_text("new\n")
    elif corpus == "claimed":
        (store / "a.md").write_text("a\n")
        (store / "c.bin").write_bytes(b"\x00base")
        (store / "t.md").write_text("pointed at\n")
        os.symlink("t.md", store / "lnk")
        historica("record", "-m", "base")
        historica("name", "base", "head", "--revision")
        (store / "x.md").write_text("left x\n")
        (store / "c.bin").write_bytes(b"\x00left")
        historica("record", "-m", "left")
        historica("name", "left", "head", "--revision")
        historica("name", "lx", "head", "x.md")
        (store / "x.md").write_text("right x\n")
        (store / "c.bin").write_bytes(b"\x00right")
        historica("record", "--onto", "base", "-m", "right")
        fields = subprocess.run([rust, "log", "--fields"], cwd=store, env=env, check=True, capture_output=True, text=True).stdout
        left = (store / "history" / "names" / "left.txt").read_text().split()[1]
        right = next(line.split()[0] for line in fields.splitlines()[1:] if "head" in line.split()[3] and line.split()[0] != left)
        historica("name", "right", right, "--revision")
        historica("name", "rx", right, "x.md")
        (store / "x.md").write_text("both x\n")
        (store / "t.md").unlink()
    elif corpus == "skipheld":
        (store / "kept.md").write_text("kept\n")
        (store / "private.md").write_text("private\n")
        (store / "also.md").write_text("also\n")
        historica("record", "-m", "one")
        (store / "history" / "skipped").mkdir(exist_ok=True)
        (store / "history" / "skipped" / "private.txt").write_text("skip private.md\n")
        (store / "history" / "skipped" / "also.txt").write_text("skip also.md\n")
    elif corpus == "recording":
        # Recorded by the pinned build, early the same day `PINS` says it is
        # now, so the store's one revision is the same bytes every run.
        def pin(*command):
            early = {**env, "HISTORICA_AUTHOR": "Check <check@example.com>", "HISTORICA_PINNED_NOW": "2026-03-04T05:06:07+00:00", "HISTORICA_PINNED_SEED": "fixture"}
            subprocess.run([pinned, *command], cwd=store, env=early, check=True, capture_output=True, timeout=120)

        (store / "notes.md").write_text("one\ntwo\nthree\n")
        (store / "old.md").write_text("old\n")
        (store / "same.md").write_text("shared text\n")
        (store / "photo.bin").write_bytes(b"\x89PNG\x00\x01")
        (store / "run.sh").write_text("#!/bin/sh\n")
        (store / "run.sh").chmod(0o755)
        (store / "unchanged.md").write_text("still\n")
        (store / "going.md").write_text("bye\n")
        os.symlink("notes.md", store / "to-notes")
        pin("record", "-m", "the first")
        historica("name", "first", "head", "--revision")
        historica("name", "main", "head")
        historica("name", "mine", "head", "--private")
        # And the folder moves on.
        (store / "notes.md").write_text("one\n2\nthree\nfour\n")
        (store / "photo.bin").write_bytes(b"\x89PNG\x00\x02")
        (store / "run.sh").chmod(0o644)
        (store / "going.md").unlink()
        (store / "new.md").write_text("brand new\n")
        (store / "copy.md").write_text("shared text\n")
        (store / "twin-a.md").write_text("twins\n")
        (store / "twin-b.md").write_text("twins\n")
        (store / "blob.bin").write_bytes(b"\x00\x00\x01")
        (store / "empty.md").write_text("")
        (store / "tool.sh").write_text("#!/bin/sh\necho\n")
        (store / "tool.sh").chmod(0o755)
        (store / "odd.ops.txt").write_text("not a document\n")
        (store / "sub").mkdir()
        (store / "sub" / "deep.md").write_text("deep\n")
        os.symlink("new.md", store / "to-new")
        os.symlink("/etc/hosts", store / "abs-link")
        (store / "to-notes").unlink()
        os.symlink("old.md", store / "to-notes")
    elif corpus in ("rewriting", "stranded"):
        # A line of work and two lines beside it, recorded by the pinned
        # build: `f.md` edited at its top, its bottom and its end along the
        # line, in its middle on one side and at its top on the other.
        def pin(now, seed, *command):
            at = {**env, "HISTORICA_AUTHOR": "Check <check@example.com>", "HISTORICA_PINNED_NOW": now, "HISTORICA_PINNED_SEED": seed}
            done = subprocess.run([pinned, *command], cwd=store, env=at, check=True, capture_output=True, text=True, timeout=120)
            return done.stdout

        def rec(name, now, seed, *command):
            said = pin(now, seed, "record", *command)
            historica("name", name, re.search(r"^recorded [a-z]+ as ([0-9a-f]+)", said, re.M).group(1), "--revision")

        def write(**files):
            for name, text in files.items():
                (store / f"{name}.md").write_text(text)

        write(f="a\nb\nc\nd\ne\nf\ng\nh\n", g="one\n")
        (store / "p.bin").write_bytes(b"\x00x")
        rec("base", "2026-03-01T10:00:00+00:00", "s1", "-m", "base")
        historica("name", "main", "head")
        write(f="A\nb\nc\nd\ne\nf\ng\nh\n")
        rec("top", "2026-03-02T10:00:00+00:00", "s2", "-m", "top")
        write(f="A\nb\nc\nd\ne\nf\ng\nH\n", g="one\ntwo\n")
        rec("bottom", "2026-03-03T10:00:00+00:00", "s3", "-m", "bottom")
        write(f="A\nb\nc\nd\ne\nf\ng\nH\nnew\n", n="n\n")
        rec("tip", "2026-03-04T10:00:00+00:00", "s4", "-m", "tip")
        write(f="a\nb\nc\nMID\ne\nf\ng\nh\n", g="one\n")
        (store / "n.md").unlink()
        rec("middle", "2026-03-05T10:00:00+00:00", "s5", "--onto", "base", "-m", "middle")
        write(f="Z\nb\nc\nd\ne\nf\ng\nh\n")
        rec("side", "2026-03-05T11:00:00+00:00", "s6", "--onto", "base", "-m", "side")
        # The folder as the tip left it, and moved on.
        write(f="A\nb\nc\nd\ne\nf\ng\nH\nnew\nmore\n", g="one\ntwo\n", n="n\n", extra="extra\n")
        if corpus == "stranded":
            # A rewrite that arrived without the carries it forced: `top`
            # abandoned alone elsewhere, and only its tombstone copied here —
            # the state `carry` with no target repairs.
            elsewhere = temporary / "stranded-elsewhere"
            shutil.copytree(store, elsewhere, symlinks=True)
            at = {**env, "HISTORICA_AUTHOR": "Check <check@example.com>", "HISTORICA_PINNED_NOW": "2026-03-06T10:00:00+00:00", "HISTORICA_PINNED_SEED": "s7"}
            subprocess.run([pinned, "abandon", "top", "--only", "-m", "gone"], cwd=elsewhere, env=at, check=True, capture_output=True, timeout=120)
            top = (store / "history" / "names" / "top.txt").read_text().split()[1]
            for path in (elsewhere / "history" / "revisions").rglob("*.rev.txt"):
                if f"\nsupersedes {top}\n" in path.read_text():
                    tombstone = store / "history" / "revisions" / path.relative_to(elsewhere / "history" / "revisions")
                    tombstone.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copy(path, tombstone)
            shutil.rmtree(elsewhere)
    elif corpus == "identity":
        (store / "notes.md").write_text("one\n")
        historica("record", "-m", "one")
        historica("name", "first", "head", "--revision")
        (store / "notes.md").write_text("one\ntwo\n")
        historica("record", "-m", "two")
        (store / "notes.md").write_text("one\ntwo\nthree\n")
        (store / "sub").mkdir()
        configs = {
            "default": "author Default Person <d@example.com>\n",
            "under": "author Default Person <d@example.com>\n\nunder ~/elsewhere/\nauthor Elsewhere <e@example.com>\n\n"
                     "under ~\nauthor Here <h@example.com>\n\nunder ~/sub\nauthor Below <b@example.com>\n",
            "nodefault": "under /nowhere/at/all\nauthor Elsewhere <e@example.com>\n",
            "twodefaults": "author A <a@example.com>\n\nauthor B <b@example.com>\n",
            "badkey": "author A <a@example.com>\nemail a@example.com\n",
            "nospace": "author\n",
            "spaced": "author  A <a@example.com>\n",
            "undertwice": "under /a\nunder /b\nauthor A <a@example.com>\n",
            "underlate": "author A <a@example.com>\nunder /a\n",
            "authortwice": "author A <a@example.com>\nauthor B <b@example.com>\n",
            "noauthor": "author A <a@example.com>\n\n\nunder /a\n",
            "sameunder": "under /a/\nauthor A <a@example.com>\n\nunder /a\nauthor B <b@example.com>\n",
            "empty": "",
            "comment": "# who I am\nauthor A <a@example.com>\n",
            "crlf": "author Carriage <c@example.com>\r\n",
        }
        for case, text in configs.items():
            (store / "history" / "configs" / case / "historica").mkdir(parents=True)
            (store / "history" / "configs" / case / "historica" / "identity").write_text(text)
        (store / "history" / "homes" / "one" / ".config" / "historica").mkdir(parents=True)
        (store / "history" / "homes" / "one" / ".config" / "historica" / "identity").write_text("author From Home <h@example.com>\n")
    elif corpus == "editing":
        (store / "notes.md").write_text("one\n")
        historica("record", "-m", "one")
        (store / "notes.md").write_text("one\ntwo\n")
        (store / "sub").mkdir()
        (store / "history" / "tmp").mkdir()
    elif corpus == "skipping":
        (store / "notes.md").write_text("one\n")
        (store / "docs").mkdir()
        (store / "docs" / "a.md").write_text("a\n")
        (store / "build").mkdir()
        (store / "build" / "out.o").write_text("o\n")
        os.symlink("docs", store / "linkdocs")
        historica("record", "-m", "one", "notes.md", "docs")
        historica("name", "first", "head", "--revision")
        (store / "branch.md").write_text("b\n")
        historica("record", "-m", "beside", "branch.md")
        (store / "branch.md").unlink()
        (store / "notes.md").write_text("one\nother\n")
        historica("record", "--onto", "first", "-m", "the other head", "notes.md")
        historica("skip", "build/")
        historica("skip", "--private", "--name", "*.tmp")
        skipped = store / "history" / "skipped"
        (skipped / "zz-dup.txt").write_text("skip build/\n")
        (skipped / "comment.txt").write_text("# nothing said\n")
        (skipped / ".DS_Store").write_text("skip notes.md\n")
        (skipped / "a").mkdir()
        (skipped / "a" / "b.txt").write_text("private build/\n")
        (skipped / "build.txt").write_text("skip buildfile\n")
        (skipped / "build-c.txt").write_text("skip b-c\n")
    elif corpus == "shell":
        (store / "notes.md").write_text("one\n")
        historica("record", "-m", "one")
        (store / "sub").mkdir()
        (store / "sub" / "deep.md").write_text("deep\n")
        historica("record", "-m", "two")
    elif corpus in ("damaged", "gutted"):
        # A store as `check` exists to find it: two revisions and a
        # forgotten payload, then what a hand, a sync or a disk did to it.
        (store / "notes.md").write_text("one\n")
        (store / "photo.bin").write_bytes(b"\x89PNG\x00one")
        (store / "kept.md").write_text("kept\n")
        historica("record", "-m", "one")
        historica("name", "first", "head", "--revision")
        (store / "notes.md").write_text("one\ntwo\n")
        (store / "photo.bin").write_bytes(b"\x89PNG\x00two")
        (store / "kept.md").write_text("kept\nmore\n")
        historica("record", "-m", "two")
        historica("forget", "first", "photo.bin")
        history = store / "history"
        one, two = (next(history.glob(f"revisions/*/* {m}.rev.txt")) for m in ("one", "two"))
        operations = lambda m: next(history.glob(f"operations/*/* {m}"))
        if corpus == "damaged":
            # What sits in the directories without being read: a file with
            # no suffix, a link, a payload nothing names; one revision
            # stored twice, once under a digest it does not hash to; and a
            # revision whose parent never arrived.
            (history / "revisions" / "notes.txt").write_text("a note\n")
            os.symlink(one.name, one.parent / "linked.rev.txt")
            (operations("two") / "stray.bin").write_bytes(b"\x00stray")
            shutil.copy(two, two.parent / ("a" * 64 + ".rev.txt"))
            (history / "revisions" / "orphan.rev.txt").write_text(
                "historica\nchange " + "m" * 24 + "\nparent " + "b" * 64 + "\n"
                "author Check <check@example.com>\nwhen 2026-09-23T12:00:00+00:00\n\nan orphan"
            )
        else:
            # What went missing: an operation document and a payload the
            # head names, and a text payload's bytes replaced by some that
            # are not text.
            (operations("two") / "kept.md.ops.txt").unlink()
            (operations("two") / "photo.bin").unlink()
            (operations("one") / "notes.md").write_bytes(b"one\n\xff\n")
    elif corpus == "tampered":
        # A line forgotten, so every head is read by the walk rather than
        # by arithmetic; and on top, written by hand, a revision whose
        # document deletes a line its author's view did not hold there.
        (store / "notes.md").write_text("one\n")
        historica("record", "-m", "one")
        (store / "notes.md").write_text("one\ntwo\n")
        historica("record", "-m", "two")
        historica("forget", "head", "notes.md", "--lines", "2..2")
        digest = lambda data: hashlib.sha256(data).hexdigest()
        history = store / "history"
        two = next(history.glob("revisions/*/* two.rev.txt"))
        file = re.search(r"^edit (\S+) ", two.read_text(), re.M).group(1)
        document = f"historica\nresult {digest(b'two')}\n\ndelete 0 1\n-WRONG\n"
        (history / "operations" / "crafted.ops.txt").write_text(document)
        (history / "revisions" / "crafted.rev.txt").write_text(
            f"historica\nchange {'m' * 24}\nparent {digest(two.read_bytes())}\nauthor Check <check@example.com>\n"
            f"when 2026-09-25T12:00:00+00:00\nedit {file} {digest(document.encode())}\n\nthree"
        )
    elif corpus == "fresh":
        (store / "a.md").write_text("only\nthe folder\n")
        (store / "b.bin").write_bytes(b"\x00")
    else:
        (store / "notes.md").write_text("one\n")
        historica("record", "-m", "one")
        historica("name", "first", "head", "--revision")
        (store / "notes.md").write_text("one\ntwo\n")
        historica("record", "-m", "two")
        historica("name", "main", "head")
        historica("name", "nb", "head", "notes.md")
        historica("name", "--private", "feature/x", "head")
        # Last, since every `head` above means the head until it exists.
        historica("name", "head", "first")
        names = store / "history" / "names"
        (names / "x").mkdir()
        (names / "x" / "pin.txt").write_text("revision " + "0" * 64 + "\n")
        (names / "gone.txt").write_text("change " + "k" * 24 + "\n")
        # Not bookmarks, and passed over: no `.txt`, and a name with a
        # leading space.
        (names / "notes").write_text("anything\n")
        (names / " lead.txt").write_text("change " + "k" * 24 + "\n")
        if corpus == "badname":
            (names / "bad.txt").write_text("change " + "k" * 24 + "\npublic\n")
    return store


def assemble(temporary, corpus):
    store = temporary / f"store-{corpus}"
    history = store / "history"
    history.mkdir(parents=True)
    (history / "historica.txt").write_text(
        "historica\n\nAssembled from tests/corpus by spike/bend/check.py.\n"
    )
    if corpus == "revisions":
        # The seven-revision history and the operations it names are two
        # flat directories rather than one corpus.
        for kind in ("revisions", "operations"):
            (history / kind).mkdir()
            for path in (CORPUS / kind).glob("*.txt"):
                shutil.copy(path, history / kind / path.name)
    elif corpus == "forgotten":
        # The corpus that forgets a payload, with its forgetting documents —
        # the one that parses and those that do not — among the operations.
        for kind in ("revisions", "operations"):
            shutil.copytree(CORPUS / "whole" / kind, history / kind)
        shutil.copytree(CORPUS / "whole" / "forgotten", history / "operations" / "forgotten")
    else:
        for kind in ("revisions", "operations"):
            source = CORPUS / corpus / kind
            if source.is_dir():
                shutil.copytree(source, history / kind, ignore=shutil.ignore_patterns("invalid"))
    return store


def check_store(temporary):
    rust = shutil.which("historica")
    if rust is None:
        run("cargo", "build", "-q", "-p", "historica-cli", cwd=REPO, timeout=600)
        rust = str(REPO / "target" / "debug" / "historica")

    # The writer's reference: the same command line with its clock and its
    # minting fixed, which only a build asking for `pinned` has.
    run("cargo", "build", "-q", "--release", "-p", "historica-cli", "--features", "pinned", cwd=REPO, timeout=1800)
    writer = str(REPO / "target" / "release" / "historica-pinned")

    archive = ROOT / "ffi" / "target" / "release" / "libhistorica_bend_ffi.a"
    # The boundary's own tests — malformed input, error paths, freeing,
    # repeated calls. The archive the native program links is built with it.
    run("cargo", "test", "-q", "--release", cwd=ROOT / "ffi", timeout=600)
    source = temporary / "main.c"
    native = temporary / "main"
    script = temporary / "main.js"

    # Emitting `main.bend` takes about a minute alone, and many times that
    # beside the mutation stage's checkers, so the builds are given long.
    def build_native():
        run("cargo", "build", "-q", "--release", cwd=ROOT / "ffi", timeout=600)
        run(BEND, "main.bend", "-o", str(source), timeout=1800)
        # `bend -o` links nothing of ours, so the C is compiled here; `-w`
        # because the generated program is not ours to lint.
        run(
            os.environ.get("CC", "cc"), "-O3", "-w", "-o", str(native), str(source),
            str(archive), "-lm", "-lpthread", timeout=1800,
        )

    # `--` before the command line, so that neither runtime takes a word of
    # it for its own: both read `--help` and `--threads` otherwise. Bun
    # takes the first `--` after a script for itself, so the JS build is
    # given two.
    tools = [("js", ["bun", str(script), "--", "--"])]
    builds = [lambda: run(BEND, "main.bend", "-o", str(script), timeout=1800)]
    if NATIVE:
        tools.insert(0, ("native", [str(native), "--"]))
        builds.append(build_native)
    parallel(builds)

    copies = itertools.count()

    # One copy per command, made afresh at the same path for each tool, so
    # a message naming a path in it names the same one.
    def fresh(store, copy):
        shutil.rmtree(copy, ignore_errors=True)
        subprocess.run(["cp", "-a", str(store), str(copy)], check=True)
        return copy

    # The folder beside the store, and the store's bookmarks — or, for
    # `init`, everything — as a walk that follows nothing sees them.
    # A record's whole store, less what only the Rust tool keeps of it: the
    # catalogues under `cache/`, which any reader rebuilds, and which carry
    # the moment each file was last seen.
    def folder_of(root, whole=False, cached=True):
        seen = []
        walks = os.walk(root) if whole else itertools.chain(os.walk(root), os.walk(root / "history" / "names"))
        for directory, dirs, files in walks:
            here = Path(directory)
            if here == root and not whole:
                dirs[:] = [d for d in dirs if d != "history"]
            if here == root / "history" / "cache" and not cached:
                files = [f for f in files if f == "README.txt"]
            dirs.sort()
            for name in sorted(dirs + files):
                path = here / name
                entry = os.lstat(path)
                if stat.S_ISLNK(entry.st_mode):
                    seen.append((str(path.relative_to(root)), "l", os.readlink(path)))
                elif stat.S_ISREG(entry.st_mode):
                    seen.append((str(path.relative_to(root)), "f", entry.st_mode & 0o111, path.read_bytes()))
                else:
                    seen.append((str(path.relative_to(root)), "o"))
        return (tuple(seen),)

    # What a command said, whole: a usage error's usage text after its
    # message included, which the port prints as the Rust tool does.
    def said(captured):
        return captured

    # The programs a dispatch finds on `PATH` (decision 0072), which say
    # where they ran and what they were given, and end with a code of their
    # own; one that a signal ends, and one that is there and not runnable.
    bin = temporary / "bin"
    bin.mkdir(exist_ok=True)
    for name, body in (
        ("historica-hello", """printf 'hello from %s:' "$(pwd -P)"; for a in "$@"; do printf ' [%s]' "$a"; done; echo; echo "to stderr" >&2; exit 3"""),
        ("historica-quiet", "exit 0"),
        ("historica-killed", "kill -9 $$"),
        ("historica-unrunnable", "exit 0"),
        ("historica-hello.sh", "exit 0"),
    ):
        (bin / name).write_text(f"#!/bin/sh\n{body}\n")
        (bin / name).chmod(0o644 if name == "historica-unrunnable" else 0o755)

    # The editors a message is asked of: one that writes a message and says
    # what it was handed, and where; one that writes nothing, one that
    # fails, one a signal ends, one that takes the file away, and one that
    # writes where it runs.
    editors = temporary / "editors"
    editors.mkdir(exist_ok=True)
    for name, body in (
        ("writes", r"""printf 'handed [%s] in %s\n' "$(cat "$1")" "$(pwd -P)"; echo editing >&2; printf 'from the editor\n\nwith a body\n' > "$1" """),
        ("nothing", "exit 0"),
        ("fails", "exit 1"),
        ("killed", "kill -9 $$"),
        ("removes", 'rm -f "$1"'),
        ("where", 'pwd -P > "$1"'),
    ):
        (editors / name).write_text(f"#!/bin/sh\n{body}\n")
        (editors / name).chmod(0o755)

    # The word a command line runs, past `-C` and its directory, as
    # `argv.bend` reads it.
    def word(command):
        while len(command) >= 2 and command[0] == "-C":
            command = command[2:]
        return command[0] if command else ""

    # A command's environment: the pins, and a home, a configuration and a
    # temporary directory inside the store's own directory — where no
    # command takes a file from, and every file a command writes there is
    # compared — then
    # what the command changes, `{temporary}` and `{path}` spelled out, and
    # a variable given `None` taken away. Bun keeps a cache of what it has
    # compiled under the home it is given, so it is told to keep it here.
    def environment(copy, changed):
        env = {**os.environ, **PINS, "HOME": str(copy / "history" / "home"), "XDG_CONFIG_HOME": str(copy / "history" / "config"),
               "TMPDIR": str(copy / "history" / "tmp"), "BUN_RUNTIME_TRANSPILER_CACHE_PATH": str(temporary / "bun-cache")}
        for key, value in changed.items():
            if value is None:
                env.pop(key, None)
            else:
                env[key] = value.format(temporary=temporary, path=os.environ.get("PATH", ""), copy=copy)
        return env

    def compare(corpus, commands):
        recorded = corpus in ("unicode", "names", "badname", "log", "merge", "walked", "folder", "badskip", "fresh", "notext", "surveyed", "skipheld", "joining", "claimed", "bare", "recording", "rewriting", "stranded", "shell", "headless", "identity", "editing", "skipping",
                               "damaged", "gutted", "tampered")
        store = record(temporary, rust, corpus, writer) if recorded else assemble(temporary, corpus)
        lines, failures = [], 0
        for command in commands:
            changed = command[0] if command and isinstance(command[0], dict) else {}
            command = command[1:] if changed else command
            # `record` may write the folder — `--move` renames before it
            # surveys, dry run or not — so each tool runs on a copy of its
            # own, and what the folder holds after is compared too; and a
            # record that is not a dry run, the whole store it wrote.
            verb = word(command)
            writes = verb in ("record", "name", "init", "identity", "skip", *REWRITES)
            recording = verb in ("record", *REWRITES) and not {"-n", "--dry-run"} & set(command)
            at = temporary / f"{store.name}-copy-{next(copies)}"
            copy = fresh(store, at) if writes else store
            env = environment(copy, changed)
            command = [word.replace("{copy}", str(copy)) for word in command]
            whole = verb in ("init", "identity", "skip") or recording
            reference = writer if verb in ("record", *REWRITES) else rust
            shown = " ".join([f"{k}={v}" for k, v in changed.items()] + command)
            expected = said(capture(reference, *command, cwd=copy, env=env)) + (folder_of(copy, whole, not recording) if writes else ())
            for name, tool in tools:
                copy = fresh(store, at) if writes else store
                got = said(capture(*tool, *command, cwd=copy, env=env)) + (folder_of(copy, whole, not recording) if writes else ())
                if got != expected:
                    failures += 1
                    lines += [f"DIFF {corpus} {name}: {shown}", f"  rust: {expected}", f"  bend: {got}"]
                else:
                    lines.append(f"same {corpus} {name}: {shown}")
        return lines, failures

    # The writer's choices, pinned by the corpus rather than by the Rust
    # tool: `opdiff` of each pair writes exactly the `recorded.ops.txt`
    # beside it.
    def pinned():
        lines, failures = [], 0
        for case in sorted((CORPUS / "diffs").iterdir()):
            if not case.is_dir():
                continue
            expected = ((case / "recorded.ops.txt").read_bytes(), b"", 0)
            for name, tool in tools:
                got = capture(*tool, "opdiff", "parent.txt", "child.txt", cwd=case)
                if got != expected:
                    failures += 1
                    lines += [f"DIFF diffs {name}: opdiff {case.name}", f"  corpus: {expected}", f"  bend: {got}"]
                else:
                    lines.append(f"same diffs {name}: opdiff {case.name}")
        return lines, failures

    results = parallel(
        [lambda c=corpus, cs=commands: compare(c, cs) for corpus, commands in STORES.items() if ONLY is None or corpus in ONLY]
        + ([pinned] if ONLY is None else [])
    )
    for lines, _ in results:
        print("\n".join(lines), flush=True)
    failures = sum(f for _, f in results)
    compared = sum(len(lines) for lines, _ in results)
    # The version the port says is the workspace's: a release it has not
    # caught up with fails here, whatever the Rust tool it is compared with
    # was built from.
    version = re.search(r'^\[workspace\.package\][^\[]*?^version = "([^"]+)"', (REPO / "Cargo.toml").read_text(), re.M | re.S).group(1)
    for name, tool in tools:
        said_version = capture(*tool, "--version", cwd=temporary)
        if said_version != (f"historica {version}\n".encode(), b"", 0):
            failures += 1
            print(f"DIFF version {name}: the workspace is {version}, and the port says {said_version}", flush=True)
    if failures:
        sys.exit(f"{failures} store commands differ from the Rust tool")
    print(f"store: {compared} comparisons, each the same as the Rust tool", flush=True)


def check_mutations(temporary):
    # Separate copies: the checkout is never temporarily broken. Require
    # a type-check failure in the expected proof, not a parse/tool error.
    mutations = (
        (
            "forgetting ignores newline",
            "Bool.and(Bool.not(Bool.xor(n1, n2)), Bool.or(Bool.or(f1, f2), T.same(t1, t2)))",
            "Bool.or(Bool.or(f1, f2), Bool.and(T.same(t1, t2), Bool.not(Bool.xor(n1, n2))))",
            "diff_lemmas.agrees_refl",
        ),
        (
            "advance reverses the moved prefix incorrectly",
            "advance(p, rest, it <> acc)",
            "advance(p, rest, List.append(&2, Item, acc, [it]))",
            "LAWS.advance_exact",
        ),
        (
            "delete ignores item disagreement",
            "drop_checked(rs, ss, Bool.and(ok, agrees(r, s)))",
            "drop_checked(rs, ss, ok)",
            "LAWS.drop_checked_exact",
        ),
        (
            "cursor drops inserted items",
            "List.append(&2, Item, List.reverse(&2, Item, items), acc)",
            "acc",
            "LAWS.cursor_walk_equivalent",
        ),
        (
            "cursor loses the trailing parent suffix",
            "Done{List.append(&2, Item, List.reverse(&2, Item, acc), state)}",
            "Done{List.reverse(&2, Item, acc)}",
            "LAWS.cursor_walk_equivalent",
        ),
        (
            "cursor overwrites an earlier deletion error",
            'Maybe.or(&2, String, err, Bool.pick(Maybe<&2, String>, agreed, None{}, Some{"a delete at " ++ Nat.show(at) ++ " quotes lines the parent does not hold"}))',
            'Bool.pick(Maybe<&2, String>, agreed, None{}, Some{"a delete at " ++ Nat.show(at) ++ " quotes lines the parent does not hold"})',
            "LAWS.cursor_walk_equivalent",
        ),
        (
            "public replay ignores the result digest",
            "apply.checked(result, items)\n\n# Blocks",
            "apply.checked(None{}, items)\n\n# Blocks",
            "LAWS.cursor_apply_equivalent",
        ),
        (
            "positional model loses the trailing-gap insertion",
            "case Nil{}:\n      inserts_at(ops, p)\n    case it <> rest:",
            "case Nil{}:\n      Nil{}\n    case it <> rest:",
            "position_lemmas.result_shift",
            "replay_spec.bend",
        ),
        (
            "positional model deletes its exclusive endpoint",
            "Nat.is_lt(p, Nat.add(at, List.length(&2, Ops.Item, items)))",
            "Nat.is_le(p, Nat.add(at, List.length(&2, Ops.Item, items)))",
            "position_lemmas.deleted_shift",
            "replay_spec.bend",
        ),
        (
            "script never advances past what a block consumed",
            "script(rest, Nat.add(here, consumed(edit)))",
            "script(rest, here)",
            "composition_lemmas.script_below",
        ),
        (
            "positional refusal ignores a disagreeing quote",
            "Maybe.or(&2, String, Cursor.disagreement(at, Spec.prefix_matches(items, List.drop(&2, Ops.Item, parent, at))), quote_error(parent, rest))",
            "quote_error(parent, rest)",
            "composition_lemmas.error_block",
            "semantic_replay.bend",
        ),
        (
            "a replacement consumes nothing",
            "    case Replacement{recorded, inserted}:\n      List.length(&2, Item, recorded)",
            "    case Replacement{recorded, inserted}:\n      0n",
            "composition_lemmas.result_block",
        ),
        (
            "ordering admits an insert inside a deleted run",
            "Bool.and(Nat.is_le(stop, at2), ordered(more, at2))",
            "ordered(more, at2)",
            "composition_lemmas.is_script",
            "semantic_replay.bend",
        ),
        (
            "the parser admits a delete after an insert at one position",
            '      Some{"a delete after an insert at one position"}',
            "      None{}",
            "parser_lemmas.after_insert.c",
        ),
        (
            "the parser admits an operation inside a deleted run",
            'Bool.pick(Maybe<&2, String>, Nat.is_lt(next_at, stop), Some{"two operations overlap"},',
            'Bool.pick(Maybe<&2, String>, Nat.is_lt(next_at, stop), None{},',
            "parser_lemmas.after_delete.c",
        ),
        (
            "the parser forgets the last delete across an insert",
            "    case Op{Insert{}, at, items}:\n      previous",
            "    case Op{Insert{}, at, items}:\n      None{}",
            "parser_lemmas.parser_ordered.replacement",
        ),
        (
            "the parser checks the previous operation but not the last delete",
            "Maybe.or(&2, String, ordered(prev, op), ordered(previous_delete, op))",
            "ordered(prev, op)",
            "parser_lemmas.bounded_ok",
        ),
        (
            "the writer omits the marker after an unterminated item",
            'Bool.pick(String, n, SNil{}, "\\\\ no newline\\n")',
            "Bool.pick(String, n, SNil{}, SNil{})",
            "spelling_lemmas.item_marker",
        ),
        (
            "the writer spells a delete's count before its position",
            '"delete " ++ T.spell(at) ++ " " ++ T.spell(List.length(&2, Item, items))',
            '"delete " ++ T.spell(List.length(&2, Item, items)) ++ " " ++ T.spell(at)',
            "spelling_lemmas.delete_sp.count",
        ),
        (
            "the parser accepts an unterminated marker line",
            "    case T.Line{t, True{}} <> +rest NoNewline{}:",
            "    case T.Line{t, term} <> +rest NoNewline{}:",
            "spelling_lemmas.taken",
        ),
        (
            "the parser accepts an unterminated header line",
            "Bool.pick(Maybe<&2, String>, term, T.strip_prefix(t, key), None{})",
            "T.strip_prefix(t, key)",
            "spelling_lemmas.header_sp",
        ),
        (
            "the reader admits a leading zero",
            "Bool.and(Nat.is_lt(d, 10n), Nat.is_lt(0n, d))",
            "Nat.is_lt(d, 10n)",
            "decimal_lemmas.pos_value",
            "text.bend",
        ),
        (
            "counting up drops the carry",
            "0n <> dsucc(rest)",
            "0n <> rest",
            "decimal_lemmas.digits_mul10",
            "text.bend",
        ),
        (
            "the backtrack drops kept lines",
            "backtrack(f, step(old, new, z2, i2, j2), i2, j2, old, new, z2, Keep{} <> script)",
            "backtrack(f, step(old, new, z2, i2, j2), i2, j2, old, new, z2, script)",
            "diff_lemmas.back.of",
        ),
        (
            "a replacement block swaps what it deletes and inserts",
            "      Replacement{d <> ds, i <> it}",
            "      Replacement{i <> it, d <> ds}",
            "diff_lemmas.consumed_block",
        ),
        (
            "a kept line after a run does not start the next gap",
            "<> runs(rest, 1n, Nil{}, Nil{})",
            "<> runs(rest, 0n, Nil{}, Nil{})",
            "diff_lemmas.runs_apply.keep",
        ),
        (
            "the digest cause ignores forgetting",
            "Bool.and(Bool.not(Ops.any_forgotten(items)), Bool.not(T.same(d, Ops.state_digest(items))))",
            "Bool.not(T.same(d, Ops.state_digest(items)))",
            "refusal_lemmas.mismatch_is",
            "semantic_replay.bend",
        ),
        (
            "the view keeps elements of unseen authors",
            "List.filter.put(Node, Node.restrict(x, seen), restrict(xs, seen), has(seen, Node.author(x)))",
            "List.filter.put(Node, Node.restrict(x, seen), restrict(xs, seen), True{})",
            "merge_lemmas.restrict_attach.at",
            "merge.bend",
        ),
        (
            "the view keeps removals by unseen events",
            "List.filter.put(Nat, y, keep(ys, seen), has(seen, y))",
            "List.filter.put(Nat, y, keep(ys, seen), True{})",
            "merge_lemmas.keep_ins.at",
            "merge.bend",
        ),
        (
            "an element is appended rather than placed by name",
            "      n <> x <> xs",
            "      x <> rest",
            "merge_lemmas.attach_comm.at",
            "merge.bend",
        ),
        (
            "a removal is appended rather than joined in order",
            "      by <> y <> ys",
            "      y <> rest",
            "merge_lemmas.ins_comm.at",
            "merge.bend",
        ),
        (
            "a causal order may put an event before its past",
            "Bool.and(none_known(past(g, e), rest), causal(rest, g))",
            "causal(rest, g)",
            "merge_lemmas.causal_remove.at",
            "merge.bend",
        ),
        (
            "an action is applied as another author's",
            "apply(rest, one(t, by, a), by)",
            "apply(rest, one(t, 0n, a), by)",
            "merge_lemmas.restrict_apply",
            "merge.bend",
        ),
        (
            "a second add of a file the tree holds is accepted",
            "Fail{AddedTwice{file}}",
            "Done{insert(t, Entry{file, p, kind_of(target, payload), payload, target, m})}",
            "tree_lemmas.adds_step",
            "tree.bend",
        ),
        (
            "two files at one path are not refused",
            "Fail{PathTaken{p, f, o}}",
            "Done{Unit{}}",
            "tree_lemmas.fits_taken",
            "tree.bend",
        ),
        (
            "a dangling reference is not checked",
            "ensure(holds(t, target), Dangling{f, target})",
            "Done{Unit{}}",
            "tree_lemmas.one_insert",
            "tree.bend",
        ),
        (
            "a mode change resets the kind",
            "      Entry{f, p, k, y, g, m}\n\ndef with_target",
            "      Entry{f, p, Lines{}, y, g, m}\n\ndef with_target",
            "tree_lemmas.modes_kind",
            "tree.bend",
        ),
        (
            "an ancestry closure keeps only the first parent",
            "      union_ids(p <> ancestors_of(ss, p), closure(rest, ss))",
            "      union_ids(p <> ancestors_of(ss, p), Nil{})",
            "graph_lemmas.closure_has",
            "tree.bend",
        ),
        (
            "a revision is ready when its first parent is known",
            "      Bool.and(is_seen(ss, p), known(ss, rest))",
            "      is_seen(ss, p)",
            "graph_lemmas.known_mem",
            "tree.bend",
        ),
        (
            "the anchor skips tombstones among the right children",
            "anchor.of(t, left, children(t, left, True{}))",
            "anchor.of(t, left, children(standing(t), left, True{}))",
            "anchor_lemmas.anchor_of_nil",
            "merge.bend",
        ),
        (
            "the descent skips tombstones among the left children",
            "leftmost(p, t, head_name(children(t, Some{at}, False{}), at))",
            "leftmost(p, t, head_name(children(standing(t), Some{at}, False{}), at))",
            "anchor_lemmas.leftmost_stay",
            "merge.bend",
        ),
        (
            "an event of a chain has seen none of the events before it",
            "      Rev{upto(n), Some{Edits{d}}} <> chain.go(ds, 1n+n)",
            "      Rev{Nil{}, Some{Edits{d}}} <> chain.go(ds, 1n+n)",
            "linear_lemmas.chain_go",
            "merge.bend",
        ),
        (
            "a closed set need not hold its events' pasts",
            "      Bool.and(subset(past(g, x), s), closed(rest, g, s))",
            "      Bool.and(True{}, closed(rest, g, s))",
            "view_lemmas.closed_has",
            "merge.bend",
        ),
        (
            "a resolution removes what its author never saw",
            "  run.acts(res.done(res(parts, Some{Resolving{v, 0n, Nil{}, Nil{}, None{}}}, e, visible(v)), visible(v)))",
            "  run.acts(res.done(res(parts, Some{Resolving{v, 0n, Nil{}, Nil{}, None{}}}, e, visible(v)), visible(t)))",
            "merge_lemmas.resolve_avoid",
            "merge.bend",
        ),
        (
            "an author's view reads the whole tree",
            "      Some{file(restrict(t, s))}",
            "      Some{file(t)}",
            "view_lemmas.intent_at",
            "merge.bend",
        ),
        (
            "the revision writer puts `when` before `author`",
            '++ "author " ++ author ++ "\\n" ++ "when " ++ when ++ "\\n" ++',
            '++ "when " ++ when ++ "\\n" ++ "author " ++ author ++ "\\n" ++',
            "revision_lemmas.written",
            "revision.bend",
        ),
        (
            "revision validation lets `change` repeat",
            "    case Key.Change{}:\n      False{}\n    case Key.Author{}:",
            "    case Key.Change{}:\n      True{}\n    case Key.Author{}:",
            "revision_lemmas.canon",
            "revision.bend",
        ),
        (
            "the key table classifies `parent` as `supersedes`",
            'Named{"parent", Key.Parent{}}',
            'Named{"parent", Key.Supersedes{}}',
            "revision_lemmas.classify_named",
            "revision.bend",
        ),
        (
            "the walk sorts by index rather than by what each had seen",
            "      Rank{List.length(&2, Nat, Merge.past(g, i)), i} <> ranks(g, rest)",
            "      Rank{i, i} <> ranks(g, rest)",
            "order_lemmas.ranks_good",
            "commands.bend",
        ),
        (
            "the walk runs where its order is not known to be causal",
            '      Fail{head ++ ", file " ++ file ++ ": a revision behind it had seen no more revisions than one it had seen, so the ancestry is not a history"}',
            "      walked.tree(head, file, names, Merge.walk(walked.order(g), g, Some{Nil{}}))",
            "order_lemmas.reads.at",
            "commands.bend",
        ),
        (
            "the diff's check lets a kept line differ",
            "      Bool.and(fit.kept(old, new), fit(r, fit.tail(old), fit.tail(new)))",
            "      fit(r, fit.tail(old), fit.tail(new))",
            "similar_lemmas.fit_apply",
            "similar.bend",
        ),
        (
            "emphasis drops the words two lines share",
            "      Piece{joined.all(List.take(&2, String, ws2, n)), False{}} <> marked.go(rest, List.drop(&2, String, ws2, n), old)",
            "      marked.go(rest, List.drop(&2, String, ws2, n), old)",
            "emphasis_lemmas.marked_text",
            "commands.bend",
        ),
        (
            "the walk takes a file without asking the rules",
            "  Bool.and(Bool.not(is_store(prefix, name)), Bool.and(Bool.not(skips(rules, path)), Bm.name_ok(path)))",
            "  Bool.and(Bool.not(is_store(prefix, name)), Bm.name_ok(path))",
            "folder_lemmas.took_ok",
            "folder.bend",
        ),
        (
            "a bookmark's revision is taken without asking the store",
            '      Bool.pick(Result<&2, &2, String, String>, Rev.member(ids(fs), id), Done{id}, Fail{"the bookmark `" ++ name ++ "` names the revision " ++ id ++ ", which this store does not hold yet"})',
            '      Bool.pick(Result<&2, &2, String, String>, True{}, Done{id}, Fail{"the bookmark `" ++ name ++ "` names the revision " ++ id ++ ", which this store does not hold yet"})',
            "target_lemmas.bookmarked_mem",
            "commands.bend",
        ),
        (
            "log lists a revision no filter was asked of",
            "      keep_full(keeps(fl, f), f, kept(fl, rest))",
            "      keep_full(True{}, f, kept(fl, rest))",
            "log_lemmas.kept_ok",
            "commands.bend",
        ),
        (
            "a file bookmark names a file the revision does not hold",
            '      Fail{Refused{1, "the bookmark `" ++ spelling ++ "` names the file " ++ file ++ ", which " ++ String.take(id, 12n) ++ " does not hold; `historica files " ++ String.take(id, 12n) ++ "` lists what it holds"}}',
            "      Done{file}",
            "fileat_lemmas.held_ok",
            "commands.bend",
        ),
        (
            "a comparison lays a removed line as context",
            '        List.append(&2, Laid, laid.all("-", List.take(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items))),',
            '        List.append(&2, Laid, laid.all(" ", List.take(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items))),',
            "laid_lemmas.old_walk",
            "commands.bend",
        ),
        (
            "blame drops a line that stayed",
            "              Row{b, it} <> r",
            "              r",
            "blame_lemmas.put_items",
            "commands.bend",
        ),
        (
            "a name rule lets its pattern hold a slash",
            '    Bool.pick(Result<&2, &2, String, String>, has_slash(v), Fail{"a pattern is one path component and holds no `/`: a path is spelled with `skip`"},',
            '    Bool.pick(Result<&2, &2, String, String>, False{}, Fail{"a pattern is one path component and holds no `/`: a path is spelled with `skip`"},',
            "folder_lemmas.pattern_ok",
            "folder.bend",
        ),
        (
            "a change bookmark reads back as a file bookmark",
            '      Bool.pick(Result<&2, &2, String, Target>, Id.is_assigned(value), Done{Target.Change{value}}, Fail{target_error()})',
            '      Bool.pick(Result<&2, &2, String, Target>, Id.is_assigned(value), Done{Target.File{value}}, Fail{target_error()})',
            "bookmark_lemmas.target_back",
            "bookmark.bend",
        ),
        (
            "an abbreviation stops at the longest share",
            '  String.take(id, Nat.max(8n, 1n+longest_shared(id, among)))',
            '  String.take(id, Nat.max(8n, longest_shared(id, among)))',
            "abbrev_lemmas.unique",
            "commands.bend",
        ),
        (
            "blame attributes the removed lines too",
            '      walked.rows(Merge.visible(t), names)',
            '      walked.rows(Merge.order(t), names)',
            "blamed_lemmas.origins_file",
            "commands.bend",
        ),
        (
            "a span that drops its last line",
            'rows.keep(Bool.and(Nat.is_le(first, k), Nat.is_le(k, last))',
            'rows.keep(Bool.and(Nat.is_le(first, k), Nat.is_lt(k, last))',
            "blamed_lemmas.in_lines",
            "commands.bend",
        ),
        (
            "blame drops the marker after a line without a newline",
            '      l <> "\\\\ no newline at end of file" <> rest',
            '      l <> rest',
            "blamed_lemmas.ends_row",
            "commands.bend",
        ),
        (
            "blame looks a `path:` spelling up with its prefix",
            '      wcf.path.r(bs, t, p, left, Tree.at(t, p))',
            '      wcf.path.r(bs, t, p, left, Tree.at(t, sp))',
            "blamed_lemmas.spelled_r",
            "commands.bend",
        ),
        (
            "blame asks the kind of the spelling, not of the file",
            '    lines_only.r(Maybe.default(&2, String, Tree.path(t, file), spelling), Tree.kind(t, file))',
            '    lines_only.r(Maybe.default(&2, String, Tree.path(t, file), spelling), Tree.kind(t, spelling))',
            "blamed_lemmas.pk_tree",
            "commands.bend",
        ),
        (
            "blame <target> <path> ignores the span",
            '    blame.limited.r(fs, changes(fs), rows, span)',
            '    blame.limited.r(fs, changes(fs), rows, None{})',
            "blamed_lemmas.recorded_printed",
            "commands.bend",
        ),
        (
            "blame <path> takes bytes the position never saw for text",
            '      wcf.sniffed.r(path, Folder.is_text(bs))',
            '      Done{Unit{}}',
            "blamed_lemmas.folder_kind",
            "commands.bend",
        ),
        (
            "blame reads its words in reverse",
            '      BlameAsked{l, List.append(&2, String, r, [w])}',
            '      BlameAsked{l, w <> r}',
            "blamed_lemmas.run_word",
            "commands.bend",
        ),
        (
            "blame <path> reads through a link in the folder",
            '    case Folder.Found.Link{p, t}:\n      lines_only.r(path, Some{Tree.Link{}})',
            '    case Folder.Found.Link{p, t}:\n      Done{Unit{}}',
            "blamed_lemmas.ck_found",
            "commands.bend",
        ),
        (
            "diff's --onto swallows every word after it",
            '    case DWant.Onto{}:\n      DRead{Done{dasked.onto(a, w)}, DWant.No{}}',
            '    case DWant.Onto{}:\n      DRead{Done{dasked.onto(a, w)}, DWant.Onto{}}',
            "diffcmd_lemmas.run_ok",
            "commands.bend",
        ),
        (
            "diff compares a revision with nothing rather than its parent",
            '    case None{}:\n      sole_parent.r(id_of(right), parents_of(right))',
            '    case None{}:\n      Done{None{}}',
            "diffcmd_lemmas.left_ok",
            "commands.bend",
        ),
        (
            "diff limits to the spelling rather than the file it names",
            '    f : String <- file_in.r(right, bs, sp, t)\n    return Limit.File{f}',
            '    f : String <- file_in.r(right, bs, sp, t)\n    return Limit.File{sp}',
            "diffcmd_lemmas.lim_file_bind",
            "commands.bend",
        ),
        (
            "diff shows a file whose sides agree",
            '  Bool.pick(Maybe<&2, Compared>, pair.differs(c), Some{c}, None{})',
            '  Some{c}',
            "diffcmd_lemmas.built_ok",
            "commands.bend",
        ),
        (
            "diff over the folder ignores the limit",
            '      Bool.pick(List<&2, Here>, here.wanted(l, h), h <> later, later)',
            '      h <> later',
            "diffcmd_lemmas.limited_ok",
            "commands.bend",
        ),
        (
            "log reads --author as --grep",
            '        case LFlag.Author{}:\n          LRaw{ws, p, fi, l, Some{v}, g, si, u}',
            '        case LFlag.Author{}:\n          LRaw{ws, p, fi, l, au, Some{v}, si, u}',
            "logargs_lemmas.run_ok",
            "commands.bend",
        ),
        (
            "check lets a document take a payload's digest",
            '      OpFiled.Doc{r} <> attach(rest, stats)',
            '      OpFiled.Doc{r} <> attach(rest, List.drop(&2, String, stats, 1n))',
            "check_lemmas.pairs_ok",
            "check.bend",
        ),
        (
            "check walks an event before what it had seen",
            "Bool.pick(List<&2, Nat>, Bool.and(Bool.not(Merge.has(placed, i)), all.in(Merge.past(g, i), placed)), [i], ready(g, placed, rest))",
            "Bool.pick(List<&2, Nat>, Bool.not(Merge.has(placed, i)), [i], ready(g, placed, rest))",
            "check_lemmas.ready_causal",
            "check.bend",
        ),
        (
            "-C counts the first directory rather than the last",
            "read.go(rest, Some{d}, lead(rest))",
            "read.go(rest, Maybe.or(&2, String, base, Some{d}), lead(rest))",
            "argv_lemmas.go",
            "argv.bend",
        ),
        (
            "dispatch looks any word up",
            'Bool.and(Bool.not(String.ends_with(w, "-")), spelled(w))))',
            'Bool.and(Bool.not(String.ends_with(w, "-")), True{})))',
            "shell_lemmas.runs",
            "shell.bend",
        ),
        (
            "a note under the header reads as a layout",
            "      +found = line.cut(rest)",
            "      +found = rest",
            "opening_lemmas.noted",
            "store.bend",
        ),
        (
            "identity forgets the default author",
            "    case Some{a} None{} Ids{None{}, us}:\n      Done{Ids{Some{a}, us}}",
            "    case Some{a} None{} Ids{None{}, us}:\n      Done{Ids{None{}, us}}",
            "identity_lemmas.reads_back",
            "identity.bend",
        ),
        (
            "show finds a document whose digest the named one starts",
            '      Bool.pick(Maybe<&2, String>, String.starts_with(i, id), Some{text}, doc_by_id(rest, id))',
            '      Bool.pick(Maybe<&2, String>, String.starts_with(id, i), Some{text}, doc_by_id(rest, id))',
            "show_lemmas.by_id",
            "commands.bend",
        ),
        (
            "cat prints through a link",
            '    not_a_link.r(t, path, file, Tree.entry_target_of(Tree.lookup(t, file)))',
            '    not_a_link.r(t, path, file, None{})',
            "show_lemmas.ck_tree",
            "commands.bend",
        ),
        (
            "diff numbers an arrival as a line of the parent",
            'hunks.walk(rest, Bool.pick(Nat, String.eq(sign, "+"), b, 1n+b)',
            'hunks.walk(rest, Bool.pick(Nat, String.eq(sign, "-"), b, 1n+b)',
            "hunk_lemmas.walk_ok",
            "commands.bend",
        ),
        (
            "a hunk holding no line of a side names its first line anyway",
            '  Bool.pick(Nat, Nat.is_eq(count, 0n), 0n, first)',
            '  first',
            "hunk_lemmas.from_nz",
            "commands.bend",
        ),
        (
            "diff shows a change only where another is near",
            '  Bool.or(changed, Bool.or(Nat.is_gt(owed, 0n), near))',
            '  Bool.or(Nat.is_gt(owed, 0n), near)',
            "hunk_lemmas.walk_cons",
            "commands.bend",
        ),
        (
            "emphasis compares each removal with its arrival the wrong way round",
            '      apart(numbered.shown(r), numbered.shown(a)) <> pairs(rs, more)',
            '      apart(numbered.shown(a), numbered.shown(r)) <> pairs(rs, more)',
            "mark_lemmas.was_fit",
            "commands.bend",
        ),
        (
            "emphasis marks the arrivals before the removals",
            'List.append(&2, Maybe<&2, List<&2, Piece>>, marks.was(ps), marks.now(ps))',
            'List.append(&2, Maybe<&2, List<&2, Piece>>, marks.now(ps), marks.was(ps))',
            "mark_lemmas.pair_fit",
            "commands.bend",
        ),
        (
            "emphasis gives a context line no mark",
            '      Chunked{[None{}], rest}',
            '      Chunked{Nil{}, rest}',
            "mark_lemmas.step_fit",
            "commands.bend",
        ),
        (
            "diff walks the two sides comparing their files the wrong way round",
            '      String.order(Tree.entry_file(x), Tree.entry_file(y))\n    case Nil{} _:\n      GT{}',
            '      String.order(Tree.entry_file(y), Tree.entry_file(x))\n    case Nil{} _:\n      GT{}',
            "pair_lemmas.join",
            "commands.bend",
        ),
        (
            "diff drops a file only the parent holds",
            '      Both{Tree.entry_file(x), Some{x}, None{}} <> both.go(f, xr, ys2, both.cmp(xr, ys2))',
            '      both.go(f, xr, ys2, both.cmp(xr, ys2))',
            "pair_lemmas.join",
            "commands.bend",
        ),
        (
            "diff sorts the child's files backwards",
            '  +ys2 = List.sort(~Tree.Entry, ~(a => b => String.is_le(Tree.entry_file(a), Tree.entry_file(b))), ys)',
            '  +ys2 = List.sort(~Tree.Entry, ~(a => b => String.is_le(Tree.entry_file(b), Tree.entry_file(a))), ys)',
            "pair_lemmas.pairs_by_file",
            "commands.bend",
        ),
        (
            "the walk refuses a path without asking the rules",
            "  Bool.pick(Maybe<&2, T.Split>, Bool.or(is_store(prefix, name), skips(rules, joined(prefix, name))), None{}, refusal.kind(",
            "  Bool.pick(Maybe<&2, T.Split>, is_store(prefix, name), None{}, refusal.kind(",
            "survey_lemmas.of_ok",
            "folder.bend",
        ),
        (
            "a refusal names a path other than the one the rules were asked about",
            '      Some{T.Split{path, "not a regular file"}}',
            '      Some{T.Split{"", "not a regular file"}}',
            "survey_lemmas.kind_ok",
            "folder.bend",
        ),
        (
            "status says an arriving file changed as well",
            'fact("added", sorted(added(os))),\n  List.append(&2, T.Split, fact("dropped", sorted(dropped_paths(os))),\n  List.append(&2, T.Split, fact("edited", without(sorted(edited(os)), arriving)),',
            'fact("added", sorted(added(os))),\n  List.append(&2, T.Split, fact("dropped", sorted(dropped_paths(os))),\n  List.append(&2, T.Split, fact("edited", sorted(edited(os))),',
            "survey_lemmas.facts_ok",
            "survey.bend",
        ),
        (
            "replay starts over at a payload after a refusal",
            "    case Fail{e}:\n      Fail{e}\n    case Done{items}:\n      Done{Ops.from_text(text)}",
            "    case Fail{e}:\n      Done{Ops.from_text(text)}\n    case Done{items}:\n      Done{Ops.from_text(text)}",
            "replay_doc_fail",
            "commands.bend",
        ),
        (
            "replay applies a document to nothing rather than to what came before",
            "    Ops.apply(items, doc)",
            "    Ops.apply(Nil{}, doc)",
            "LAWS.opdiff_replays_to_the_child",
            "commands.bend",
        ),
        (
            "status keeps the revisions joined newest first",
            "      status.args.go(rest, onto, List.append(&2, String, merges, [v]), sword(rest))",
            "      status.args.go(rest, onto, v <> merges, sword(rest))",
            "status_lemmas.args_go",
            "commands.bend",
        ),
        (
            "status joins a `--merge` by its spelling rather than the revision it names",
            "      Done{List.append(&2, String, ps, [id])}",
            "      Done{List.append(&2, String, ps, [m])}",
            "status_lemmas.named_held",
            "commands.bend",
        ),
        (
            "name takes a name without asking the path rules",
            "    Sv.path_check(n)))\n\ndef name.usable.r(",
            "    None{}))\n\ndef name.usable.r(",
            "name_lemmas.stays",
            "commands.bend",
        ),
    )
    def mutate(index, name, before, after, proof, *source_files):
        mutant = temporary / f"mutation-{index}"
        # The Rust build under `ffi/` is a hundred megabytes nothing here reads.
        shutil.copytree(ROOT, mutant, ignore=shutil.ignore_patterns("target"))
        source = mutant / (source_files[0] if source_files else "ops.bend")
        original = source.read_text()
        assert original.count(before) == 1, name
        source.write_text(original.replace(before, after))
        with SLOTS:
            checked = subprocess.run(
                [BEND, "PROOF.bend"], cwd=mutant,
                capture_output=True, text=True, timeout=120,
            )
        diagnostic = checked.stdout + checked.stderr
        if checked.returncode == 0 or proof not in diagnostic or "expected" not in diagnostic:
            raise RuntimeError(f"Mutation did not fail in {proof}: {name}\n{diagnostic}")
        print(f"ok    proof rejects: {name}", flush=True)
        if index == 0:
            with SLOTS:
                regression = subprocess.run(
                    [BEND, "replay_tests.bend"], cwd=mutant,
                    capture_output=True, text=True, timeout=120,
                )
            diagnostic = regression.stdout + regression.stderr
            if regression.returncode == 0 or "forgotten quote preserves newline" not in diagnostic:
                raise RuntimeError(f"Original newline bug escaped the regression test:\n{diagnostic}")
            print("ok    replay regression rejects the original newline bug", flush=True)

    parallel([lambda i=i, m=m: mutate(i, *m) for i, m in enumerate(mutations)])


if __name__ == "__main__":
    main()
