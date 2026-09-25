#!/usr/bin/env python3
"""Check proofs, run JS/native corpora, ensure replay mutations are rejected,
and hold the store commands to the Rust tool's output.

The stages are independent and run at once; `check.py <stage>...` runs only
those named, for iterating on one: store, corpora, similar, nfc, proof,
mutations.

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
import functools
import http.server

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
        "nfc": check_nfc,
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


# Normal form C
# -------------

# `nfc.bend` is the `unicode-normalization` crate's normal form C, held to
# the crate itself: every character that decomposes, alone and before a
# mark; and strings drawn from what the tables are about — starters that
# compose and marks of every class in every order, a mark blocked by
# another of its class, starters that compose with starters, characters
# composition excludes, Hangul jamo and syllables, and the quick check's
# Latin — each compared on normal form C and on normal form D, the
# decomposition composition starts from.
def nfc_cases(rng, classes, decompositions, pairs):
    firsts = sorted({a for a, _, _ in pairs})
    seconds = sorted({b for _, b, _ in pairs})
    composites = sorted({x for _, _, x in pairs})
    marks = sorted(classes)
    excluded = sorted(set(decompositions) - set(composites))
    jamo = list(range(0x1100, 0x1113)) + list(range(0x1161, 0x1176)) + list(range(0x11A7, 0x11C3))
    syllables = [0xAC00, 0xAC01, 0xAC1C, 0xD7A3, 0xB098, 0xD55C]
    latin = [ord(c) for c in "aeiouAEKZ ;`/._-09"] + list(range(0xC0, 0x180, 7))
    pools = [firsts, seconds, composites, marks, excluded, jamo, syllables, latin, latin]
    cases = []
    for c in sorted(decompositions):
        cases.append(chr(c))
        cases.append(chr(c) + chr(rng.choice(marks)) + chr(rng.choice(marks)))
    for _ in range(12000):
        size = rng.randint(1, 9)
        cases.append("".join(chr(rng.choice(rng.choice(pools))) for _ in range(size)))
    # A pair's halves with marks between them, in every order of two.
    for _ in range(3000):
        a, b, _ = rng.choice(pairs)
        between = [chr(rng.choice(marks)) for _ in range(rng.randint(0, 3))]
        cases.append(chr(a) + "".join(between) + chr(b) + chr(rng.choice(marks)))
    return [c for c in cases if "\n" not in c and "\r" not in c]


def check_nfc(temporary):
    run("cargo", "build", "-q", "--release", "--example", "nfc_tables", cwd=ROOT / "ffi", timeout=600)
    reference = ROOT / "ffi" / "target" / "release" / "examples" / "nfc_tables"
    source = temporary / "nfc.c"
    native = temporary / "nfc"
    run(BEND, "nfc.bend", "-o", str(source), timeout=600)
    run(os.environ.get("CC", "cc"), "-O2", "-w", "-o", str(native), str(source), "-lm", "-lpthread", timeout=900)
    classes, decompositions, pairs = {}, {}, []
    for line in subprocess.run([str(reference), "tables"], capture_output=True, text=True, check=True).stdout.splitlines():
        kind, *fields = line.split()
        if kind == "c":
            classes[int(fields[0], 16)] = int(fields[1], 16)
        elif kind == "d":
            decompositions[int(fields[0], 16)] = [int(f, 16) for f in fields[1:]]
        elif kind == "p":
            pairs.append(tuple(int(f, 16) for f in fields))
    cases = nfc_cases(random.Random(20260925), classes, decompositions, pairs)
    text = "".join(c + "\n" for c in cases)
    (temporary / "nfc-cases.txt").write_text(text)
    expected = subprocess.run([str(reference), "nfc"], input=text, capture_output=True, text=True, check=True).stdout.splitlines()
    got = subprocess.run([str(native), str(temporary / "nfc-cases.txt")], capture_output=True, text=True, check=True).stdout.splitlines()
    differ = [i for i, want in enumerate(expected) if i >= len(got) or got[i] != want]
    for i in differ[:5]:
        print(f"DIFF nfc case {i}: {' '.join(f'{ord(c):x}' for c in cases[i])}\n  want {expected[i]}\n  got  {got[i] if i < len(got) else ''}")
    if differ or len(got) != len(cases):
        sys.exit(f"{len(differ)} of {len(cases)} strings normalise otherwise than `unicode-normalization` does")
    print(f"nfc: {len(cases)} strings, as the crate normalises them")


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

# The commands that move, remove and copy what a store holds: after each,
# the whole of every store under the copy is compared, less `cache/`.
MOVES = ("arrange", "prune", "receive", "offer", "export", "fetch")

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
    "revisions": [["log"], ["log", "kxryzmor"], ["show", "head"], ["status"], ["record", "-n"], ["arrange", "-n"], ["arrange"], ["arrange", "--refile"]],
    "merged": [["log"], ["files", "head"], ["status"], ["update"], ["arrange"]],
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
        ["arrange", "--refile"],
        # A store that arrived with no folder: every file written, and each
        # link made where its target is now.
        ["update", "-n"],
        ["update"],
    ],
    "modes": [["log"], ["files", "head"], ["diff", "head"], ["blame", "head", "run.sh"], ["diff"], ["status"], ["record", "-n"], ["update"], ["arrange", "--refile"]],
    "whole": [
        ["log"], ["files", "head"], ["cat", "head", "notes/2026-08-20.md"],
        ["diff", "head"], ["blame", "head", "notes/photo.png"], ["blame", "head", "notes/2026-08-20.md"],
        # An assembled store has no folder beside it, so everything is gone.
        ["diff"], ["blame", "notes/2026-08-20.md"], ["status"], ["record", "-n"], ["record", "-n", "notes/photo.png"],
        ["update"],
        ["arrange", "-n"], ["arrange"],
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
                ["record", "--fields", "-m", "x"], ["amend", "--fields", "-m", "y"], ["abandon", "head", "--fields", "-m", "z"], ["carry", "--fields"],
                ["prune", "-n"], ["prune", "--fields"]],
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
        # Written by the Rust tool, so already arranged.
        ["arrange", "-n"],
        ["arrange"],
    ],
    # The folder against the position: an edit, a file gone, files new —
    # text and bytes — a file of bytes changed, a mode, links retargeted,
    # made and removed, a file become a link, and rules skipping a path, a
    # directory, a name and a directory's name, filed flat and in folders.
    "folder": [
        # Its folder exported whole and laid out alone: links, a mode, and
        # the rules that travel.
        ["export", "out"],
        ["export", "--files-only", "out", "first"],
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
        ["merge"],
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
        ["prune", "-n"],
        ["prune", "--fields"],
    ],
    # A rewrite that arrived without its carries: the repair, swept, named,
    # and planned; and what already rewritten refuses.
    # Decisions 0014, 0050 and 0066, read: a store the Rust tool's `forget`
    # destroyed lines of — of an edit, of a file added whole, of a line a
    # merge's resolution copied — and a payload of bytes in, with two
    # stand-ins for one document. Every reading command reads the stand-ins
    # where the originals were; `record`, `amend` and `carry` read them too.
    "forgotten": [
        ["log"],
        # A copy of a store that forgot: every forgetting document travels
        # with what it stands in for, and each file is laid out as `cat`
        # reads it.
        ["export", "out"],
        ["export", "out", "first"],
        ["export", "--files-only", "out", "r1"],
        # And the other moves over it: what may be pruned while a forgetting
        # document stands in for what is named, a receive from itself, and
        # its manifest, each forgetting document listed with what it forgets.
        ["prune", "-n"],
        ["prune"],
        ["receive", ".", "-n"],
        ["offer", "."],
        ["files", "head"],
        ["cat", "head", "notes.md"],
        ["cat", "first", "notes.md"],
        ["cat", "r1", "notes.md"],
        ["cat", "r3", "notes.md"],
        ["cat", "r9", "notes.md"],
        ["cat", "first", "photo.bin"],
        ["cat", "r5", "photo.bin"],
        ["cat", "m1", "f.md"],
        ["cat", "left", "f.md"],
        ["cat", "head", "f.md"],
        ["show", "head", "notes.md"],
        ["show", "first", "notes.md"],
        ["show", "r1", "notes.md"],
        ["show", "r3", "notes.md"],
        ["show", "first", "photo.bin"],
        ["show", "m1", "f.md"],
        ["show", "left", "f.md"],
        ["diff", "head"],
        ["diff", "first"],
        ["diff", "r1"],
        ["diff", "r3"],
        ["diff", "r5"],
        ["diff", "left"],
        ["diff", "m1", "--onto", "left"],
        ["diff", "m1", "--onto", "right"],
        ["diff", "head", "--onto", "first"],
        ["blame", "head", "notes.md"],
        ["blame", "first", "notes.md"],
        ["blame", "r3", "notes.md"],
        ["blame", "m1", "f.md"],
        ["blame", "left", "f.md"],
        ["blame", "notes.md"],
        ["blame", "f.md"],
        ["status"],
        ["status", "--onto", "r9"],
        ["diff"],
        ["diff", "--onto", "r1"],
        ["record", "-n"],
        ["record", "-m", "again"],
        ["record", "notes.md", "-m", "some"],
        ["amend", "-m", "reworded"],
        ["carry", "r13", "--onto", "r11"],
        ["carry", "left", "--onto", "right"],
        # Forgetting what is already forgotten, and more of a document
        # something already stands in for.
        ["forget", "first", "notes.md", "--lines", "2"],
        ["forget", "first", "notes.md", "--lines", "2", "--fields"],
        ["forget", "first", "notes.md", "--lines", "2..4"],
        ["forget", "first", "notes.md", "--lines", "1..6"],
        ["forget", "head", "notes.md", "--lines", "3..4"],
        ["forget", "left", "f.md", "--lines", "3"],
        ["forget", "m1", "f.md", "--lines", "1..4"],
        ["forget", "first", "photo.bin"],
        ["forget", "first", "photo.bin", "--fields"],
        ["forget", "r5", "photo.bin"],
    ],
    # Decisions 0014, 0050 and 0066, written: `forget` over the same history
    # with nothing forgotten yet, and with a state of `notes.md` and a
    # catalogue in `cache/`, compared with the whole store after — `cache/`
    # included, whose copies of what goes go with it.
    "forgetting": [
        ["forget", "head", "notes.md", "--lines", "2..3", "--dry-run"],
        ["forget", "head", "notes.md", "--lines", "2..3"],
        ["forget", "-n", "head", "notes.md", "--lines", "1"],
        ["forget", "head", "notes.md", "--lines", "1..6"],
        ["forget", "first", "notes.md", "--lines", "2"],
        ["forget", "r9", "notes.md", "--lines", "+2..03"],
        ["forget", "head", "notes.md", "--lines", "2", "--fields"],
        ["forget", "left", "f.md", "--lines", "3"],
        ["forget", "m1", "f.md", "--lines", "1"],
        ["forget", "m1", "f.md", "--lines", "1..4"],
        ["forget", "right", "f.md", "--lines", "1..3", "--fields"],
        ["forget", "first", "photo.bin"],
        ["forget", "first", "photo.bin", "--dry-run"],
        ["forget", "head", "photo.bin", "--fields"],
        ["forget", "r5", "photo.bin"],
        ["forget", "file:ffff", "notes.md", "--lines", "1"],
        # Every refusal.
        ["forget", "head", "notes.md"],
        ["forget", "head", "empty.md"],
        ["forget", "head", "empty.md", "--lines", "1"],
        ["forget", "head", "photo.bin", "--lines", "1..2"],
        ["forget", "head", "link", "--lines", "1"],
        ["forget", "head", "link"],
        ["forget", "head", "notes.md", "--lines", "0..1"],
        ["forget", "head", "notes.md", "--lines", "3..2"],
        ["forget", "head", "notes.md", "--lines", "7"],
        ["forget", "head", "notes.md", "--lines", "18446744073709551615"],
        ["forget", "head", "notes.md", "--lines", "0..1", "--fields"],
        ["forget", "nope", "notes.md", "--lines", "1"],
        ["forget", "nope", "notes.md", "--lines", "1", "--fields"],
        ["forget", "head", "nothere.md", "--lines", "1"],
        ["forget", "head", "file:", "--lines", "1", "--fields"],
        ["forget", "", "notes.md", "--fields"],
        # And every command line that is wrong.
        ["forget"],
        ["forget", "head"],
        ["forget", "head", "notes.md", "extra"],
        ["forget", "head", "notes.md", "--lines"],
        ["forget", "head", "notes.md", "--lines", "x"],
        ["forget", "head", "notes.md", "--lines", "1..2..3"],
        ["forget", "head", "notes.md", "--lines", "18446744073709551616"],
        ["forget", "head", "notes.md", "--lines", "-1"],
        ["forget", "head", "notes.md", "--frob"],
        ["forget", "head", "notes.md", "--lines", "1", "--dry-run", "--fields"],
    ],
    # Decision 0014 with the originals still held: stand-ins the Rust tool
    # wrote elsewhere copied in beside them, as a sync that copies files
    # leaves a store. Every reader reads through them where the Rust tool
    # does — an operation document and a `text` payload with each item a
    # stand-in forgets forgotten, a resolution and a payload of bytes as
    # held — and `forget` takes them as what is already forgotten.
    "resurrected": [
        ["log"],
        ["files", "head"],
        ["cat", "head", "notes.md"],
        ["cat", "first", "notes.md"],
        ["cat", "r3", "notes.md"],
        ["cat", "r9", "notes.md"],
        ["cat", "first", "photo.bin"],
        ["cat", "m1", "f.md"],
        ["cat", "left", "f.md"],
        ["show", "head", "notes.md"],
        ["show", "first", "notes.md"],
        ["show", "first", "photo.bin"],
        ["show", "m1", "f.md"],
        ["show", "left", "f.md"],
        # Not `diff head`: the Rust store catalogues nothing a resolution
        # forgets, so it finds the stand-in beside `m1`'s resolution only
        # once something has made it scan every document — which assembling
        # that resolution once does, since it keeps from a payload. `diff
        # head` reads it twice, and says the revision after the merge turned
        # `L` into `\ forgotten` in a file it did not touch.
        ["diff", "first"],
        ["diff", "r3"],
        ["diff", "left"],
        ["diff", "m1", "--onto", "left"],
        ["diff", "head", "--onto", "first"],
        ["blame", "head", "notes.md"],
        ["blame", "first", "notes.md"],
        ["blame", "m1", "f.md"],
        ["blame", "left", "f.md"],
        ["blame", "notes.md"],
        ["blame", "f.md"],
        ["status"],
        ["status", "--onto", "r9"],
        ["diff"],
        ["diff", "--onto", "r1"],
        ["record", "-n"],
        ["record", "-m", "again"],
        ["amend", "-m", "reworded"],
        ["carry", "r13", "--onto", "r11"],
        ["carry", "left", "--onto", "right"],
        ["forget", "first", "notes.md", "--lines", "2"],
        ["forget", "first", "notes.md", "--lines", "2..4"],
        ["forget", "head", "notes.md", "--lines", "3..4"],
        ["forget", "head", "notes.md", "--lines", "1..2", "--fields"],
        ["forget", "left", "f.md", "--lines", "3"],
        ["forget", "m1", "f.md", "--lines", "1"],
        ["forget", "first", "photo.bin"],
        ["forget", "r5", "photo.bin", "--dry-run"],
    ],
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
        ["merge"],
        ["prune", "-n"],
        ["prune"],
    ],
    # `fetch` from a published copy served over HTTP from a thread of this
    # script (`{web}` is its address): into an empty store, every file the
    # manifest names; a copy of this store's own, nothing new; a copy that
    # forgot a line and a payload; a stranger, which an empty store may take;
    # a manifest naming a digest a payload's bytes do not have; one naming a
    # revision that is not there, read four times and refused; one being
    # rewritten, read twice; one naming a directory this historica does not
    # carry and a kind it does not know; one in a spelling it does not
    # know, one malformed, one not text, and none at all; and every usage
    # error, and `--fields` beside each kind of ending.
    "fetching": [
        ["fetch", "{web}/pub/offer.txt"],
        ["fetch", "{web}/pub/offer.txt", "--fields"],
        ["fetch", "--fields", "{web}/pub/offer.txt"],
        ["fetch", "{web}/same/offer.txt"],
        ["fetch", "{web}/fg/offer.txt"],
        ["fetch", "{web}/stranger/offer.txt"],
        ["fetch", "{web}/lie/offer.txt"],
        ["fetch", "{web}/lie/offer.txt", "--fields"],
        ["fetch", "{web}/stale/offer.txt"],
        ["fetch", "{web}/stale/offer.txt", "--fields"],
        ["fetch", "{web}/moving/offer.txt"],
        ["fetch", "{web}/declined/offer.txt"],
        ["fetch", "{web}/spelled/offer.txt"],
        ["fetch", "{web}/malformed/offer.txt"],
        ["fetch", "{web}/headless/offer.txt"],
        ["fetch", "{web}/binary/offer.txt"],
        ["fetch", "{web}/nowhere/offer.txt"],
        ["fetch", "{web}/nowhere/offer.txt", "--fields"],
        ["fetch"],
        ["fetch", "--fields"],
        ["fetch", "-x", "{web}/pub/offer.txt"],
        ["fetch", "{web}/pub/offer.txt", "{web}/same/offer.txt"],
        ["fetch", "127.0.0.1/offer.txt"],
        ["fetch", "http://127.0.0.1"],
        ["fetch", "http://127.0.0.1/pub/"],
        ["fetch", "{web}/pub/offer.txt?v=2"],
        ["fetch", "{web}/pub/offer.txt#top"],
    ],
    # And into a store holding the first revision of what was published: the
    # rest taken; the store's own copy, holding nothing new, its bookmark
    # kept; the forgetting copy, whose stand-ins destroy the originals here;
    # a stranger refused, and joined when asked.
    "fetched": [
        ["fetch", "{web}/pub/offer.txt"],
        ["fetch", "{web}/pub/offer.txt", "--fields"],
        ["fetch", "{web}/same/offer.txt"],
        ["fetch", "{web}/same/offer.txt", "--fields"],
        ["fetch", "{web}/fg/offer.txt"],
        ["fetch", "{web}/stranger/offer.txt"],
        ["fetch", "{web}/stranger/offer.txt", "--fields"],
        ["fetch", "{web}/stranger/offer.txt", "--join-unrelated"],
        ["fetch", "--join-unrelated", "--fields", "{web}/stranger/offer.txt"],
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
        ["update"],
        ["prune"],
        ["prune", "--fields"],
        ["arrange", "-n"],
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
                       "underlate", "authortwice", "noauthor", "sameunder", "empty", "comment", "crlf", "latin1", "cut")),
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
                ["record", "--fields", "-m", "x"], ["amend", "--fields", "-m", "y"], ["abandon", "head", "--fields", "-m", "z"], ["carry", "--fields"], ["name", "--fields", "x", "head"], ["prune", "-n"]],
    # A store filed flat, by digest, as an older writer or a copy by hand
    # leaves one: one revision in a folder of a person's own, one filed in
    # its month already, content under digest names and in a directory of
    # its own, two files holding one document, a file no revision names,
    # and three revisions sharing a summary — two changes, and a reword of
    # one — so every tier of a name is reached. Arranged in place and
    # refiled, planned and done, and a word it does not take refused.
    "arranging": [
        ["arrange", "-n"],
        ["arrange", "--dry-run", "--refile"],
        ["arrange"],
        ["arrange", "--refile", "-n", "--refile"],
        ["arrange", "--refile"],
        ["arrange", "-n", "extra"],
        ["arrange", "--bogus", "-n"],
    ],
    # A revision amended, and a run of three abandoned, so pruning takes
    # the one and clears the run over passes; content only they named, and
    # content a kept revision shares; a second copy of a pruned revision in
    # a folder of its own; an empty directory, a platform's file and a
    # cache entry. And two stores `check` calls broken: a revision filed
    # under a digest it does not have, and one that does not parse.
    "pruning": [
        # A copy of what the head stands on, which leaves the amended and
        # abandoned revisions behind and a `supersedes` edge dangling.
        ["export", "out"],
        ["prune", "-n"],
        ["prune"],
        ["prune", "--fields"],
        ["prune", "--dry-run", "--fields"],
        ["prune", "--bogus", "-n"],
        ["prune", "-n", "extra"],
        ["arrange", "-n"],
    ],
    "lying": [["prune", "-n"], ["prune", "--fields"], ["arrange", "-n"]],
    # (The parser's reasons are the port's own words, not the Rust tool's,
    # so `arrange`'s refusal to open this store is not compared.)
    "unparsed": [["prune", "-n"], ["prune", "--fields"]],
    # A store and three beside it, filed in its folder: a copy that went on —
    # a revision, a document and a payload this one lacks, bookmarks new,
    # moved, and made private at one target, three rules one of which takes
    # a label a file here already has, and a file of `claims/` — with its
    # `main` moved elsewhere and without; and a stranger. Planned, done and
    # stated; refused over the disagreement, over the stranger unless
    # joined, over a directory with no store, and over the words.
    "receiving": [
        ["receive", "agreeing", "-n"],
        ["receive", "agreeing"],
        ["receive", "--fields", "agreeing"],
        ["receive", "agreeing/history", "--dry-run"],
        ["receive", "other", "-n"],
        ["receive", "other"],
        ["receive", "other", "--fields"],
        ["receive", "stranger", "-n"],
        ["receive", "stranger", "--join-unrelated", "-n"],
        ["receive", "stranger", "--join-unrelated"],
        ["receive", "nowhere"],
        ["receive", "nowhere", "--fields"],
        ["receive", "."],
        ["receive"],
        ["receive", "a", "b"],
        ["receive", "-x", "agreeing"],
        ["receive", "agreeing", "-n", "--fields"],
        ["receive", "forgetful", "-n"],
        ["receive", "forgetful"],
        ["receive", "forgetful", "--fields"],
        # The manifest of each store in the folder, and of this one: every
        # kind a file can be listed as, what a forgetting document forgets,
        # and the private rule and bookmark left out.
        ["offer", "."],
        ["offer", "agreeing"],
        ["offer", "forgetful"],
        ["offer", "stranger"],
        ["offer", "history"],
        ["offer", "nowhere"],
        ["offer"],
        ["offer", "a", "b"],
        ["offer", "agreeing", "-x"],
    ],
    # A store with every kind of file — lines, bytes, a runnable file, a
    # link by reference and one verbatim, one in a directory — over three
    # revisions, a forgetting document for a file the head no longer holds,
    # bookmarks shared, private, pinned to the first revision and naming a
    # file, rules shared, private and none, a file of `claims/`, and a
    # directory in its folder holding somebody's file. Exported whole and
    # as a folder, at the head and at the first revision, planned and done;
    # refused over the occupied directory, a target that is not one, and the
    # words.
    # Copies an export made, before the store went on: at the first revision,
    # at the head, and each of those touched — a file edited, a stray file
    # added, a revision recorded in it, a revision file that does not parse
    # — and a stranger's store. Since then a line of a file only the second
    # revision held was forgotten, a bookmark deleted and one made private, a
    # rule deleted and one added. Each is brought up to date, planned and
    # done, at the head and at the first revision, or refused.
    "updating": [
        ["export", "-n", "copy-old"],
        ["export", "copy-old"],
        ["export", "copy-old", "old"],
        ["export", "-n", "copy-head"],
        ["export", "copy-head"],
        ["export", "--dry-run", "copy-head", "old"],
        ["export", "copy-head", "old"],
        ["export", "-n", "copy-edited"],
        ["export", "copy-edited"],
        ["export", "copy-stray"],
        ["export", "copy-disturbed", "old"],
        ["export", "copy-recorded"],
        ["export", "-n", "copy-recorded"],
        ["export", "copy-stranger"],
        ["export", "copy-broken"],
        ["export", "notes.md"],
        ["export", "-n", "notes.md/deeper"],
        ["export", "--files-only", "notes.md"],
        ["export", "--files-only", "-n", "notes.md/deeper"],
    ],
    "exporting": [
        ["export", "-n", "out"],
        ["export", "out"],
        ["export", "--dry-run", "out", "old"],
        ["export", "out", "old"],
        ["export", "deep/er/out"],
        ["export", "--files-only", "-n", "out"],
        ["export", "--files-only", "out"],
        ["export", "out", "old", "--files-only"],
        ["export", "occupied"],
        ["export", "-n", "occupied"],
        ["export", "--files-only", "occupied"],
        ["export", "out", "nosuch"],
        ["export"],
        ["export", "a", "b", "c"],
        ["export", "-x", "out"],
        ["export", "out", "--files"],
    ],
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
        ["update"],
        ["update", "-n", "head"],
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
        ["merge"],
        ["merge", "left"],
        ["record", "--onto", "left", "--merge", "right", "-m", "joined"],
        ["record", "--merge", "left", "--merge", "right", "-m", "joined", "a.md"],
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
        ["merge", "right", "left"],
        ["record", "--onto", "left", "--merge", "right", "--at", "lx=x.md", "--at", "rx=x-right.md", "--accept", "c.bin", "-m", "settled"],
        ["record", "--onto", "left", "--merge", "right", "--at", "lx=x.md", "--at", "rx=x-right.md", "--accept", "c.bin", "--accept", "a.md", "-m", "settled"],
    ],
    # Decision 0033: a folder whose names the filesystem hands back
    # decomposed — a file, a directory, a file of bytes, and a link whose
    # target is spelled so — recorded, then edited, renamed with `mv`, and
    # joined by new ones, one of them beside the same name composed; a rule
    # and a pattern stated decomposed; and every command given paths
    # decomposed, `path:` and all. Each reads them in normal form C, as the
    # Rust tool does, and opens each file where the folder spells it.
    "normal": [
        ["status"], ["status", "--onto", "first"],
        ["diff"], ["diff", "cafe\u0301.md"], ["diff", "path:cafe\u0301.md"], ["diff", "caf\u00e9.md"],
        ["diff", "head", "cafe\u0301.md"], ["diff", "--onto", "first", "re\u0301sume\u0301/cv.md"],
        ["blame", "cafe\u0301.md"], ["blame", "head", "cafe\u0301.md"], ["blame", "twi\u0301n.md"], ["blame", "path:nai\u0308ve.md"],
        ["cat", "head", "cafe\u0301.md"], ["cat", "first", "photo\u0301.bin"], ["cat", "head", "nope\u0301.md"],
        ["show", "head", "cafe\u0301.md"], ["files", "head"], ["log", "--path", "cafe\u0301.md"],
        ["name", "mark", "head", "cafe\u0301.md"], ["name", "cafe\u0301", "head"], ["name", "caf\u00e9", "head"],
        ["record", "-n"], ["record", "-n", "cafe\u0301.md"], ["record", "-n", "re\u0301sume\u0301/"],
        ["record", "-n", "--move", "notes.md=no\u0308tes.md"], ["record", "-n", "--move", "cafe\u0301.md=moved.md"],
        ["record", "-n", "--bytes", "nai\u0308ve.md"], ["record", "-n", "--lines", "cafe\u0301.bin"],
        ["record", "-n", "--move", "twi\u0301n.md=twin2.md"],
        ["record", "-m", "second"], ["record", "-m", "only", "cafe\u0301.bin", "twi\u0301n.md"],
        ["amend", "-n", "--move", "cafe\u0301.md=moved.md"],
    ],
    # The same spelling where a command writes the folder: a folder spelled
    # decomposed and in step with one head, a second line of work beside it.
    # `update` opens each file the walk found where the folder spells it —
    # rewriting, removing, relinking and setting the bit on that one rather
    # than laying another beside it — tidies above a removal as the tree
    # spells it, so a directory spelled decomposed that it empties stays, and
    # joins a path the walk did not find onto the folder as the tree spells
    # it; `merge` asks the folder at the tree's spelling, as the Rust tool's
    # does, walk or none.
    "renormal": [
        ["status"], ["update"], ["update", "-n", "first"], ["update", "first"],
        ["update", "-n", "side"], ["update", "side"], ["update", "second"],
        ["merge", "second", "side"], ["merge"],
        ["status", "--onto", "second", "--merge", "side"],
        ["record", "-n", "--onto", "second", "--merge", "side"],
    ],
    # Names that are not UTF-8, which the format cannot hold: beside the
    # store and in a directory, one a directory itself, one sorting between
    # two names the lossy spelling would put the other way round, and one
    # under a directory spelled decomposed — among other refusals, which
    # they are listed in the walk's order with. `status` and `record` refuse
    # each in the Rust tool's words, naming where it is on disk, and a
    # record that is not looking at them goes on.
    "unspelled": [
        ["status"], ["record", "-n"], ["record", "-n", "notes.md"], ["record", "-n", "sub"], ["record", "-n", "sub/ok.md"],
        ["diff"], ["blame", "notes.md"], ["record", "-m", "refused"], ["record", "-m", "notes only", "notes.md"],
    ],
    # A revision stating a path not in normal form C, which no writer
    # makes: the Rust tool opens the store on its causal headers and refuses
    # it where the whole of it is read, naming the line. So every reader of
    # it refuses in those words — `log` and `show` as they are, a tree with
    # what the revisions did — and one that reads only what came before it,
    # or only its causal headers, goes on.
    "unnormal": [
        ["log"], ["log", "first"], ["log", "--limit", "0"], ["log", "--fields"],
        ["files", "head"], ["files", "first"], ["files", "main"],
        ["cat", "head", "notes.md"], ["cat", "first", "notes.md"],
        ["show", "head"], ["show", "head", "notes.md"], ["show", "first"],
        ["diff"], ["diff", "head"], ["diff", "first"], ["diff", "--onto", "first"],
        ["blame", "notes.md"], ["blame", "head", "notes.md"], ["blame", "first", "notes.md"],
        ["status"], ["status", "--onto", "first"], ["record", "-n"], ["record", "-n", "--onto", "first"],
        ["names"], ["name", "x", "head"], ["name", "y", "head", "notes.md"], ["name", "z", "first", "notes.md"],
    ],
    # Two merges the Rust tool resolved, the first by hand: resolutions that
    # keep a payload's lines, an operation document's inserts and an earlier
    # resolution's, and insert their own — and a merge written here for each
    # way a resolution can fail to assemble or to parse.
    "merge": [
        # A store `check` calls broken is not copied.
        ["export", "out", "m1"],
        *(["cat", target, path] for target in ("left", "m1", "after", "m2") for path in ("f.md", "h.md")),
        *(["cat", target, "f.md"] for target in ("unknown", "range", "result", "notlast", "adjacent", "positioned", "twice")),
        ["cat", "across", "f.md"],
        ["blame", "across", "f.md"],
        ["merge", "left", "right"],
        ["status", "--onto", "twice", "--merge", "x"],
        ["record", "-n", "--onto", "twice", "--merge", "x"],
        ["diff", "m1"],
        ["diff", "m1", "--onto", "left"],
        ["diff", "m2", "--onto", "x", "f.md"],
        *(["blame", target, path] for target in ("m1", "m2") for path in ("f.md", "h.md")),
        *(["update", target] for target in ("m2", "unknown", "result")),
    ],
    # Merges that state no resolution, written by hand as the Rust tool
    # never would: where decision 0032's rule stops, and the file is what
    # `merge.bend`'s proven walk reads. Two branches edit apart, and one
    # deletes beside the other's insert; two insert at one place, so the
    # digests break the tie; a third merge joins all three; and `after` is
    # recorded on top of one, so its edit counts into the walked file; and
    # a merge joining a resolution with an edit concurrent with it.
    # The folder behind the store, caught up: `update` to a head writes what
    # the head records, removes what it does not where history records the
    # bytes, sets modes, points links, and leaves a stray and a file nobody
    # recorded alone; a second head, a revision that is not one, and the
    # words it refuses.
    "updating": [
        ["update"],
        ["update", "-n", "tip"],
        ["update", "--dry-run", "tip"],
        ["update", "tip"],
        ["update", "side"],
        ["update", "-n", "side"],
        ["update", "base"],
        ["update", "nope"],
        ["update", "tip", "side"],
        ["update", "--bogus"],
        ["update", "-n", "--bogus", "tip"],
    ],
    # The same store once the folder holds the tip: settled, and the other
    # head from there, into directories that are not there yet.
    "caught": [
        ["update", "tip"],
        ["update", "-n", "tip"],
        ["update", "side"],
        ["update", "-n", "side"],
    ],
    # A head the folder cannot take: two files at one path, bytes stated
    # whole on both sides, a file and a directory at one path, a payload the
    # store does not hold; and in the folder a link where a file goes, a
    # directory, unrecorded bytes where a link goes, a pipe, and a file a
    # rule skips.
    "blocked": [["update"], ["update", "-n"], ["update", "clash"]],
    # Two lines of work that met: one line rewritten both ways, a line one
    # side deleted beside the other's insertion, a last line two sides end
    # differently, edits apart, a file only one side edited, and a mode one
    # side set — `merge` fences what met and writes the rest; and a file
    # the folder holds that neither side recorded, which it leaves alone.
    "meeting": [
        ["merge"],
        ["merge", "left"],
        ["merge", "right", "left"],
        ["merge", "nope"],
        ["merge", "--bogus"],
        ["record", "--merge", "left", "--merge", "right", "-m", "the right side"],
    ],
    # The same once `merge` has written it and a person has started: one
    # file resolved, one untouched, one with only the closing line
    # deleted, and a file quoting a fence nobody rendered here. `status`
    # counts what stands, `record` refuses it, and `merge` again leaves
    # the work alone.
    "marked": [
        ["status", "--onto", "left", "--merge", "right"],
        ["status", "--merge", "right", "--merge", "left"],
        ["record", "-n", "--onto", "left", "--merge", "right"],
        ["record", "-n", "--merge", "left", "--merge", "right"],
        ["record", "-n", "--merge", "left", "--merge", "right", "h.md"],
        ["merge"],
    ],
    # And with one file left marked.
    "marked1": [["status", "--onto", "left", "--merge", "right"], ["record", "-n", "--onto", "left", "--merge", "right"]],
    # And resolved: a merge recorded, each file the parents disagree about
    # stated as a resolution of what the walk proposed — named items kept,
    # what the person wrote inserted — beside an ordinary edit of a file
    # they agree about.
    # Files of lines laid down through the links standing at their paths,
    # as `std::fs::write` lays them, and a payload's link replaced.
    "through": [["merge"], ["merge", "left"]],
    "resolved": [
        ["status", "--onto", "left", "--merge", "right"],
        ["record", "-n", "--merge", "left", "--merge", "right"],
        ["record", "--merge", "left", "--merge", "right", "-m", "joined"],
        ["record", "--onto", "left", "--merge", "right", "-m", "joined", "--fields"],
        ["record", "--merge", "right", "--onto", "left", "-m", "joined\n\nat length"],
        ["merge"],
    ],
    "walked": [
        # A merge's resolution travels with every document it keeps items
        # of, and a folder is laid out from the walk where nothing states it.
        ["export", "out", "resolved"],
        ["export", "--files-only", "out", "crossed"],
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
        *(["update", target] for target in ("after", "all", "crossed", "joined")),
        ["merge", "tops"],
        ["merge", "after", "tops"],
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
    "redacted": [],
    "quoting": [],
    "unnamed": [["log"], ["names"], ["status"], ["files", "head"], ["skip"], ["record", "-n"], ["record", "-m", "x", "--fields"], ["name", "x", "head"]],
    "unruled": [["log"], ["names"], ["status"], ["skip"], ["skip", "y"], ["record", "-n"], ["record", "-m", "x", "--fields"]],
    "requoted": [],
    "unreadable": [["log"], ["cat", "head", "notes.md"], ["cat", "head", "other.md"], ["show", "head", "notes.md"], ["show", "head", "other.md"],
                   ["diff", "head"], ["blame", "head", "notes.md"], ["blame", "head", "other.md"], ["files", "head"], ["status"],
                   ["diff"], ["blame", "notes.md"], ["record", "-n"]],
}


# The corpora's documents that do not parse, filed among the ones that do:
# every command that opens the store refuses a revision whose shape does
# not read, in the parser's words and naming the file; one that reads only
# as far as opening is in the graph, and refused where a command asks what
# it did; an operation document that does not parse is refused where it is
# read. `check` reports every one. Each revision is asked after, and its
# file, by digest.
def invalid_cases(corpus, path):
    digests = []
    for folder in (CORPUS / corpus / "revisions", CORPUS / corpus / "invalid", CORPUS / corpus):
        if folder.is_dir():
            digests += [hashlib.sha256(p.read_bytes()).hexdigest()[:12] for p in sorted(folder.glob("*.rev.txt"))]
    cases = [["log"], ["names"], ["status"], ["files", "head"], ["show", "head"], ["cat", "head", path]]
    for d in digests:
        cases += [["log", d], ["files", d], ["show", d], ["cat", d, path], ["show", d, path]]
    return cases


for corpus, path in (("links", "config"), ("modes", "run.sh"), ("whole", "notes/2026-08-20.md"), ("revisions", "notes.txt"), ("merged", "notes.txt")):
    STORES[f"{corpus}-invalid"] = invalid_cases(corpus, path)

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
    """Merges like `m1`, each naming a resolution of `f.md` broken one way:
    for `cat`, or, keeping one line twice, for a walk reaching across it.

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
        # Assembles, as `cat` reads it, to the first line twice; the walk
        # of a merge reaching across it refuses the second keep.
        "twice": re.sub(r"^result \S+", "result " + digest(b"a\na\nBOTH\nc\nd"), resolution.replace(f"keep {kept} 0 1\n", f"keep {kept} 0 1\nkeep {kept} 0 1\n", 1), flags=re.M),
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
    if corpus == "fetched":
        # The published source as it stood at its first revision, which
        # `serve` kept aside.
        shutil.rmtree(store)
        shutil.copytree(temporary / "web-first", store, symlinks=True)
    elif corpus == "unicode":
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
        join(store / "history", "across", ("twice", "x"), "t" * 24)
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
    elif corpus in ("updating", "caught"):
        def rec(name, *command):
            done = subprocess.run([rust, "record", *command], cwd=store, env=env, check=True, capture_output=True, text=True, timeout=120)
            digest = re.search(r"^recorded [a-z]+ as ([0-9a-f]+)", done.stdout, re.M).group(1)
            historica("name", name, digest, "--revision")

        def base():
            (store / "a.md").write_text("a\n")
            (store / "b.bin").write_bytes(b"\x00base")
            (store / "run.sh").write_text("#!/bin/sh\n")
            (store / "run.sh").chmod(0o755)
            (store / "keep.md").write_text("kept\n")
            (store / "d").mkdir(exist_ok=True)
            (store / "d" / "deep.md").write_text("deep\n")
            for link, target in (("lnk", "a.md"), ("gone-link", "d/deep.md")):
                if os.path.lexists(store / link):
                    os.remove(store / link)
                os.symlink(target, store / link)

        base()
        rec("base", "-m", "base")
        (store / "a.md").write_text("a\nand more\n")
        (store / "b.bin").write_bytes(b"\x00tip")
        (store / "run.sh").chmod(0o644)
        shutil.rmtree(store / "d")
        os.remove(store / "lnk")
        os.symlink("keep.md", store / "lnk")
        os.remove(store / "gone-link")
        (store / "new.md").write_text("new\n")
        (store / "e").mkdir()
        (store / "e" / "x.sh").write_text("#!/bin/sh\necho\n")
        (store / "e" / "x.sh").chmod(0o755)
        rec("tip", "-m", "tip")
        (store / "new.md").unlink()
        shutil.rmtree(store / "e")
        base()
        (store / "a.md").write_text("a\nside\n")
        (store / "side.md").write_text("side\n")
        rec("side", "--onto", "base", "-m", "side")
        # The folder as the base left it, a stray nobody recorded, and the
        # side's file edited and not recorded.
        (store / "a.md").write_text("a\n")
        (store / "stray.md").write_text("stray\n")
        (store / "side.md").write_text("side, edited\n")
        if corpus == "caught":
            historica("update", "tip")
            (store / "side.md").unlink()
    elif corpus in ("meeting", "marked", "marked1", "resolved"):
        def rec(name, *command):
            done = subprocess.run([rust, "record", *command], cwd=store, env=env, check=True, capture_output=True, text=True, timeout=120)
            digest = re.search(r"^recorded [a-z]+ as ([0-9a-f]+)", done.stdout, re.M).group(1)
            historica("name", name, digest, "--revision")

        def write(**files):
            for path, text in files.items():
                (store / f"{path}.md").write_text(text)

        write(f="a\nb\nc\n", g="one\ntwo\nthree\nfour\n", h="x\ny\nz\n", t="end", o="only\n", k="kept\n")
        (store / "run.sh").write_text("#!/bin/sh\n")
        rec("base", "-m", "base")
        write(f="a\nLEFT\nc\n", g="zero\none\ntwo\nthree\nfour\n", h="x\nz\n", t="end, left", o="only, left\n")
        (store / "run.sh").chmod(0o755)
        rec("left", "-m", "left")
        write(f="a\nRIGHT\nc\n", g="one\ntwo\nthree\nfour\nfive\n", h="x\ny\nY\nz\n", t="end, right\n", o="only\n", k="kept, and not recorded\n")
        (store / "run.sh").chmod(0o644)
        (store / "run.sh").write_text("#!/bin/sh\necho right\n")
        write(k="kept\n")
        rec("right", "--onto", "base", "-m", "right")
        write(k="kept, and not recorded\n")
        if corpus in ("marked", "marked1", "resolved"):
            historica("merge")
            text = (store / "t.md").read_text()
            write(f="a\nLEFT and RIGHT\nc\n", t=text[: text.rindex("^^^ historica")], k="kept, and not recorded\nvvv historica: 0badbeef wrote vvv\n")
            if corpus in ("marked1", "resolved"):
                write(h="x\nY\nz\n")
            if corpus == "resolved":
                write(t="end, both ways\n", g="zero\none\ntwo, then\nthree\nfour\nfive\n")
    elif corpus == "through":
        # Two lines of work, and a folder whose files of lines are links:
        # one to a file holding a head's version, one naming nothing yet,
        # one to a plain copy of a file the tree runs, one to a file holding
        # work nobody recorded; and a payload's path a link to its bytes.
        def rec(name, *command):
            done = subprocess.run([rust, "record", *command], cwd=store, env=env, check=True, capture_output=True, text=True, timeout=120)
            digest = re.search(r"^recorded [a-z]+ as ([0-9a-f]+)", done.stdout, re.M).group(1)
            historica("name", name, digest, "--revision")

        def write(**files):
            for path, text in files.items():
                (store / f"{path}.md").write_text(text)

        write(f="a\nb\nc\n", g="g\n", h="h\n", o="o\n")
        (store / "run.sh").write_text("#!/bin/sh\n")
        (store / "run.sh").chmod(0o755)
        (store / "p.bin").write_bytes(b"\x00p")
        rec("base", "-m", "base")
        write(f="a\nLEFT\nc\n", o="o, left\n")
        rec("left", "-m", "left")
        write(f="a\nRIGHT\nc\n", o="o\n")
        rec("right", "--onto", "base", "-m", "right")
        real = store / "real"
        real.mkdir()
        (real / "f.txt").write_text("a\nRIGHT\nc\n")
        (real / "h.txt").write_text("mine\n")
        (real / "run.txt").write_text("#!/bin/sh\n")
        (real / "run.txt").chmod(0o644)
        (real / "p.bin").write_bytes(b"\x00p")
        for name, target in (("f.md", "real/f.txt"), ("g.md", "real/g.txt"), ("h.md", "real/h.txt"), ("run.sh", "real/run.txt"), ("p.bin", "real/p.bin")):
            (store / name).unlink()
            os.symlink(target, store / name)
    elif corpus == "blocked":
        (store / "a.md").write_text("a\n")
        (store / "c.bin").write_bytes(b"\x00base")
        (store / "t.md").write_text("t\n")
        (store / "p.md").write_text("p\n")
        (store / "m.bin").write_bytes(b"\x00missing")
        (store / "secret.md").write_text("secret\n")
        os.symlink("t.md", store / "lnk")
        historica("record", "-m", "base")
        historica("name", "base", "head", "--revision")
        (store / "x.md").write_text("left x\n")
        (store / "c.bin").write_bytes(b"\x00left")
        (store / "n").write_text("n\n")
        historica("record", "-m", "left")
        historica("name", "left", "head", "--revision")
        (store / "x.md").write_text("right x\n")
        (store / "c.bin").write_bytes(b"\x00right")
        (store / "n").unlink()
        (store / "n").mkdir()
        (store / "n" / "m.md").write_text("m\n")
        historica("record", "--onto", "base", "-m", "right")
        fields = subprocess.run([rust, "log", "--fields"], cwd=store, env=env, check=True, capture_output=True, text=True).stdout
        left = (store / "history" / "names" / "left.txt").read_text().split()[1]
        right = next(line.split()[0] for line in fields.splitlines()[1:] if "head" in line.split()[3] and line.split()[0] != left)
        historica("name", "right", right, "--revision")
        join(store / "history", "clash", ("left", "right"), "k" * 24)
        # What stands in the folder's way.
        (store / "a.md").unlink()
        os.symlink("t.md", store / "a.md")
        (store / "t.md").unlink()
        (store / "t.md").mkdir()
        (store / "t.md" / "inner.md").write_text("inner\n")
        os.remove(store / "lnk")
        (store / "lnk").write_text("not a link\n")
        (store / "p.md").unlink()
        os.mkfifo(store / "p.md")
        (store / "history" / "skipped").mkdir(exist_ok=True)
        (store / "history" / "skipped" / "secret.txt").write_text("skip secret.md\n")
        missing = hashlib.sha256(b"\x00missing").hexdigest()
        for payload in (store / "history" / "operations").rglob("*"):
            if payload.is_file() and hashlib.sha256(payload.read_bytes()).hexdigest() == missing:
                payload.unlink()
        (store / "history" / "cache" / "operations.txt").unlink(missing_ok=True)
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
            # A carriage return ending the file, with no newline after it to
            # make it a line ending: it is the value's.
            (store / "history" / "skipped" / "unended.txt").write_bytes(b"skip a\r")
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
        # Files whose bytes are not UTF-8: a byte no character begins with,
        # and a character cut off by the end of the file.
        for case, data in (("latin1", b"author Caf\xe9 <c@example.com>\n"), ("cut", b"author Caf\xc3")):
            (store / "history" / "configs" / case / "historica").mkdir(parents=True)
            (store / "history" / "configs" / case / "historica" / "identity").write_bytes(data)
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
    elif corpus in ("quoting", "requoted"):
        # A line forgotten where one revision wrote it and a later one
        # deleted it, and then one of the two documents back as it was and
        # its forgetting gone: the redaction has not finished arriving, from
        # the side that deleted the line, or from the side that wrote it.
        (store / "n.md").write_text("one\n")
        historica("record", "-m", "one")
        (store / "n.md").write_text("one\ntwo\n")
        historica("record", "-m", "two")
        historica("name", "second", "head", "--revision")
        (store / "n.md").write_text("one\n")
        historica("record", "-m", "three")
        historica("forget", "second", "n.md", "--lines", "2..2")
        digest = lambda data: hashlib.sha256(data).hexdigest()
        operations = store / "history" / "operations"
        original = (
            f"historica\nresult {digest(b'one' + chr(10).encode())}\n\ndelete 1 1\n-two\n" if corpus == "quoting"
            else f"historica\nresult {digest(b'one' + chr(10).encode() + b'two' + chr(10).encode())}\n\ninsert 1\n+two\n"
        ).encode()
        (operations / "restored.ops.txt").write_bytes(original)
        for path in operations.glob("*.ops.txt"):
            if f"forgets {digest(original)}\n".encode() in path.read_bytes():
                path.unlink()
    elif corpus in ("unnamed", "unruled"):
        # A bookmark or a rule whose bytes are not UTF-8, which every
        # command refuses as it opens the store and `check` calls unreadable;
        # and in `unruled`, a rule cut off inside a character too.
        (store / "notes.md").write_text("one\n")
        historica("record", "-m", "one")
        if corpus == "unnamed":
            (store / "history" / "names" / "caf\u00e9.txt").write_bytes(b"change \xff\n")
        else:
            (store / "history" / "skipped" / "latin1.txt").write_bytes(b"skip caf\xe9\n")
            (store / "history" / "skipped" / "cut.txt").write_bytes(b"skip a\n\xe2\x82")
    elif corpus == "unreadable":
        # A revision written by hand naming an operation document, and a
        # resolution, that do not parse: nothing reads them until a command
        # asks what the revision did to the file.
        (store / "notes.md").write_text("one\n")
        (store / "other.md").write_text("a\n")
        historica("record", "-m", "one")
        (store / "notes.md").write_text("one\ntwo\n")
        (store / "other.md").write_text("a\nb\n")
        historica("record", "-m", "two")
        digest = lambda data: hashlib.sha256(data).hexdigest()
        history = store / "history"
        two = next(history.glob("revisions/*/* two.rev.txt"))
        first, second = sorted(re.findall(r"^edit (\S+) ", two.read_text(), re.M))
        document = f"historica\nresult {'b' * 64}\n\ndelete 0 1\n-one\ndelete 1 1\n-two\n"
        resolution = f"historica\nresult {'c' * 64}\n\nkeep {'a' * 64} 0 1\nkeep {'a' * 64} 1 1\n"
        (history / "operations" / "crafted.ops.txt").write_text(document)
        (history / "operations" / "resolved.ops.txt").write_text(resolution)
        (history / "revisions" / "crafted.rev.txt").write_text(
            f"historica\nchange {'m' * 24}\nparent {digest(two.read_bytes())}\nauthor Check <check@example.com>\n"
            f"when 2026-09-25T12:00:00+00:00\nedit {first} {digest(document.encode())}\nedit {second} {digest(resolution.encode())}\n\nthree"
        )
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
    elif corpus == "arranging":
        (store / "notes.md").write_text("one\n")
        (store / "sub").mkdir()
        (store / "sub" / "deep.md").write_text("deep\n")
        (store / "b.bin").write_bytes(b"\x00bin")
        (store / "odd.ops.txt").write_text("not a document\n")
        historica("record", "-m", "one")
        (store / "notes.md").write_text("one\ntwo\n")
        (store / "b.bin").write_bytes(b"\x00bin, again")
        historica("record", "-m", "same: again")
        (store / "notes.md").write_text("one\ntwo\nthree\n")
        historica("record", "-m", "same: again")
        (store / "notes.md").write_text("one\ntwo\nthree\nfour\n")
        historica("amend", "-m", "same: again")
        history = store / "history"
        digest = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
        first = next(p for p in history.glob("revisions/*/*.rev.txt") if p.name.endswith(" one.rev.txt"))
        # Everything but the first revision and its content filed flat, by
        # digest; one revision in a folder of a person's own, one file of
        # content in a directory of its own.
        for path in sorted(history.glob("revisions/*/*.rev.txt")):
            if path != first:
                path.rename(history / "revisions" / f"{digest(path)}.rev.txt")
        own = sorted(history.glob("revisions/*.rev.txt"))[0]
        (history / "revisions" / "mine").mkdir()
        own.rename(history / "revisions" / "mine" / own.name)
        kept = history / "operations" / first.parent.name / first.name.removesuffix(".rev.txt")
        for path in sorted(p for p in history.glob("operations/**/*") if p.is_file() and kept not in p.parents):
            name = digest(path) + (".ops.txt" if path.name.endswith(".ops.txt") and not path.name.startswith("odd") else "")
            path.rename(history / "operations" / name)
        for directory in sorted((p for p in history.glob("operations/**/*") if p.is_dir()), reverse=True):
            if not any(directory.iterdir()):
                directory.rmdir()
        document = next(p for p in history.glob("operations/*.ops.txt"))
        (history / "operations" / "by hand" / "deep").mkdir(parents=True)
        document.rename(history / "operations" / "by hand" / "deep" / document.name)
        shutil.copy(history / "operations" / "by hand" / "deep" / document.name, history / "operations" / "copy.ops.txt")
        shutil.copy(own.parent / "mine" / own.name, history / "revisions" / "copy.rev.txt")
        (history / "operations" / "stray.txt").write_text("named by nothing\n")
    elif corpus == "receiving":
        def at(where, *command):
            return subprocess.run([rust, *command], cwd=where, env=env, check=True, capture_output=True, text=True, timeout=120).stdout

        (store / "notes.md").write_text("one\n")
        (store / "p.bin").write_bytes(b"\x00p")
        historica("record", "-m", "one")
        historica("name", "main", "head")
        historica("name", "shared", "head")
        change = at(store, "log", "--fields").splitlines()[1].split()[1]
        # A copy that forgot the one line this store's first file holds, so
        # a forgetting document arrives and the original here is destroyed.
        forgetful = temporary / "receiving-forgetful"
        shutil.copytree(store, forgetful, symlinks=True)
        at(forgetful, "forget", "head", "notes.md", "--lines", "1..1")
        other = temporary / "receiving-other"
        shutil.copytree(store, other, symlinks=True)
        (other / "notes.md").write_text("one\ntwo\n")
        (other / "q.bin").write_bytes(b"\x00q")
        at(other, "record", "-m", "two")
        at(other, "name", "side", "head", "--revision")
        at(other, "name", "priv", "head", "--private")
        at(other, "name", "shared", change, "--private")
        at(other, "skip", "build/")
        at(other, "skip", "--private", "--name", "*.tmp")
        at(other, "skip", "--name", "x")
        (other / "history" / "claims" / "by").mkdir(parents=True)
        (other / "history" / "claims" / "by" / "one.txt").write_text("vouched\n")
        (other / "history" / "claims" / ".DS_Store").write_bytes(b"\x00")
        (store / "history" / "skipped" / "name x.txt").write_text("# a note, stating no rule\n")
        agreeing = temporary / "receiving-agreeing"
        shutil.copytree(other, agreeing, symlinks=True)
        (agreeing / "history" / "names" / "main.txt").unlink()
        stranger = temporary / "receiving-stranger"
        stranger.mkdir()
        at(stranger, "init", ".")
        (stranger / "else.md").write_text("elsewhere\n")
        at(stranger, "record", "-m", "elsewhere")
        for name, path in (("other", other), ("agreeing", agreeing), ("stranger", stranger), ("forgetful", forgetful)):
            path.rename(store / name)
    elif corpus == "updating":
        def at(where, *command):
            return subprocess.run([rust, *command], cwd=where, env=env, check=True, capture_output=True, text=True, timeout=120).stdout

        (store / "notes.md").write_text("one\n")
        (store / "photo.bin").write_bytes(b"\x00one")
        (store / "run.sh").write_text("#!/bin/sh\necho run\n")
        (store / "run.sh").chmod(0o755)
        (store / "sub").mkdir()
        (store / "sub" / "deep.md").write_text("deep\n")
        os.symlink("notes.md", store / "to-notes")
        os.symlink("/etc/hosts", store / "abs")
        historica("record", "-m", "one")
        historica("name", "old", "head", "--revision")
        (store / "gone.md").write_text("secret\nline\n")
        (store / "notes.md").write_text("one\ntwo\n")
        (store / "photo.bin").write_bytes(b"\x00two")
        historica("record", "-m", "two")
        two = at(store, "log", "--fields").splitlines()[1].split()[0]
        (store / "gone.md").unlink()
        (store / "sub" / "deep.md").write_text("deep\ner\n")
        (store / "run.sh").chmod(0o644)
        historica("record", "-m", "three")
        historica("name", "main", "head")
        historica("name", "doc", "head", "notes.md")
        historica("name", "gone", "head")
        historica("skip", "build/")
        historica("skip", "--name", "*.log")
        (store / "history" / "claims").mkdir()
        (store / "history" / "claims" / "one.txt").write_text("vouched\n")
        historica("export", "copy-old", "old")
        historica("export", "copy-head")
        historica("export", "copy-edited", "old")
        (store / "copy-edited" / "notes.md").write_text("mine\n")
        historica("export", "copy-stray", "old")
        (store / "copy-stray" / "stray.md").write_text("stray\n")
        historica("export", "copy-disturbed")
        (store / "copy-disturbed" / "notes.md").write_text("mine\n")
        historica("export", "copy-recorded", "old")
        (store / "copy-recorded" / "x.md").write_text("x\n")
        at(store / "copy-recorded", "record", "-m", "in the copy")
        historica("export", "copy-broken", "old")
        (store / "copy-broken" / "history" / "revisions" / "bad.rev.txt").write_text("garbage\n")
        (store / "copy-stranger").mkdir()
        at(store / "copy-stranger", "init", ".")
        (store / "copy-stranger" / "else.md").write_text("elsewhere\n")
        at(store / "copy-stranger", "record", "-m", "elsewhere")
        # The store goes on without recording: nothing the copies hold is
        # tracked by it.
        historica("forget", two, "gone.md", "--lines", "1..1")
        historica("name", "--delete", "gone")
        historica("name", "doc", "head", "notes.md", "--private")
        (store / "history" / "skipped" / "build" / "all.txt").unlink()
        historica("skip", "dist/")
    elif corpus == "exporting":
        def at(*command):
            return subprocess.run([rust, *command], cwd=store, env=env, check=True, capture_output=True, text=True, timeout=120).stdout

        (store / "notes.md").write_text("one\n")
        (store / "photo.bin").write_bytes(b"\x00one")
        (store / "run.sh").write_text("#!/bin/sh\necho run\n")
        (store / "run.sh").chmod(0o755)
        (store / "sub").mkdir()
        (store / "sub" / "deep.md").write_text("deep\n")
        os.symlink("notes.md", store / "to-notes")
        os.symlink("../notes.md", store / "sub" / "up")
        os.symlink("/etc/hosts", store / "abs")
        historica("record", "-m", "one")
        historica("name", "old", "head", "--revision")
        (store / "gone.md").write_text("secret\nline\n")
        (store / "notes.md").write_text("one\ntwo\n")
        (store / "photo.bin").write_bytes(b"\x00two")
        historica("record", "-m", "two")
        two = at("log", "--fields").splitlines()[1].split()[0]
        (store / "gone.md").unlink()
        (store / "sub" / "deep.md").write_text("deep\ner\n")
        historica("record", "-m", "three")
        # A forgetting document for a file only the second revision holds.
        historica("forget", two, "gone.md", "--lines", "1..1")
        historica("name", "main", "head")
        historica("name", "priv", "head", "--private")
        historica("name", "doc", "head", "notes.md")
        historica("skip", "build/")
        historica("skip", "--private", "--name", "*.tmp")
        (store / "history" / "skipped" / "note.txt").write_text("# a note, stating no rule\n")
        (store / "history" / "claims" / "by").mkdir(parents=True)
        (store / "history" / "claims" / "by" / "one.txt").write_text("vouched\n")
        (store / "history" / "claims" / ".DS_Store").write_bytes(b"\x00")
        (store / "occupied").mkdir()
        (store / "occupied" / "x.md").write_text("somebody's\n")
    elif corpus in ("pruning", "lying", "unparsed"):
        def rec(*command):
            done = subprocess.run([rust, "record", *command], cwd=store, env=env, check=True, capture_output=True, text=True, timeout=120)
            return re.search(r"^recorded [a-z]+ as ([0-9a-f]+)", done.stdout, re.M).group(1)

        (store / "notes.md").write_text("one\n")
        (store / "photo.bin").write_bytes(b"\x00one")
        rec("-m", "one")
        (store / "notes.md").write_text("one\ntwo\n")
        (store / "photo.bin").write_bytes(b"\x00two")
        rec("-m", "two")
        (store / "notes.md").write_text("one\ntwo\nthree\n")
        historica("amend", "-m", "two, amended")
        a = None
        for name in ("a", "b", "c"):
            (store / f"{name}.md").write_text(f"{name}\n")
            if name == "c":
                (store / "photo.bin").write_bytes(b"\x00one")
            digest = rec("-m", f"work {name}")
            a = a or digest
        historica("abandon", a, "-m", "not this line of work")
        history = store / "history"
        two = next(history.glob("revisions/*/* two.rev.txt"))
        (history / "revisions" / "copy").mkdir()
        shutil.copy(two, history / "revisions" / "copy" / two.name)
        (history / "operations" / "empty" / "er").mkdir(parents=True)
        (history / "operations" / ".DS_Store").write_bytes(b"\x00")
        (history / "cache" / ("0" * 64)).write_text("derived\n")
        if corpus == "lying":
            (history / "revisions" / ("1" * 64 + ".rev.txt")).write_bytes(two.read_bytes())
        if corpus == "unparsed":
            (history / "revisions" / "bad.rev.txt").write_text("garbage\n")
    elif corpus == "normal":
        # Spelled decomposed, as a filesystem that normalises to NFD hands
        # names back: `e` and U+0301 rather than `é`.
        (store / "cafe\u0301.md").write_text("one\ntwo\n")
        (store / "notes.md").write_text("notes\n")
        (store / "re\u0301sume\u0301").mkdir()
        (store / "re\u0301sume\u0301" / "cv.md").write_text("cv\n")
        (store / "photo\u0301.bin").write_bytes(b"\x00\x01")
        os.symlink("cafe\u0301.md", store / "to-cafe")
        historica("record", "-m", "one")
        historica("name", "first", "head", "--revision")
        (store / "cafe\u0301.md").write_text("one\ntwo\nthree\n")
        historica("record", "-m", "two")
        # And the folder moves on: an edit, a rename by `mv` to a name
        # spelled decomposed, new files beside ones the store holds, and one
        # name twice, decomposed and composed, which are one path.
        (store / "cafe\u0301.md").write_text("one\n2\nthree\nfour\n")
        (store / "notes.md").rename(store / "no\u0308tes.md")
        (store / "nai\u0308ve.md").write_text("naive\n")
        (store / "cafe\u0301.bin").write_bytes(b"\x00bytes")
        (store / "re\u0301sume\u0301" / "new.md").write_text("new\n")
        (store / "twi\u0301n.md").write_text("decomposed\n")
        (store / "tw\u00edn.md").write_text("composed\n")
        # A rule stated decomposed skips what the folder spells composed.
        (store / "history" / "skipped" / "idea.txt").write_text("skip ide\u0301e.md\n")
        (store / "history" / "skipped" / "drafts.txt").write_text("skip-name cafe\u0301-*\n")
        (store / "id\u00e9e.md").write_text("skipped\n")
        (store / "caf\u00e9-draft.txt").write_text("skipped by name\n")
    elif corpus == "renormal":
        def rec(name, *command):
            done = subprocess.run([rust, "record", *command], cwd=store, env=env, check=True, capture_output=True, text=True, timeout=120)
            digest = re.search(r"^recorded [a-z]+ as ([0-9a-f]+)", done.stdout, re.M).group(1)
            historica("name", name, digest, "--revision")

        def relink(name, target):
            if os.path.lexists(store / name):
                os.remove(store / name)
            os.symlink(target, store / name)

        def first():
            (store / "cafe\u0301.md").write_text("a\nb\nc\n")
            (store / "re\u0301sume\u0301").mkdir(exist_ok=True)
            (store / "re\u0301sume\u0301" / "cv.md").write_text("cv\n")
            (store / "photo\u0301.bin").write_bytes(b"\x00one")
            (store / "run\u0301.sh").write_text("#!/bin/sh\n")
            (store / "run\u0301.sh").chmod(0o644)
            relink("li\u0301nk", "cafe\u0301.md")

        first()
        rec("first", "-m", "first")
        (store / "cafe\u0301.md").write_text("A\nb\nc\n")
        (store / "photo\u0301.bin").write_bytes(b"\x00two")
        (store / "run\u0301.sh").chmod(0o755)
        relink("li\u0301nk", "re\u0301sume\u0301/cv.md")
        (store / "e\u0301te\u0301.md").write_text("summer\n")
        (store / "re\u0301sume\u0301" / "new.md").write_text("new\n")
        (store / "di\u0301r").mkdir()
        (store / "di\u0301r" / "only.md").write_text("only\n")
        rec("second", "-m", "second")
        # A line of work beside it, from the first, and the folder back in
        # step with the second.
        (store / "e\u0301te\u0301.md").unlink()
        (store / "re\u0301sume\u0301" / "new.md").unlink()
        shutil.rmtree(store / "di\u0301r")
        first()
        (store / "cafe\u0301.md").write_text("a\nb\nC\n")
        (store / "side\u0301.md").write_text("side\n")
        rec("side", "--onto", "first", "-m", "side")
        (store / "side\u0301.md").unlink()
        (store / "cafe\u0301.md").write_text("A\nb\nc\n")
        (store / "photo\u0301.bin").write_bytes(b"\x00two")
        (store / "run\u0301.sh").chmod(0o755)
        relink("li\u0301nk", "re\u0301sume\u0301/cv.md")
        (store / "e\u0301te\u0301.md").write_text("summer\n")
        (store / "re\u0301sume\u0301" / "new.md").write_text("new\n")
        (store / "di\u0301r").mkdir()
        (store / "di\u0301r" / "only.md").write_text("only\n")
    elif corpus == "unspelled":
        (store / "notes.md").write_text("one\n")
        (store / "a.md").write_text("a\n")
        historica("record", "-m", "one")
        (store / "notes.md").write_text("one\ntwo\n")
        (store / "a\u00e9.md").write_text("after the byte 0x80, before 0xff\n")
        (store / "bell\x07.md").write_text("a control character\n")
        os.mkfifo(store / "pipe")
        (store / "sub").mkdir()
        (store / "sub" / "ok.md").write_text("ok\n")
        (store / "d\u0301ir").mkdir()
        (store / "d\u0301ir" / "fine.md").write_text("fine\n")
        root = os.fsencode(store)
        for name in (b"a\x80.md", b"bad\xff.md", b"sub/in\xff.md", b"sub/\xfe\xfe", b"d\xcc\x81ir/x\xff.md"):
            with open(root + b"/" + name, "wb") as f:
                f.write(b"cannot be named\n")
        os.mkdir(root + b"/dir\xfe")
        with open(root + b"/dir\xfe/inner.md", "wb") as f:
            f.write(b"beneath a name that cannot be spelled\n")
    elif corpus == "unnormal":
        (store / "notes.md").write_text("one\n")
        (store / "caf\u00e9.md").write_text("cafe\n")
        historica("record", "-m", "first")
        historica("name", "first", "head", "--revision")
        historica("name", "main", "head")
        (store / "notes.md").write_text("one\ntwo\n")
        (store / "d\u00e9j\u00e0.md").write_text("again\n")
        historica("record", "-m", "second")
        # The second revision restated by hand with the path it adds
        # decomposed: a new revision, since a revision is its bytes' digest,
        # and the head, since nothing names it as a parent.
        history = store / "history"
        revision = next(p for p in (history / "revisions").rglob("*.rev.txt") if p.read_text().endswith("\n\nsecond"))
        text = revision.read_text()
        assert "d\u00e9j\u00e0.md" in text
        revision.write_text(text.replace("d\u00e9j\u00e0.md", "de\u0301ja\u0300.md"))
        for cached in (history / "cache").glob("*.txt"):
            cached.unlink()
    elif corpus in ("forgotten", "forgetting", "resurrected"):
        # A file of lines edited a line at a time, long enough that reading
        # it leaves the Rust tool a state in `cache/`; a file of bytes
        # replaced twice; a merge whose resolution copies a line it moved;
        # an empty file and a link. `forgotten` then has the Rust tool's
        # `forget` destroy some of each; `forgetting` is where `forget`
        # itself is compared.
        def rec(name, *command):
            done = subprocess.run([rust, "record", *command], cwd=store, env=env, check=True, capture_output=True, text=True, timeout=120)
            digest = re.search(r"^recorded [a-z]+ as ([0-9a-f]+)", done.stdout, re.M).group(1)
            historica("name", name, digest, "--revision")

        notes = ["one", "two", "three", "four", "five", "six"]
        (store / "notes.md").write_text("".join(f"{line}\n" for line in notes))
        (store / "photo.bin").write_bytes(b"\x00\x01first")
        (store / "f.md").write_text("a\nb\n")
        (store / "empty.md").write_text("")
        os.symlink("notes.md", store / "link")
        rec("first", "-m", "first")
        for n in range(1, 18):
            notes[n % 5] = f"edit {n}"
            (store / "notes.md").write_text("".join(f"{line}\n" for line in notes))
            if n in (5, 10):
                (store / "photo.bin").write_bytes(b"\x00\x02" + bytes(str(n), "ascii"))
            rec(f"r{n}", "-m", f"edit {n}")
        (store / "f.md").write_text("a\nb\nL\n")
        rec("left", "-m", "left")
        (store / "f.md").write_text("R\na\nb\n")
        rec("right", "--onto", "r17", "-m", "right")
        (store / "f.md").write_text("L\nR\na\nb\n")
        rec("m1", "--merge", "left", "--merge", "right", "-m", "merged")
        notes[5] = "six, at last"
        (store / "notes.md").write_text("".join(f"{line}\n" for line in notes))
        rec("after", "-m", "after the merge")
        if corpus == "resurrected":
            # The originals kept, and beside them the stand-ins the Rust
            # tool's `forget` wrote in a copy of this store: what a sync
            # that copies files, rather than `receive`, leaves behind. The
            # copy's `cache/` is left there, and this one's cleared, so that
            # the catalogue the Rust tool reads here is taken from the
            # directory as it now stands.
            elsewhere = temporary / f"elsewhere-{corpus}"
            shutil.rmtree(elsewhere, ignore_errors=True)
            shutil.copytree(store, elsewhere, symlinks=True)
            for command in (
                ("first", "notes.md", "--lines", "2"),
                ("head", "notes.md", "--lines", "3..4"),
                ("left", "f.md", "--lines", "3"),
                ("first", "photo.bin"),
                ("first", "notes.md", "--lines", "4"),
            ):
                subprocess.run([rust, "forget", *command], cwd=elsewhere, env=env, check=True, capture_output=True, timeout=120)
            there = elsewhere / "history" / "operations"
            for path in sorted(there.rglob("*")):
                here = store / "history" / "operations" / path.relative_to(there)
                if path.is_file() and not here.exists():
                    here.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copyfile(path, here)
            for path in (store / "history" / "cache").iterdir():
                if path.name != "README.txt":
                    path.unlink()
        if corpus == "forgetting":
            # Directories under `operations/` that nothing fills, which the
            # Rust tool's `forget` sweeps away with the ones it empties.
            (store / "history" / "operations" / "2026-09" / "nothing").mkdir(parents=True)
            (store / "history" / "operations" / "2026-01" / "deep" / "er").mkdir(parents=True)
        if corpus == "forgotten":
            historica("forget", "first", "notes.md", "--lines", "2")
            historica("forget", "head", "notes.md", "--lines", "3..4")
            historica("forget", "left", "f.md", "--lines", "3")
            historica("forget", "first", "photo.bin")
            # A second span of a document already forgotten: two stand-ins
            # for one digest, read together.
            historica("forget", "first", "notes.md", "--lines", "4")
        # Read, so that `cache/` holds a state of the file and a catalogue
        # of `operations/` as it now stands: what `forget` destroys the
        # copies in, and what it leaves alone.
        historica("cat", "head", "notes.md")
        historica("cat", "r9", "notes.md")
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


def assemble(temporary, corpus, store=None):
    store = store or temporary / f"store-{corpus}"
    history = store / "history"
    history.mkdir(parents=True, exist_ok=True)
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
    elif corpus.endswith("-invalid"):
        # A corpus, and the documents it holds that do not parse, filed
        # where their kind is kept.
        assemble(temporary, corpus[: -len("-invalid")], store)
        for kind in ("revisions", "operations"):
            source = CORPUS / (kind if corpus == "revisions-invalid" else corpus[: -len("-invalid")]) / "invalid"
            for path in sorted(source.glob(f"*.{'rev' if kind == 'revisions' else 'ops'}.txt")):
                (history / kind / "invalid").mkdir(parents=True, exist_ok=True)
                shutil.copy(path, history / kind / "invalid" / path.name)
    elif corpus == "redacted":
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


class Web(http.server.SimpleHTTPRequestHandler):
    """A static directory of files, as a publisher's host serves one.

    One address is not static: `moving/offer.txt` is the manifest of a copy
    being rewritten, which names a path that has since moved on every odd
    request and is the copy's current manifest on every even one — so each
    fetch of it reads a stale manifest, finds a path gone, and reads again.
    """

    asked = {}
    lock = threading.Lock()

    def log_message(self, *arguments):
        pass

    def do_GET(self):
        if self.path == "/moving/offer.txt":
            with Web.lock:
                n = Web.asked.get(self.path, 0)
                Web.asked[self.path] = n + 1
            if n % 2 == 0:
                self.path = "/moving/offer.stale.txt"
        super().do_GET()


def publish(temporary, rust):
    """The copies `fetch` is held to the Rust tool over, each exported and
    offered by the Rust tool, under `temporary / "web"`."""
    web = temporary / "web"
    source = temporary / "web-source"
    home = temporary / "home-web"
    env = {**os.environ, **PINS, "HOME": str(home), "XDG_CONFIG_HOME": str(home / ".config")}
    web.mkdir()
    source.mkdir()

    def at(where, *command):
        return subprocess.run([rust, *command], cwd=where, env=env, check=True, capture_output=True, timeout=120).stdout

    def offered(where, name):
        at(where, "export", str(web / name / "store"))
        (web / name / "offer.txt").write_bytes(at(web / name, "offer", "store"))

    at(source, "init", ".")
    (source / "notes.md").write_text("one\ntwo\n")
    (source / "p.bin").write_bytes(b"\x00one")
    at(source, "record", "-m", "one")
    at(source, "name", "first", "head")
    first = temporary / "web-first"
    shutil.copytree(source, first, symlinks=True)
    offered(first, "same")
    (source / "notes.md").write_text("one\ntwo\nthree\n")
    (source / "q.bin").write_bytes(b"\x00two")
    (source / "sub").mkdir()
    (source / "sub" / "deep.md").write_text("deep\n")
    at(source, "record", "-m", "two")
    at(source, "name", "main", "head")
    at(source, "name", "priv", "head", "--private")
    at(source, "name", "old", "first", "--revision")
    at(source, "skip", "build/")
    at(source, "skip", "--private", "--name", "*.tmp")
    (source / "history" / "claims" / "by").mkdir(parents=True)
    (source / "history" / "claims" / "by" / "one.txt").write_text("vouched\n")
    offered(source, "pub")
    manifest = (web / "pub" / "offer.txt").read_text()
    # A payload whose bytes are not the digest its line gives.
    shutil.copytree(web / "pub", web / "lie", symlinks=True)
    payload = next(line for line in manifest.splitlines() if line.startswith("payload ")).split(" ", 3)[3]
    (web / "lie" / payload).write_bytes(b"\x00lie")
    # A revision the manifest names and the copy no longer holds.
    shutil.copytree(web / "pub", web / "stale", symlinks=True)
    revision = [line for line in manifest.splitlines() if line.startswith("revision ")][-1].split(" ", 3)[3]
    (web / "stale" / revision).unlink()
    # A copy being rewritten: its stale manifest names that revision where it
    # was before the publisher moved it.
    shutil.copytree(web / "pub", web / "moving", symlinks=True)
    (web / "moving" / "offer.stale.txt").write_text(manifest.replace(revision, revision.replace(".rev.txt", " moved.rev.txt")))
    # A directory this historica does not carry, and a kind it does not know.
    shutil.copytree(web / "pub", web / "declined", symlinks=True)
    digest = hashlib.sha256(b"x").hexdigest()
    (web / "declined" / "offer.txt").write_text(manifest + f"reserved {digest} - store/history/trust/key.txt\nreserved {digest} - store/history/trust/other.txt\nreserved {digest} - store/history/elsewhere/a.txt\nfuture {digest} - store/history/future/x\n")
    for name, text in (("spelled", "historica-offer-2\n"), ("malformed", manifest + "payload nothex - store/x\n"), ("headless", manifest + f"head {digest}\n")):
        (web / name).mkdir()
        (web / name / "offer.txt").write_text(text)
    (web / "binary").mkdir()
    (web / "binary" / "offer.txt").write_bytes(b"\xff\xfe not text\n")
    # What it forgot: a line of a file and a payload, before it was
    # exported again, so its stand-ins arrive.
    forgetting = temporary / "web-forgetting"
    shutil.copytree(source, forgetting, symlinks=True)
    at(forgetting, "forget", "head", "notes.md", "--lines", "1..1")
    at(forgetting, "forget", "head", "q.bin")
    (forgetting / "q.bin").unlink()
    at(forgetting, "record", "-m", "three")
    offered(forgetting, "fg")
    stranger = temporary / "web-stranger"
    stranger.mkdir()
    at(stranger, "init", ".")
    (stranger / "else.md").write_text("elsewhere\n")
    at(stranger, "record", "-m", "elsewhere")
    offered(stranger, "stranger")
    return web


def serve(web):
    """Serve a directory from a thread, on a free port; its address."""
    server = http.server.ThreadingHTTPServer(("127.0.0.1", 0), functools.partial(Web, directory=str(web)))
    threading.Thread(target=server.serve_forever, daemon=True).start()
    return f"http://127.0.0.1:{server.server_address[1]}"


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
        # What the archive's HTTP needs beside it, as `cargo rustc --print
        # native-static-libs` lists it: `fetch`'s transport is the host's
        # libcurl, built into the archive, over the system's TLS and zlib.
        run(
            os.environ.get("CC", "cc"), "-O3", "-w", "-o", str(native), str(source),
            str(archive), "-lssl", "-lcrypto", "-lz", "-ldl", "-lrt", "-lutil", "-lm", "-lpthread", timeout=1800,
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
    # One at a time: emitting `main.bend` as C takes some thirteen gigabytes
    # at its peak, and the JS emit beside it is enough to exhaust a machine
    # of sixteen.
    for build in builds:
        build()

    copies = itertools.count()

    # `fetch`'s publisher: the copies exported and offered, served from here.
    web = serve(publish(temporary, rust))

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
            if here.name == "cache" and here.parent.name == "history" and not cached:
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
        recorded = corpus in ("normal", "renormal", "unspelled", "unnormal", "unicode", "names", "badname", "log", "merge", "walked", "folder", "badskip", "fresh", "notext", "surveyed", "skipheld", "joining", "claimed", "bare", "recording", "rewriting", "stranded", "shell", "headless", "identity", "editing", "skipping",
                               "damaged", "gutted", "tampered", "unreadable", "quoting", "requoted", "unnamed", "unruled", "forgotten", "forgetting",
                               "updating", "caught", "blocked", "meeting", "marked", "marked1", "resolved", "through", "resurrected",
                               "arranging", "pruning", "lying", "unparsed", "receiving", "exporting", "fetching", "fetched")
        store = record(temporary, rust, corpus, writer) if recorded else assemble(temporary, corpus)
        lines, failures = [], 0
        for command in commands:
            changed = command[0] if command and isinstance(command[0], dict) else {}
            command = command[1:] if changed else command
            command = [word.replace("{web}", web) for word in command]
            # `record` may write the folder — `--move` renames before it
            # surveys, dry run or not — so each tool runs on a copy of its
            # own, and what the folder holds after is compared too; and a
            # record that is not a dry run, the whole store it wrote.
            verb = word(command)
            writes = verb in ("record", "name", "init", "identity", "skip", "update", "merge", "forget", *REWRITES, *MOVES)
            recording = verb in ("record", *REWRITES) and not {"-n", "--dry-run"} & set(command)
            moving = verb in MOVES
            # `forget` destroys what `cache/` holds copies of, so its store is
            # compared whole, `cache/` and all.
            forgetting = verb == "forget"
            at = temporary / f"{store.name}-copy-{next(copies)}"
            copy = fresh(store, at) if writes else store
            env = environment(copy, changed)
            command = [word.replace("{copy}", str(copy)) for word in command]
            whole = verb in ("init", "identity", "skip") or recording or moving or forgetting
            cached = forgetting or not (recording or moving)
            reference = writer if verb in ("record", "forget", *REWRITES) else rust
            shown = " ".join([f"{k}={v}" for k, v in changed.items()] + command)
            expected = said(capture(reference, *command, cwd=copy, env=env)) + (folder_of(copy, whole, cached) if writes else ())
            for name, tool in tools:
                copy = fresh(store, at) if writes else store
                got = said(capture(*tool, *command, cwd=copy, env=env)) + (folder_of(copy, whole, cached) if writes else ())
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
            # `LAWS.advance_exact` rejects it too; the checker meets the
            # stand-in replay lemmas, which unfold the same walk, first.
            "forget_lemmas.advance_like",
        ),
        (
            "delete ignores item disagreement",
            "drop_checked(rs, ss, Bool.and(ok, agrees(r, s)))",
            "drop_checked(rs, ss, ok)",
            # And `LAWS.drop_checked_exact`, met after it.
            "forget_lemmas.drop_like",
        ),
        (
            "cursor drops inserted items",
            "List.append(&2, Item, List.reverse(&2, Item, items), acc)",
            "acc",
            # And `LAWS.cursor_walk_equivalent`, met after it.
            "forget_lemmas.go_like",
        ),
        (
            "cursor loses the trailing parent suffix",
            "Done{List.append(&2, Item, List.reverse(&2, Item, acc), state)}",
            "Done{List.reverse(&2, Item, acc)}",
            # And `LAWS.cursor_walk_equivalent`, met after it.
            "forget_lemmas.go_end",
        ),
        (
            "cursor overwrites an earlier deletion error",
            'Maybe.or(&2, String, err, Bool.pick(Maybe<&2, String>, agreed, None{}, Some{"a delete at " ++ Nat.show(at) ++ " quotes lines the parent does not hold"}))',
            'Bool.pick(Maybe<&2, String>, agreed, None{}, Some{"a delete at " ++ Nat.show(at) ++ " quotes lines the parent does not hold"})',
            # And `LAWS.cursor_walk_equivalent`, met after it.
            "forget_lemmas.go_like",
        ),
        (
            "public replay ignores the result digest",
            "apply.checked(result, items)\n\n# Blocks",
            "apply.checked(None{}, items)\n\n# Blocks",
            # And `LAWS.cursor_apply_equivalent`, met after it.
            "forget_lemmas.apply_is",
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
            "-V is not read as the version",
            '  Bool.pick(Lead, Bool.or(String.eq(w, "-V"), String.eq(w, "--version")), Lead.Version{},',
            '  Bool.pick(Lead, String.eq(w, "--version"), Lead.Version{},',
            "argv_lemmas.version.at",
            "argv.bend",
        ),
        (
            "-h is not read as help",
            '  Bool.pick(Lead, Bool.or(String.eq(w, "help"), Bool.or(String.eq(w, "-h"), String.eq(w, "--help"))), Lead.Usage{},',
            '  Bool.pick(Lead, Bool.or(String.eq(w, "help"), String.eq(w, "--help")), Lead.Usage{},',
            "argv_lemmas.help.at",
            "argv.bend",
        ),
        (
            "check reads only the last word as asking for --complete",
            "      asked.go(rest, Bool.or(complete, flag), Bool.pick(List<&2, String>, flag, words, List.append(&2, String, words, [w])))",
            "      asked.go(rest, flag, Bool.pick(List<&2, String>, flag, words, List.append(&2, String, words, [w])))",
            "check_lemmas.asked_go",
            "check.bend",
        ),
        (
            "check reads the note under a new store's format line as a layout",
            "      +found = Store.line.cut(rest)",
            "      +found = rest",
            "check_lemmas.fresh",
            "check.bend",
        ),
        (
            "skip's rule equality ignores privacy",
            "      Bool.and(scope.eq(x, y), Bool.not(Bool.xor(p, q)))",
            "      scope.eq(x, y)",
            "skip_lemmas.rule_eq_sound",
            "skip.bend",
        ),
        (
            "skip writes a directory's rule without its slash",
            '      key(named(sc), p) ++ " " ++ value(sc) ++ Bool.pick(String, under(sc), "/", SNil{})',
            '      key(named(sc), p) ++ " " ++ value(sc) ++ Bool.pick(String, under(sc), SNil{}, SNil{})',
            "skip_lemmas.read_under",
            "skip.bend",
        ),
        (
            "skip reads a private name rule as shared",
            '        Bool.or(String.starts_with(l, "private "), String.starts_with(l, "private-name ")))',
            '        String.starts_with(l, "private "))',
            # `LAWS.skip_name_rule_reads_back` rejects it; the checker meets
            # the path's proof, which spells the same line, first.
            "skip_lemmas.read_path",
            "skip.bend",
        ),
        (
            "a directory's rule does not skip the directory",
            "    case Scope.Under{v}:\n      String.eq(path, v)",
            "    case Scope.Under{v}:\n      False{}",
            "skip_lemmas.skips_scoped",
            "folder.bend",
        ),
        (
            "skip's listing forgets the rule it just kept",
            "      Stating{r, f} <> once(rest, r <> seen, once.dup(rest, r <> seen))",
            "      Stating{r, f} <> once(rest, seen, once.dup(rest, seen))",
            "skip_lemmas.disj.at",
            "skip.bend",
        ),
        (
            "skip asks whether a rule is new against what it had before the last",
            "      sorted.go(rest, had, more, already, sorted.dup(rest, had, more))",
            "      sorted.go(rest, had, more, already, sorted.dup(rest, had, fresh))",
            "skip_lemmas.mono.at",
            "skip.bend",
        ),
        (
            "show finds a document whose digest the named one starts",
            '      Bool.pick(Maybe<&2, String>, String.starts_with(i, id), Some{text}, held(rest, id))',
            '      Bool.pick(Maybe<&2, String>, String.starts_with(id, i), Some{text}, held(rest, id))',
            "show_lemmas.by_id",
            "standin.bend",
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
        (
            "arrange plans a rename onto a name that is taken",
            "    Bool.pick(Placing, has(taken, target), Placing.Occupied{path, target}, Placing.Rename{path, target}))",
            "    Bool.pick(Placing, False{}, Placing.Occupied{path, target}, Placing.Rename{path, target}))",
            "arrange_lemmas.place_safe",
            "arrange.bend",
        ),
        (
            "arrange refiles a revision it was not asked to",
            '      String.append(Naming.head(path), leaf(stem) ++ ".rev.txt")',
            '      "revisions/" ++ stem ++ ".rev.txt"',
            "arrange_lemmas.kept_here",
            "arrange.bend",
        ),
        (
            "arrange's dry run leaves out the files it would leave",
            "  Came{done.renamed(ps), done.already(ps), done.occupied(ps), done.unnamed(ps)}\n",
            "  Came{done.renamed(ps), done.already(ps), Nil{}, done.unnamed(ps)}\n",
            "arrange_lemmas.tally_planned",
            "arrange.bend",
        ),
        (
            "arrange opens a store past a revision that does not parse",
            '      Some{Main.Refused{1, path ++ ": " ++ e}}',
            "      None{}",
            "arrange_lemmas.fault_parses",
            "arrange.bend",
        ),
        (
            "prune lets go of a revision work still stands on",
            "  Bool.and(superseded(kept, Main.id_of(f)), Bool.and(Bool.not(stood_on(kept, Main.id_of(f))), Bool.not(evidence(supersedes_of(f), Main.ids(kept)))))",
            "  Bool.and(superseded(kept, Main.id_of(f)), Bool.and(True{}, Bool.not(evidence(supersedes_of(f), Main.ids(kept)))))",
            "prune_lemmas.goes_stood",
            "prune.bend",
        ),
        (
            "prune removes content a revision it keeps names",
            "      Tree.keep(~T.Split, Bool.not(Arrange.has(keep, id)), T.Split{path, id}, gone.of(rest, keep))",
            "      Tree.keep(~T.Split, True{}, T.Split{path, id}, gone.of(rest, keep))",
            "prune_lemmas.gone_unneeded",
            "prune.bend",
        ),
        (
            "prune takes a plan and a statement at once",
            "  Bool.pick(Result<&2, &2, Main.Refused, PruneCmd>, Bool.and(dry, fields),",
            "  Bool.pick(Result<&2, &2, Main.Refused, PruneCmd>, False{},",
            "words_lemmas.prn.planned",
            "prune.bend",
        ),
        (
            "receive takes a document this store already holds",
            "      doc.keep(Bool.not(Arrange.has(have, Store.id_of(d))), d, docs.lacking(rest, have))",
            "      doc.keep(True{}, d, docs.lacking(rest, have))",
            "receive_lemmas.docs_lacking",
            "receive.bend",
        ),
        (
            "receive moves a bookmark this store holds elsewhere",
            "      Bool.pick(Marked, same_target(tt, ht), marked.joined(n, ht, hp, tp), Marked{Nil{}, [Conflict{n, Bm.Bookmark{hn, ht, hp}, Bm.Bookmark{n, tt, tp}}]})",
            "      Bool.pick(Marked, same_target(tt, ht), marked.joined(n, ht, hp, tp), Marked{[Bm.Bookmark{n, tt, tp}], Nil{}})",
            "receive_lemmas.one_kept",
            "receive.bend",
        ),
        (
            "receive destroys an original nothing forgets",
            "  Main.sorted_distinct(among(forgotten(here, there), Set.from_list(",
            "  Main.sorted_distinct(among(List.append(&2, String, forgotten(here, there), body.ids(stored.bodies(stored.of(there)))), Set.from_list(",
            "receive_lemmas.destroys",
            "receive.bend",
        ),
        (
            "offer names a private bookmark",
            "      offered.found(Bool.not(p), Arrange.lookup(ids, \"names/\" ++ n ++ \".txt\")",
            "      offered.found(True{}, Arrange.lookup(ids, \"names/\" ++ n ++ \".txt\")",
            "offer_lemmas.names_shared",
            "offer.bend",
        ),
        (
            "offer names a private rule",
            "      offered.found(Bool.not(String.starts_with(line, \"private\")), Arrange.lookup(ids, \"skipped/\" ++ file)",
            "      offered.found(True{}, Arrange.lookup(ids, \"skipped/\" ++ file)",
            "offer_lemmas.rule_kept",
            "offer.bend",
        ),
        (
            "export lays a link somewhere other than where it sits",
            "      Outcome.Laid{Put.Link{path, s}}",
            "      Outcome.Laid{Put.Link{\"link\", s}}",
            "export_lemmas.link_path",
            "export.bend",
        ),
        (
            "export gives a copy a private bookmark",
            "          travel.withheld(t)",
            "          travel.held(Bm.Bookmark{n, g, True{}}, True{}, t)",
            "export_lemmas.push_travels",
            "export.bend",
        ),
        (
            "export gives a copy a bookmark pointing past the target",
            "          travel.held(Bm.Bookmark{n, g, False{}}, pointed.holds(pt, g), t)",
            "          travel.held(Bm.Bookmark{n, g, False{}}, True{}, t)",
            "export_lemmas.push_travels",
            "export.bend",
        ),
        (
            "export writes a private rule into the copy",
            "      Tree.keep(~Receive.Ruled, Bool.not(ruled.private(r)), r, rules.shared(rest))",
            "      Tree.keep(~Receive.Ruled, True{}, r, rules.shared(rest))",
            "export_lemmas.shared_all",
            "export.bend",
        ),
        (
            "export writes over a file nothing recorded",
            "      +over = Bool.pick(Step, recorded(whole, rs, path, d),",
            "      +over = Bool.pick(Step, True{},",
            "export_lemmas.held_safe",
            "export.bend",
        ),
        (
            "export removes a stray file nothing recorded",
            "      Tree.keep(~String, Bool.and(Bool.not(Arrange.has(placed, p)), seen.gone(s, whole, rs)), p, removes(rest, placed, whole, rs))",
            "      Tree.keep(~String, Bool.not(Arrange.has(placed, p)), p, removes(rest, placed, whole, rs))",
            "export_lemmas.removes_safe",
            "export.bend",
        ),
        (
            "export takes a word it does not know",
            "      Bool.pick(Maybe<&2, String>, Bool.and(String.starts_with(w, \"-\"), Bool.not(is_flag(w))), Some{w}, stray(rest))",
            "      Bool.pick(Maybe<&2, String>, False{}, Some{w}, stray(rest))",
            "words_lemmas.exp.shape",
            "export.bend",
        ),
        (
            "export updates a directory holding no store",
            "    case False{} False{}:\n      Fail{Main.Refused{1, into ++ \" already holds something",
            "    case False{} False{}:\n      Done{Dest.Copy{}}\n    case True{} True{}:\n      Fail{Main.Refused{1, into ++ \" already holds something",
            "export_lemmas.held_dest",
            "export.bend",
        ),
        (
            "export lays a file of lines out as plain whatever its mode",
            "      Outcome.Laid{Put.Text{path, Ops.text(items), r}}",
            "      Outcome.Laid{Put.Text{path, Ops.text(items), False{}}}",
            "export_lemmas.lines_as",
            "export.bend",
        ),
        (
            "export copies a payload from a file named for it rather than the one holding it",
            "      Outcome.Laid{Put.Bytes{path, from, d, r}}",
            "      Outcome.Laid{Put.Bytes{path, d, d, r}}",
            "export_lemmas.held_as",
            "export.bend",
        ),
        (
            "export carries a payload from a file the store does not hold",
            "      Bool.pick(List<&2, T.Split>, Arrange.has(docs, id), later, payload.push(id, split.find(ps, id), later))",
            "      Bool.pick(List<&2, T.Split>, Arrange.has(docs, id), later, payload.push(id, Some{id}, later))",
            "export_lemmas.pays_among",
            "export.bend",
        ),
        (
            "export renames a revision the copy holds",
            "      T.Split{id, Maybe.default(&2, String, kept, Naming.stem(w, m, c, id, existing))}",
            "      T.Split{id, Naming.stem(w, m, c, id, existing)}",
            "export_lemmas.stems_kept",
            "export.bend",
        ),
        (
            "receive plans from a store the check calls broken",
            "      plan.source(Prune.sound(stored.of(there)), here, there, join)",
            "      plan.source(True{}, here, there, join)",
            "receive_lemmas.gate_there",
            "receive.bend",
        ),
        (
            "receive takes a plan and a statement at once",
            "  args.end.of(Bool.and(dry, fields), dry, fields, join, source)",
            "  args.end.of(False{}, dry, fields, join, source)",
            "words_lemmas.recv.nil",
            "receive.bend",
        ),
        (
            "offer takes a directory that starts like a flag",
            "      Bool.pick(Maybe<&2, String>, String.starts_with(w, \"-\"), Some{w}, first_dash(rest))",
            "      Bool.pick(Maybe<&2, String>, False{}, Some{w}, first_dash(rest))",
            "words_lemmas.off.shape",
            "offer.bend",
        ),
        (
            "export lays out a path a rule of the copy covers",
            "          refuse.if(Folder.skips(rules, path), path, \"a `skip` rule in history/skipped.txt covers it, so the walk could never offer it back\",",
            "          refuse.if(False{}, path, \"a `skip` rule in history/skipped.txt covers it, so the walk could never offer it back\",",
            "export_lemmas.tree_clear",
            "export.bend",
        ),
        (
            "export destroys every original the copy holds",
            "  Main.sorted_distinct(Receive.among(forgotten, Set.from_list(List.append(&2, String, body.digests(Receive.stored.bodies(cst)), split.digests(Receive.stored.payloads(cst))))))",
            "  Main.sorted_distinct(List.append(&2, String, body.digests(Receive.stored.bodies(cst)), split.digests(Receive.stored.payloads(cst))))",
            "export_lemmas.destroys_of",
            "export.bend",
        ),
        (
            "the check that every revision parses reads the first alone",
            "      Bool.and(parses(d), all_parse(rest))",
            "      parses(d)",
            "arrange_lemmas.faults_none",
            "arrange.bend",
        ),
        (
            "receive reads a document's own digest as what it forgets",
            "      forgets.push(f, body.forgets(rest))",
            "      forgets.push(Some{i}, body.forgets(rest))",
            "receive_lemmas.forgets_member",
            "receive.bend",
        ),
        (
            "export reads a copy's document's own digest as what it forgets",
            "      maybe.push(f, forgets.all(rest))",
            "      maybe.push(Some{id}, forgets.all(rest))",
            "export_lemmas.forgets_all",
            "export.bend",
        ),
        (
            "export reads the first record of the copy whatever path it is of",
            "      Bool.pick(Maybe<&2, Rec>, String.eq(p, path), Some{Rec{p, ds, ls}}, rec.find(rest, path))",
            "      Bool.pick(Maybe<&2, Rec>, True{}, Some{Rec{p, ds, ls}}, rec.find(rest, path))",
            "export_lemmas.rec_find",
            "export.bend",
        ),
        (
            "fetch files a document whose text is not the digest offered",
            "      Bool.pick(Land, String.eq(found, entry.digest(o)), text.land(root, held, o, t), Land.Refuse{TAMPERED(entry.path(o), entry.digest(o), found)})",
            "      Bool.pick(Land, True{}, text.land(root, held, o, t), Land.Refuse{TAMPERED(entry.path(o), entry.digest(o), found)})",
            "fetching_lemmas.filed_is_its_digest",
            "fetch.bend",
        ),
        (
            "fetch lands a payload whatever it hashes to",
            "      Bool.pick(Land, String.eq(found, entry.digest(o)), Land.Move{folder, staged(name), name}, Land.Discard{folder, staged(name), TAMPERED(entry.path(o), entry.digest(o), found)})",
            "      Bool.pick(Land, True{}, Land.Move{folder, staged(name), name}, Land.Discard{folder, staged(name), TAMPERED(entry.path(o), entry.digest(o), found)})",
            "fetching_lemmas.moved_is_its_digest",
            "fetch.bend",
        ),
        (
            "fetch files a payload under the name it was staged at",
            "      Bool.pick(Land, String.eq(found, entry.digest(o)), Land.Move{folder, staged(name), name}, Land.Discard{",
            "      Bool.pick(Land, String.eq(found, entry.digest(o)), Land.Move{folder, staged(name), staged(name)}, Land.Discard{",
            "fetching_lemmas.moved_is_its_digest",
            "fetch.bend",
        ),
        (
            "fetch asks for a path beside the one the manifest names",
            "      Tree.keep(~Offer.Offered, Bool.and(Bool.not(Rev.member(held, d)), Bool.not(Rev.member(forgotten, d))), o, fresh(rest, held, forgotten))",
            "      Tree.keep(~Offer.Offered, Bool.and(Bool.not(Rev.member(held, d)), Bool.not(Rev.member(forgotten, d))), Offer.Offered{entry.kind(o), d, None{}, \"../\" ++ entry.path(o)}, fresh(rest, held, forgotten))",
            "fetching_lemmas.fresh_held",
            "fetch.bend",
        ),
        (
            "fetch cuts a URL's last slash off its directory",
            "      Bool.pick(Maybe<&2, T.Split>, Char.is_eq(c, '/'), Some{T.Split{String.reverse(t) ++ \"/\", acc}}, slash.last(t, SCon{c, acc}))",
            "      Bool.pick(Maybe<&2, T.Split>, Char.is_eq(c, '/'), Some{T.Split{String.reverse(t), acc}}, slash.last(t, SCon{c, acc}))",
            "fetching_lemmas.slash_ok",
            "fetch.bend",
        ),
        (
            "fetch takes a second URL over the first",
            "              Fail{Main.Refused{2, \"`fetch` wants one URL, not `\" ++ w ++ \"`\"}}",
            "              args.go(rest, fword.of(rest), join, fields, Some{w})",
            "words_lemmas.fch.other.a",
            "fetch.bend",
        ),
        (
            "fetch reads `--fields` as joining unrelated histories",
            "  Bool.pick(FWord, String.eq(w, \"--fields\"), FWord.Fields{},",
            "  Bool.pick(FWord, String.eq(w, \"--fields\"), FWord.Join{},",
            "words_lemmas.fch.go",
            "fetch.bend",
        ),
        (
            "arrange takes a word it does not know",
            "      Bool.pick(Maybe<&2, String>, is_flag(w), first_other(rest), Some{w})",
            "      Bool.pick(Maybe<&2, String>, True{}, first_other(rest), Some{w})",
            "words_lemmas.arr.shape",
            "arrange.bend",
        ),
        (
            "arrange reads `--refile` as a dry run too",
            "  args.of(any_dry(ws), any_refile(ws), first_other(ws))",
            "  args.of(Bool.or(any_dry(ws), any_refile(ws)), any_refile(ws), first_other(ws))",
            "words_lemmas.arrange_words",
            "arrange.bend",
        ),
        (
            "prune hears `--fields` only as the first word",
            "      Bool.or(is_fields(w), any_fields(rest))",
            "      is_fields(w)",
            "words_lemmas.prn.fields",
            "prune.bend",
        ),
        (
            "export reads its target as the directory",
            "      Done{ExportCmd{dry, files, d, Some{t}}}",
            "      Done{ExportCmd{dry, files, t, Some{d}}}",
            "words_lemmas.exp.words",
            "export.bend",
        ),
        (
            "receive takes a second source over the first",
            "              Fail{Main.Refused{2, \"`receive` wants one source directory, not `\" ++ w ++ \"`\"}}",
            "              args.go(rest, rword.of(rest), dry, fields, join, Some{w})",
            "words_lemmas.recv.other.a",
            "receive.bend",
        ),
        (
            "receive reads `--fields` as joining unrelated histories",
            "  Bool.pick(RWord, String.eq(w, \"--fields\"), RWord.Fields{},",
            "  Bool.pick(RWord, String.eq(w, \"--fields\"), RWord.Join{},",
            "words_lemmas.recv.go",
            "receive.bend",
        ),
        (
            "offer takes the first of two directories",
            "      Fail{Main.Refused{2, \"`offer` takes one directory, and `\" ++ extra ++ \"` is a second\"}}",
            "      Done{d}",
            "words_lemmas.off.plain",
            "offer.bend",
        ),
        (
            "offer names a file by its path rather than its digest",
            "      Offered{kind, d, None{}, addressed(prefix, p)} <> splits.offered(rest, kind, prefix)",
            "      Offered{kind, p, None{}, addressed(prefix, p)} <> splits.offered(rest, kind, prefix)",
            "offer_lemmas.splits_from",
            "offer.bend",
        ),
        (
            "update writes over bytes no revision records",
            "        Bool.pick(Step, Rev.member(recorded, d), Step.Write{}, Step.Refuse{UNRECORDED()}))",
            "        Bool.pick(Step, True{}, Step.Write{}, Step.Refuse{UNRECORDED()}))",
            "update_lemmas.file_sound",
            "update.bend",
        ),
        (
            "update keeps a file whose mode is not the one recorded",
            "        Bool.pick(Step, Bool.xor(r, runs(mode)), Step.Mode{}, Step.Keep{}),",
            "        Step.Keep{},",
            "update_lemmas.file_sound",
            "update.bend",
        ),
        (
            "update takes away a file nobody recorded",
            "      Bool.pick(Leaving, tracked, Leaving.Leave{}, Leaving.Stay{})",
            "      Leaving.Remove{}",
            "update_lemmas.leave_pick",
            "update.bend",
        ),
        (
            "update writes a file of lines without the mode its tree names",
            "      wants.lines(m, Main.content.found(fs, ds, id, f, Main.content_of(Main.contents.go(oldest, ds, f, Nil{}), id)))",
            "      wants.lines(Tree.Plain{}, Main.content.found(fs, ds, id, f, Main.content_of(Main.contents.go(oldest, ds, f, Nil{}), id)))",
            "update_lemmas.lands_reads",
            "update.bend",
        ),
        (
            "update points a link at the path it names, not from where the link stands",
            "      Maybe.map(&2, String, String, to => Main.relative_path(Main.directory_of(at), to), Tree.path(t, named))",
            "      Maybe.map(&2, String, String, to => to, Tree.path(t, named))",
            "update_lemmas.spelled_same",
            "update.bend",
        ),
        (
            "update takes history to hold every file of lines empty",
            "      Some{Ops.state_digest(items)}",
            "      Some{Ops.state_digest(Nil{})}",
            "update_lemmas.lines_rec",
            "update.bend",
        ),
        (
            "update says the folder holds the target while a link is still to point",
            "Bool.and(List.is_empty(&2, Decided, modes(ds)), List.is_empty(&2, Decided, links(ds))))",
            "List.is_empty(&2, Decided, modes(ds)))",
            "update_lemmas.settled_same",
            "update.bend",
        ),
        (
            "a resolution runs a name into a keep it does not continue",
            "Bool.and(String.eq(d, e), Nat.is_eq(1n+m, first))",
            "Bool.and(String.eq(d, e), Nat.is_eq(m, first))",
            "conflict_lemmas.put_kept",
            "conflict.bend",
        ),
        (
            "a resolution keeps a line the person deleted",
            "    case Ops.Del{x} <> rest n <> more:\n      said.of(rest, more)",
            "    case Ops.Del{x} <> rest n <> more:\n      Said.Kept{n} <> said.of(rest, more)",
            "conflict_lemmas.said_fit",
            "conflict.bend",
        ),
        (
            "cat reads a keep from one item past where it starts",
            "Done{List.take(&2, Ops.Item, List.drop(&2, Ops.Item, items, first), count)}",
            "Done{List.take(&2, Ops.Item, List.drop(&2, Ops.Item, items, 1n+first), count)}",
            "conflict_lemmas.keep_one.got",
            "commands.bend",
        ),
        (
            "merge labels a run where nothing met",
            "Bool.pick(String, open, closing(), SNil{}) ++ Ops.text(its)) ++ render.go",
            "label(names, a) ++ Ops.text(its)) ++ render.go",
            "conflict_lemmas.put_render.pick",
            "conflict.bend",
        ),
        (
            "merge leaves uncounted a region that meets at a file's end",
            "      Bool.pick(Nat, hit, 1n, 0n)",
            "      0n",
            "conflict_lemmas.regions_hit",
            "conflict.bend",
        ),
        (
            "merge leaves out the current heads nobody named",
            "    typed.enough(typed.standing(Upd.heads.sorted(fs), named))",
            "    typed.enough(named)",
            "merging_lemmas.joined_all",
            "merging.bend",
        ),
        (
            "merge joins what a person typed rather than the revision it names",
            "        typed.named(fs, bs, rest, typed.add(acc, Main.id_of(f), s))",
            "        typed.named(fs, bs, rest, typed.add(acc, s, s))",
            "merging_lemmas.named_held",
            "merging.bend",
        ),
        (
            "merge writes over text nobody recorded",
            "Laid{Bool.pick(List<&2, Act>, Bool.and(text, unrecorded(",
            "Laid{Bool.pick(List<&2, Act>, Bool.and(Bool.not(text), unrecorded(",
            "merging_lemmas.lines_each",
            "merging.bend",
        ),
        (
            "merge lays a payload over work nobody recorded",
            "Bool.pick(List<&2, Act>, unrecorded(held, p <> heads), [Act.Said{LEFT_UNRECORDED(at)}], [Act.Whole{at, from, p, m}])",
            "Bool.pick(List<&2, Act>, False{}, [Act.Said{LEFT_UNRECORDED(at)}], [Act.Whole{at, from, p, m}])",
            "merging_lemmas.whole_each",
            "merging.bend",
        ),
        (
            "merge writes a file at its identifier rather than its path",
            "  Maybe.default(&2, String, split.get(bs, Tree.entry_file(e)), Tree.entry_path(e))",
            "  Maybe.default(&2, String, split.get(bs, Tree.entry_file(e)), Tree.entry_file(e))",
            "merging_lemmas.lay_each",
            "merging.bend",
        ),
        (
            "merge asks the folder about a file's own path rather than where it writes it",
            "  Place{e, at, Main.status.folder_digest(dg, at),",
            "  Place{e, at, Main.status.folder_digest(dg, Tree.entry_path(e)),",
            "merging_lemmas.lay_each",
            "merging.bend",
        ),
        (
            "merge takes what a head leaves a file of lines as from its tree's payload",
            "  Bool.pick(List<&2, String>, is_lines(Tree.entry_kind(e)), head.lines(fs, ds, Tree.entry_file(e), heads), head.wholes(fs, Tree.entry_file(e), heads))",
            "  Bool.pick(List<&2, String>, is_lines(Tree.entry_kind(e)), head.wholes(fs, Tree.entry_file(e), heads), head.lines(fs, ds, Tree.entry_file(e), heads))",
            "merging_lemmas.lay_each",
            "merging.bend",
        ),
        (
            "merge writes a file of lines without the mode its tree names",
            "[Act.Lines{at, rendered, m}]",
            "[Act.Lines{at, rendered, Tree.Plain{}}]",
            "merging_lemmas.lines_each",
            "merging.bend",
        ),
        (
            "merge writes beside a path the file that keeps it too",
            "      beside.files(p, rest)",
            "      beside.files(p, f <> rest)",
            "merging_lemmas.contest_written",
            "merging.bend",
        ),
        (
            "show takes a document as standing in whatever its header forgets",
            "    case True{} True{} _:\n      Taken.Stands{}",
            "    case _ True{} _:\n      Taken.Stands{}",
            "show_lemmas.taken_says",
            "standin.bend",
        ),
        (
            "forget resets a forgotten item's terminator",
            "      Ops.Item{SNil{}, n, True{}}",
            "      Ops.Item{SNil{}, True{}, True{}}",
            "forget_lemmas.item_shape",
            "forget.bend",
        ),
        (
            "forget writes an empty line where the text was rather than the marker",
            "      Ops.Item{SNil{}, n, True{}}",
            "      Ops.Item{SNil{}, n, False{}}",
            "forget_lemmas.item_forgot",
            "forget.bend",
        ),
        (
            "forget picks the revision that wrote an item rather than the document it names",
            "      pick.if(named.find(ns, by), op, item, picks.deletes(dl, ns))",
            "      pick.if(Some{by}, op, item, picks.deletes(dl, ns))",
            "forget_lemmas.picks_of",
            "forget.bend",
        ),
        (
            "forget of a payload names its length where its digest goes",
            "      Done{Fg.Plan{[target], Bool.pick(",
            "      Done{Fg.Plan{[n], Bool.pick(",
            "forget_lemmas.whole_of",
            "forget.bend",
        ),
        (
            "forget destroys a file without asking whether its bytes are forgotten",
            "      Rev.keep(Bool.and(Rev.member(targets, d), Bool.not(Bool.xor(filed.document(p), documents))), p, destroyed.of(rest, targets, documents))",
            "      Rev.keep(Bool.and(True{}, Bool.not(Bool.xor(filed.document(p), documents))), p, destroyed.of(rest, targets, documents))",
            "forget_lemmas.of_held",
            "forget.bend",
        ),
        (
            "forget takes the span after `--lines` as a word as well",
            "      Done{Fg.Reading{Some{w}, d, f, ws, False{}}}",
            "      Done{Fg.Reading{Some{w}, d, f, List.append(&2, String, ws, [w]), False{}}}",
            "forget_lemmas.step_ok",
            "forget.bend",
        ),
        (
            "forget clears every file of `cache/` but its note",
            "      Rev.keep(T.is_digest(String.drop(p, 6n)), p, cached(rest))",
            "      Rev.keep(Bool.not(String.eq(p, \"cache/README.txt\")), p, cached(rest))",
            "forget_lemmas.clears",
            "forget.bend",
        ),
        (
            "a stand-in beside the original rewrites a line it does not forget",
            "      Ops.Item{t, n, f}\n",
            "      Ops.Item{t2, n, f}\n",
            "forget_lemmas.item_union_like",
            "standin.bend",
        ),
        (
            "the stand-in folded last names a forgotten line's text",
            "      Ops.Item{SNil{}, n, True{}}\n",
            "      Ops.Item{t2, n, True{}}\n",
            "forget_lemmas.item_union_comm",
            "standin.bend",
        ),
        (
            "a stand-in beside the original forgets nothing",
            "      Ops.Item{SNil{}, n, True{}}\n",
            "      Ops.Item{t, n, f}\n",
            "forget_lemmas.item_cover_union",
            "standin.bend",
        ),
        (
            "forget counts the version it forgets among the others",
            "      Rev.keep(Bool.not(String.eq(d, target)), d, others.of(rest, target))",
            "      Rev.keep(True{}, d, others.of(rest, target))",
            "forget_lemmas.excl",
            "forget.bend",
        ),
        (
            "name keeps the other words newest first",
            "      NameCmd{p, a, d, f, sh, List.append(&2, String, r, [w])}",
            "      NameCmd{p, a, d, f, sh, w <> r}",
            "name_lemmas.args_step",
            "commands.bend",
        ),
        (
            "name sends the header early without `--fields`",
            "      Done{NamePlan.Set{n, t, None{}, pin, axis, fields, Bool.and(fields, Bool.not(String.is_empty(t)))}}",
            "      Done{NamePlan.Set{n, t, None{}, pin, axis, fields, Bool.not(String.is_empty(t))}}",
            "name_lemmas.plan_meant",
            "commands.bend",
        ),
        (
            "a bookmark moved forgets it was private",
            "    return Bm.Bookmark{n, t, Maybe.default(&2, Bool, axis, private_of(bs, n))}",
            "    return Bm.Bookmark{n, t, Maybe.default(&2, Bool, axis, False{})}",
            "name_lemmas.points_ok",
            "commands.bend",
        ),
        (
            "`name --revision` pins the change",
            "      Done{Bm.Target.Revision{id_of(f)}}",
            "      Done{Bm.Target.Change{change_of(f)}}",
            "name_lemmas.aimed_ok",
            "commands.bend",
        ),
        (
            "`name --fields` says its header twice",
            '      List.append(&2, String, name.head(Bool.not(early)), ["name " ++ n])',
            '      List.append(&2, String, name.head(True{}), ["name " ++ n])',
            "name_lemmas.said_fields",
            "commands.bend",
        ),
        (
            "files lists paths in reverse order",
            "  List.sort(~Tree.Entry, ~(a => b => String.is_le(files.key(a), files.key(b))), es)",
            "  List.sort(~Tree.Entry, ~(a => b => String.is_le(files.key(b), files.key(a))), es)",
            "listing_lemmas.files_sorted",
            "commands.bend",
        ),
        (
            "files prints the path last",
            '      (pad(Tree.entry_path(e), width) ++ "  " ++ Tree.entry_file(e)) <> files.lines(rest, width)',
            '      (Tree.entry_file(e) ++ "  " ++ pad(Tree.entry_path(e), width)) <> files.lines(rest, width)',
            "listing_lemmas.lines_end",
            "commands.bend",
        ),
        (
            "names says a pin the store lacks is its digest",
            '      Bool.pick(String, Rev.member(all_ids, id), abbreviate(id, all_ids), "(not here yet)")',
            '      Bool.pick(String, Rev.member(all_ids, id), abbreviate(id, all_ids), id)',
            "listing_lemmas.resolution_held",
            "commands.bend",
        ),
        (
            "bookmarks are read in reverse name order",
            "  List.sort(~Named, ~(a => b => named.le(a, b)), named(ps))",
            "  List.sort(~Named, ~(a => b => named.le(b, a)), named(ps))",
            "listing_lemmas.order_sorted",
            "commands.bend",
        ),
        (
            "log --fields puts the change first",
            '      id ++ " " ++ change ++ " " ++ when ++ " " ++ found(id, change, heads, gone, h)',
            '      change ++ " " ++ id ++ " " ++ when ++ " " ++ found(id, change, heads, gone, h)',
            "listing_lemmas.fields_each",
            "commands.bend",
        ),
        (
            "log counts facts of every kind",
            "    case False{}:\n      0n\n    case True{}:\n      count_facts.excl(added, v, exclude)",
            "    case False{}:\n      1n\n    case True{}:\n      count_facts.excl(added, v, exclude)",
            "listing_lemmas.one_count",
            "commands.bend",
        ),
        (
            "status names a fact by its path first",
            '      (pad(k, 7n) ++ " " ++ p) <> facts.said(rest)',
            '      (pad(p, 7n) ++ " " ++ k) <> facts.said(rest)',
            "status_lemmas.facts_exact",
            "commands.bend",
        ),
        (
            "status leaves the accepts out",
            "      List.append(&2, String, accepts.said(accept),",
            "      List.append(&2, String, Nil{},",
            "status_lemmas.report_says",
            "commands.bend",
        ),
        (
            "status says contests where no work is joined",
            "  Bool.pick(List<&2, String>, Nat.is_gt(List.length(&2, String, ps), 1n), contest.lines(cs), Nil{})",
            "  Bool.pick(List<&2, String>, Nat.is_gt(List.length(&2, String, ps), 0n), contest.lines(cs), Nil{})",
            "status_lemmas.contests_said",
            "commands.bend",
        ),
        (
            "a contest line names the lower digest first",
            '      Some{String.take(f, 8n) ++ lower_of(" is ", cs)}',
            '      Some{lower_of(" is ", cs) ++ String.take(f, 8n)}',
            "status_lemmas.push_open",
            "commands.bend",
        ),
        (
            "status merges only the parents after the first",
            "      status.tree.read.r(first, picked(reached.all(fs, ps), Pick{waiting(fs), Nil{}}))",
            "      status.tree.read.r(first, picked(reached.all(fs, rest), Pick{waiting(fs), Nil{}}))",
            "status_lemmas.one_tree",
            "commands.bend",
        ),
        (
            "status reads a file of bytes from the folder",
            "    case Here{+path, Some{Tree.Entry{+f, q, Tree.Lines{}, y, g, m}}, Some{Folder.Found.File{r, x, n}}}:",
            "    case Here{+path, Some{Tree.Entry{+f, q, Tree.Whole{}, y, g, m}}, Some{Folder.Found.File{r, x, n}}}:",
            "status_lemmas.read_lines",
            "commands.bend",
        ),
        (
            "status replays a file whatever its kind",
            "      Bool.pick(List<&2, String>, Bool.and(status.lines(h), Maybe.is_none(&2, String, stated_digest(eds, origin(os, here.file(h))))), here.file(h) <> later, later)",
            "      Bool.pick(List<&2, String>, Maybe.is_none(&2, String, stated_digest(eds, origin(os, here.file(h)))), here.file(h) <> later, later)",
            "status_lemmas.unknown_lined",
            "commands.bend",
        ),
        (
            "status compares a file the parents dispute with a digest",
            "Bool.pick(Maybe<&2, String>, proposed, None{}, status.before(bf, e))",
            "status.before(bf, e)",
            "status_lemmas.seens_ok",
            "commands.bend",
        ),
        (
            "status says an arriving path on another line too",
            "  facts.with(Set.from_list(added(os)), os, links)",
            "  facts.with(Set.new(), os, links)",
            "Laws.status_says_an_arrival_once",
            "survey.bend",
        ),
        (
            "status gives no path the host's digest for it",
            "      stats.map(rest, more, Map.set(&2, String, m, p, s))",
            "      stats.map(rest, more, m)",
            "status_lemmas.stats_map_answer",
            "commands.bend",
        ),
        (
            "status replays a file a statement settles",
            "    case Some{d}:\n      Done{d}\n    case None{}:\n      Result.map(&2, &2, String, List<&2, Ops.Item>, String, items => Ops.state_digest(items), content.in(older, ds, left, file))",
            "    case Some{d}:\n      Result.map(&2, &2, String, List<&2, Ops.Item>, String, items => d, content.in(older, ds, left, file))\n    case None{}:\n      Result.map(&2, &2, String, List<&2, Ops.Item>, String, items => Ops.state_digest(items), content.in(older, ds, left, file))",
            "status_lemmas.fails_digest",
            "commands.bend",
        ),
        (
            "joining refuses where no parent was read",
            "    case Nil{}:\n      Done{Nil{}}\n    case +p <> rest:\n      do Result<&2, &2, String, List<&2, Maybe<&2, String>>>:",
            "    case Nil{}:\n      Fail{\"no parent\"}\n    case +p <> rest:\n      do Result<&2, &2, String, List<&2, Maybe<&2, String>>>:",
            "status_lemmas.each_fails",
            "commands.bend",
        ),
        (
            "record lets a link to a file it drops dangle",
            "      Bool.pick(Maybe<&2, String>, has(gone, named),\n",
            "      Bool.pick(Maybe<&2, String>, False{},\n",
            "survey_lemmas.target_later",
            "survey.bend",
        ),
        (
            "record looks for the folder's link at a dangling link's file rather than its path",
            "Bool.or(has(gone, f), Rev.member(pointing, p))",
            "Bool.or(has(gone, f), Rev.member(pointing, f))",
            "survey_lemmas.dangle_suffix",
            "survey.bend",
        ),
        (
            "status refuses a file of lines at another path than its own",
            '      [Obs.Refused{path, "recorded as lines and no longer UTF-8 text; drop it and add it again"}]',
            '      [Obs.Refused{SNil{}, "recorded as lines and no longer UTF-8 text; drop it and add it again"}]',
            "survey_lemmas.each_changed",
            "survey.bend",
        ),
        (
            "status checks a link's own path rather than its target",
            "  link.checked(path, target, held, shown, fresh, link_fault(target))",
            "  link.checked(path, target, held, shown, fresh, link_fault(path))",
            # `LAWS.status_refuses_what_the_folder_holds` rejects it too; the
            # checker meets the dangling-link lemmas, which read the same
            # links, first.
            "survey_lemmas.pt_held_link",
            "survey.bend",
        ),
        (
            "record states a kind for a file the position already holds",
            "      Bool.pick(Maybe<&2, String>, String.eq(Tree.entry_path(e), p),\n",
            "      Bool.pick(Maybe<&2, String>, False{},\n",
            "survey_lemmas.fixed_later",
            "survey.bend",
        ),
        (
            "record takes a kind for a path it is not looking at",
            "      Bool.pick(Maybe<&2, String>, covers(only, p), kind_fixed(p, t, kind_fault(only, t, rest)),",
            "      Bool.pick(Maybe<&2, String>, True{}, kind_fixed(p, t, kind_fault(only, t, rest)),",
            "survey_lemmas.kinds_tail",
            "survey.bend",
        ),
        (
            "record writes a move line for a file moved again later",
            "Bool.pick(List<&2, T.Split>, Bool.or(has(gone, f), moved.later(rest, f)), later, T.Split{f, to} <> later)",
            "Bool.pick(List<&2, T.Split>, has(gone, f), later, T.Split{f, to} <> later)",
            "survey_lemmas.final_moves",
            "survey.bend",
        ),
        (
            "a file moved twice given a `move` line for each",
            "      Bool.or(String.eq(f, file), moved.later(rest, file))",
            "      moved.later(rest, file)",
            "survey_lemmas.later_none",
            "survey.bend",
        ),
        (
            "a move moves every file but the one named",
            "Tree.Entry{f, Bool.pick(String, String.eq(f, file), to, p), k, y, g, m}",
            "Tree.Entry{f, Bool.pick(String, Bool.not(String.eq(f, file)), to, p), k, y, g, m}",
            "survey_lemmas.holds_relocated",
            "survey.bend",
        ),
        (
            "a restricted record refuses what the walk refused elsewhere",
            "Bool.pick(List<&2, T.Split>, covers(only, p), T.Split{p, b} <> later, later)",
            "Bool.pick(List<&2, T.Split>, True{}, T.Split{p, b} <> later, later)",
            "survey_lemmas.only_refused_ok",
            "survey.bend",
        ),
        (
            "status offers a rename of bytes more than one path left",
            "Bool.and(Nat.is_eq(count(all, d), 1n), Nat.is_eq(count(arr, d), 1n))",
            "Nat.is_eq(count(arr, d), 1n)",
            "survey_lemmas.go_good",
            "survey.bend",
        ),
        (
            "a run of one path counted once too few",
            "claims.go(rest, path, 1n+n, heads_eq(rest, path))",
            "claims.go(rest, path, n, heads_eq(rest, path))",
            "survey_lemmas.go_same",
            "survey.bend",
        ),
        (
            "a link written as a reference where the revision states nothing",
            'Bool.pick(String, stated(t, gone, arriving, at), "r" ++ at, "v" ++ target)',
            'Bool.pick(String, True{}, "r" ++ at, "v" ++ target)',
            "survey_lemmas.ref_held",
            "survey.bend",
        ),
        (
            "a link written as a reference to a file the record drops",
            "      Bool.or(Bool.not(has(gone, f)), any_kept(rest, gone))",
            "      Bool.or(True{}, any_kept(rest, gone))",
            "survey_lemmas.held_ref",
            "survey.bend",
        ),
        (
            "a link's `..` pushed rather than climbed",
            'res.push(p, xs, Bool.or(String.is_empty(p), String.eq(p, ".")), String.eq(p, ".."))',
            'res.push(p, xs, Bool.or(String.is_empty(p), String.eq(p, ".")), False{})',
            "survey_lemmas.step_inv",
            "survey.bend",
        ),
        (
            "record goes on with a path nothing answers to",
            "  Bool.pick(Result<&2, &2, Refused, Unit>, Bool.not(List.is_empty(&2, String, absent)),",
            "  Bool.pick(Result<&2, &2, Refused, Unit>, False{},",
            "survey_lemmas.named_done",
            "commands.bend",
        ),
        (
            "record refuses a path only the renames put there",
            "Bool.pick(List<&2, String>, Bool.or(any_beneath(n, folder), Bool.or(any_beneath(n, was), any_beneath(n, placed))), later, n <> later)",
            "Bool.pick(List<&2, String>, Bool.or(any_beneath(n, folder), any_beneath(n, was)), later, n <> later)",
            "survey_lemmas.unknown_empty",
            "survey.bend",
        ),
        (
            "abandon takes a reason that is only whitespace",
            "  Bool.pick(Result<&2, &2, Refused, Unit>, String.is_empty(Naming.trim_space(m)),",
            "  Bool.pick(Result<&2, &2, Refused, Unit>, String.is_empty(m),",
            # Written against `LAWS.abandon_takes_a_reason_that_says_something`; the checker now stops
            # first at `rewrite_lemmas.asked_ok`.
            "rewrite_lemmas.asked_ok",
            "commands.bend",
        ),
        (
            "a summary keeps a separator",
            "SCon{Bool.pick(Char, Bool.or(reserved(c), is_space(c)), ' ', c), spaced(rest)}",
            "SCon{Bool.pick(Char, is_space(c), ' ', c), spaced(rest)}",
            "naming_lemmas.plain_spaced",
            "naming.bend",
        ),
        (
            "a summary of nothing falls back on more letters than fit",
            "def CHANGE_CHARS() -> Nat:\n  8n",
            "def CHANGE_CHARS() -> Nat:\n  64n",
            "naming_lemmas.summary_le_pick",
            "naming.bend",
        ),
        (
            "a filed path keeps its control characters",
            "SCon{Bool.pick(Char, Folder.is_control(c), ' ', c), scrubbed(rest)}",
            "SCon{c, scrubbed(rest)}",
            "naming_lemmas.scrubbed_ok",
            "naming.bend",
        ),
        (
            "record compares the clock with the earliest work",
            "Nat.is_ge(instant(w), Maybe.default",
            "Nat.is_le(instant(w), Maybe.default",
            "naming_lemmas.newest_inv",
            "naming.bend",
        ),
        (
            "a marked line drawn without its sign",
            "Piece{sign, False{}} <> ps}]",
            "ps}]",
            "colour_lemmas.marked_some",
            "commands.bend",
        ),
        (
            "diff replays a file of lines its stated digest settles",
            "Planned{h, digest, Bool.and(lines, Bool.not(Bool.and(regular, same))), ",
            "Planned{h, digest, lines, ",
            "plan_lemmas.replayed_unsettled",
            "commands.bend",
        ),
        (
            "diff reads a folder file the position holds as bytes",
            "Bool.and(regular, Bool.or(Bool.not(here.held(h)), Bool.and(lines, Bool.not(same))))}",
            "regular}",
            "plan_lemmas.read_unsettled",
            "commands.bend",
        ),
        (
            "a chain that stays at the revision it began at",
            "f <> chain.go(q, fs, first_parent(fs, parents_of(f)))",
            "f <> chain.go(q, fs, Some{f})",
            "chain_lemmas.line_at",
            "commands.bend",
        ),
        (
            "a document outside revisions/ read as a revision",
            "push_full(Bool.pick(Maybe<&2, Full>, Store.in_revisions(root, path), full.read(id, path, text, Rev.parse(text)), None{}), fulls(root, rest))",
            "push_full(full.read(id, path, text, Rev.parse(text)), fulls(root, rest))",
            "fulls_lemmas.fulls_filed",
            "commands.bend",
        ),
        (
            "a size believed whatever digest the host's line names",
            "sizes.read(rest, more), String.eq(T.word(st), d))",
            "sizes.read(rest, more), True{})",
            "sizes_lemmas.says",
            "commands.bend",
        ),
        (
            "diff fetches nothing for a file it replays",
            "    case True{}:\n      wanted(fs, f)\n",
            "    case True{}:\n      Nil{}\n",
            "fetch_lemmas.one_fetched",
            "commands.bend",
        ),
        (
            "what a resolution keeps left unfetched",
            "    case True{}:\n      Res.keeps(Res.parse(text))\n",
            "    case True{}:\n      Nil{}\n",
            "fetch_lemmas.kept_one",
            "commands.bend",
        ),
        (
            "a span a..b read as b..a",
            "      among(fs, Rev.without(reached(fs, to), reached(fs, from)))",
            "      among(fs, Rev.without(reached(fs, from), reached(fs, to)))",
            "span_lemmas.span_listed",
            "commands.bend",
        ),
        (
            "diff over the folder leaves an edit it believes unfetched",
            "    case True{}:\n      edit_of.split(origin(os, here.file(h)))\n",
            "    case True{}:\n      Nil{}\n",
            "fetch_lemmas.edit_one",
            "commands.bend",
        ),
        (
            "a payload diff shows left unasked",
            "    case Some{Side.Whole{d, n}}:\n      [d]\n    case _:\n      Nil{}\n",
            "    case Some{Side.Whole{d, n}}:\n      Nil{}\n    case _:\n      Nil{}\n",
            "fetch_lemmas.payload_side",
            "commands.bend",
        ),
        (
            "a payload the host could not find asked the stat of",
            "      sizes.keep(d, p, sizes.of(root, rest, more), String.eq(p, \"-\"))",
            "      sizes.keep(d, p, sizes.of(root, rest, more), False{})",
            "fetch_lemmas.sizes_located",
            "commands.bend",
        ),
        (
            "record keeps the first `--onto` instead of the last",
            "      RecordCmd{Some{v}, ms, ac, at, mv, ks, ns, d, f, mg}",
            "      RecordCmd{Maybe.or(&2, String, o, Some{v}), ms, ac, at, mv, ks, ns, d, f, mg}",
            "record_lemmas.words_read",
            "commands.bend",
        ),
        (
            "a rewrite keeps the first `-m` instead of the last",
            "      RwCmd{Some{v}, mv, o, n, d, f, y}",
            "      RwCmd{Maybe.or(&2, String, m, Some{v}), mv, o, n, d, f, y}",
            "record_lemmas.amend_reads_its_words_ok",
            "commands.bend",
        ),
        (
            "record merges the last `--merge` first",
            "      RecordCmd{o, List.append(&2, String, ms, [v]), ac, at, mv, ks, ns, d, f, mg}",
            "      RecordCmd{o, v <> ms, ac, at, mv, ks, ns, d, f, mg}",
            "record_lemmas.words_read",
            "commands.bend",
        ),
        (
            "record cuts a rename's new path at a second `=`",
            "      Done{T.Split{a, String.join(b <> rest, \"=\")}}",
            "      Done{T.Split{a, b}}",
            "record_lemmas.cut_cons",
            "commands.bend",
        ),
        (
            "record keeps the slash a shell leaves after a directory",
            "  String.reverse(drop_slashes(r, heads_slash(r)))",
            "  String.reverse(r)",
            "record_lemmas.trim_slash",
            "commands.bend",
        ),
        (
            "a rewrite takes a second target in place of the first",
            "    case RwCmd{m, mv, o, Some{n}, d, f, y}:\n      Fail{Refused{2, rw.second(cmd, w)}}",
            "    case RwCmd{m, mv, o, Some{n}, d, f, y}:\n      Done{RwCmd{m, mv, o, Some{w}, d, f, y}}",
            "record_lemmas.word_n",
            "commands.bend",
        ),
        (
            "a carried revision is authored by whoever carried it",
            "Rev.Rev{change, parents, [id], author, when, revised_by(split.rest(stamp), author), Some{split.head(stamp)}, new_facts, message}",
            "Rev.Rev{change, parents, [id], split.rest(stamp), when, revised_by(split.rest(stamp), author), Some{split.head(stamp)}, new_facts, message}",
            "rewrite_lemmas.made_kept",
            "commands.bend",
        ),
        (
            "abandon takes in a merge standing on the run",
            "Bool.and(Nat.is_eq(List.length(&2, String, ps), 1n), Rev.member(ps, p))",
            "Rev.member(ps, p)",
            "rewrite_lemmas.joins_ok",
            "commands.bend",
        ),
        (
            "a reword drops what the revision stated",
            "Rev.Rev{change, parents, [id], author, when, revised_by(reviser, author), Some{revised}, facts, msg}",
            "Rev.Rev{change, parents, [id], author, when, revised_by(reviser, author), Some{revised}, Nil{}, msg}",
            "rewrite_lemmas.reword",
            "commands.bend",
        ),
        (
            "record diffs an edited file against nothing",
            "edited.content(f, p, Ops.diff(before_of(befores, f), after))",
            "edited.content(f, p, Ops.diff(Nil{}, after))",
            "record_lemmas.lines_state",
            "commands.bend",
        ),
        (
            "record moves the bookmarks on every change but its parents'",
            "Bool.pick(List<&2, Bm.Bookmark>, Rev.member(changes, c), Bm.Bookmark{n, Bm.Target.Change{c}, p} <> later, later)",
            "Bool.pick(List<&2, Bm.Bookmark>, Rev.member(changes, c), later, Bm.Bookmark{n, Bm.Target.Change{c}, p} <> later)",
            "record_lemmas.ah.step",
            "commands.bend",
        ),
        (
            "record reads a parent's identifier as its change",
            "      Bool.pick(Maybe<&2, String>, String.eq(i, id), Some{change}, full.change_of(rest, id))",
            "      Bool.pick(Maybe<&2, String>, String.eq(i, id), Some{i}, full.change_of(rest, id))",
            "record_lemmas.co.step",
            "commands.bend",
        ),
        (
            "record moves the bookmarks on its first parent alone",
            "full.change_of(fs, p)), Nil{}), parents.changes(fs, rest))",
            "full.change_of(fs, p)), Nil{}), Nil{})",
            "record_lemmas.pc.has",
            "commands.bend",
        ),
        (
            "record writes what the survey refused",
            "moved.paths(moves, gone)), List.append(&2, T.Split, walked, refusals(os)), cs,",
            "moved.paths(moves, gone)), walked, cs,",
            # `record_lemmas.settled_read` rejects it too; the checker meets
            # `survey_lemmas.restricted_ok`, which unfolds the same field, first.
            "survey_lemmas.restricted_ok",
            "survey.bend",
        ),
        (
            "record writes a contested file of lines left empty",
            "sorted(accepts(os)), emptied(os), dangle(",
            "sorted(accepts(os)), Nil{}, dangle(",
            "record_lemmas.settled_read",
            "survey.bend",
        ),
        (
            "record lets through an acceptance nothing contests",
            "Bool.pick(Result<&2, &2, Refused, Sv.Planned>, Bool.not(List.is_empty(&2, String, needless)),",
            "Bool.pick(Result<&2, &2, Refused, Sv.Planned>, False{},",
            # Written against `record_lemmas.settled`; the checker now stops
            # first at `survey_lemmas.planned_claims`.
            "survey_lemmas.planned_claims",
            "commands.bend",
        ),
        (
            "carry takes a change for the revision named",
            "Result.map(&2, &2, Refused, Full, Maybe<&2, String>, f => Some{id_of(f)}, resolved.r(fs, bs, s))",
            "Result.map(&2, &2, Refused, Full, Maybe<&2, String>, f => Some{change_of(f)}, resolved.r(fs, bs, s))",
            "rewrite_lemmas.carry_held",
            "commands.bend",
        ),
        (
            "record moves the path named rather than the file at it",
            "      placed.move.r(rest, t2, List.append(&2, T.Split, moved, [T.Split{f, to}]), placed.head(t2, rest), placed.fault(rest))",
            "      placed.move.r(rest, t2, List.append(&2, T.Split, moved, [T.Split{from, to}]), placed.head(t2, rest), placed.fault(rest))",
            # Written against `record_lemmas.move_held`; the checker now stops
            # first at `survey_lemmas.move_moved`.
            "survey_lemmas.move_moved",
            "commands.bend",
        ),
        (
            "record takes no `--at` at all",
            "      placed.at.r(rest, t2, List.append(&2, T.Split, moved, [T.Split{f, to}]), placed.holds(t2, rest))",
            "      placed.at.r(rest, t, moved, placed.holds(t, rest))",
            "survey_lemmas.at_ats",
            "commands.bend",
        ),
        (
            "record lets a restriction take one end of a rename",
            "Bool.pick(Result<&2, &2, Refused, Unit>, Bool.and(Sv.covers(named, from), Sv.covers(named, to)), restricted.half.r(named, rest),",
            "Bool.pick(Result<&2, &2, Refused, Unit>, Bool.or(Sv.covers(named, from), Sv.covers(named, to)), restricted.half.r(named, rest),",
            "record_lemmas.half_iff",
            "commands.bend",
        ),
        (
            "record lets a merge of two be restricted",
            "  Bool.pick(Result<&2, &2, Refused, Unit>, Nat.is_gt(List.length(&2, String, ps), 1n),",
            "  Bool.pick(Result<&2, &2, Refused, Unit>, Nat.is_gt(List.length(&2, String, ps), 2n),",
            "record_lemmas.restriction_iff",
            "commands.bend",
        ),
        (
            "record lets a skipped name nothing answers to through",
            "  Bool.pick(Result<&2, &2, Refused, Unit>, Bool.not(List.is_empty(&2, String, out)),",
            "  Bool.pick(Result<&2, &2, Refused, Unit>, False{},",
            # Written against `record_lemmas.named_ok`; the checker now stops
            # first at `survey_lemmas.named_done`.
            "survey_lemmas.named_done",
            "commands.bend",
        ),
        (
            "record --dry-run says a link for a file arriving",
            'fact("link", without(sorted(links), arriving)))))))',
            'fact("link", sorted(links)))))))',
            "record_lemmas.recorded_once",
            "survey.bend",
        ),
        (
            "--fields names a revision it wrote in the carry twice",
            "WROTE() <> said.lines(\"revision \", SNil{}, sorted_distinct(carried.ids(steps))),",
            "WROTE() <> said.lines(\"revision \", SNil{}, List.sort(~String, ~(a => b => String.is_le(a, b)), carried.ids(steps))),",
            "rewrite_lemmas.writes_fields",
            "commands.bend",
        ),
        (
            "record takes a file with no NUL for text",
            "Bool.pick(Maybe<&2, String>, Bool.and(lines.stated(ks, p), Bool.not(Folder.is_utf8(bytes_of(p, Map.get(List<&2, U32>, Nil{}, reads, p))))),",
            "Bool.pick(Maybe<&2, String>, Bool.and(lines.stated(ks, p), Folder.has_nul(bytes_of(p, Map.get(List<&2, U32>, Nil{}, reads, p)))),",
            "record_lemmas.lines_head",
            "commands.bend",
        ),
        (
            "record checks the kind of the last path named alone",
            "      Bool.pick(List<&2, T.Split>, String.eq(split_key(a), split_key(b)), later, a <> later)",
            "      later",
            "record_lemmas.distinct_keeps",
            "commands.bend",
        ),
        (
            "record checks only the first attachment accepted",
            "      Rev.keep(Bool.not(Rev.member(ys, x)), x, minus(rest, ys))",
            "      Rev.keep(Bool.not(Rev.member(ys, x)), x, Nil{})",
            "record_lemmas.minus_nil",
            "commands.bend",
        ),
        (
            "record extends a name no revision the store holds has",
            "def sharing_base(ns: List<&2, Named>, +base: String) -> Bool:\n  match ns:\n    case Nil{}:\n      False{}",
            "def sharing_base(ns: List<&2, Named>, +base: String) -> Bool:\n  match ns:\n    case Nil{}:\n      True{}",
            "record_lemmas.sb_mem",
            "naming.bend",
        ),
        (
            "record moves only the first bookmark on a parent's change",
            "      Bool.pick(List<&2, Bm.Bookmark>, Rev.member(changes, c), Bm.Bookmark{n, Bm.Target.Change{c}, p} <> later, later)",
            "      Bool.pick(List<&2, Bm.Bookmark>, Rev.member(changes, c), [Bm.Bookmark{n, Bm.Target.Change{c}, p}], later)",
            "record_lemmas.ah.step",
            "commands.bend",
        ),
        (
            "record reads only the first file `--lines` names",
            "      Rev.keep(lines.stated(ks, p), p, lined_added(ks, rest))",
            "      Rev.keep(lines.stated(ks, p), p, Nil{})",
            "record_lemmas.lines_head",
            "commands.bend",
        ),
        (
            "record reads the position as empty",
            "        return Before{f, items} <> later",
            "        return Before{f, Nil{}} <> later",
            "record_lemmas.bi.of",
            "commands.bend",
        ),
        (
            "amend changes the identifier of a file it added",
            "      T.Split{p, f} <> amend.mint(rest, more, ids)",
            "      T.Split{p, f ++ \"x\"} <> amend.mint(rest, more, ids)",
            "rewrite_lemmas.kp_case",
            "commands.bend",
        ),
        (
            "abandon takes a reason of spaces",
            "  Bool.pick(Result<&2, &2, Refused, Unit>, String.is_empty(Naming.trim_space(m)),",
            "  Bool.pick(Result<&2, &2, Refused, Unit>, String.is_empty(m),",
            "rewrite_lemmas.asked_ok",
            "commands.bend",
        ),
        (
            "an abandon dry run names the run in reverse",
            '[each.lines("would abandon ", spelled_all(bs, history(fs), run)),',
            '[each.lines("would abandon ", spelled_all(bs, history(fs), List.reverse(&2, String, run))),',
            "rewrite_lemmas.dry_names",
            "commands.bend",
        ),
        (
            "a mark is put on its run unsorted",
            "      order.go(rest, insert(run, m), starts(rest))",
            "      order.go(rest, m <> run, starts(rest))",
            "nfc_lemmas.order_canonical",
            "nfc.bend",
        ),
        (
            "the class lookup stops at a run that begins with the character",
            "      U32.is_lt(c, lo)\n    case _:\n      True{}",
            "      U32.is_le(c, lo)\n    case _:\n      True{}",
            "nfc_lemmas.class_scan",
            "nfc.bend",
        ),
        (
            "the walk keeps both of two names that are one path",
            "    case f <> +rest True{}:\n      distinct.go(rest, last, distinct.same(rest, last))",
            "    case f <> +rest True{}:\n      f <> distinct.go(rest, last, distinct.same(rest, last))",
            "nfc_lemmas.go_apart",
            "folder.bend",
        ),
        (
            "a read opens whatever name the listing has, normal form or not",
            "Bool.and(Bool.not(String.starts_with(line, \"u \")), String.eq(Nfc.nfc(name), want))",
            "Bool.not(String.starts_with(line, \"u \"))",
            "nfc_lemmas.take_ok",
            "folder.bend",
        ),
        (
            "a name that cannot be spelled is passed over",
            "unspelled.is(rest), Keyed{unspelled.key(before, k), T.Split{dir ++ \"/\" ++ String.drop(line, 2n), unspelled.because()}} <> acc)",
            "unspelled.is(rest), acc)",
            "nfc_lemmas.read_back",
            "folder.bend",
        ),
        (
            "the quick check passes only what is below a space",
            "Bool.and(Bool.or(U32.is_lt(x, 128), U32.is_lt(x, Tab.inert_below())), quick(t))",
            "Bool.and(Bool.or(U32.is_lt(x, 32), U32.is_lt(x, Tab.inert_below())), quick(t))",
            "nfc_lemmas.quick_ascii",
            "nfc.bend",
        ),
        (
            "ordering drops the run it closes at a starter",
            "      List.append(&2, Mark, run, m <> order.go(rest, Nil{}, starts(rest)))",
            "      m <> order.go(rest, Nil{}, starts(rest))",
            "nfc_lemmas.order_canonical",
            "nfc.bend",
        ),
        (
            "the walk drops the file it keeps for a path",
            "    case +f <> +rest False{}:\n      f <> distinct.go(rest, found.path(f), distinct.same(rest, found.path(f)))",
            "    case +f <> +rest False{}:\n      distinct.go(rest, found.path(f), distinct.same(rest, found.path(f)))",
            "nfc_lemmas.go_apart",
            "folder.bend",
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
