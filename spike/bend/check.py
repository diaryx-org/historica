#!/usr/bin/env python3
"""Check proofs, run JS/native corpora, ensure replay mutations are rejected,
and hold the store commands to the Rust tool's output.

The stages are independent and run at once; `check.py <stage>...` runs only
those named, for iterating on one: store, corpora, similar, proof, mutations.

The corpora and the store commands run on the JS build alone unless given
`--native`, which builds and runs each natively as well: emitting and
compiling `main.bend`'s C takes minutes the JS build does not.
"""
from concurrent.futures import ThreadPoolExecutor
import time
from pathlib import Path
import hashlib
import os
import random
import re
import shutil
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


def run(*args, cwd=ROOT, timeout=120):
    print("+", " ".join(map(str, args)), flush=True)
    with SLOTS:
        subprocess.run(args, cwd=cwd, check=True, timeout=timeout)


def capture(*args, cwd):
    """A command's stdout, stderr and exit code, for comparing two tools."""
    done = subprocess.run(args, cwd=cwd, capture_output=True, timeout=120)
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
    asked = [a for a in sys.argv[1:] if a != "--native"] or list(stages)
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
# refusals, whose text is compared too.
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
    ],
    "revisions": [["log"], ["log", "kxryzmor"], ["show", "head"]],
    "merged": [["log"], ["files", "head"]],
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
    ],
    "modes": [["log"], ["files", "head"], ["diff", "head"], ["blame", "head", "run.sh"], ["diff"]],
    "whole": [
        ["log"], ["files", "head"], ["cat", "head", "notes/2026-08-20.md"],
        ["diff", "head"], ["blame", "head", "notes/photo.png"], ["blame", "head", "notes/2026-08-20.md"],
        # An assembled store has no folder beside it, so everything is gone.
        ["diff"], ["blame", "notes/2026-08-20.md"],
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
    ],
    # The same, with a bookmark file that is not one: every command refuses.
    "badname": [["names"], ["log"], ["files", "main"]],
    # Two authors, a rename, and a line of work beside the main one, for
    # `log`'s filters, ranges and `--fields`. Usage errors are not compared:
    # the Rust tool prints its own usage after the message.
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
    ],
    # A rule file stating two rules: the store will not open.
    "badskip": [["diff"], ["blame", "notes.md"], ["log"], ["files", "head"], ["cat", "head", "kept.md"], ["show", "head"], ["names"]],
    # Nothing recorded yet: every file is the folder's own.
    "fresh": [["diff"], ["blame", "a.md"], ["blame", "file:a"], ["diff", "file:a"]],
    # A file recorded as lines that is no longer text.
    "notext": [["diff"], ["diff", "kept.md"], ["blame", "notes.md"]],

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
    ],
}


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


def record(temporary, rust, corpus):
    store = temporary / f"store-{corpus}"
    home = temporary / f"home-{corpus}"
    env = {**os.environ, "HOME": str(home), "XDG_CONFIG_HOME": str(home / ".config")}

    def historica(*command):
        subprocess.run([rust, *command], cwd=store, env=env, check=True, capture_output=True, timeout=120)

    store.mkdir(parents=True)
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

    archive = ROOT / "ffi" / "target" / "release" / "libhistorica_bend_ffi.a"
    # The boundary's own tests — malformed input, error paths, freeing,
    # repeated calls. The archive the native program links is built with it.
    run("cargo", "test", "-q", "--release", cwd=ROOT / "ffi", timeout=600)
    source = temporary / "main.c"
    native = temporary / "main"
    script = temporary / "main.js"

    def build_native():
        run("cargo", "build", "-q", "--release", cwd=ROOT / "ffi", timeout=600)
        run(BEND, "main.bend", "-o", str(source), timeout=600)
        # `bend -o` links nothing of ours, so the C is compiled here; `-w`
        # because the generated program is not ours to lint.
        run(
            os.environ.get("CC", "cc"), "-O3", "-w", "-o", str(native), str(source),
            str(archive), "-lm", "-lpthread", timeout=900,
        )

    tools = [("js", ["bun", str(script)])]
    builds = [lambda: run(BEND, "main.bend", "-o", str(script), timeout=600)]
    if NATIVE:
        tools.insert(0, ("native", [str(native)]))
        builds.append(build_native)
    parallel(builds)

    def compare(corpus, commands):
        recorded = corpus in ("unicode", "names", "badname", "log", "merge", "walked", "folder", "badskip", "fresh", "notext")
        store = record(temporary, rust, corpus) if recorded else assemble(temporary, corpus)
        lines, failures = [], 0
        for command in commands:
            expected = capture(rust, *command, cwd=store)
            for name, tool in tools:
                got = capture(*tool, *command, cwd=store)
                if got != expected:
                    failures += 1
                    lines += [f"DIFF {corpus} {name}: {' '.join(command)}", f"  rust: {expected}", f"  bend: {got}"]
                else:
                    lines.append(f"same {corpus} {name}: {' '.join(command)}")
        return lines, failures

    results = parallel([lambda c=corpus, cs=commands: compare(c, cs) for corpus, commands in STORES.items()])
    for lines, _ in results:
        print("\n".join(lines), flush=True)
    failures = sum(f for _, f in results)
    compared = sum(len(lines) for lines, _ in results)
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
            "main.bend",
        ),
        (
            "the walk runs where its order is not known to be causal",
            '      Fail{head ++ ", file " ++ file ++ ": a revision behind it had seen no more revisions than one it had seen, so the ancestry is not a history"}',
            "      walked.tree(head, file, names, Merge.walk(walked.order(g), g, Some{Nil{}}))",
            "order_lemmas.reads.at",
            "main.bend",
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
            "main.bend",
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
            "main.bend",
        ),
        (
            "log lists a revision no filter was asked of",
            "      keep_full(keeps(fl, f), f, kept(fl, rest))",
            "      keep_full(True{}, f, kept(fl, rest))",
            "log_lemmas.kept_ok",
            "main.bend",
        ),
        (
            "a file bookmark names a file the revision does not hold",
            '      Fail{Refused{1, "the bookmark `" ++ spelling ++ "` names the file " ++ file ++ ", which " ++ String.take(id, 12n) ++ " does not hold; `historica files " ++ String.take(id, 12n) ++ "` lists what it holds"}}',
            "      Done{file}",
            "fileat_lemmas.held_ok",
            "main.bend",
        ),
        (
            "a comparison lays a removed line as context",
            '        List.append(&2, Laid, laid.all("-", List.take(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items))),',
            '        List.append(&2, Laid, laid.all(" ", List.take(&2, Ops.Item, List.drop(&2, Ops.Item, state, Nat.sub(at, pos)), List.length(&2, Ops.Item, items))),',
            "laid_lemmas.old_walk",
            "main.bend",
        ),
        (
            "blame drops a line that stayed",
            "              Row{b, it} <> r",
            "              r",
            "blame_lemmas.put_items",
            "main.bend",
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
            "main.bend",
        ),
        (
            "blame attributes the removed lines too",
            '      walked.rows(Merge.visible(t), names)',
            '      walked.rows(Merge.order(t), names)',
            "blamed_lemmas.origins_file",
            "main.bend",
        ),
        (
            "a span that drops its last line",
            'rows.keep(Bool.and(Nat.is_le(first, k), Nat.is_le(k, last))',
            'rows.keep(Bool.and(Nat.is_le(first, k), Nat.is_lt(k, last))',
            "blamed_lemmas.in_lines",
            "main.bend",
        ),
        (
            "blame drops the marker after a line without a newline",
            '      l <> "\\\\ no newline at end of file" <> rest',
            '      l <> rest',
            "blamed_lemmas.ends_row",
            "main.bend",
        ),
        (
            "blame looks a `path:` spelling up with its prefix",
            '      wcf.path.r(bs, t, p, left, Tree.at(t, p))',
            '      wcf.path.r(bs, t, p, left, Tree.at(t, sp))',
            "blamed_lemmas.spelled_r",
            "main.bend",
        ),
        (
            "blame asks the kind of the spelling, not of the file",
            '    lines_only.r(Maybe.default(&2, String, Tree.path(t, file), spelling), Tree.kind(t, file))',
            '    lines_only.r(Maybe.default(&2, String, Tree.path(t, file), spelling), Tree.kind(t, spelling))',
            "blamed_lemmas.pk_tree",
            "main.bend",
        ),
        (
            "blame <target> <path> ignores the span",
            '    blame.limited.r(fs, changes(fs), rows, span)',
            '    blame.limited.r(fs, changes(fs), rows, None{})',
            "blamed_lemmas.recorded_printed",
            "main.bend",
        ),
        (
            "blame <path> takes bytes the position never saw for text",
            '      wcf.sniffed.r(path, Folder.is_text(bs))',
            '      Done{Unit{}}',
            "blamed_lemmas.folder_kind",
            "main.bend",
        ),
        (
            "blame reads its words in reverse",
            '      BlameAsked{l, List.append(&2, String, r, [w])}',
            '      BlameAsked{l, w <> r}',
            "blamed_lemmas.run_word",
            "main.bend",
        ),
        (
            "blame <path> reads through a link in the folder",
            '    case Folder.Found.Link{p, t}:\n      lines_only.r(path, Some{Tree.Link{}})',
            '    case Folder.Found.Link{p, t}:\n      Done{Unit{}}',
            "blamed_lemmas.ck_found",
            "main.bend",
        ),
        (
            "diff's --onto swallows every word after it",
            '    case DWant.Onto{}:\n      DRead{Done{dasked.onto(a, w)}, DWant.No{}}',
            '    case DWant.Onto{}:\n      DRead{Done{dasked.onto(a, w)}, DWant.Onto{}}',
            "diffcmd_lemmas.run_ok",
            "main.bend",
        ),
        (
            "diff compares a revision with nothing rather than its parent",
            '    case None{}:\n      sole_parent.r(id_of(right), parents_of(right))',
            '    case None{}:\n      Done{None{}}',
            "diffcmd_lemmas.left_ok",
            "main.bend",
        ),
        (
            "diff limits to the spelling rather than the file it names",
            '    f : String <- file_in.r(right, bs, sp, t)\n    return Limit.File{f}',
            '    f : String <- file_in.r(right, bs, sp, t)\n    return Limit.File{sp}',
            "diffcmd_lemmas.lim_file_bind",
            "main.bend",
        ),
        (
            "diff shows a file whose sides agree",
            '  Bool.pick(Maybe<&2, Compared>, pair.differs(c), Some{c}, None{})',
            '  Some{c}',
            "diffcmd_lemmas.built_ok",
            "main.bend",
        ),
        (
            "diff over the folder ignores the limit",
            '      Bool.pick(List<&2, Here>, here.wanted(l, h), h <> later, later)',
            '      h <> later',
            "diffcmd_lemmas.limited_ok",
            "main.bend",
        ),
        (
            "log reads --author as --grep",
            '        case LFlag.Author{}:\n          LRaw{ws, p, fi, l, Some{v}, g, si, u}',
            '        case LFlag.Author{}:\n          LRaw{ws, p, fi, l, au, Some{v}, si, u}',
            "logargs_lemmas.run_ok",
            "main.bend",
        ),
        (
            "check lets a document take a payload's digest",
            '          Filed{path, True{}, rev, stat} <> attach(rest, stats)',
            '          Filed{path, True{}, rev, stat} <> attach(rest, List.drop(&2, String, stats, 1n))',
            "check_lemmas.att_step",
            "main.bend",
        ),
        (
            "check calls a parsed operation document refused",
            '      "edit     " ++ String.take(id, 12n)',
            '      "refused  " ++ String.take(id, 12n)',
            "check_lemmas.ops_line",
            "main.bend",
        ),
        (
            "show finds a document whose digest the named one starts",
            '      Bool.pick(Maybe<&2, String>, String.starts_with(i, id), Some{text}, doc_by_id(rest, id))',
            '      Bool.pick(Maybe<&2, String>, String.starts_with(id, i), Some{text}, doc_by_id(rest, id))',
            "show_lemmas.by_id",
            "main.bend",
        ),
        (
            "cat prints through a link",
            '    not_a_link.r(t, path, file, Tree.entry_target_of(Tree.lookup(t, file)))',
            '    not_a_link.r(t, path, file, None{})',
            "show_lemmas.ck_tree",
            "main.bend",
        ),
        (
            "diff numbers an arrival as a line of the parent",
            'hunks.walk(rest, Bool.pick(Nat, String.eq(sign, "+"), b, 1n+b)',
            'hunks.walk(rest, Bool.pick(Nat, String.eq(sign, "-"), b, 1n+b)',
            "hunk_lemmas.walk_ok",
            "main.bend",
        ),
        (
            "a hunk holding no line of a side names its first line anyway",
            '  Bool.pick(Nat, Nat.is_eq(count, 0n), 0n, first)',
            '  first',
            "hunk_lemmas.from_nz",
            "main.bend",
        ),
        (
            "diff shows a change only where another is near",
            '  Bool.or(changed, Bool.or(Nat.is_gt(owed, 0n), near))',
            '  Bool.or(Nat.is_gt(owed, 0n), near)',
            "hunk_lemmas.walk_cons",
            "main.bend",
        ),
        (
            "emphasis compares each removal with its arrival the wrong way round",
            '      apart(numbered.shown(r), numbered.shown(a)) <> pairs(rs, more)',
            '      apart(numbered.shown(a), numbered.shown(r)) <> pairs(rs, more)',
            "mark_lemmas.was_fit",
            "main.bend",
        ),
        (
            "emphasis marks the arrivals before the removals",
            'List.append(&2, Maybe<&2, List<&2, Piece>>, marks.was(ps), marks.now(ps))',
            'List.append(&2, Maybe<&2, List<&2, Piece>>, marks.now(ps), marks.was(ps))',
            "mark_lemmas.pair_fit",
            "main.bend",
        ),
        (
            "emphasis gives a context line no mark",
            '      Chunked{[None{}], rest}',
            '      Chunked{Nil{}, rest}',
            "mark_lemmas.step_fit",
            "main.bend",
        ),
        (
            "diff walks the two sides comparing their files the wrong way round",
            '      String.order(Tree.entry_file(x), Tree.entry_file(y))\n    case Nil{} _:\n      GT{}',
            '      String.order(Tree.entry_file(y), Tree.entry_file(x))\n    case Nil{} _:\n      GT{}',
            "pair_lemmas.join",
            "main.bend",
        ),
        (
            "diff drops a file only the parent holds",
            '      Both{Tree.entry_file(x), Some{x}, None{}} <> both.go(f, xr, ys2, both.cmp(xr, ys2))',
            '      both.go(f, xr, ys2, both.cmp(xr, ys2))',
            "pair_lemmas.join",
            "main.bend",
        ),
        (
            "diff sorts the child's files backwards",
            '  +ys2 = List.sort(~Tree.Entry, ~(a => b => String.is_le(Tree.entry_file(a), Tree.entry_file(b))), ys)',
            '  +ys2 = List.sort(~Tree.Entry, ~(a => b => String.is_le(Tree.entry_file(b), Tree.entry_file(a))), ys)',
            "pair_lemmas.pairs_by_file",
            "main.bend",
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
