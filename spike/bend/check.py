#!/usr/bin/env python3
"""Check proofs, run JS/native corpora, ensure replay mutations are rejected,
and hold the store commands to the Rust tool's output."""
from pathlib import Path
import os
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parent.parent
CORPUS = REPO / "tests" / "corpus"
# A Nix profile (or another package manager) can update while a gate runs.
# Resolve once so the printed version identifies every check in this run.
BEND = shutil.which("bend")
if BEND is None:
    raise SystemExit("bend is required on PATH")
BEND = str(Path(BEND).resolve())


def run(*args, cwd=ROOT, timeout=120):
    print("+", " ".join(map(str, args)), flush=True)
    subprocess.run(args, cwd=cwd, check=True, timeout=timeout)


def capture(*args, cwd):
    """A command's stdout, stderr and exit code, for comparing two tools."""
    done = subprocess.run(args, cwd=cwd, capture_output=True, timeout=120)
    return done.stdout, done.stderr, done.returncode


def main():
    run(BEND, "version")
    run(BEND, "PROOF.bend")
    with tempfile.TemporaryDirectory(prefix="historica-bend-") as directory:
        temporary = Path(directory)
        for suite in ("corpus_ops", "corpus_rev", "corpus_tree", "replay_tests"):
            run(BEND, f"{suite}.bend")
            executable = temporary / suite
            run(BEND, f"{suite}.bend", "-o", str(executable), timeout=600)
            run(str(executable))

        check_mutations(temporary)
        check_store(temporary)


# The store commands
# ------------------

# `main.bend`'s `log`, `files`, `cat` and `show` are held to the Rust tool,
# byte for byte, on stores assembled from the corpora: each corpus's
# `revisions/` and `operations/` under a `history/` with the header file the
# tool looks for. What is compared is the native binary, linked against the
# Rust archive in `ffi/`, and the `.js` build, which runs the adapter's JS
# twins — so a twin that drifts from its C side fails here.
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
    ],
    "modes": [["log"], ["files", "head"]],
    "whole": [["log"], ["files", "head"], ["cat", "head", "notes/2026-08-20.md"]],
    # Recorded here by the Rust tool rather than taken from a corpus: the
    # widest path holds characters outside ASCII, which the Rust tool
    # measures in bytes and pads in characters.
    "unicode": [["files", "head"], ["cat", "head", "café/naïve résumé.md"]],
}


def record(temporary, rust):
    store = temporary / "store-unicode"
    (store / "café").mkdir(parents=True)
    (store / "café" / "naïve résumé.md").write_text("an accent\n")
    (store / "notes.md").write_text("plain\n")
    home = temporary / "home"
    env = {**os.environ, "HOME": str(home), "XDG_CONFIG_HOME": str(home / ".config")}
    for command in (["init", "."], ["identity", "Check <check@example.com>"], ["record", "-m", "one"]):
        subprocess.run([rust, *command], cwd=store, env=env, check=True, capture_output=True, timeout=120)
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
    # repeated calls — then the archive the program links.
    run("cargo", "test", "-q", "--release", cwd=ROOT / "ffi", timeout=600)
    run("cargo", "build", "-q", "--release", cwd=ROOT / "ffi", timeout=600)
    source = temporary / "main.c"
    native = temporary / "main"
    run(BEND, "main.bend", "-o", str(source), timeout=600)
    # `bend -o` links nothing of ours, so the C is compiled here; `-w` because
    # the generated program is not ours to lint.
    run(
        os.environ.get("CC", "cc"), "-O3", "-w", "-o", str(native), str(source),
        str(archive), "-lm", "-lpthread", timeout=900,
    )
    script = temporary / "main.js"
    run(BEND, "main.bend", "-o", str(script), timeout=600)

    failures = 0
    for corpus, commands in STORES.items():
        store = record(temporary, rust) if corpus == "unicode" else assemble(temporary, corpus)
        for command in commands:
            expected = capture(rust, *command, cwd=store)
            for name, tool in (("native", [str(native)]), ("js", ["bun", str(script)])):
                got = capture(*tool, *command, cwd=store)
                if got != expected:
                    failures += 1
                    print(f"DIFF {corpus} {name}: {' '.join(command)}")
                    print("  rust:", expected)
                    print("  bend:", got)
                else:
                    print(f"same {corpus} {name}: {' '.join(command)}")
    if failures:
        sys.exit(f"{failures} store commands differ from the Rust tool")


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
    )
    for index, (name, before, after, proof, *source_files) in enumerate(mutations):
        mutant = temporary / f"mutation-{index}"
        shutil.copytree(ROOT, mutant)
        source = mutant / (source_files[0] if source_files else "ops.bend")
        original = source.read_text()
        assert original.count(before) == 1, name
        source.write_text(original.replace(before, after))
        checked = subprocess.run(
            [BEND, "PROOF.bend"], cwd=mutant,
            capture_output=True, text=True, timeout=120,
        )
        diagnostic = checked.stdout + checked.stderr
        if checked.returncode == 0 or proof not in diagnostic or "expected" not in diagnostic:
            raise RuntimeError(f"Mutation did not fail in {proof}: {name}\n{diagnostic}")
        print(f"ok    proof rejects: {name}", flush=True)
        if index == 0:
            regression = subprocess.run(
                [BEND, "replay_tests.bend"], cwd=mutant,
                capture_output=True, text=True, timeout=120,
            )
            diagnostic = regression.stdout + regression.stderr
            if regression.returncode == 0 or "forgotten quote preserves newline" not in diagnostic:
                raise RuntimeError(f"Original newline bug escaped the regression test:\n{diagnostic}")
            print("ok    replay regression rejects the original newline bug", flush=True)


if __name__ == "__main__":
    main()
