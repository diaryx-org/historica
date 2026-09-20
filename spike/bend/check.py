#!/usr/bin/env python3
"""Check proofs, run JS/native corpora, and ensure replay mutations are rejected."""
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
# A Nix profile (or another package manager) can update while a gate runs.
# Resolve once so the printed version identifies every check in this run.
BEND = shutil.which("bend")
if BEND is None:
    raise SystemExit("bend is required on PATH")
BEND = str(Path(BEND).resolve())


def run(*args, cwd=ROOT, timeout=120):
    print("+", " ".join(map(str, args)), flush=True)
    subprocess.run(args, cwd=cwd, check=True, timeout=timeout)


def main():
    run(BEND, "version")
    run(BEND, "PROOF.bend")
    with tempfile.TemporaryDirectory(prefix="historica-bend-") as directory:
        temporary = Path(directory)
        for suite in ("corpus_ops", "corpus_rev", "replay_tests"):
            run(BEND, f"{suite}.bend")
            executable = temporary / suite
            run(BEND, f"{suite}.bend", "-o", str(executable), timeout=600)
            run(str(executable))

        check_mutations(temporary)


def check_mutations(temporary):
    # Separate copies: the checkout is never temporarily broken. Require
    # a type-check failure in the expected proof, not a parse/tool error.
    mutations = (
        (
            "forgetting ignores newline",
            "Bool.and(Bool.not(Bool.xor(n1, n2)), Bool.or(Bool.or(f1, f2), String.eq(t1, t2)))",
            "Bool.or(Bool.or(f1, f2), Bool.and(String.eq(t1, t2), Bool.not(Bool.xor(n1, n2))))",
            "LAWS.forgotten_agrees",
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
            "apply.checked(result, items)\n\n# Diff",
            "apply.checked(None{}, items)\n\n# Diff",
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
            "semantic_replay.bend",
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
            "    case Replacement{recorded, inserted}:\n      List.length(&2, Ops.Item, recorded)",
            "    case Replacement{recorded, inserted}:\n      0n",
            "composition_lemmas.result_block",
            "semantic_replay.bend",
        ),
        (
            "ordering admits an insert inside a deleted run",
            "Bool.and(Nat.is_le(stop, at2), ordered(more, at2))",
            "ordered(more, at2)",
            "composition_lemmas.is_script",
            "semantic_replay.bend",
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
