"""Write `nfc_tables.bend`: what `nfc.bend` normalises paths with.

Unicode normal form C is decomposition, reordering by combining class, and
composition, and every step asks a table: a character's canonical combining
class, its full canonical decomposition, and which pairs compose. The Rust
tool asks the `unicode-normalization` crate its `Cargo.lock` resolves, so the
port takes its tables from that crate rather than from Python's
`unicodedata`, which is whatever Unicode the interpreter was built with:
`ffi/examples/nfc_tables.rs` asks the crate about every scalar value, and
this writes what it answers as Bend. `check.py`'s `nfc` stage holds
`nfc.bend` to the crate on a large sample, so tables that drifted from it
fail there; run this to take them up again:

    python3 nfc.py
"""
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent
FFI = ROOT / "ffi"
EXAMPLE = FFI / "target" / "release" / "examples" / "nfc_tables"
# Five triples to a line, so that no run or pair is cut between two.
PER_LINE = 15


def dump():
    """The crate's answers, as `nfc_tables tables` prints them."""
    subprocess.run(["cargo", "build", "-q", "--release", "--example", "nfc_tables"], cwd=FFI, check=True)
    text = subprocess.run([str(EXAMPLE), "tables"], check=True, capture_output=True, text=True).stdout
    classes, decompositions, pairs, version = {}, {}, [], None
    for line in text.splitlines():
        kind, *fields = line.split()
        if kind == "u":
            version = fields[0]
            continue
        numbers = [int(f, 16) for f in fields]
        if kind == "c":
            classes[numbers[0]] = numbers[1]
        elif kind == "d":
            decompositions[numbers[0]] = numbers[1:]
        elif kind == "p":
            pairs.append(tuple(numbers))
    return classes, decompositions, pairs, version


def runs(classes):
    """Each run of consecutive code points sharing one class: first, last, class."""
    out = []
    for c in sorted(classes):
        if out and out[-1][1] == c - 1 and out[-1][2] == classes[c]:
            out[-1][1] = c
        else:
            out.append([c, c, classes[c]])
    return out


def numbers(values, indent="    "):
    values = list(values)
    lines = []
    for i in range(0, len(values), PER_LINE):
        chunk = ", ".join(str(v) for v in values[i:i + PER_LINE])
        lines.append(indent + chunk + ("," if i + PER_LINE < len(values) else ""))
    return lines


def entries(items, indent="   "):
    lines, line = [], indent
    for i, item in enumerate(items):
        piece = " " + item + ("," if i + 1 < len(items) else "")
        if len(line) + len(piece) > 100:
            lines.append(line)
            line = indent
        line += piece
    return lines + [line]


# A list literal is as deep as it is long in the JavaScript Bend emits, and
# the JavaScript engine gives up on one past a couple of thousand; so a
# table is written in parts of at most this many elements, joined by
# `List.append` when it is read.
PART = 900


def table(name, kind, element, items, render):
    """`def name() -> kind`, from parts no longer than `PART` elements."""
    parts = [items[i:i + PART] for i in range(0, len(items), PART)]
    out = []
    for k, part in enumerate(parts):
        out += [f"def {name}.{k}() -> {kind}:", "  [", *render(part), "  ]", ""]
    joined = f"{name}.{len(parts) - 1}()"
    for k in reversed(range(len(parts) - 1)):
        joined = f"List.append(&2, {element}, {name}.{k}(), {joined})"
    return out + [f"def {name}() -> {kind}:", f"  {joined}"]


def main():
    classes, decompositions, pairs, version = dump()
    full = lambda c: decompositions.get(c, [c])
    # What the tables have to be for `nfc.bend` to read them as it does: a
    # composite decomposes to what its two halves decompose to, which is
    # what makes decomposing then composing a round trip; and the pairs are
    # in order, as the lookup stops at the first past what it wants.
    for a, b, x in pairs:
        assert full(x) == full(a) + full(b), (hex(a), hex(b), hex(x))
    assert pairs == sorted(pairs) and len({(a, b) for a, b, _ in pairs}) == len(pairs)
    # Below the first code point that has a class, is the second of a pair,
    # or decomposes to something composition does not put back, a string is
    # its own normal form: `nfc.bend`'s quick check, as the crate's is.
    seconds = {b for _, b, _ in pairs}
    composites = {x for _, _, x in pairs}
    bound = 0
    while not (classes.get(bound, 0) or bound in seconds or (bound in decompositions and bound not in composites)):
        bound += 1
    # The ASCII characters another character decomposes to alone: a path of
    # ASCII without them has no spelling but itself.
    images = sorted({d[0] for c, d in decompositions.items() if c >= 128 and all(x < 128 for x in d) and len(d) == 1})
    assert all(len(d) == 1 for c, d in decompositions.items() if c >= 128 and all(x < 128 for x in d))

    out = [
        f"# The tables `nfc.bend` reads, as `unicode-normalization` 0.1.25 states",
        f"# them for Unicode {version}: written by `nfc.py` from what",
        "# `ffi/examples/nfc_tables.rs` asks the crate of every scalar value, and",
        "# held to the crate by `check.py`'s `nfc` stage. Hangul syllables are in",
        "# none of them; `nfc.bend` does their arithmetic.",
        "",
        "import Base",
        "",
        "# The Unicode version the crate normalises by.",
        "def version() -> String:",
        f'  "{version}"',
        "",
        "# Below this code point every character is its own normal form, and has",
        "# no class, no decomposition composition does not undo, and no place as",
        "# the second of a pair: so is every string of them.",
        "def inert_below() -> U32:",
        f"  {bound}",
        "",
        "# The ASCII characters some other character decomposes to alone.",
        "def ascii_images() -> List<&2, U32>:",
        f"  [{', '.join(str(i) for i in images)}]",
        "",
        "# Each run of consecutive code points with one canonical combining class",
        "# other than 0 — first, last, class — in order.",
        *table("classes", "List<&2, U32>", "U32", [v for r in runs(classes) for v in r], numbers),
        "",
        "# Each character whose full canonical decomposition is not itself, and",
        "# what it decomposes to: the character first, in order of it.",
        *table("decompositions", "List<&2, List<&2, U32>>", "List<&2, U32>",
               [f"[{c}, {', '.join(str(d) for d in ds)}]" for c, ds in sorted(decompositions.items())], entries),
        "",
        "# Each pair canonical composition joins — first, second, and what they",
        "# make — in order of the first and then the second.",
        *table("pairs", "List<&2, U32>", "U32", [v for p in pairs for v in p], numbers),
    ]
    (ROOT / "nfc_tables.bend").write_text("\n".join(out) + "\n")
    print(f"nfc_tables.bend: Unicode {version}, {len(runs(classes))} class runs, {len(decompositions)} decompositions, {len(pairs)} pairs")


if __name__ == "__main__":
    main()
