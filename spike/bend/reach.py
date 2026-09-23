#!/usr/bin/env python3
"""How much of what the tool runs a law reaches.

`main.bend` runs some defs; `LAWS.bend` states claims about some. This
reads every `.bend` file here, follows each def to the defs it names —
through the module aliases each file imports — and reports, per file, the
lines the tool can run and how many of them some law's statement reaches.

"Reached" is generous on purpose: a def a law names, or one those name, is
counted, whether the law pins it down or only mentions it in a hypothesis.
What this reports as unreached is certain; what it reports as reached is a
place to look, not a proof. It is the number to push down, not the claim.

    python3 reach.py            # the summary, per file
    python3 reach.py --unproven # and every unreached def the tool runs
"""

import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
TOP = re.compile(r"^(def|law|type|import)\b")
DEF = re.compile(r"^def\s+([A-Za-z_][\w.]*)\s*\(")
LAW = re.compile(r"^law\s+([A-Za-z_]\w*)\s*:")
IMPORT = re.compile(r"^import\s+\./([\w]+)\.bend\s+as\s+(\w+)")
WORD = re.compile(r"[A-Za-z_][\w.]*")


def blocks(path):
    """Each top-level declaration: its first line, its line count, its text."""
    lines = path.read_text().splitlines()
    starts = [i for i, line in enumerate(lines) if TOP.match(line)] + [len(lines)]
    for a, b in zip(starts, starts[1:]):
        body = lines[a:b]
        # Trailing comments and blanks belong to the next declaration.
        while body and (not body[-1].strip() or body[-1].startswith("#")):
            body.pop()
        yield lines[a], len(body), "\n".join(line.split("#", 1)[0] for line in body)


def read():
    defs, sizes, laws = {}, {}, {}
    for path in sorted(HERE.glob("*.bend")):
        module = path.stem
        aliases = {}
        for first, _, _ in blocks(path):
            m = IMPORT.match(first)
            if m:
                aliases[m.group(2)] = m.group(1)
        for first, size, text in blocks(path):
            d, l = DEF.match(first), LAW.match(first)
            if d and module != "PROOF":
                defs[(module, d.group(1))] = (text, aliases)
                sizes[(module, d.group(1))] = size
            elif l and module == "LAWS":
                laws[l.group(1)] = (text, aliases)
    return defs, sizes, laws


BINDER = re.compile(r"[+\-@]?([A-Za-z_]\w*)\s*:(?!\s*$)")


def bound(text):
    """The plain names a declaration binds: its parameters and quantified
    variables, what its patterns and lambdas bind, and its `do` lets. They
    shadow a def of the same name, so a use of one is not a reference."""
    names = set()
    for line in text.splitlines():
        stripped = line.strip()
        if stripped.startswith("case "):
            names.update(WORD.findall(stripped[5:]))
        for m in re.finditer(r"([A-Za-z_]\w*)\s*=>", line):
            names.add(m.group(1))
        m = re.match(r"\s*[+\-]?([A-Za-z_]\w*)\s*:.*(<-|=)", line)
        if m and not stripped.startswith(("def ", "law ")):
            names.add(m.group(1))
        m = re.match(r"\s*for\s+[+\-]?([A-Za-z_]\w*)\s*:", line)
        if m:
            names.add(m.group(1))
    first = text.splitlines()[0] if text else ""
    if first.startswith("def "):
        signature = first[first.index("(") + 1:]
        names.update(m.group(1) for m in BINDER.finditer(signature))
    return names


def named(text, aliases, module, defs):
    """The defs a piece of text names, from inside `module`."""
    shadowed = bound(text)
    for word in set(WORD.findall(text)):
        if word in shadowed:
            continue
        head, _, rest = word.partition(".")
        if head in aliases and rest:
            key = (aliases[head], rest)
        else:
            key = (module, word)
        if key in defs:
            yield key


def closure(roots, defs):
    seen, todo = set(), list(roots)
    while todo:
        key = todo.pop()
        if key in seen:
            continue
        seen.add(key)
        text, aliases = defs[key]
        todo.extend(named(text, aliases, key[0], defs))
    return seen


def main():
    defs, sizes, laws = read()
    run = closure([("main", "main")], defs)
    roots = [k for text, aliases in laws.values() for k in named(text, aliases, "LAWS", defs)]
    lawful = closure(roots, defs)

    files = {}
    for key in run:
        total, reached = files.get(key[0], (0, 0))
        files[key[0]] = (total + sizes[key], reached + (sizes[key] if key in lawful else 0))
    width = max(map(len, files))
    print(f"{'file':<{width}}  {'runs':>6}  {'reached':>7}")
    for module, (total, reached) in sorted(files.items(), key=lambda kv: kv[1][1] - kv[1][0]):
        print(f"{module:<{width}}  {total:>6}  {reached:>7}  {100 * reached // total:>3}%")
    total = sum(t for t, _ in files.values())
    reached = sum(r for _, r in files.values())
    print(f"{'all':<{width}}  {total:>6}  {reached:>7}  {100 * reached // total:>3}%")
    print(f"reach: {reached} of the {total} lines the tool runs are reached by a law ({len(laws)} laws)")

    if "--unproven" in sys.argv:
        for key in sorted(run - lawful):
            print(f"  {key[0]}.bend  {key[1]}  ({sizes[key]} lines)")


if __name__ == "__main__":
    main()
