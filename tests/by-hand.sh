#!/bin/sh
# Decision 0032's tool-less merge, carried out.
#
# Nothing in this script is Historica. Every file it writes is typed out, and
# every digest it needs comes from a checksum program. What it builds is a
# store with a merge in it — the thing nobody could write by hand before 0032,
# because the only spelling of a resolution was a delta positioned into a
# state no editor can compute.
#
# What it produces is `tests/corpus/merged/`, byte for byte. The corpus is not
# a fixture somebody generated: it is what these commands print.
#
# Run it as `sh tests/by-hand.sh <directory>`.
set -eu

if command -v shasum > /dev/null 2>&1; then
	sum() { shasum -a 256 "$1" | cut -d' ' -f1; }
elif command -v sha256sum > /dev/null 2>&1; then
	sum() { sha256sum "$1" | cut -d' ' -f1; }
else
	echo "no checksum program: install shasum or sha256sum" >&2
	exit 1
fi

store="${1:?usage: by-hand.sh <directory>}"
mkdir -p "$store/revisions" "$store/operations" "$store/names" "$store/cache"
scratch="$store/../by-hand"
mkdir -p "$scratch"

# The first line is the format, and the rest of that file is a note for
# whoever opens the folder. A store with only the first line is a store.
printf 'historica\n' > "$store/historica.txt"

# Two file identifiers, 24 characters from `k` to `z`. A person makes these up;
# nothing derives them, and nothing but their spelling makes them identifiers.
notes=nrqvtkzlmwyxsptonvqrklmz
readme=swtlmnkqvzyrxopwstlnmkqv

# ---------------------------------------------------------------------------
# The root. Two files, each arriving as its payload: the file itself, stored
# whole, named by the digest of its own bytes. A payload's lines are items
# 0, 1, 2, ... in file order, which is what a `keep` later counts into.
# ---------------------------------------------------------------------------

printf 'alpha\nbravo\ncharlie\n' > "$store/operations/01-notes.txt"
printf '# Notes\n\nA journal kept in Historica.\n' > "$store/operations/01-readme.md"

cat > "$store/revisions/01-root.rev.txt" <<EOF
historica
change qpvuntsmwlrkzxonmvtplsyq
author Adam Harris <adam@example.com>
when 2026-08-19T09:12:04-06:00
add $notes notes.txt
add $readme README.md
text $notes $(sum "$store/operations/01-notes.txt")
text $readme $(sum "$store/operations/01-readme.md")

Start the notes both hands will edit
EOF
root=$(sum "$store/revisions/01-root.rev.txt")

# ---------------------------------------------------------------------------
# Two hands on the root, neither having seen the other. Positions count into
# the state at the parent, which is `01-root.txt` above, and never move.
# ---------------------------------------------------------------------------

printf 'alpha\ndelta\nbravo\ncharlie\n' > "$scratch/02-left.txt"
cat > "$store/operations/02-notes.ops.txt" <<EOF
historica
result $(sum "$scratch/02-left.txt")

insert 1
+delta
EOF

cat > "$store/revisions/02-left.rev.txt" <<EOF
historica
change kxryzmornsvltwqpuzkymxol
parent $root
author Adam Harris <adam@example.com>
when 2026-08-19T10:41:18-06:00
edit $notes $(sum "$store/operations/02-notes.ops.txt")

Add a line between the first two
EOF
left=$(sum "$store/revisions/02-left.rev.txt")

printf 'alpha\nbravo\necho\n' > "$scratch/03-right.txt"
cat > "$store/operations/03-notes.ops.txt" <<EOF
historica
result $(sum "$scratch/03-right.txt")

delete 2 1
-charlie
insert 3
+echo
EOF

cat > "$store/revisions/03-right.rev.txt" <<EOF
historica
change mzvwutklopqrsnyxwkltvmzu
parent $root
author Rowan Ash <rowan@example.com>
when 2026-08-19T10:55:02-06:00
edit $notes $(sum "$store/operations/03-notes.ops.txt")

Replace the last line, without seeing the other branch
EOF
right=$(sum "$store/revisions/03-right.rev.txt")

# ---------------------------------------------------------------------------
# The merge. This is the part 0032 made possible.
#
# The person opens both branches, decides the file should read
# alpha/delta/bravo/foxtrot/echo, and writes that down as a sequence of
# references and one insertion. Each `keep` counts into a document they have
# open: the payload `01-notes.txt` mints alpha, bravo, charlie as items
# 0, 1, 2 — count the lines — `02-notes.ops.txt` mints delta as item 0, and
# `03-notes.ops.txt` mints echo as item 0.
#
# Nothing here needs the merge algorithm. Nothing here even needs to know what
# the algorithm would have said.
# ---------------------------------------------------------------------------

printf 'alpha\ndelta\nbravo\nfoxtrot\necho\n' > "$scratch/04-merge.txt"
cat > "$store/operations/04-notes.ops.txt" <<EOF
historica
result $(sum "$scratch/04-merge.txt")

keep $(sum "$store/operations/01-notes.txt") 0 1
keep $(sum "$store/operations/02-notes.ops.txt") 0 1
keep $(sum "$store/operations/01-notes.txt") 1 1
insert
+foxtrot
keep $(sum "$store/operations/03-notes.ops.txt") 0 1
EOF

# Repeated headers are sorted by the value after them, so the two parents go
# in digest order whichever branch the person thinks of as theirs.
parents=$(printf 'parent %s\nparent %s\n' "$left" "$right" | sort)
cat > "$store/revisions/04-merge.rev.txt" <<EOF
historica
change nwlxsqotvkzmuprysltnwxqk
$parents
author Adam Harris <adam@example.com>
when 2026-08-19T17:20:39-06:00
edit $notes $(sum "$store/operations/04-notes.ops.txt")

Read both sides and say what the file is

README.md is not mentioned: both parents leave it exactly as the root wrote
it, so there is nothing to resolve and the file is that agreed state.
EOF
merge=$(sum "$store/revisions/04-merge.rev.txt")

# ---------------------------------------------------------------------------
# And carrying on from the merge, which is the other half of what a resolution
# buys: positions here count into the file the merge *stated*, so writing this
# revision needed nothing but `04-merge.txt` and an editor.
# ---------------------------------------------------------------------------

printf 'alpha\ndelta\nbravo\necho\ngolf\n' > "$scratch/05-after.txt"
cat > "$store/operations/05-notes.ops.txt" <<EOF
historica
result $(sum "$scratch/05-after.txt")

delete 3 1
-foxtrot
insert 5
+golf
EOF

cat > "$store/revisions/05-after.rev.txt" <<EOF
historica
change lyqrxwnkmtvzsoplyqrxwnkm
parent $merge
author Adam Harris <adam@example.com>
when 2026-08-20T08:03:55-06:00
edit $notes $(sum "$store/operations/05-notes.ops.txt")

Carry on from the merge, counting into the file it stated
EOF

rm -rf "$scratch"
