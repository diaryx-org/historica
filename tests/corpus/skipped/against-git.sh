#!/bin/sh
# Decision 0087's corpus, checked against git.
#
# Nothing in this script is Historica. Each case in `cases.txt` is written as
# the `.gitignore` that means what the rule means, and `git check-ignore` gives
# each path's verdict. A case whose verdict is not git's is printed, and the
# script fails. That is what makes the corpus git's answers and not ours.
#
# A file rule `skip-glob P` is `/P` and `!/P/`: git's pattern matches a
# directory too, and the second line gives directories back. A directory rule
# `skip-glob P/` is `/P/`. An `except E` is `!/E`. The leading `/` anchors, as
# every glob is anchored, and makes a `#` or `!` at the value's start ordinary.
#
# Run it as `sh tests/corpus/skipped/against-git.sh`.
set -eu

here=$(cd "$(dirname "$0")" && pwd)
work=$(mktemp -d "${TMPDIR:-/tmp}/historica-skipped-XXXXXX")
trap 'rm -rf "$work"' EXIT
git init -q "$work/repo"
ignore="$work/repo/.gitignore"
expected="$work/expected"
: > "$ignore"
: > "$expected"
cases=0
failed=0

check() {
	[ -s "$ignore" ] || return 0
	cases=$((cases + 1))
	while IFS= read -r line; do
		verdict=${line%% *}
		path=${line#* }
		if git -C "$work/repo" check-ignore -q --no-index -- "$path"; then
			got=+
		else
			got=-
		fi
		if [ "$got" != "$verdict" ]; then
			failed=$((failed + 1))
			printf 'git says %s for "%s" under:\n' "$got" "$path"
			sed 's/^/    /' "$ignore"
		fi
	done < "$expected"
	: > "$ignore"
	: > "$expected"
}

while IFS= read -r line || [ -n "$line" ]; do
	case $line in
	'#'*) ;;
	'') check ;;
	'+ '* | '- '*) printf '%s\n' "$line" >> "$expected" ;;
	skip-glob\ * | private-glob\ *)
		value=${line#* }
		case $value in
		*/) printf '/%s\n' "$value" >> "$ignore" ;;
		*) printf '/%s\n!/%s/\n' "$value" "$value" >> "$ignore" ;;
		esac
		;;
	except\ *) printf '!/%s\n' "${line#except }" >> "$ignore" ;;
	*)
		printf 'not a line of a case: %s\n' "$line" >&2
		exit 2
		;;
	esac
done < "$here/cases.txt"
check

if [ "$failed" -ne 0 ]; then
	printf '%s verdicts of %s cases are not git'"'"'s\n' "$failed" "$cases" >&2
	exit 1
fi
printf 'git agrees with all %s cases\n' "$cases"
