#!/usr/bin/env bash
# Type-check one Lean file against the workspace environment without touching the shared build dir.
# Usage: ./check.sh Solutions/Sol_Foo.lean   (prints errors/warnings; exit 0 iff no errors)
set -u
export PATH="$HOME/.elan/bin:$PATH"
cd "$(dirname "$0")"
f="$1"
out=$(lake env lean "$f" 2>&1); rc=$?
echo "$out"
if [ $rc -ne 0 ] || echo "$out" | grep -q -E '^[^:]+:[0-9]+:[0-9]+: error'; then echo "CHECK FAILED: $f"; exit 1; fi
if grep -q -E '\bsorry\b' "$f"; then echo "CHECK FAILED: file contains sorry"; exit 1; fi
echo "CHECK OK: $f"
