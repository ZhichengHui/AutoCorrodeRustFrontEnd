#!/usr/bin/env bash
# Translate every test case in tests/cases/*.rs and check the generated theories with Isabelle.
#
#   scripts/run_tests.sh [CASE...]       (default: all cases)
#
# Environment:
#   AUTOCORRODE   AutoCorrode checkout providing the session "AutoCorrode"
#                 (default: the merged signed-integers + break/continue worktree)
#   ISABELLE      isabelle executable (default: ~/Applications/Isabelle2025-2/bin/isabelle)
#   MEMORY_MAX    memory cap for the Isabelle build (default 4G)
#   NO_ISABELLE=1 only run the translation
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
AUTOCORRODE=${AUTOCORRODE:-$HOME/Work/AutoCorrode/.claude/worktrees/frontend-base}
ISABELLE=${ISABELLE:-$HOME/Applications/Isabelle2025-2/bin/isabelle}
MEMORY_MAX=${MEMORY_MAX:-4G}
OUT="$HERE/out"
mkdir -p "$OUT"

cases=("$@")
if [ ${#cases[@]} -eq 0 ]; then
  for f in "$HERE"/tests/cases/*.rs; do cases+=("$(basename "$f" .rs)"); done
fi

theories=()
fail_translate=()
for c in "${cases[@]}"; do
  name="$(echo "$c" | sed -E 's/^(.)/\U\1/')"
  rm -rf "$OUT/$c"
  if "$HERE/scripts/urust-frontend.sh" --out "$OUT/$c" --name "$name" "$HERE/tests/cases/$c.rs" \
       > "$OUT/$c.translate.log" 2>&1; then
    theories+=("\"$c/${name}_Funs\"")
    echo "translated $c ($(head -1 "$OUT/$c/PLACEHOLDERS.txt" | sed 's/.*: //') placeholders)"
  else
    fail_translate+=("$c")
    echo "TRANSLATION FAILED: $c (see out/$c.translate.log)"
  fi
done

[ "${NO_ISABELLE:-0}" = 1 ] && exit 0

{
  echo "session Frontend_Tests = AutoCorrode +"
  echo "  options [document = false, timeout = 3600]"
  echo "  theories"
  for t in "${theories[@]}"; do echo "    $t"; done
} > "$OUT/ROOT"

echo "checking ${#theories[@]} crates with Isabelle (memory cap $MEMORY_MAX) ..."
systemd-run --user --scope -q -p MemoryMax="$MEMORY_MAX" -p MemorySwapMax=0 \
  "$ISABELLE" build -o threads=2 -d "$AUTOCORRODE" -d "$OUT" -v Frontend_Tests > "$OUT/isabelle.log" 2>&1
rc=$?
grep -E "^\*\*\*|FAILED|Finished|elapsed" "$OUT/isabelle.log" | head -80
"$ISABELLE" build_log -H Error Frontend_Tests > "$OUT/isabelle_errors.log" 2>&1 || true
echo "isabelle exit code: $rc"
exit $rc
