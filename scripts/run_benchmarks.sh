#!/usr/bin/env bash
# Translate a benchmark suite (tests/benchmarks/SUITE/*.rs, one crate per file) and check
# every translated crate with Isabelle in one session; write out/bench/SUITE/SUMMARY.md.
#
#   scripts/run_benchmarks.sh SUITE [FILE.rs...]
#
# Environment: AUTOCORRODE, ISABELLE, MEMORY_MAX, NO_ISABELLE as for run_tests.sh.
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
AUTOCORRODE=${AUTOCORRODE:-$HOME/Work/AutoCorrode/.claude/worktrees/frontend-base}
ISABELLE=${ISABELLE:-$HOME/Applications/Isabelle2025-2/bin/isabelle}
MEMORY_MAX=${MEMORY_MAX:-4G}
SUITE=$1; shift
SRC="$HERE/tests/benchmarks/$SUITE"
OUT="$HERE/out/bench/$SUITE"
mkdir -p "$OUT"

case "$SUITE" in
  aeneas) TAG=Ae ;;
  humaneval_x) TAG=He ;;
  *) TAG=Bm ;;
esac

# rustc arguments for one file: Aeneas tests use the tool attributes #[charon::..] / #[aeneas::..]
rustc_args() {
  local f=$1 edition=$2
  RUSTC_ARGS=(--edition="$edition")
  if [ "$SUITE" = aeneas ]; then
    grep -q 'feature(.*register_tool' "$f" || RUSTC_ARGS+=(-Zcrate-attr=feature\(register_tool\))
    grep -q 'register_tool(charon' "$f" || RUSTC_ARGS+=(-Zcrate-attr=register_tool\(charon\))
    grep -q 'register_tool(.*aeneas' "$f" || RUSTC_ARGS+=(-Zcrate-attr=register_tool\(aeneas\))
  fi
}

files=("$@")
if [ ${#files[@]} -eq 0 ]; then files=("$SRC"/*.rs); fi

status="$OUT/status.tsv"
: > "$status"
theories=()
dirs=()
for f in "${files[@]}"; do
  stem="$(basename "$f" .rs | tr -c 'A-Za-z0-9_\n' '_')"
  name="${TAG}_${stem}"
  rm -rf "$OUT/$stem"
  log="$OUT/$stem.translate.log"
  rustc_args "$f" 2021
  "$HERE/scripts/urust-frontend.sh" --out "$OUT/$stem" --name "$name" "$f" -- "${RUSTC_ARGS[@]}" > "$log" 2>&1
  if grep -q "only allowed in Rust 2024\|edition 2024 or later" "$log"; then
    rustc_args "$f" 2024
    "$HERE/scripts/urust-frontend.sh" --out "$OUT/$stem" --name "$name" "$f" -- "${RUSTC_ARGS[@]}" > "$log" 2>&1
  fi
  if [ -f "$OUT/$stem/${name}_Funs.thy" ]; then
    ph="$(head -1 "$OUT/$stem/PLACEHOLDERS.txt" | sed 's/.*: //')"
    printf '%s\t%s\ttranslated\t%s\n' "$stem" "$name" "$ph" >> "$status"
    theories+=("\"$stem/${name}_Funs\"")
    dirs+=("\"$stem\"")
  elif grep -q "panicked at\|internal compiler error" "$log"; then
    printf '%s\t%s\tfrontend-crash\t-\n' "$stem" "$name" >> "$status"
  else
    printf '%s\t%s\trustc-rejected\t-\n' "$stem" "$name" >> "$status"
  fi
done
echo "translation: $(cut -f3 "$status" | sort | uniq -c | tr '\n' ' ')"

if [ "${NO_ISABELLE:-0}" != 1 ] && [ ${#theories[@]} -gt 0 ]; then
  session="Bench_${SUITE}"
  {
    echo "session $session = AutoCorrode +"
    echo "  options [document = false, timeout = 7200]"
    echo "  directories"
    for d in "${dirs[@]}"; do echo "    $d"; done
    echo "  theories"
    for t in "${theories[@]}"; do echo "    $t"; done
  } > "$OUT/ROOT"
  echo "checking ${#theories[@]} crates with Isabelle (memory cap $MEMORY_MAX) ..."
  systemd-run --user --scope -q -p MemoryMax="$MEMORY_MAX" -p MemorySwapMax=0 \
    "$ISABELLE" build -o threads=2 -d "$AUTOCORRODE" -d "$OUT" -v "$session" > "$OUT/isabelle.log" 2>&1
  rc=$?
  echo "$rc" > "$OUT/isabelle.rc"
  echo "isabelle exit code: $rc"
  "$ISABELLE" build_log -H Error "$session" > "$OUT/isabelle_errors.log" 2>&1 || true
fi
python3 -I "$HERE/scripts/bench_summary.py" "$OUT" "$SUITE"
