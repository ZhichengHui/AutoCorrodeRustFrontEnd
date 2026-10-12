#!/usr/bin/env bash
# Translate a benchmark suite (tests/benchmarks/SUITE/*.rs, one crate per file) and check
# every translated crate with Isabelle (one session per 30 crates); write out/bench/SUITE/SUMMARY.md.
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
  charon) TAG=Ch ;;
  algorithms) TAG=Al ;;
  crust) TAG=Cr ;;
  humaneval_x) TAG=He ;;
  *) TAG=Bm ;;
esac

# rustc arguments for one file: Aeneas tests use the tool attributes #[charon::..] / #[aeneas::..]
rustc_args() {
  local f=$1 edition=$2
  RUSTC_ARGS=(--edition="$edition")
  if [ "$SUITE" = aeneas ] || [ "$SUITE" = charon ]; then
    grep -q 'feature(.*register_tool' "$f" || RUSTC_ARGS+=(-Zcrate-attr=feature\(register_tool\))
    grep -q 'register_tool(charon' "$f" || RUSTC_ARGS+=(-Zcrate-attr=register_tool\(charon\))
    grep -q 'register_tool(.*aeneas' "$f" || RUSTC_ARGS+=(-Zcrate-attr=register_tool\(aeneas\))
  fi
}

files=("$@")
if [ ${#files[@]} -eq 0 ]; then
  shopt -s nullglob
  files=("$SRC"/*.rs "$SRC"/*/lib.rs)
fi

# translated crates go to $OUT/cK/STEM: one Isabelle session per directory cK (CHUNK crates)
CHUNK=${CHUNK:-30}
rm -rf "$OUT"/c[0-9]* "$OUT/work"
mkdir -p "$OUT/work"
status="$OUT/status.tsv"
: > "$status"
ntr=0
for f in "${files[@]}"; do
  if [ "$(basename "$f")" = lib.rs ]; then base="$(basename "$(dirname "$f")")"; else base="$(basename "$f" .rs)"; fi
  stem="$(echo "$base" | tr -c 'A-Za-z0-9_\n' '_')"
  name="${TAG}_${stem}"
  work="$OUT/work/$stem"
  log="$OUT/$stem.translate.log"
  rustc_args "$f" 2021
  "$HERE/scripts/urust-frontend.sh" --out "$work" --name "$name" "$f" -- "${RUSTC_ARGS[@]}" > "$log" 2>&1
  if grep -q "only allowed in Rust 2024\|edition 2024 or later" "$log"; then
    rustc_args "$f" 2024
    "$HERE/scripts/urust-frontend.sh" --out "$work" --name "$name" "$f" -- "${RUSTC_ARGS[@]}" > "$log" 2>&1
  fi
  if [ -f "$work/${name}_Funs.thy" ]; then
    k=$((ntr / CHUNK + 1))
    ntr=$((ntr + 1))
    mkdir -p "$OUT/c$k"
    mv "$work" "$OUT/c$k/$stem"
    ph="$(head -1 "$OUT/c$k/$stem/PLACEHOLDERS.txt" | sed 's/.*: //')"
    printf '%s\t%s\ttranslated\t%s\tc%s\n' "$stem" "$name" "$ph" "$k" >> "$status"
  elif grep -q "panicked at\|internal compiler error" "$log"; then
    printf '%s\t%s\tfrontend-crash\t-\t-\n' "$stem" "$name" >> "$status"
  else
    printf '%s\t%s\trustc-rejected\t-\t-\n' "$stem" "$name" >> "$status"
  fi
done
rm -rf "$OUT/work"
echo "translation: $(cut -f3 "$status" | sort | uniq -c | tr '\n' ' ')"

if [ "${NO_ISABELLE:-0}" != 1 ] && [ "$ntr" -gt 0 ]; then
  sessions=()
  : > "$OUT/ROOT"
  for d in "$OUT"/c[0-9]*; do
    k="$(basename "$d")"
    session="Bench_${SUITE}_${k}"
    sessions+=("$session")
    {
      echo "session $session in \"$k\" = AutoCorrode +"
      echo "  options [document = false, timeout = 7200]"
      echo "  directories"
      for c in "$d"/*/; do echo "    \"$(basename "$c")\""; done
      echo "  theories"
      for c in "$d"/*/; do
        s="$(basename "$c")"
        echo "    \"$s/$(grep -P "^$s\t" "$status" | cut -f2)_Funs\""
      done
      echo
    } >> "$OUT/ROOT"
  done
  echo "checking $ntr crates in ${#sessions[@]} sessions with Isabelle (memory cap $MEMORY_MAX) ..."
  systemd-run --user --scope -q -p MemoryMax="$MEMORY_MAX" -p MemorySwapMax=0 \
    "$ISABELLE" build -j 1 -o threads=2 -d "$AUTOCORRODE" -d "$OUT" -v "${sessions[@]}" > "$OUT/isabelle.log" 2>&1
  rc=$?
  echo "$rc" > "$OUT/isabelle.rc"
  echo "isabelle exit code: $rc"
  : > "$OUT/isabelle_errors.log"
  for s in "${sessions[@]}"; do
    "$ISABELLE" build_log -H Error "$s" >> "$OUT/isabelle_errors.log" 2>&1 || true
  done
fi

python3 -I "$HERE/scripts/bench_summary.py" "$OUT" "$SUITE"
