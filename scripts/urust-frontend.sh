#!/usr/bin/env bash
# Run the frontend binary with the pinned toolchain's libraries on the library path.
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
RUSTUP_HOME=${RUSTUP_HOME:-$HOME/Work/aeneas-env/rustup}
TC="$RUSTUP_HOME/toolchains/nightly-2026-09-17-x86_64-unknown-linux-gnu"
export LD_LIBRARY_PATH="$TC/lib:$TC/lib/rustlib/x86_64-unknown-linux-gnu/lib:${LD_LIBRARY_PATH:-}"
BIN="$HERE/target/release/urust-frontend"
[ -x "$BIN" ] || BIN="$HERE/target/debug/urust-frontend"
exec "$BIN" "$@"
