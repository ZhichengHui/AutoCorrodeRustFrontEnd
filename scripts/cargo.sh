#!/usr/bin/env bash
# Run cargo with the pinned nightly toolchain (rustc 1.100.0-nightly 923c95cdf 2026-09-16, with rustc-dev).
# The toolchain is installed under ~/Work/aeneas-env; override RUSTUP_HOME / CARGO_HOME to use another one.
set -euo pipefail
export RUSTUP_HOME=${RUSTUP_HOME:-$HOME/Work/aeneas-env/rustup}
export CARGO_HOME=${CARGO_HOME:-$HOME/Work/aeneas-env/cargo}
export RUSTUP_TOOLCHAIN=nightly-2026-09-17
exec "$CARGO_HOME/bin/cargo" "$@"
