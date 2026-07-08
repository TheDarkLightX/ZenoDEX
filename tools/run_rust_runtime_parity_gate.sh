#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

if [[ -n "${PYTHON:-}" ]]; then
  PY="$PYTHON"
elif [[ -x "$ROOT_DIR/.venv/bin/python" ]]; then
  PY="$ROOT_DIR/.venv/bin/python"
else
  PY="python3"
fi

require_tool() {
  local tool="$1"
  if ! command -v "$tool" >/dev/null 2>&1; then
    echo "error: missing required Rust parity tool: $tool" >&2
    exit 2
  fi
}

require_file() {
  local label="$1"
  local path="$2"
  if [[ ! -f "$path" ]]; then
    echo "error: missing required $label: $path" >&2
    exit 2
  fi
}

require_tool cargo
require_tool rustfmt

if ! cargo clippy --version >/dev/null 2>&1; then
  echo "error: cargo clippy is required for Rust runtime parity promotion" >&2
  exit 2
fi

RUST_MANIFESTS=(
  "$ROOT_DIR/src/kernels/rust/lp_math_v7/Cargo.toml"
  "$ROOT_DIR/src/kernels/rust/fee_split_dust_carry_v1/Cargo.toml"
  "$ROOT_DIR/src/kernels/rust/settlement_delta_aggregation_v1/Cargo.toml"
  "$ROOT_DIR/src/kernels/rust/cow_star_capacity_v1/Cargo.toml"
  "$ROOT_DIR/src/kernels/rust/cow_sender_slot_quotient_v1/Cargo.toml"
  "$ROOT_DIR/src/kernels/rust/cow_capacity_dp_v1/Cargo.toml"
  "$ROOT_DIR/src/kernels/rust/cow_atomic_bmatching_v1/Cargo.toml"
  "$ROOT_DIR/src/kernels/rust/cow_component_status_selector_v1/Cargo.toml"
  "$ROOT_DIR/src/kernels/rust/cow_component_status_api_response_v1/Cargo.toml"
  "$ROOT_DIR/src/kernels/rust/oracle_median_v1/Cargo.toml"
  "$ROOT_DIR/src/kernels/rust/perp_source_admission_envelope_v1/Cargo.toml"
)

RISC0_WORKSPACE_MANIFEST="$ROOT_DIR/zk/state_proof_risc0/Cargo.toml"
RISC0_FORMAT_MANIFESTS=(
  "$ROOT_DIR/zk/state_proof_risc0/shared/Cargo.toml"
  "$ROOT_DIR/zk/state_proof_risc0/methods/Cargo.toml"
  "$ROOT_DIR/zk/state_proof_risc0/methods/guest/Cargo.toml"
  "$ROOT_DIR/zk/state_proof_risc0/cli/Cargo.toml"
)
RISC0_GUEST_TARGET="riscv32im-risc0-zkvm-elf"

PYTHON_RUST_PARITY_TESTS=(
  "$ROOT_DIR/tests/kernels/test_lp_math_v7.py"
  "$ROOT_DIR/tests/core/test_fees_rust_port.py"
  "$ROOT_DIR/tests/core/test_settlement_delta_aggregation_rust_port.py"
  "$ROOT_DIR/tests/kernels/test_cow_star_capacity_rust_port.py"
  "$ROOT_DIR/tests/kernels/test_cow_sender_slot_quotient_rust_port.py"
  "$ROOT_DIR/tests/kernels/test_cow_capacity_dp_rust_port.py"
  "$ROOT_DIR/tests/kernels/test_cow_atomic_bmatching_rust_port.py"
  "$ROOT_DIR/tests/kernels/test_cow_component_status_selector_rust_port.py"
  "$ROOT_DIR/tests/kernels/test_cow_component_status_api_response_rust_port.py"
  "$ROOT_DIR/tests/kernels/test_oracle_median_v1_rust_port.py"
  "$ROOT_DIR/tests/kernels/test_perp_source_admission_envelope_rust_port.py"
  "$ROOT_DIR/tests/core/test_risc0_tx_execution_order.py"
  "$ROOT_DIR/tests/integration/test_zeno_ledger_risc0_proof_metadata.py"
)

for manifest in "${RUST_MANIFESTS[@]}"; do
  require_file "Rust kernel manifest" "$manifest"
done

require_file "RISC0 state-proof workspace manifest" "$RISC0_WORKSPACE_MANIFEST"
for manifest in "${RISC0_FORMAT_MANIFESTS[@]}"; do
  require_file "RISC0 state-proof package manifest" "$manifest"
done

for test_path in "${PYTHON_RUST_PARITY_TESTS[@]}"; do
  require_file "Python-to-Rust parity test" "$test_path"
done

find_risc0_rustup_toolchain() {
  if [[ -n "${RISC0_RUSTUP_TOOLCHAIN:-}" ]]; then
    echo "$RISC0_RUSTUP_TOOLCHAIN"
    return 0
  fi
  if rustup +risc0 target list --installed 2>/dev/null | grep -qx "$RISC0_GUEST_TARGET"; then
    echo "risc0"
    return 0
  fi
  local risc0_home="${RISC0_HOME:-$HOME/.risc0}"
  local toolchain_dir="$risc0_home/toolchains"
  if [[ -d "$toolchain_dir" ]]; then
    while IFS= read -r candidate; do
      if compgen -G "$candidate/lib/rustlib/$RISC0_GUEST_TARGET/lib/libcore-*.rlib" >/dev/null; then
        echo "$candidate"
        return 0
      fi
    done < <(find "$toolchain_dir" -maxdepth 1 -type d -name 'v*-rust-*' | sort -Vr)
  fi
  return 1
}

RISC0_RUST_TOOLCHAIN="$(find_risc0_rustup_toolchain || true)"
if [[ -z "$RISC0_RUST_TOOLCHAIN" ]]; then
  echo "error: missing RISC0 Rust toolchain with $RISC0_GUEST_TARGET support" >&2
  echo "error: install via rzup or set RISC0_RUSTUP_TOOLCHAIN to the toolchain path" >&2
  exit 2
fi

echo "== rust runtime parity: cargo fmt/test/clippy =="
# Review finding (grade B -> A-): the release gate had Python differential
# tests for promoted Rust leaves, but no single fail-closed lane that also
# checked Rust formatting, unit tests, and lint health. This prevents a
# Python-only or stale Rust leaf from being treated as production-complete.
for manifest in "${RUST_MANIFESTS[@]}"; do
  cargo fmt --check --manifest-path "$manifest"
  cargo test --manifest-path "$manifest"
  cargo clippy --manifest-path "$manifest" -- -D warnings
done

echo "== rust runtime parity: RISC0 state-proof Rust workspace =="
# The RISC0 workspace is the production-oriented proof surface. Force real guest
# method embedding here so this release lane cannot pass with the all-zero
# placeholder image used only for explicit local skip builds.
for manifest in "${RISC0_FORMAT_MANIFESTS[@]}"; do
  cargo fmt --check --manifest-path "$manifest"
done
env RISC0_FORCE_BUILD=1 RUSTUP_TOOLCHAIN="$RISC0_RUST_TOOLCHAIN" \
  cargo test --manifest-path "$RISC0_WORKSPACE_MANIFEST" -p tau-state-proof-risc0-shared --lib
env RISC0_FORCE_BUILD=1 RUSTUP_TOOLCHAIN="$RISC0_RUST_TOOLCHAIN" \
  cargo test --manifest-path "$RISC0_WORKSPACE_MANIFEST" -p tau-state-proof-risc0-cli --bin tau-state-proof-risc0-cli
env RISC0_FORCE_BUILD=1 RUSTUP_TOOLCHAIN="$RISC0_RUST_TOOLCHAIN" \
  cargo check --manifest-path "$RISC0_WORKSPACE_MANIFEST" -p tau-state-proof-risc0-cli
env RISC0_FORCE_BUILD=1 RUSTUP_TOOLCHAIN="$RISC0_RUST_TOOLCHAIN" \
  cargo clippy --manifest-path "$RISC0_WORKSPACE_MANIFEST" -p tau-state-proof-risc0-shared -- -D warnings
env RISC0_FORCE_BUILD=1 RUSTUP_TOOLCHAIN="$RISC0_RUST_TOOLCHAIN" \
  cargo clippy --manifest-path "$RISC0_WORKSPACE_MANIFEST" -p tau-state-proof-risc0-cli -- -D warnings

echo "== rust runtime parity: Python-to-Rust differentials =="
"$PY" -m pytest -q "${PYTHON_RUST_PARITY_TESTS[@]}"
