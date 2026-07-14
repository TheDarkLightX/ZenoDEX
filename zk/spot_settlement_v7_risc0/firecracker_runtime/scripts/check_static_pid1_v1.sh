#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
workspace="$(cd -- "$script_dir/../.." && pwd -P)"
target_dir="${CARGO_TARGET_DIR:-$workspace/target}"
binary="$target_dir/x86_64-unknown-linux-gnu/release/zenodex-zrpf-spot-v7-firecracker-protocol-init"

export CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS="-C target-feature=+crt-static"

cargo build \
  --manifest-path "$workspace/Cargo.toml" \
  --locked \
  --offline \
  -p zenodex-zrpf-spot-v7-firecracker-runtime \
  --bin zenodex-zrpf-spot-v7-firecracker-protocol-init \
  --release \
  --target x86_64-unknown-linux-gnu

program_headers="$(readelf -l "$binary")"
if grep -q 'INTERP' <<<"$program_headers"; then
  echo "static PID-1 check rejected PT_INTERP" >&2
  exit 1
fi

dynamic_section="$(readelf -d "$binary")"
if grep -q 'NEEDED' <<<"$dynamic_section"; then
  echo "static PID-1 check rejected DT_NEEDED" >&2
  exit 1
fi

file "$binary"
sha256sum "$binary"
