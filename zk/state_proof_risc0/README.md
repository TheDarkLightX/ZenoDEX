---
title: README
type: note
permalink: autonomous-tau-dex-review/zk/state-proof-risc0/readme
---

# Tau State Proof (Risc0): Workspace

This workspace builds a standalone generator/verifier binary for Tau Testnet `state_proof:<state_hash>` envelopes.

## Crates

- `shared/`: no-std types + deterministic hashing used by guest + host
- `methods/guest/`: Risc0 zkVM guest (proves the ZenoDEX spot app-state transition for v1 scope)
- `methods/`: embeds the guest ELF + image ID
- `cli/`: `tau-state-proof-risc0-cli` (reads JSON on stdin; writes JSON on stdout)

## Build

Host CLI (offline, if your Cargo cache is primed):

```bash
cd zk/state_proof_risc0
cargo build --release --offline -p tau-state-proof-risc0-cli
```

Real proofs require the Risc0 toolchain/guest target. Prefer the upstream
`rzup` installer:

```bash
export PATH="$HOME/.risc0/bin:$PATH"
rzup install
```

The workspace currently uses `risc0-build` 1.2, whose method builder invokes the
named rustup toolchain `risc0`. If that named toolchain is unavailable or lacks
the guest target under its sysroot, normal local builds emit placeholder
methods. Production and CI proof-generation lanes should use
`RISC0_FORCE_BUILD=1` so a missing or misconfigured toolchain fails closed
instead of producing placeholder image IDs.
Clippy builds use placeholder methods because `risc0-build` 1.2 launches a
nested guest build that is incompatible with the clippy wrapper. Lint success is
not proof-generation evidence.

The repo parity gate contains the audited local toolchain detection path:

```bash
bash tools/run_rust_runtime_parity_gate.sh
```

## Use with local Tau Testnet smoke

From the repo root:

```bash
TAU_STATE_PROOF_RISC0=1 bash tools/run_tau_testnet_local_smoke.sh
```
