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

Real proofs require the Risc0 components:

```bash
rzup install
rzup show
```

Set `RISC0_FORCE_BUILD=1` for fail-closed builds that must reject placeholder
methods instead of silently embedding an empty guest ELF and all-zero image ID.

## Use with local Tau Testnet smoke

From the repo root:

```bash
TAU_STATE_PROOF_RISC0=1 bash tools/run_tau_testnet_local_smoke.sh
```
