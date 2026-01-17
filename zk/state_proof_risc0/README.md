# Tau State Proof (Risc0): Workspace

This workspace builds a standalone generator/verifier binary for Tau Testnet `state_proof:<state_hash>` envelopes.

## Crates

- `shared/`: no-std types + deterministic hashing used by guest + host
- `methods/guest/`: Risc0 zkVM guest (proves TauSwap app-state transition for v1 scope)
- `methods/`: embeds the guest ELF + image ID
- `cli/`: `tau-state-proof-risc0-cli` (reads JSON on stdin; writes JSON on stdout)

## Build

Host CLI (offline, if your Cargo cache is primed):

```bash
cd zk/state_proof_risc0
cargo build --release --offline -p tau-state-proof-risc0-cli
```

Real proofs require the Risc0 toolchain/guest target:

```bash
rustup toolchain install risc0
rustup target add riscv32im-risc0-zkvm-elf --toolchain risc0
```

## Use with local Tau Testnet smoke

From the repo root:

```bash
TAU_STATE_PROOF_RISC0=1 bash tools/run_tau_testnet_local_smoke.sh
```
