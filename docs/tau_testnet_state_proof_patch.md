# Tau Testnet `state_proof` Patch (local, PR-ready)

This repo includes a PR-ready patch for Tau Testnet that adds an **optional per-block state proof record** published to the DHT:

- DHT key: `state_proof:<state_hash>`
- Value: JSON envelope with schema `tau_state_proof`

This is designed to be generic (Tau Net is general) and **does not change block format or consensus hashing**.

Patch file: `patches/tau-testnet-state-proof.patch`

## Prerequisite

This patch is designed to apply **on top of** the app bridge patch:

- `patches/tau-testnet-app-bridge.patch`

## Apply it to a Tau Testnet clone

From a clean `tau-testnet` checkout:

```bash
git apply /path/to/your-dex/patches/tau-testnet-app-bridge.patch
git apply /path/to/your-dex/patches/tau-testnet-state-proof.patch
```

If Tau Testnet has moved a bit and a patch doesn’t apply cleanly, try:

```bash
git apply -3 /path/to/your-dex/patches/tau-testnet-app-bridge.patch
git apply -3 /path/to/your-dex/patches/tau-testnet-state-proof.patch
```

## Run patch tests (Tau Testnet)

```bash
pytest -q tests/test_app_bridge.py tests/test_state_proof.py
```

## Configuration (Tau Testnet)

Mining / publishing (optional):

- `TAU_STATE_PROOF_GENERATE_CMD="<command ...>"`: generator returns a `tau_state_proof` JSON envelope on stdout.
- `TAU_STATE_PROOF_GENERATE_REQUIRE=1`: fail block creation if generation fails or is not configured.

Followers / enforcement (optional, fail-closed when enabled):

- `TAU_STATE_PROOF_REQUIRE=1`: require a proof for each new block.
- `TAU_STATE_PROOF_VERIFY_CMD="<command ...>"`: verifier returns `{"ok": true}` or `{"ok": false, "error": "..."}`.

Debugging:

- TCP command: `getstateproof [full]`

### Generator/verifier context passthrough

The patch forwards optional `block`, `tau_state`, and `context` objects into the subprocess JSON request so real ZK proof systems can bind to:

- the block’s tx list (via `block.transactions`), and
- the expected application commitment (via `tau_state.app_hash`), and
- app-specific extra inputs (via `context`, e.g. `app_state_pre`, `chain_balances_post`).

See `docs/tau_state_proof_risc0_tauswap_v1.md` for the concrete Risc0 generator requirements used by this repo.

## Local smoke (debug proof)

If you have this repo checked out with `external/tau-testnet` patched, you can run:

```bash
TAU_STATE_PROOF_DEBUG=1 bash tools/run_tau_testnet_local_smoke.sh
```

This uses `tools/state_proof_debug_generate.py` + `tools/state_proof_debug_verify.py` (debug-only; not ZK) to prove the end-to-end plumbing works.

## Local TauSwap smoke (Risc0 proof)

Requires Rust + the Risc0 toolchain/target.

```bash
TAU_STATE_PROOF_RISC0=1 bash tools/run_tau_testnet_local_smoke.sh
```

This runs the same end-to-end swap smoke test, but publishes a real Risc0 receipt in `state_proof:<state_hash>` and verifies it locally by reading the node DB.
