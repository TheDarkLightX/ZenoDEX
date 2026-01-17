# Tau Testnet "App Bridge" Patch (local, PR-ready)

This repo includes a PR-ready patch for Tau Testnet that adds a **generic application bridge** (`app_state`) committed into the block `state_hash` and published via the DHT.

The patch file lives at `patches/tau-testnet-app-bridge.patch`.

Optional follow-on patch:
- `patches/tau-testnet-state-proof.patch` (adds `state_proof:<state_hash>` plumbing)

## What it adds (high level)

- `app_bridge.py`: loads an optional app plugin and normalizes its output (canonical JSON + `sha256` content hash).
- `getappstate` command: query current `app_hash` / decoded snapshot.
- Consensus commitment: `state_hash = BLAKE3(rules_bytes + accounts_hash + app_hash)` (app hash optional).
- DHT records:
  - `tau_state:<state_hash>` JSON payload includes optional `app_hash`
  - `app_state:<app_hash>` stores canonical JSON bytes
- Tests: `tests/test_app_bridge.py` (app bridge canonicalization/hash behavior).

## Apply it to a Tau Testnet clone

From a clean `tau-testnet` checkout:

```bash
git apply /path/to/your-dex/patches/tau-testnet-app-bridge.patch
```

If Tau Testnet has moved a bit and the patch doesn’t apply cleanly, try:

```bash
git apply -3 /path/to/your-dex/patches/tau-testnet-app-bridge.patch
```

## Run the patch tests (Tau Testnet)

```bash
pytest -q tests/test_app_bridge.py
```

## Local DEX integration (example)

Enable the bridge (mining node) and point it at this repo’s plugin:

```bash
export TAU_APP_BRIDGE_SYS_PATH=/path/to/your-dex
export TAU_APP_BRIDGE_MODULE=src.integration.tau_testnet_dex_plugin
export TAU_DEX_CHAIN_ID=tau-local
```

Then run the local smoke harness:

```bash
bash tools/run_tau_testnet_local_smoke.sh
```

Notes:
- `balances_patch` is **disabled by default** in Tau Testnet; enable only if you intentionally want an app plugin to rewrite native balances:
  - `export TAU_APP_BRIDGE_ALLOW_BALANCE_PATCH=1`
