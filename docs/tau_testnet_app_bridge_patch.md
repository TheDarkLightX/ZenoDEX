# Tau Testnet "App Bridge" Patch (local, PR-ready)

This repo includes a PR-ready patch for Tau Testnet that adds a **generic application bridge** (`app_state`) committed into the block `state_hash` and published via the DHT.

The patch file lives at `patches/tau-testnet-app-bridge.patch`.
For current upstream commit `69deea00ac291cc28dbca319a2a3465d9a9256a9`, use:
- `patches/tau-testnet-app-bridge-upstream-69deea0.patch`

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
- Custom-input compatibility for app payloads in `sendtx`:
  - Upstream `sendtx` restricts custom operation streams (`>=5`) to `str|int` (or lists thereof).
  - The DEX client encodes structured ops (dict/list) as **canonical JSON strings**.
  - The app plugin decodes those JSON strings back into objects before validation/execution.

## Upstream stream-key compatibility

At upstream commit `2deccad`, user-supplied operation keys `2/3/4` are reserved.
Use app streams `>=5` in tx payloads:

- `5`: DEX intents
- `6`: DEX settlement
- `7`: faucet (test-only)
- `8`: perps
- `9`: token ops (`module: "TauToken"` transfer/mint/burn for non-native assets)

The local DEX app plugin accepts these keys and still supports legacy aliases for direct plugin tests.

## Apply it to a Tau Testnet clone

From a clean `tau-testnet` checkout:

```bash
git apply /path/to/your-dex/patches/tau-testnet-app-bridge-upstream-69deea0.patch
```

If Tau Testnet has moved a bit and the patch doesn’t apply cleanly, try:

```bash
git apply -3 /path/to/your-dex/patches/tau-testnet-app-bridge-upstream-69deea0.patch
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
