# Tau Testnet "App Bridge" Patch (local, PR-ready)

This repo includes a PR-ready patch for Tau Testnet that adds a **generic application bridge** (`app_state`) committed into the block `state_hash` and published via the DHT.

The patch file lives at `patches/tau-testnet-app-bridge.patch`.

Optional follow-on patch:
- `patches/tau-testnet-state-proof.patch` (adds `state_proof:<state_hash>` plumbing)
- `patches/tau-testnet-gettaustate.patch` (adds `gettaustate <state_hash>` transport for committed Tau-state payloads)

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

## Follow-on transport for runtime provenance

The app-bridge patch publishes the committed payload we need under `tau_state:<state_hash>`, but by itself the documented TCP surface only exposes `getappstate [full]`.

The companion patch `patches/tau-testnet-gettaustate.patch` adds:

```text
gettaustate <state_hash>
```

Recommended response shape:

```json
{
  "state_hash": "<64-hex>",
  "present": true,
  "rules": "<utf-8 Tau rules text>",
  "accounts_hash": "<64-hex>",
  "app_hash": "<64-hex or empty>"
}
```

Why this matters:
- `getstateproof full` gives the stable `state_hash`
- `gettaustate <state_hash>` reveals the committed `tau_state:<state_hash>` payload
- when the requested hash is the node's current committed snapshot, `gettaustate` can serve that payload locally without waiting for DHT propagation
- `getappstate full` reveals the decoded app snapshot and its `app_hash`

That lets the runtime reject unless the app snapshot hash matches the `app_hash` committed inside the stable Tau-state payload, instead of only trusting two separate TCP views.

See also:
- [docs/tau_testnet_gettaustate_patch.md](/home/trevormoc/Downloads/Autonomous%20Tau%20DEX/docs/tau_testnet_gettaustate_patch.md)
