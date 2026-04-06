# Tau Testnet `gettaustate` Patch (local, PR-ready)

This repo includes a small follow-on patch for Tau Testnet that exposes the committed `tau_state:<state_hash>` payload over the TCP command surface.

The patch file lives at `patches/tau-testnet-gettaustate.patch`.

## Purpose

The app-bridge patch already commits and publishes:

- `tau_state:<state_hash>` with:
  - `rules`
  - `accounts_hash`
  - `app_hash` (optional)

But the default TCP surface only exposes:

- `getappstate [full]`
- `getstateproof [full]`

That is not enough for a runtime to prove that the committed `app_hash` inside the stable Tau-state payload matches the `app_hash` returned by `getappstate full`.

This patch adds:

```text
gettaustate <state_hash>
```

If the requested `state_hash` is the node's current committed snapshot, the command serves that payload directly from local chain state even if the DHT copy has not propagated yet.

## Apply order

Apply this patch after:

1. `patches/tau-testnet-app-bridge.patch`

Optional:

2. `patches/tau-testnet-state-proof.patch`

Example:

```bash
git apply /path/to/your-dex/patches/tau-testnet-app-bridge.patch
git apply /path/to/your-dex/patches/tau-testnet-gettaustate.patch
```

## Command contract

Success response:

```json
{
  "state_hash": "<64-hex>",
  "present": true,
  "rules": "<utf-8 Tau rules text>",
  "accounts_hash": "<64-hex>",
  "app_hash": "<64-hex or empty>"
}
```

Missing payload / malformed request:

```json
{
  "state_hash": "<64-hex or raw input>",
  "present": false,
  "error": "<reason>"
}
```

Current-snapshot fallback:

- the command first tries `tau_state:<state_hash>` from the DHT
- if that payload is absent but `state_hash` matches the node's current committed snapshot, it rebuilds the payload from local committed chain state
- only non-current, non-published snapshots return `present=false`

## Why this matters

With:

1. `getstateproof full`
2. `gettaustate <state_hash>`
3. `getappstate full`

the runtime can fail closed on:

- unstable `state_hash`
- missing `tau_state:<state_hash>`
- `tau_state.app_hash != getappstate.app_hash`
- malformed committed Tau-state payloads

That is the missing transport needed by the stronger ZenoDEX-side provenance check in the settlement signer-registry loader.
