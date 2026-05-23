---
title: TOKEN_REGISTRY_DESIGN
type: note
permalink: autonomous-tau-dex-review/docs/token-registry-design
---

# Token Registry & Listing Design (AGRS + ZDEX Launch)

## Purpose

This document specifies how TauSwap/ZenoDEX should:

1. Add tokens in a **cryptographically bound** and **formally checkable** way.
2. Guarantee the DEX supports **AGRS** (Tau Net native token) and **ZDEX** (DEX token) at launch.
3. Integrate AGRS on **Tau Net Testnet Alpha** (when AGRS already exists as the chain’s native balance).

The design is explicitly **fail-closed**: missing proofs/unknown tokens/ambiguous metadata must cause rejection, not silent fallback.

**Status:** design/spec only. Implementation work (Tau specs + snapshot format + validation plumbing) is tracked by the “Implementation Checklist” at the end.

---

## Scope and Assumptions

### What this repo currently implements

- The DEX core is multi-asset: balances are keyed by `(pubkey, asset_id)` where `asset_id` is a 32-byte hex string (`src/state/balances.py`).
- The native asset is represented as:
  - `NATIVE_ASSET = "0x" + "00" * 32` (`src/state/balances.py`)
- In Tau Testnet Alpha integration, the DEX plugin:
  - syncs chain native balances into `NATIVE_ASSET`,
  - and can optionally emit a `balances_patch` that rewrites chain balances (`src/integration/tau_testnet_dex_plugin.py`, `docs/tau_testnet_app_bridge_patch.md`, `docs/tau_testnet_local_node.md`).

### What this document adds (design + spec)

- A **Token Registry** that maps `asset_id → token metadata + semantics commitments`.
- A **governance + timelock** workflow for adding tokens.
- A **formal gate** (Tau spec variants) ensuring DEX execution only references listed tokens.

### Non-goals (for this document)

- Defining the full governance system and voting mechanics.
- Specifying a full on-chain token standard for Tau Net.
- Designing the UI/SDK in full detail (only the integrity contract with the registry is specified).

---

## Definitions

### Identifiers

- **`asset_id`**: 32-byte hex string (`0x` + 64 hex chars). Used everywhere in intents, pools, balances.
- **AGRS**: Tau Net native currency.
- **ZDEX**: DEX protocol token (governance/utility). Historical docs/specs in this repo sometimes use `TDEX`; treat that as a naming predecessor.

### Token registry entry (canonical)

A **Token Entry** is the canonical, signed object that describes a token:

```json
{
  "schema": "zenodex.token_entry",
  "schema_version": 1,
  "chain_id": "tau-net-alpha",
  "asset_id": "0x…32-bytes…",
  "symbol": "AGRS",
  "name": "Agoras",
  "decimals": 18,
  "kind": "native|dex_internal|wrapped|chain_token",
  "transfer_semantics": "exact|fee_on_transfer|rebasing|unknown",
  "spec_ref": {
    "spec_id": "protocol_token_v1",
    "spec_path": "src/tau_specs/protocol_token_v1.tau",
    "spec_hash": "0x…sha256…"
  },
  "issuer_pubkey": "0x…48-bytes…",
  "issuer_sig": "0x…96-bytes…"
}
```

Notes:

- `spec_ref` binds the token to a **formal transition spec**. For `native` tokens, `spec_ref` can be present but is informational; the chain defines semantics. For `dex_internal`/`wrapped`, it is normative.
- `issuer_sig` is a BLS12-381 signature over the canonical entry payload (details below).
- `transfer_semantics` is a safety classification used to decide whether the AMM math is valid without special handling.

### Token registry commitment

- **`token_registry_root`**: a cryptographic commitment (sha256) over the ordered list of Token Entries (excluding signatures, or including them—see “Commitment rules”).
- The DEX state snapshot MUST commit to the registry root so that:
  - `app_hash` binds the token set (ZK proofs and followers inherit that binding),
  - UI and indexers can verify the token list is not being spoofed by a node.

---

## Security Goals

### Threats we explicitly defend against

1. **Fake metadata**: a node serves “AGRS” but maps to a different `asset_id`.
2. **Ambiguous symbols**: two different tokens share the same symbol (`USDC`, `AGRS`, etc.).
3. **Decimals spoofing**: UI shows wrong decimals causing users to sign unintended amounts.
4. **Non-standard transfer tokens**: fee-on-transfer/rebasing tokens break CPMM invariants unless explicitly modeled.
5. **Silent downgrades**: “missing registry entry” or “proof unavailable” must not fallback to permissive behavior.

### What “cryptographically guaranteed” means here

For any DEX operation that references a token by `asset_id`, honest clients can verify:

- The token was listed in the committed registry root.
- The token’s metadata/semantics match what was committed.
- The entry was authorized (issuer signature + governance/timelock policy).

### What “formally guaranteed” means here

The DEX execution path must be able to enforce, via Tau specs (and/or proof-gated Tau checks), that:

- Only listed tokens can be used in intents/pools/settlement.
- Tokens used in CPMM satisfy the required `transfer_semantics` (typically `exact`).
- Registry updates obey governance/timelock constraints and monotonic safety rules.

---

## Token Registry State and Commitment Rules

### Registry state (consensus/app state)

The DEX app state MUST include, at minimum:

- `token_registry_version` (u32)
- `token_registry_root` (32 bytes hex)

Recommended (for auditability and UI bootstrapping):

- `token_registry_entries` (the entries themselves), or
- `token_registry_delta` (append-only additions since last checkpoint).

### Commitment encoding

Define:

- `entry_bytes = canonical_json_bytes(entry_without_issuer_sig)`  
  (exclude `issuer_sig` from the hash input; it is verified separately).
- Sort entries by `asset_id` ascending.
- `token_registry_root = sha256(domain_sep_bytes("token_registry_root", version=1) || uvarint(n) || entry_bytes...)`

Rationale:

- Excluding `issuer_sig` avoids dependence on signature encoding details.
- Sorting by `asset_id` makes the root deterministic and easy to reproduce.

### Where to commit the root

- `DexSnapshot` (next version) MUST include `token_registry_root` so `app_hash` commits to the token set.
  - Current snapshot format is in `src/integration/dex_snapshot.py`.
- Any ZK state proof (e.g. Risc0) MUST treat `token_registry_root` as part of the proven transition state.

---

## Formal Gates (Tau Specs)

This design requires a dedicated “token listing gate” component with two variants, aligned with the existing profile scheme (`docs/TAU_SPECS_PROFILES.md`, `src/tau_specs/recommended/spec_profiles.json`):

### Variant A: `tau_only_structural` (small allowlist)

For early launch and tight determinism, provide a Tau spec:

- `token_registry_allowlist_v1.tau`

Behavior:

- Inputs include `asset_id` limbs for the assets referenced in a step (e.g., `asset_in`, `asset_out`, pool assets).
- Tau checks those `asset_id`s are equal to one of a fixed set of listed ids (bounded `N`, e.g. 2–16).

Use case:

- Launch guarantee that **AGRS and ZDEX** are supported even before scalable proof plumbing exists.

Limits:

- Not scalable to many tokens (Tau file size grows with N).

### Variant B: `fast_proof_gated` (Merkle/append proof gated)

For scalability, provide a Tau spec:

- `token_registry_gate_v2.tau` (proof-gated)

Behavior:

- Inputs: `exec_req`, `revision_ok`, `token_registry_root`, plus `proof_ok` and `binding_ok`.
- Tau enforces only:
  - `gate_ok = exec_req & revision_ok & proof_ok & binding_ok`
  - and echoes the committed root forward.

Interpretation:

- An external verifier (and optionally a ZK proof) validates:
  - membership proofs for all referenced assets,
  - registry update legality (append-only, symbol uniqueness, semantics constraints),
  - binding of the proof to the exact `token_registry_root` and the exact batch being executed.

This mirrors the existing pattern in `src/tau_specs/recommended/parameter_registry_v2.tau`.

---

## Listing Policy (What Tokens Are Allowed)

### DEX-compatible token profile (minimum)

To be listed for CPMM pools, a token MUST satisfy:

1. **Deterministic base units**: integer amount accounting (already true in this repo).
2. **Exact transfer semantics**: `transfer_semantics = "exact"`.
3. **Stable decimals**: `decimals` must never change once listed.
4. **Stable identity**: `asset_id` must never be re-assigned to a different symbol/name.

If a token is not “exact transfer”, it MAY still be listed, but it MUST be:

- restricted to special pool types that model its semantics, or
- wrapped into an exact-transfer representation before being allowed in CPMM.

### Special cases

- **AGRS**: listed as `kind="native"`, `asset_id = NATIVE_ASSET`.
- **LP tokens**: are not user-listed “assets”; they are protocol artifacts. If represented as assets, they should be `kind="dex_internal"` and generally not swappable.

---

## Token Addition Workflow (Cryptographic + Formal)

### Step 1: Determine the token’s custody model

Each token must fit one of:

- `native`: chain-native (AGRS).
- `dex_internal`: lives in DEX app state (e.g., testnet-only tokens, protocol token if not chain-issued).
- `wrapped`: a DEX-issued wrapper around an external/native asset (recommended if chain balance patching is disallowed).
- `chain_token`: chain-issued token with a stable chain identifier (future, if Tau Net supports it).

### Step 2: Produce a Token Entry + issuer signature

Issuer signature requirements:

- Define signing payload as `canonical_json_bytes(entry_without_issuer_sig)` with a domain separator:
  - `msg = domain_sep_bytes("token_entry_sig", version=1) || payload`
  - `sig = BLS.Sign(issuer_sk, sha256(msg))`

For `native` tokens, issuer can be a chain governance key (or omitted if you want “native is self-authenticating”).

### Step 3: Governance proposal + timelock

Token listing MUST be governed. Minimal policy:

- `approved` must be true,
- timelock delay must elapse (see `src/tau_specs/governance_timelock_v1.tau`),
- then execution can update the registry root (see “Formal Gates”).

This policy can be expressed either:

- directly in Tau for small lists, or
- proof-gated with an external verifier for scalable lists.

### Step 4: Apply registry update (append-only)

Registry updates MUST be **append-only** unless a hard-fork protocol upgrade is executed.

Allowed update types:

- `ADD_TOKEN`: add a new `(asset_id → entry)` mapping.

Disallowed (in v1):

- `REMOVE_TOKEN` (creates ambiguity and breaks historic proofs)
- `CHANGE_DECIMALS`, `CHANGE_SYMBOL` (breaks UX safety)

Optional: allow `DISABLE_TOKEN` (soft-disable) via a separate field, but treat it as a distinct “status” update that does not rewrite identity fields.

---

## Launch Requirement: AGRS + ZDEX Must Be Supported

### Minimum launch invariants

At “genesis” of the DEX deployment (first app state / first committed registry root):

1. The registry contains an entry for:
   - AGRS: `asset_id = NATIVE_ASSET`
2. The registry contains an entry for:
   - ZDEX: `asset_id = ZDEX_ASSET_ID` (fixed constant for the deployment)
3. The DEX rejects intents referencing assets not in the registry (fail-closed).

### ZDEX: required decisions before launch

ZDEX must have a single, unambiguous definition:

- **Asset id**: choose one:
  1. **Chain-issued** id (if Tau Net supports chain tokens), or
  2. **DEX-derived** id:
     - `ZDEX_ASSET_ID = sha256_hex(domain_sep_bytes("dex_asset_id", version=1) || b"ZDEX" || chain_id_bytes)`
- **Semantics**: choose one:
  - exact-transfer fungible token (recommended for CPMM), or
  - deflationary/fee-on-transfer token (requires non-standard pool math or wrapper)
- **Initial distribution**:
  - genesis mint allocation and/or an explicit mint policy module.

If using the existing deflationary spec family in this repo (`src/tau_specs/tdex_token_v1.tau`; current public token doc: `docs/ZDEX_TOKEN.md`), do not allow ZDEX into CPMM pools unless the swap math is upgraded to model transfer burns exactly.

---

## AGRS on Tau Net Testnet Alpha: How to Bring It Into the DEX

### What “AGRS exists on testnet” means in this repo today

In the current Tau Testnet Alpha integration:

- The node exposes a single `getbalance` per address (`src/integration/tau_net_client.py`), consistent with a single native currency.
- The DEX plugin treats that balance as `NATIVE_ASSET` and mirrors it into the DEX balance table (`src/integration/tau_testnet_dex_plugin.py`).

Therefore: **AGRS integration = native asset integration**.

### Required node-side configuration (native rewrite mode)

If the DEX is allowed to debit/credit AGRS directly, the Tau node must allow the app bridge to patch native balances:

- `TAU_APP_BRIDGE_ALLOW_BALANCE_PATCH=1` (see `docs/tau_testnet_app_bridge_patch.md`)

With this enabled:

- A swap that spends AGRS will produce a `balances_patch` that reduces the sender’s chain balance.
- A swap that receives AGRS will increase the recipient’s chain balance.

This is the simplest “bring AGRS into the DEX” path on testnet.

### Safer alternative (recommended for production posture): wrap AGRS

If native balance patching is disabled (or considered too dangerous for production), use a wrapper:

- Introduce `wAGRS` as `kind="wrapped"`, `transfer_semantics="exact"`.
- Add two new DEX operations:
  - `DEPOSIT_NATIVE(amount)`:
    - requires an on-chain transfer of AGRS into a DEX escrow address,
    - mints `wAGRS` in DEX state to the depositor.
  - `WITHDRAW_NATIVE(amount)`:
    - burns `wAGRS`,
    - releases AGRS from escrow on chain.

This turns “native external balance” into an internal exact-transfer asset, simplifying:

- CPMM correctness,
- ZK proving (no need for per-tx chain balance oracles),
- consensus determinism.

---

## Implementation Checklist (Concrete Next Steps)

1. Add `docs/TOKEN_REGISTRY_DESIGN.md` (this doc) and link it from higher-level docs if desired.
2. Decide `ZDEX_ASSET_ID` and whether ZDEX is exact-transfer (recommended).
3. Add a registry root + entries into the DEX snapshot (new snapshot version) so `app_hash` commits to tokens.
4. Add a “reject unknown assets” check in intent validation (core or integration layer).
5. Add Tau spec component(s) for token registry gating:
   - small allowlist v1 (AGRS + ZDEX),
   - proof-gated v2 (scalable).
6. For testnet:
   - either enable `TAU_APP_BRIDGE_ALLOW_BALANCE_PATCH=1` and use native AGRS directly,
   - or implement `wAGRS` deposit/withdraw and keep the DEX purely internal.

## Companion Designs

- [TOKEN_ADMISSION_AND_POOL_LAUNCH.md](TOKEN_ADMISSION_AND_POOL_LAUNCH.md)
  describes the user-facing admission flow, the AGRS/ZDEX launch pair, and how
  custom tokens become eligible for pools.
