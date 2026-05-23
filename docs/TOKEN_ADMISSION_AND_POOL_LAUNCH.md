---
title: TOKEN_ADMISSION_AND_POOL_LAUNCH
type: note
permalink: autonomous-tau-dex-review/docs/token-admission-and-pool-launch
---

# Token Admission And Pool Launch

Status: internal design. This document extends
[TOKEN_REGISTRY_DESIGN.md](TOKEN_REGISTRY_DESIGN.md) with the operational path
for adding user tokens and creating initial pools.

The Tau Net team has not published enough final token-interface detail for this
repo to hard-code a permanent token standard. The design below therefore treats
Tau-token support as an adapter problem: ZenoDEX admits only assets whose
identity, custody, and transfer semantics are proven or wrapped into a known
local model.

External assumptions to re-check before implementation:

- Tau states that Agoras (`AGRS`) is the native token and gas for Tau Net.
- Tau states that Tau Net software and interactions are written in Tau
  Language.

Those are enough for architecture direction, not enough for final custody code.

## Launch Pair

The natural first pair is:

```text
AGRS / ZDEX
```

Reason:

- `AGRS` is the chain-native economic asset.
- `ZDEX` is the DEX-native utility/governance/value-flow asset.
- A first AGRS/ZDEX pool gives users one obvious entry point into the ZenoDEX
  economy without requiring third-party token support on day one.

But this pair should not be launched blindly. There is a tokenomics conflict to
resolve first:

```text
CPMM exact-transfer invariant + deflationary transfer burn -> unsafe unless modeled or wrapped
```

If ZDEX burns or taxes on transfer, raw ZDEX cannot be treated as an ordinary
constant-product asset. The safe launch choices are:

1. Make the AMM-facing ZDEX representation exact-transfer and keep deflation in
   the fee-funded buyback/burn path.
2. Use `wZDEX` as an exact-transfer AMM wrapper.
3. Build a special burn-aware pool whose invariant explicitly accounts for the
   transfer burn.

Choice 1 is the cleanest for launch.

## Admission Objects

Every token admission starts with a `TokenAdmissionPacket`.

```json
{
  "schema": "zenodex.token_admission_packet.v1",
  "chain_id": "tau-net-alpha",
  "requested_asset_id": "0x...",
  "symbol": "TOKEN",
  "name": "Example Token",
  "decimals": 18,
  "custody_kind": "native|chain_token|dex_internal|wrapped",
  "transfer_semantics": "exact|fee_on_transfer|rebasing|unknown",
  "issuer_pubkey": "0x...",
  "issuer_signature": "0x...",
  "semantics_evidence": {
    "kind": "tau_spec|host_verifier|wrapper_contract|governance_native",
    "artifact_hash": "0x...",
    "claim": "exact_transfer"
  },
  "risk_disclosures": [
    "metadata_not_chain_final",
    "adapter_semantics_unproven"
  ]
}
```

The packet is not the listing. It is the request. Listing happens only after
the registry gate accepts it.

## Token Classes

### 1. Native Token

Example: `AGRS`.

Rules:

- Asset identity is chain-defined.
- Custody is chain-native.
- DEX support requires either direct native balance integration or a wrapped
  representation.

Recommended launch posture:

- Use native AGRS directly on early testnet if the app bridge safely supports
  balance patches.
- Prefer `wAGRS` for production posture so the DEX sees exact internal balances
  and withdrawal is a separate audited path.

### 2. DEX Internal Token

Example: `ZDEX` if the DEX owns the token ledger before Tau exposes a standard
token contract.

Rules:

- Asset identity is derived by ZenoDEX.
- Supply, transfer, burn, and governance constraints are ZenoDEX state
  transitions.
- Entry must bind to Tau specs or proof-gated receipts.

Recommended launch posture:

- AMM-facing ZDEX should be exact-transfer.
- Deflation happens through buyback/burn from protocol revenue, not through
  transfer taxation inside the pool.

### 3. Wrapped Token

Example: `wAGRS`, `wExternalX`.

Rules:

- Deposit locks the underlying asset in a controlled escrow.
- Mint creates exact-transfer wrapper units in DEX state.
- Withdraw burns wrapper units and releases the underlying asset.

This is the safest generic path while Tau token interfaces are uncertain.

### 4. Chain Token

Future Tau-native custom token once Tau publishes a stable token interface.

Rules:

- The chain token identifier must be stable.
- The DEX adapter must prove or classify transfer semantics.
- Unknown, rebasing, or fee-on-transfer behavior must not be routed through
  ordinary CPMM pools unless wrapped or modeled.

## Admission Workflow

### Step 1: Submit Admission Packet

Anyone may submit a packet. Submission only creates a candidate entry.

Fail-closed checks:

- `asset_id` is 32-byte canonical hex.
- symbol and decimals are present but never used as identity.
- issuer signature binds the exact packet.
- `transfer_semantics` is not `unknown` for AMM admission.

### Step 2: Classify Transfer Semantics

The core question is:

```text
for every transfer(amount), receiver_delta = amount and sender_delta = -amount
```

If true, the token is exact-transfer. If false, the token is either rejected for
standard pools or admitted only through a wrapper/special pool.

Evidence lanes:

- Tau spec proving exact transfer.
- Host verifier against a published token adapter.
- Wrapper contract whose internal accounting is exact.
- Governance-native assertion for chain-native AGRS, later replaced by a formal
  adapter once Tau exposes final semantics.

### Step 3: Registry Proposal

A valid packet becomes a registry proposal.

Minimum governance checks:

- duplicate `asset_id` rejected;
- duplicate symbol allowed only with UI warning and disambiguation, never as
  identity;
- decimals immutable after listing;
- custody kind immutable after listing;
- timelock elapses before activation.

### Step 4: Activate Registry Entry

Activation appends the entry to the token registry and changes the committed
`token_registry_root`.

No pool can reference the token until the registry root containing the token is
active.

### Step 5: Pool Launch Packet

Creating a pool is a separate action:

```json
{
  "schema": "zenodex.pool_launch_packet.v1",
  "asset0": "0x...",
  "asset1": "0x...",
  "curve": "CPMM",
  "initial_deposit0": 1000000000,
  "initial_deposit1": 500000000,
  "fee_bps": 30,
  "launch_guard": {
    "both_assets_listed": true,
    "both_exact_transfer": true,
    "initial_price_acknowledged": true,
    "min_liquidity_locked": true
  }
}
```

Pool launch is not token listing. It requires both assets to already be active
and compatible with the selected pool curve.

## User Experience

### Adding a Token

The user should see a flow like:

1. Paste token identifier or select "create wrapped token".
2. Wallet/DEX resolves token class and displays the registry candidate.
3. UI shows the actual `asset_id`, not only the symbol.
4. UI explains whether the token is exact-transfer, wrapped, or restricted.
5. User submits admission packet.
6. Governance/timelock/proof checks run.
7. Once active, the token appears as "listed" with its registry proof.

The UI must not say "verified token" unless the registry proof is actually
active under the current `token_registry_root`.

### Creating a Pair

The user should see:

1. Select two active listed assets.
2. Select pool curve.
3. UI checks transfer-semantics compatibility.
4. UI shows initial price implied by deposits.
5. User acknowledges initial-price risk.
6. Pool is created only if the create-pool gate passes.

For launch, the first guided path should be:

```text
Create AGRS/ZDEX pool -> deposit AGRS + exact-transfer ZDEX -> receive LP position
```

If ZDEX is not exact-transfer, the guided path becomes:

```text
Create wAGRS/wZDEX pool -> deposit wrapped exact-transfer assets -> receive LP position
```

## What Can Go Wrong

### Fake Token Metadata

Failure shape: attacker creates a token named `AGRS` or `ZDEX`.

Mitigation:

- identity is `asset_id`, never symbol;
- symbol collision warning;
- launch assets hard-pinned in genesis registry.

### Non-Exact Transfer Token In A CPMM

Failure shape: fee-on-transfer or rebasing token causes reserve accounting drift.

Mitigation:

- standard CPMM requires `transfer_semantics = exact`;
- otherwise wrapper or special pool only.

### Premature Pair Creation

Failure shape: users create pools before listing evidence is active.

Mitigation:

- create-pool gate requires active registry root membership for both assets.

### Tau Interface Drift

Failure shape: Tau's eventual token model differs from this design.

Mitigation:

- keep token support behind custody adapters;
- make wrappers the default generic path;
- require adapter evidence before chain tokens become standard-pool assets.

### Governance Capture Or Spam Listings

Failure shape: many worthless or malicious tokens flood the registry.

Mitigation:

- listing bond or fee;
- timelock;
- user-visible risk class;
- optional "untrusted but listed" tier;
- pool creation requires separate liquidity and launch guard.

## Minimal Implementation Plan

1. Keep `AGRS` and `ZDEX` hard-pinned in the launch registry.
2. Decide whether AMM-facing ZDEX is exact-transfer or wrapped.
3. Promote the `TokenAdmissionPacket` schema and checker into the runtime
   admission gate.
4. Promote the `PoolLaunchPacket` schema and checker into the create-pool gate.
5. Add Tau allowlist gate for AGRS/ZDEX.
6. Add proof-gated registry membership for scalable custom tokens.
7. Build UI flow that shows `asset_id`, transfer semantics, and active registry
   proof before submit.
