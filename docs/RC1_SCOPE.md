---
title: RC1_SCOPE
type: note
permalink: autonomous-tau-dex-review/docs/rc1-scope
---

# ZenoDEX RC1 Scope

This document defines the **recommended conservative RC1 surface**.

It exists to prevent accidental overclaiming. The repo contains more code than
should be considered RC1-backed.

Use this together with [RC1_READINESS.md](RC1_READINESS.md).

The seL4-style verified-configuration view for the same conservative boundary is:

- [RC1_VERIFIED_SURFACE_MATRIX.md](RC1_VERIFIED_SURFACE_MATRIX.md)
- [RC1_SUPPORTED_RUNTIME_PATH.md](RC1_SUPPORTED_RUNTIME_PATH.md)

The machine-readable form of this boundary lives in:

- `tools/rc1_scope_manifest.json`

And the executable status/check surface is:

```bash
python3 tools/rc1_readiness.py
python3 tools/rc1_readiness.py --check
python3 tools/render_rc1_supported_runtime_path.py --check
python3 tools/render_rc1_verified_surface_matrix.py --check
```

The candidate runner for the same conservative surface is:

```bash
python3 tools/rc1_candidate.py --plan
python3 tools/rc1_candidate.py
python3 tools/rc1_candidate.py --plan --report-out rc1_candidate_report.json
python3 tools/rc1_candidate.py --plan --campaign-root rc1_candidates --run-id rc1-smoke
python3 tools/rc1_candidate_index.py
python3 tools/rc1_candidate_index.py --format markdown
python3 tools/rc1_candidate_report.py --html-out rc1_candidates.html
```

## RC1 Principle

RC1 should include only surfaces that are:

- clearly bounded
- replay-backed
- covered by the public assurance lanes
- not explicitly experimental
- not explicitly disputed

## In Scope For RC1

### 1. Core spot DEX path

Include the core spot path:

- CPMM swap and pool math
- batch settlement path
- exact-in / exact-out spot semantics that are already part of the core proof and release lanes

This is the primary mechanism surface of RC1.

### 2. Public assurance and release gates

The RC1-backed release commands should be:

```bash
python3 tools/permissionless_assurance.py status
python3 tools/permissionless_assurance.py replay public
python3 tools/permissionless_assurance.py replay critical
python3 tools/permissionless_assurance.py replay full
```

And for the local production gate:

```bash
bash tools/prod_gate.sh
```

These are part of the RC1 contract because they define the replayable release posture.

For the acceptance fuzz lane specifically, RC1 should treat the tiers as:

- fast default hygiene:
  - `bash tools/run_acceptance_tcb_fuzz_gate.sh`
- deep stateful campaign:
  - `bash tools/run_acceptance_tcb_fuzz_gate_deep.sh`
  - `python3 tools/acceptance_tcb_fuzz_campaign.py`

Interpretation:

- the fast lane is the RC1-default acceptance posture used by the release gate
- the deep lane is a stronger stateful discovery campaign that remains replayable, but is too expensive to require on every routine RC1 hygiene run

### 3. TLA / formal public claim surface

The generated public TLA summary is in scope:

- [TLA_CLAIM_SUMMARY.md](TLA_CLAIM_SUMMARY.md)

And the release posture depends on:

```bash
python3 tools/render_tla_claim_summary.py --check
python3 tools/run_tla_models.py --json
```

### Verified surface matrix

The checked RC1 matrix is also part of the release boundary:

```bash
python3 tools/render_rc1_supported_runtime_path.py --check
python3 tools/render_rc1_verified_surface_matrix.py --check
```

These checked artifacts exist to keep the RC1 claim configuration-specific and path-specific rather than prose-only.

### 4. Supported HTTP boundary

The minimal supported HTTP surface for RC1 should be:

- `GET /health`
- `GET /version`
- `POST /api/dex/quote`
- `POST /api/dex/verify_quote_receipt`
- `POST /api/dex/build_settlement_end_to_end_certificate_packet`
- `POST /api/dex/verify_settlement_end_to_end_certificate_packet`

Reason:

- this is a conservative subset of the integration API
- it covers health/version, quote, quote verification, and settlement certificate packeting
- it avoids claiming the entire `api_server.py` surface as RC1-backed

The larger proof-mining, adaptive-routing, repaired-advisory, and many-pool
certificate families should remain outside RC1 unless separately promoted.

### 5. Tau wallet / transport replay lane for zUSD

The public replay lane already exposes a narrow wallet-facing transport surface:

- [ZUSD_TAU_WALLET.md](ZUSD_TAU_WALLET.md)

Recommended RC1-supported wallet CLI:

```bash
python3 tools/zusd_tau_wallet.py transfer ...
python3 tools/zusd_tau_wallet.py mint ...
python3 tools/zusd_tau_wallet.py burn ...
```

Replay lane:

```bash
bash tools/run_zusd_evidence.sh
python3 tools/permissionless_assurance.py replay zusd
```

This is a much cleaner RC1 claim than “generic wallet support.”

### 6. Tau wallet veto / policy guard as a bounded control-plane feature

The sender-scoped Tau wallet veto pattern is in scope as a bounded guard/control feature:

- [TAU_WALLET_O5_GUARD.md](TAU_WALLET_O5_GUARD.md)

But the local demo should be treated as:

- operator/demo support
- not a broad end-user product claim

## Explicitly Out Of Scope For RC1

### 1. Experimental autotrader authority

Out of scope:

- `tools/autotrader_shadow.py` as an authority surface
- `tools/autotrader_live.py` as a general-user live feature
- KRR as an execution authority
- any claim of safe/profitable autonomous trading

These remain advanced experimental tooling only.

### 2. ZenoGraph runtime influence

Out of scope:

- ZenoGraph ranking influence
- ZenoGraph execution influence
- any claim that signed ZenoGraph packs improve live decisions

Current posture:

- advisory-only
- ranking gate still required
- experimental

### 3. Disputed derivatives authorization claims

Out of scope until resolved:

- `funding_rate_market_v1` as an authorization-complete settlement guarantee
- `curve_selection_market_v1` as an authorization-complete settlement guarantee

Do not market these as RC1-backed guarantees while they remain disputed.

### 4. Broad `api_server.py` surface

Out of scope unless separately promoted:

- proof-mining status endpoints
- repaired advisory exact-out endpoints
- bounded-advisory / certified-advisory families
- many-pool exact-out research endpoints
- heavy suggestion endpoints
- perps and zUSD API families as broad product claims

The repo can contain these without them being part of RC1.

### 5. Confidential / TEE / SMPC / alpha-only extensions

Out of scope:

- confidential extensions
- alpha-only sealed-bid or privacy surfaces
- research-only composite experiments

## RC1-Supported Commands

The recommended RC1 command list is:

```bash
python3 tools/permissionless_assurance.py status
python3 tools/permissionless_assurance.py replay public
python3 tools/permissionless_assurance.py replay critical
python3 tools/permissionless_assurance.py replay full
python3 tools/permissionless_assurance.py replay zusd
bash tools/prod_gate.sh
python3 tools/render_rc1_supported_runtime_path.py --check
python3 tools/render_rc1_verified_surface_matrix.py --check
python3 tools/render_tla_claim_summary.py --check
python3 tools/run_tla_models.py --json
python3 tools/zusd_tau_wallet.py transfer ...
python3 tools/zusd_tau_wallet.py mint ...
python3 tools/zusd_tau_wallet.py burn ...
```

Anything beyond this list should not be described as RC1-backed unless it is
explicitly promoted into scope.

## Release Language For RC1

Safe release language:

- replay-backed
- bounded
- fail-closed
- supported spot DEX path
- public assurance surface
- zUSD wallet/transport replay lane

Unsafe release language:

- production-complete autonomous trading
- authorization-complete derivatives guarantees
- AI-managed investing
- full API surface supported
- all research endpoints production-ready

## Promotion Rule

A surface moves from “present in repo” to “RC1-backed” only when all are true:

1. it is named here or in a future RC scope update
2. it has a replay/check command
3. it is not explicitly experimental or disputed
4. it has a clear fail-closed story
5. it does not depend on unresolved research claims
