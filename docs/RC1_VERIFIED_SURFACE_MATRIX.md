---
title: RC2_VERIFIED_SURFACE_MATRIX
type: note
permalink: autonomous-tau-dex-review/docs/rc1-verified-surface-matrix
---

# RC2 Candidate Verified Surface Matrix

<!-- Generated from tools/rc1_scope_manifest.json, docs/claims_registry.yaml, and tools/permissionless_assurance.py lane inventory. -->

Historical release baseline: `RC1` already shipped. This file keeps the `RC1_*` path for compatibility, but the live candidate label is `RC2`.

This matrix defines the exact conservative RC2 candidate claim boundary for ZenoDEX.

```text
RC2CandidateOK := CleanTree ∧ ScopeFrozen ∧ ReplayGreen ∧ ExclusionsHonest
```

Standard reading: RC2 is honest only when the tree is clean, the supported surface is explicit, the replay lanes are green, and excluded or disputed surfaces stay excluded.

Practical consequence: this matrix is configuration-specific. It is not a claim about every file in the repo.

## Included Surfaces

| Surface | Authority | Backing lanes | Primary check |
| --- | --- | --- | --- |
| Core spot DEX path | `consensus/runtime` | `kernel-assurance` (READY)<br>`spot-proof` (READY)<br>`spot-evidence` (READY)<br>`tau-runtime`<br>`critical` (READY)<br>`release` (READY) | `python3 tools/permissionless_assurance.py replay public` |
| Public assurance and release replay surface | `release/replay` | `kernel-assurance` (READY)<br>`spot-proof` (READY)<br>`spot-evidence` (READY)<br>`derivatives` (READY)<br>`perps` (READY)<br>`tau-runtime`<br>`zusd`<br>`critical` (READY)<br>`release` (READY) | `python3 tools/permissionless_assurance.py status` |
| Bounded TLA claim surface | `public formal claim` | `release` (READY) | `python3 tools/run_tla_models.py --json` |
| Supported HTTP boundary | `runtime ingress` | `critical` (READY)<br>`release` (READY) | `python3 tools/rc1_readiness.py` |
| zUSD Tau wallet and transport replay lane | `wallet/transport` | `zusd`<br>`release` (READY) | `python3 tools/permissionless_assurance.py replay zusd` |
| Tau wallet veto / O5 policy guard | `bounded control-plane guard` | `zusd`<br>`release` (READY) | `python3 tools/permissionless_assurance.py replay zusd` |

## Surface Details

### Core spot DEX path

- Authority: `consensus/runtime`
- Claim class: bounded spot mechanism surface
- Docs:
  - `docs/RC1_SCOPE.md`
  - `docs/RC1_READINESS.md`
  - `docs/PUBLIC_ASSURANCE_REPLAY.md`
- Runtime and artifact paths:
  - `src/core/amm_dispatch.py`
  - `src/core/batch_clearing.py`
  - `generated/batch_auction_settler_v1/python_ref/batch_auction_settler_v1_ref.py`
- Backing lanes:
  - `kernel-assurance`: READY
    Re-run the manifest-backed kernel assurance corpus and solver checks.
  - `spot-proof`: READY
    Rebuild the spot proof artifacts, then pin-check the manifest.
  - `spot-evidence`: READY
    Replay the spot functional-core tests and spot-kernel verify-multi checks.
  - `tau-runtime`
  - `critical`: READY
    Run the publishable critical quality gate with branch coverage and static checks.
  - `release`: READY
    Run the full release gate, including Tau, proof, evidence, and audit lanes.
- Primary commands:
  - `python3 tools/permissionless_assurance.py replay public`
  - `python3 tools/permissionless_assurance.py replay critical`
  - `python3 tools/permissionless_assurance.py replay full`
- Notes:
  - This is the primary value-moving candidate mechanism surface.
  - Only the bounded spot path is included, not every core module in the repo.

### Public assurance and release replay surface

- Authority: `release/replay`
- Claim class: publishable proofboard and replay contract
- Docs:
  - `docs/ASSURANCE_RELEASE_SNAPSHOT.md`
  - `docs/PUBLIC_ASSURANCE_REPLAY.md`
  - `docs/RC1_SCOPE.md`
- Runtime and artifact paths:
  - `docs/tau_supported_runtime_contract.json`
  - `tools/check_tau_supported_runtime_subset.py`
  - `tools/permissionless_assurance.py`
  - `tools/run_critical_quality_gate.sh`
  - `tools/run_release_gate.sh`
  - `tools/run_spot_evidence.sh`
  - `tools/run_spot_proof_assurance_gate.sh`
  - `tools/run_derivatives_evidence.sh`
  - `tools/run_perps_evidence.sh`
  - `tools/run_zusd_evidence.sh`
- Backing lanes:
  - `kernel-assurance`: READY
    Re-run the manifest-backed kernel assurance corpus and solver checks.
  - `spot-proof`: READY
    Rebuild the spot proof artifacts, then pin-check the manifest.
  - `spot-evidence`: READY
    Replay the spot functional-core tests and spot-kernel verify-multi checks.
  - `derivatives`: READY
    Rebuild the derivatives evidence lane, then pin-check the manifest.
  - `perps`: READY
    Replay the perps functional-core tests, micro-gate assurances, kernel verify-multi checks, and Lean safety proofs.
  - `tau-runtime`
  - `zusd`
  - `critical`: READY
    Run the publishable critical quality gate with branch coverage and static checks.
  - `release`: READY
    Run the full release gate, including Tau, proof, evidence, and audit lanes.
- Primary commands:
  - `python3 tools/permissionless_assurance.py status`
  - `python3 tools/permissionless_assurance.py replay public`
  - `python3 tools/permissionless_assurance.py replay critical`
  - `python3 tools/permissionless_assurance.py replay full`
  - `python3 tools/check_tau_supported_runtime_subset.py`
- Notes:
  - This is the repo-visible replay contract for a fresh clone.
  - The release claim is only as strong as these tracked replay lanes.
  - The supported Tau runtime subset is part of the replay contract for the narrow runtime-facing boundary.

### Bounded TLA claim surface

- Authority: `public formal claim`
- Claim class: bounded model-check summary
- Docs:
  - `docs/TLA_CLAIM_SUMMARY.md`
  - `docs/RC1_SCOPE.md`
- Runtime and artifact paths:
  - `formal/tla/README.md`
  - `tools/run_tla_models.py`
  - `tools/render_tla_claim_summary.py`
- Backing lanes:
  - `release`: READY
    Run the full release gate, including Tau, proof, evidence, and audit lanes.
- Primary commands:
  - `python3 tools/run_tla_models.py --json`
  - `python3 tools/render_tla_claim_summary.py --check`
- Notes:
  - These are bounded TLC model checks, not unbounded proofs.
  - The generated summary must stay synchronized with the claims registry and live TLC configs.

### Supported HTTP boundary

- Authority: `runtime ingress`
- Claim class: narrow supported API subset
- Docs:
  - `docs/RC1_SCOPE.md`
- Runtime and artifact paths:
  - `src/integration/api_server.py`
- Supported HTTP routes:
  - `/health`
  - `/version`
  - `/api/dex/quote`
  - `/api/dex/verify_quote_receipt`
  - `/api/dex/build_settlement_end_to_end_certificate_packet`
  - `/api/dex/verify_settlement_end_to_end_certificate_packet`
- Backing lanes:
  - `critical`: READY
    Run the publishable critical quality gate with branch coverage and static checks.
  - `release`: READY
    Run the full release gate, including Tau, proof, evidence, and audit lanes.
- Primary commands:
  - `python3 tools/rc1_readiness.py`
  - `python3 tools/rc1_readiness.py --check`
- Notes:
  - Only the listed quote and settlement-certificate routes are candidate-backed.
  - The broader API server remains out of scope unless separately promoted.

### zUSD Tau wallet and transport replay lane

- Authority: `wallet/transport`
- Claim class: narrow wallet-facing transfer and mint/burn contract
- Docs:
  - `docs/ZUSD_TAU_WALLET.md`
  - `docs/RC1_SCOPE.md`
- Runtime and artifact paths:
  - `tools/zusd_tau_wallet.py`
  - `src/integration/zusd_tau_token.py`
  - `src/tau_specs/recommended/protocol_token_v1.tau`
  - `src/tau_specs/recommended/zusd_transfer_guard_v1.tau`
- Backing lanes:
  - `zusd`
  - `release`: READY
    Run the full release gate, including Tau, proof, evidence, and audit lanes.
- Primary commands:
  - `python3 tools/permissionless_assurance.py replay zusd`
  - `python3 tools/zusd_tau_wallet.py transfer ...`
  - `python3 tools/zusd_tau_wallet.py mint ...`
  - `python3 tools/zusd_tau_wallet.py burn ...`
- Notes:
  - This is intentionally narrower than a claim of generic wallet support.

### Tau wallet veto / O5 policy guard

- Authority: `bounded control-plane guard`
- Claim class: sender-scoped veto and policy guard
- Docs:
  - `docs/TAU_WALLET_O5_GUARD.md`
  - `docs/RC1_SCOPE.md`
- Runtime and artifact paths:
  - `docs/TAU_WALLET_O5_GUARD.md`
- Backing lanes:
  - `zusd`
  - `release`: READY
    Run the full release gate, including Tau, proof, evidence, and audit lanes.
- Primary commands:
  - `python3 tools/permissionless_assurance.py replay zusd`
- Notes:
  - This is in scope only as a bounded operator and control-plane feature.
  - It is not a broad end-user wallet product claim.

## Excluded Claims That Must Stay Out Of RC2


| Claim | Registry status |
| --- | --- |
| `smt:funding_rate_market_v1:inductive_z3_cvc5` | `disputed` |
| `smt:curve_selection_market_v1:inductive_z3_cvc5` | `disputed` |

## Explicitly Excluded Surfaces

| Surface | Reason | Paths / claims |
| --- | --- | --- |
| Experimental autotrader authority | Autotrader and KRR remain experimental and non-authoritative for the active candidate. | `tools/autotrader_shadow.py`<br>`tools/autotrader_live.py` |
| ZenoGraph runtime influence | ZenoGraph ranking and execution influence remain advisory-only. | `tools/zenograph_autotrader_ranking_stage.py`<br>`tools/zenograph_autotrader_ranking_review_bundle.py` |
| Disputed derivatives authorization claims | These claims remain disputed and must stay outside the active candidate authorization surface until resolved. | `smt:funding_rate_market_v1:inductive_z3_cvc5` (disputed)<br>`smt:curve_selection_market_v1:inductive_z3_cvc5` (disputed) |
| Broad api_server surface | Only the narrow supported HTTP subset is candidate-backed. | `src/integration/api_server.py` |
| Confidential and alpha-only extensions | Confidential, TEE, sealed-bid, and other alpha-only surfaces remain out of scope for the active candidate. | `src/core/confidential_extension_receipts.py`<br>`src/core/confidential_extension_live_admission.py` |

## Release Hooks

- `python3 tools/rc1_readiness.py`
- `python3 tools/rc1_readiness.py --check`
- `python3 tools/render_rc1_verified_surface_matrix.py --check`

These checks are intentionally narrower than the full repo. They exist to keep the RC2 claim specific and auditable.

