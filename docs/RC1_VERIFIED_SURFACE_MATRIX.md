---
title: RC1_VERIFIED_SURFACE_MATRIX
type: note
permalink: autonomous-tau-dex-review/docs/rc1-verified-surface-matrix
---

# RC1 Verified Surface Matrix

<!-- Generated from tools/rc1_scope_manifest.json, docs/claims_registry.yaml, and tools/permissionless_assurance.py lane inventory. -->

This matrix defines the exact conservative RC1 claim boundary for ZenoDEX.

```text
RC1ClaimOK := CleanTree ∧ ScopeFrozen ∧ ReplayGreen ∧ ExclusionsHonest
```

Standard reading: RC1 is honest only when the tree is clean, the supported surface is explicit, the replay lanes are green, and excluded or disputed surfaces stay excluded.

Practical consequence: this matrix is configuration-specific. It is not a claim about every file in the repo.

## Included Surfaces

| Surface | Authority | Backing lanes | Primary check |
| --- | --- | --- | --- |
| Core spot DEX path | `consensus/runtime` | `kernel-assurance` (READY)<br>`spot-proof` (READY)<br>`spot-evidence` (READY)<br>`critical` (READY)<br>`release` (READY) | `python3 tools/permissionless_assurance.py replay public` |
| Public assurance and release replay surface | `release/replay` | `kernel-assurance` (READY)<br>`spot-proof` (READY)<br>`spot-evidence` (READY)<br>`derivatives` (READY)<br>`perps` (READY)<br>`critical` (READY)<br>`release` (READY) | `python3 tools/permissionless_assurance.py status` |
| Bounded TLA claim surface | `public formal claim` | `release` (READY) | `python3 tools/run_tla_models.py --json` |
| Supported HTTP boundary | `runtime ingress` | `critical` (READY)<br>`release` (READY) | `python3 tools/permissionless_assurance.py replay critical` |

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
  - `critical`: READY
    Run the publishable critical quality gate with branch coverage and static checks.
  - `release`: READY
    Run the full release gate, including Tau, proof, evidence, and audit lanes.
- Primary commands:
  - `python3 tools/permissionless_assurance.py replay public`
  - `python3 tools/permissionless_assurance.py replay critical`
  - `python3 tools/permissionless_assurance.py replay full`
- Notes:
  - This is the primary value-moving RC1 mechanism surface.
  - Only the bounded spot path is included, not every core module in the repo.

### Public assurance and release replay surface

- Authority: `release/replay`
- Claim class: publishable proofboard and replay contract
- Docs:
  - `docs/PUBLIC_ASSURANCE_REPLAY.md`
  - `docs/RC1_SCOPE.md`
- Runtime and artifact paths:
  - `tools/permissionless_assurance.py`
  - `tools/run_critical_quality_gate.sh`
  - `tools/run_release_gate.sh`
  - `tools/run_spot_evidence.sh`
  - `tools/run_spot_proof_assurance_gate.sh`
  - `tools/run_derivatives_evidence.sh`
  - `tools/run_perps_evidence.sh`
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
  - `critical`: READY
    Run the publishable critical quality gate with branch coverage and static checks.
  - `release`: READY
    Run the full release gate, including Tau, proof, evidence, and audit lanes.
- Primary commands:
  - `python3 tools/permissionless_assurance.py status`
  - `python3 tools/permissionless_assurance.py replay public`
  - `python3 tools/permissionless_assurance.py replay critical`
  - `python3 tools/permissionless_assurance.py replay full`
- Notes:
  - This is the repo-visible replay contract for a clean checkout plus the documented external toolchains.
  - The release claim is only as strong as these tracked replay lanes.

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
  - `python3 tools/permissionless_assurance.py replay critical`
  - `python3 tools/permissionless_assurance.py replay full`
- Notes:
  - Only the listed quote and settlement-certificate routes are RC1-backed.
  - The broader API server remains out of scope unless separately promoted.

### Tau wallet veto / O5 policy guard

- Status: not part of the current public RC1 replay contract.
- Notes:
  - related wallet/policy materials may exist in the repo
  - the runnable lane and its full gate family are not published as part of the conservative RC1 surface
  - do not describe this as RC1-backed until the full transport slice is published coherently

## Excluded Claims That Must Stay Out Of RC1

| Claim | Registry status |
| --- | --- |
| `smt:funding_rate_market_v1:inductive_z3_cvc5` | `disputed` |
| `smt:curve_selection_market_v1:inductive_z3_cvc5` | `disputed` |

## Explicitly Excluded Surfaces

| Surface | Reason | Paths / claims |
| --- | --- | --- |
| Experimental autotrader authority | Autotrader and experimental advisory engines remain experimental and non-authoritative for RC1. | `tools/autotrader_shadow.py`<br>`tools/autotrader_live.py` |
| Experimental ranking runtime influence | Experimental ranking and execution influence remain advisory-only. | experimental ranking-stage tooling |
| Disputed derivatives authorization claims | These claims remain disputed and must stay outside the RC1 authorization surface until resolved. | `smt:funding_rate_market_v1:inductive_z3_cvc5` (disputed)<br>`smt:curve_selection_market_v1:inductive_z3_cvc5` (disputed) |
| Broad api_server surface | Only the narrow supported HTTP subset is RC1-backed. | `src/integration/api_server.py` |
| Confidential and alpha-only extensions | Confidential, TEE, sealed-bid, and other alpha-only surfaces remain out of scope for RC1. | `src/core/confidential_extension_receipts.py`<br>`src/core/confidential_extension_live_admission.py` |

## Release Hooks

- `python3 tools/permissionless_assurance.py status`
- `python3 tools/permissionless_assurance.py replay critical`
- `python3 tools/permissionless_assurance.py replay full`
- `python3 tools/render_tla_claim_summary.py --check`

These checks are intentionally narrower than the full repo. They exist to keep the RC1 claim specific and auditable.

