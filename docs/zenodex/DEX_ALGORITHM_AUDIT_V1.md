# ZenoDEX Algorithm Audit v1

## Purpose

This document is the single reviewer-facing entry point for auditing the main
algorithms and assurance boundaries of ZenoDEX.

It is not an exhaustive dump of every predicate in every file. Its job is
sharper:

- state the core formulas a reviewer must inspect
- give the standard reading for each formula
- identify the main source artifacts
- separate what is proved, implemented, replay-gated, and externally assumed
- give a repeatable audit method

If a reviewer can work through this document carefully, they should be able to
peer review the architectural spine of the DEX without first reconstructing the
repo from scratch.

## Status Legend

- `PROVED`: backed by a mechanized proof artifact in-repo
- `TAU_CONTRACT`: backed by an inspected Tau guard / contract
- `TLA_SHADOW`: backed by an inspected TLA+ model or invariant
- `ESSO_GUARD`: backed by an ESSO verification artifact
- `IMPLEMENTED`: backed by executable runtime code
- `REPLAY_GATED`: backed by a published checker or replay command
- `EXTERNAL_ASSUMPTION`: required from infrastructure outside this repository

## Standard Readings

Use the following readings consistently:

```text
:=    is defined as
->    implies
<->   iff
∧     and
∨     or
¬     not
∀     for all
∃     there exists
Σ ⊨ P  Sigma semantically entails P
```

For quantified objects, use "such that" in the standard way:

```text
∃x. P(x)
```

reads as:

- there exists an `x` such that `P(x)`

For semantic entailment, the standard countermodel reading is:

```text
Σ ⊨ P
```

reads as:

- Sigma entails `P`
- equivalently: there is no model `M` in the model class under discussion such
  that `M ⊨ Σ` and `M ⊭ P`

## How To Audit With This Document

For each algorithm below:

1. Read the formula first.
2. Read the standard reading immediately after it.
3. Inspect the cited source artifact.
4. Check whether the status is `PROVED`, `IMPLEMENTED`, `REPLAY_GATED`, or only
   `EXTERNAL_ASSUMPTION`.
5. Ask:
   - what value or state transition does this formula control?
   - what bad state does it rule out?
   - what remains outside the proof or replay boundary?
6. If the artifact is release-facing, run the cited checker or replay command.

The audit is complete only when the reviewer can say, for each entry:

- what the formula means
- what the formula controls
- what evidence class backs it
- what failures still remain possible

## Audit Entry 1: Spot Swap Arithmetic And Reserve Safety

**Status**

- `IMPLEMENTED`
- `TAU_CONTRACT`

**Primary sources**

- `src/core/cpmm.py`
- `src/tau_specs/recommended/reserve_invariant_guard_v1.tau`

**Formula**

```text
fee := ceil(amount_in * fee_bps / 10_000)
net_in := amount_in - fee
amount_out := floor(reserve_out * net_in / (reserve_in + net_in))

reserve_in_after := reserve_in + amount_in
reserve_out_after := reserve_out - amount_out

K_before := reserve_in * reserve_out
K_after := reserve_in_after * reserve_out_after

ReserveInvariantOK := K_after >= K_before
```

**Standard reading**

- `fee` is defined as the ceiling fee charged on the input amount.
- `amount_out` is defined as the floored constant-product output.
- `ReserveInvariantOK` is defined as `K_after` is greater than or equal to
  `K_before`.

**Audit question**

- Does the implementation preserve the constant-product monotonicity claim under
  the declared integer semantics and Tau guard preconditions?

**Failure to rule out**

```text
¬ReserveInvariantOK -> reject
```

reads as:

- not `ReserveInvariantOK` implies reject

## Audit Entry 2: Canonical Winner Selection

**Status**

- `PROVED`
- `REPLAY_GATED`

**Primary sources**

- `docs/zenodex/SHAPE_V1.md`
- `lean-mathlib/Proofs/ZenoDEXUniqueCanonicalWinnerEverywhere.lean`

**Formula**

```text
winner := argmin(key, candidates)
```

**Standard reading**

- `winner` is defined as the candidate with minimal `key`

The finite uniqueness law is:

```text
∀ finite nonempty S.
  ∃! w ∈ S.
    ∀ x ∈ S, key(w) <= key(x)
```

**Standard reading**

- for every finite nonempty candidate set `S`, there exists exactly one winner
  `w` in `S` such that every candidate `x` in `S` has key at least `key(w)`

**Audit question**

- Is the key total?
- Is the winner relation fail-closed?
- Is the claimed domain bounded and explicit?

**Why this matters**

This is the main determinism primitive in the repo. Routing, batch clearing,
and certificate verification all become suspect if the canonical key is not
total.

## Audit Entry 3: Exact-In Canonical Route Lane

**Status**

- `PROVED`
- `IMPLEMENTED`
- `REPLAY_GATED`

**Primary sources**

- `src/integration/exact_in_route_certificate.py`
- `lean-mathlib/Proofs/ZenoDEXUniqueCanonicalWinnerEverywhere.lean`
- `lean-mathlib/Proofs/ZenoDEXExactInTrueKeyWinner.lean`
- `lean-mathlib/Proofs/ZenoDEXExactInRouteRankProjectionPacket.lean`
- `lean-mathlib/Proofs/ZenoDEXExactInRouteTrueKeyInterpretationPacket.lean`
- `docs/zenodex/SHAPE_V1.md`

**Formula**

```text
ExactInKey(candidate) := (routeKeyRank, candidateIndex)
winner := argmin(ExactInKey, candidates)
```

The main interpretation-packet shell is:

```text
packet_ok
  := rank_projection_packet_ok
   ∧ winner_index_in_range
   ∧ candidate_indices_match_stream
   ∧ candidate_route_keys_match_quotes
   ∧ winner_matches_certificate_candidate
   ∧ winner_true_key_minimal
```

**Standard reading**

- `ExactInKey` is defined as the lexicographic pair
  `(routeKeyRank, candidateIndex)`
- `winner` is defined as the candidate with minimal exact-in key
- `packet_ok` is defined as rank projection success and winner index in range
  and candidate/stream alignment and route-key agreement and certificate/winner
  agreement and true-key minimality

**Audit question**

- Does the exact-in certificate lane actually prove that the emitted winner is
  the minimal `(routeKeyRank, candidateIndex)` candidate over the admitted
  stream?

**Why this matters**

The exact-in lane is one of the promoted optimizer/certificate surfaces in
`SHAPE_V1`. A single-document reviewer entry is incomplete if it omits this
route canonicality path.

## Audit Entry 4: Batch Auction Canonical Objective

**Status**

- `PROVED`
- `IMPLEMENTED`

**Primary sources**

- `src/core/batch_clearing.py`
- `lean-mathlib/Proofs/BatchAuctionCanonical.lean`

**Formula**

```text
Key := (Volume^op ×_lex Surplus^op) ×_lex Order
```

Expanded comparison law:

```text
key(v1, s1, o1) <= key(v2, s2, o2)
<-> (v2 < v1)
 ∨ (v1 = v2 ∧ ((s2 < s1) ∨ (s1 = s2 ∧ o1 <= o2)))
```

Bounded runtime scope law:

```text
bounded_ab_mode
  := same_direction_batch
   ∧ batch_size <= 7
   ∧ post_swap_ordering = optimal_ab_bounded

bounded_ab_mode -> runtime_uses_optimal_ab_bounded
¬bounded_ab_mode -> no_blanket_ab_optimality_claim
```

**Standard reading**

- the batch key is defined as volume in descending order, then surplus in
  descending order, then order in ascending lexicographic order
- the comparison law says higher volume wins; among equal volume, higher
  surplus wins; among equal volume and surplus, smaller order wins
- `bounded_ab_mode` is defined as the same-direction bounded batch lane with at
  most seven swaps and explicit `optimal_ab_bounded` ordering selected
- `bounded_ab_mode` implies the runtime uses the exact bounded `A/B/lex` path
- not `bounded_ab_mode` implies there is no blanket `A/B/lex` optimality claim
  for every batch-clearing path

**Audit question**

- Does the reviewer distinguish the proved bounded same-direction `A/B/lex`
  lane from the broader runtime paths that can still fall back to other
  orderings?

**Why this matters**

This is the core anti-ambiguity rule for batched execution. If this order
changes, the fairness and canonicality story changes. But it must be scoped
honestly to the bounded mode where that statement is actually proved and wired.

## Audit Entry 5: Exact-Out Audited-Domain Canonical Quote

**Status**

- `IMPLEMENTED`
- `REPLAY_GATED`

**Primary sources**

- `src/kernels/python/exact_out_many_pool_canonical_domain_v1.py`
- `src/integration/exact_out_route_certificate.py`
- `docs/zenodex/SHAPE_V1.md`

**Formula**

```text
canonical_quote := argmin(canonical_key, candidate_quotes)
```

**Standard reading**

- `canonical_quote` is defined as the quote with minimal canonical key over the
  emitted audited-domain candidate set

**Important scope law**

```text
audited_domain_only -> no_global_generator_completeness_claim
```

**Standard reading**

- audited-domain-only support implies there is no claim of unrestricted global
  generator completeness

**Audit question**

- Is the claimed exact-out result explicitly bounded to the repaired audited
  lane, rather than overstated as global completeness?

## Audit Entry 6: Settlement End-To-End Certificate Gate

**Status**

- `PROVED`
- `ESSO_GUARD`
- `IMPLEMENTED`
- `REPLAY_GATED`

**Primary sources**

- `src/integration/settlement_end_to_end_certificate_packet.py`
- `src/kernels/dex/settlement_end_to_end_certificate_packet_v1.yaml`
- `lean-mathlib/Proofs/ZenoDEXSettlementEndToEndCertificatePacket.lean`

**Formula**

```text
packet_ok
  := strong_certificate_ok
   ∧ feature_extension_packet_ok
   ∧ module_bundle_ok
   ∧ full_price_rails_ok
   ∧ value_packet_ok
```

**Standard reading**

- `packet_ok` is defined as strong certificate success and feature-extension
  packet success and module-bundle success and full-price-rails success and
  nested value-packet success

**Audit question**

- Is settlement admission exactly the conjunction above, with no hidden
  side-channel acceptance path?

**Failure to rule out**

```text
¬packet_ok -> reject
```

reads as:

- not `packet_ok` implies reject

## Audit Entry 7: Perps Funding Rule

**Status**

- `IMPLEMENTED`

**Primary source**

- `src/core/perp_v2/funding_rule.py`

**Formula**

```text
diff := mark_price_e8 - index_price_e8
basis_bps := floor(abs(diff) * 10_000 / index_price_e8)
mag := min(funding_cap_bps, basis_bps)

rate_bps
  := mag    if diff >= 0
   else -mag
```

**Standard reading**

- `basis_bps` is defined as the absolute mark/index basis in basis points
- `rate_bps` is defined as the signed capped basis

**Audit question**

- Does the rule remain deterministic, integer-only, and capped by
  `funding_cap_bps` on every path?

**Why this matters**

Funding is small in code size but large in mechanism effect. A sign or cap bug
here is economically material.

## Audit Entry 8: zUSD Oracle Pending Gate

**Status**

- `IMPLEMENTED`
- `TAU_CONTRACT`

**Primary sources**

- `src/integration/zusd_oracle_contracts.py`
- `src/tau_specs/recommended/zusd_cross_module_oracle_sync_gate_v1.tau`

**Formula**

```text
pending_eq := oracle_seen ∧ price_e8 > 0 ∧ price_pending_e8 > 0 ∧ price_pending_e8 = price_e8
price_pos := oracle_seen ∧ price_e8 > 0 ∧ price_pending_e8 > 0
fresh := oracle_seen ∧ abs(now_epoch - oracle_last_update_epoch) <= max_staleness_epochs

env_ok := oracle_seen ∧ price_pos ∧ pending_eq ∧ fresh
risky_ops_allowed := env_ok ∧ tcr_ok
action_allowed := ¬risky_requested ∨ risky_ops_allowed
```

**Standard reading**

- `env_ok` is defined as oracle seen and positive prices and pending price equal
  to committed price and freshness
- `action_allowed` is defined as either risky action was not requested or risky
  operations are allowed

**Audit question**

- Does every risky zUSD action remain fail-closed on stale, missing, or
  diverged oracle state?

## Audit Entry 9: Tau Provenance Loader

**Status**

- `IMPLEMENTED`
- `ESSO_GUARD`
- `TLA_SHADOW`
- `PROVED`
- `EXTERNAL_ASSUMPTION`

**Primary sources**

- `src/integration/tau_net_client.py`
- `src/integration/settlement_signer_registry.py`
- `docs/zenodex/TAU_STATE_APP_HASH_PROVENANCE_FORMALISM_V1.md`
- `docs/zenodex/TAU_STATE_APP_HASH_REFINEMENT_CHAIN_V1.md`
- `docs/zenodex/TAU_TCP_VIEW_CONTRACT_V1.md`

**Formula**

```text
BridgePayloadReady
  := exec_req
   ∧ bridge_payload_present
   ∧ request_binding_ok
   ∧ anchor_binding_ok
   ∧ policy_binding_ok

BaselineProvenanceOK
  := state_proof_present
   ∧ state_hash_present
   ∧ state_proof_stable
   ∧ app_state_present
   ∧ app_state_stable
   ∧ app_state_hash_ok

StrongTauStateBindingOK
  := tau_state_transport_available
   ∧ tau_state_present
   ∧ tau_state_stable
   ∧ tau_state_hash_matches_proof
   ∧ tau_state_app_hash_present
   ∧ tau_state_app_hash_matches_app_state

LoaderOK
  := BridgePayloadReady
   ∧ BaselineProvenanceOK
   ∧ (¬strong_binding_required ∨ StrongTauStateBindingOK)
```

**Standard reading**

- `LoaderOK` is defined as bridge payload ready and baseline provenance OK and
  either strong binding is not required or strong Tau-state binding is OK

Equivalent implication form:

```text
strong_binding_required -> StrongTauStateBindingOK
```

reads as:

- strong binding required implies strong Tau-state binding OK

**Audit question**

- Does the loader reject every path where strong binding is required but the
  Tau-state/app-hash relation is missing, drifted, unstable, or silently
  downgraded?

**Disaster paths to keep in mind**

```text
BridgePayloadReady ∧ BaselineProvenanceOK ∧ strong_binding_required ∧ ¬StrongTauStateBindingOK ∧ settlement_admitted
```

reads as:

- bridge payload ready and baseline provenance OK and strong binding required
  and not strong Tau-state binding OK and settlement admitted

That is precisely the path the current formal bundle is designed to rule out.

## Audit Entry 10: External Assumption Boundary

**Status**

- `EXTERNAL_ASSUMPTION`
- `REPLAY_GATED` for the in-repo side

**Primary sources**

- `docs/zenodex/EXTERNAL_ASSUMPTION_BOUNDARY_V1.md`
- `docs/ASSURANCE.md`

**Formula**

```text
HostArtifactsOK
  := LoaderOK
   ∧ TransportRefinementOK
   ∧ ViewContractsOK

ExternalTauContractOK
  := upstream_tau_node_exposes_expected_command_surface
   ∧ upstream_tau_node_emits_payloads satisfying typed view contracts
   ∧ upstream_tau_node_does_not silently downgrade required provenance lanes

ConditionalCorrectness
  := HostArtifactsOK ∧ ExternalTauContractOK
   -> AdmissionBehaviorMatchesPublishedContract
```

**Standard reading**

- `ConditionalCorrectness` is defined as `HostArtifactsOK` and
  `ExternalTauContractOK` imply admission behavior matches the published
  contract

Fail-closed corollary:

```text
¬ExternalTauContractOK
  -> reject
   ∨ disable_stronger_path
   ∨ narrow_public_claim
```

**Standard reading**

- not `ExternalTauContractOK` implies reject or disable the stronger path or
  narrow the public claim

**Audit question**

- Is the public assurance statement conditional where it must be conditional,
  rather than pretending that external Tau Testnet internals are proved in this
  repo?

## Release-Lane Audit Commands

Minimum review commands for the current release-facing spine:

```bash
python3 tools/check_shape_v1_ratchet.py
python3 tools/permissionless_assurance.py replay release
bash tools/run_tau_provenance_formal_gate.sh
```

Use those together with the algorithm-specific focused test or proof commands
listed in `docs/zenodex/SHAPE_V1.md`.

## Reviewer Exit Criteria

A reviewer should be able to answer all of the following after reading this
document and checking the cited artifacts:

1. What is the canonical winner relation for each audited optimization lane?
2. What is the exact settlement admission conjunction?
3. What is the exact Tau provenance acceptance law?
4. Which parts are formally backed in-repo?
5. Which parts are only replay-gated?
6. Which parts remain external assumptions?

If any of those answers are unclear, the audit is incomplete.
