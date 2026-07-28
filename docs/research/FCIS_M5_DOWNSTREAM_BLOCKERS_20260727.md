# FCIS M5 downstream blocker ledger

Status: `BLOCKED`
Mount status: `UNMOUNTED`
Audited source: `99da842b6606e6f10ce8ab6b2c94c2d36f2e169f`
Current checkpoint: `M5-P4B4`, exact strong-settlement validator
Normalized audit inputs: two independent code-audit results

The machine-readable companion is
`docs/research/FCIS_M5_DOWNSTREAM_BLOCKERS_20260727.json`. It is the
authoritative inventory for checkpoint IDs and closed status codes.

## Scope

This ledger preserves the boundary between the current P4B4 work and the
downstream safety repairs. P4B4 remains an unmounted exact-validator
checkpoint. It does not close fee denomination, fee custody, production nonce
policy, evidence recomputation, history continuity, nullifier enforcement,
context authority, proof recomputation, or zUSD supply-cap correctness.

The proof-gate finding has corrected wording:

```text
Demonstrated:
  expected-valid settlement proof material crashes or rejects during
  recomputation.

Not demonstrated:
  a stale or mismatched proof is unsoundly accepted.
```

No finding in this ledger supports release or mount readiness.

## Closed status vocabulary

| Field | Allowed values |
| --- | --- |
| Finding status | `CONFIRMED_DEFECT`, `CONFIRMED_ENFORCEMENT_GAP`, `CONFIRMED_GATE_FAILURE`, `CONFIRMED_SECURITY_PREMISE_GAP` |
| Exploitability | `DIRECT_COUNTEREXAMPLE`, `CONDITIONAL_ON_MOUNT_OR_POLICY`, `ENFORCEMENT_GAP_WITHOUT_LIVE_EXPLOIT_CLAIM`, `GATE_FAILURE_WITHOUT_UNSOUND_ACCEPTANCE_CLAIM` |
| Checkpoint status | `REQUIRED_NOT_STARTED` |
| Mount status | `UNMOUNTED` |
| Claim status | `BLOCKED` |

## Required checkpoint order

| Sequence | Checkpoint | Required closure | Finding IDs |
| ---: | --- | --- | --- |
| 10 | `M5-P4B5A` | Fee dimensions and protocol custody | `FEE-UNIT-001`, `FEE-CUSTODY-002` |
| 20 | `M5-P4B5B` | Production nonce policy | `NONCE-PROFILE-001` |
| 30 | `M5-P4B5C` | Fresh evidence recomputation | `EVIDENCE-REVALIDATE-001` |
| 40 | `M5-P4B5D` | Chained history and enforced nullifiers | `COMMIT-HISTORY-001`, `REPLAY-NULLIFIER-001` |
| 50 | `M5-P4B5E` | Authenticated context and green proof gate | `CONTEXT-PROVENANCE-001`, `PROOF-RECOMPUTE-001` |
| 60 | `ZUSD-P0` | Total-debt system supply cap | `ZUSD-CAP-001` |

`ZUSD-P0` is a separate zUSD repair lane. It must close before an all-value M6
claim even if the spot M5 checkpoints close first.

## Findings

### FEE-UNIT-001: cross-asset fee-unit collapse

- Status: `CONFIRMED_DEFECT`
- Exploitability: `DIRECT_COUNTEREXAMPLE`
- Priority: `P0_BEFORE_FEE_EFFECT_MOUNT`
- Blocking checkpoint: `M5-P4B5A`
- Invariant: amounts in different assets cannot enter one authoritative sum or
  dust account without an explicit authenticated conversion.
- Minimal witness: one fill pays `100` units of asset A and another pays `1`
  unit of asset C. `_total_settlement_fees_v1` and `_derive_plan_v1` produce the
  scalar `101`. `FCISFeeAllocationV1` and
  `CommittedFeeAccumulatorStateV1` retain no asset.
- Affected code:
  - `src/core/fcis_step_evaluator.py::_total_settlement_fees_v1`
  - `src/core/fcis_step_evaluator.py::_fee_candidate_observed_v5`
  - `src/core/fcis_decision_derivation.py::_derive_plan_v1`
  - `src/core/fcis_step_evaluation_values.py::FCISFeeAllocationV1`
  - `src/state/state_snapshot_values.py::CommittedFeeAccumulatorStateV1`
- Required repair: introduce canonical per-asset totals, allocations, and
  dust. Derive the asset from admitted intent/fill lineage. Version the
  affected schemas, codecs, patches, roots, receipts, and migrations.
- Required regressions: mixed-asset batches, different decimal domains,
  per-asset dust, disjoint-batch partition invariance, and byte parity across
  promoted implementations.
- Nonclaim: this unmounted plan defect is not an allegation of a current
  external payout.

### FEE-CUSTODY-002: total-fee split exceeds protocol custody

- Status: `CONFIRMED_DEFECT`
- Exploitability: `CONDITIONAL_ON_MOUNT_OR_POLICY`
- Priority: `P0_IF_ALLOCATION_EXECUTABLE`
- Blocking checkpoint: `M5-P4B5A`
- Invariant: an executable allocation per asset equals the amount actually
  credited to protocol custody and names every source and destination owner.
- Minimal witness: a fill pays a fee of `100` and has
  `protocol_fee_paid=10`. Settlement replay moves only `10` into protocol
  custody while FCIS derives the split from `100`.
- Affected code:
  - `src/core/settlement_snapshots.py::OwnedFillV1`
  - `src/core/fcis_step_evaluator.py::_total_settlement_fees_v1`
  - `src/core/fcis_step_evaluator.py::_fee_candidate_observed_v5`
  - `src/core/fcis_decision_derivation.py::_derive_plan_v1`
  - `src/core/settlement_strong_validator.py::_validate_settlement_strong_impl`
- Required repair: derive distributable fees from `protocol_fee_paid`, grouped
  by asset. Encode source custody, destination custody, amount, rounding, and
  dust. If the value is analytics-only, remove it from executable commit
  authority and give it a non-authoritative type.
- Required regressions: protocol shares at `0`, `1`, `9999`, and `10000` bps;
  LP remainder custody; trader/recipient/pool/protocol-recipient aliases; and
  effect-to-balance/reserve conservation.
- Nonclaim: exploitability depends on a shell treating the unmounted allocation
  as executable authority.

### ZUSD-CAP-001: multi-vault system supply-cap bypass

- Status: `CONFIRMED_DEFECT`
- Exploitability: `DIRECT_COUNTEREXAMPLE`
- Priority: `P0`
- Blocking checkpoint: `ZUSD-P0`
- Invariant:

  ```text
  total_debt_before + debt_delta <= max_debt_supply
  free_debt + sp_debt = total_debt
  ```

- Minimal witness: configure both system and per-vault caps to `20,000,000`.
  Start with vault debt `15,000,000 + 4,000,000`, free debt `1,000,000`, and
  Stability Pool debt `18,000,000`. Mint a `2,000,000` debt delta into the
  second vault. The free-debt guard passes and total debt becomes `21,000,000`.
  Supply conservation still passes.
- Affected code:
  - `src/core/zusd.py::_total_debt`
  - `src/core/zusd.py::_zusd_mh_mint_zusd`
  - `src/core/zusd.py::check_multi_invariants`
  - `src/tau_specs/recommended/zusd_mint_guard_v1.tau::mint_allowed`
  - `src/tau_specs/recommended/zusd_supply_conservation_v2.tau::supply_conserved`
- Required repair: guard total debt plus debt delta, add the cap to permanent
  invariants, and make Tau derive the cap relation instead of trusting the
  unbound `max_supply_ok` Boolean.
- Required regressions: cap-minus-one, cap, and cap-plus-one with most debt in
  the Stability Pool; deposit-to-SP then mint; Python/Rust/Tau/ESSO/proof-guest
  parity.
- Nonclaim: the spot P4B4 work does not close this separate zUSD defect.

### NONCE-PROFILE-001: nonce-free production state is representable

- Status: `CONFIRMED_SECURITY_PREMISE_GAP`
- Exploitability: `CONDITIONAL_ON_MOUNT_OR_POLICY`
- Priority: `P0_AT_MOUNT`
- Blocking checkpoint: `M5-P4B5B`
- Invariant: every production signed-intent batch advances complete replay
  state under an authenticated, receipt-bound policy.
- Minimal witness: admit `FCISStepExecutionContextV1(require_all_nonces=False)`
  and a nonempty all-nonce-free batch.
  `_validate_and_apply_intent_nonce_batch_admitted_observed_v5` accepts while
  leaving nonce state unchanged.
- Affected code:
  - `src/state/fcis_execution_context_values.py::FCISStepExecutionContextV1`
  - `src/core/nonce_batch_transition.py::_validate_and_apply_intent_nonce_batch_admitted_observed_v5`
  - `src/core/dex.py::DexConfig.requires_complete_nonce_coverage`
- Required repair: replace the Boolean with a closed production/test policy.
  Make legacy nonce-free construction unreachable from production admission
  and mount modules. Receipt-bind the authenticated deployment policy.
- Required regressions: identical nonce-free replay, structural import and
  constructor bans, and the complete legacy two-Boolean differential truth
  table.
- Nonclaim: exploitability requires a future production mount to admit the
  unsafe profile.

### COMMIT-HISTORY-001: publication history is not chained

- Status: `CONFIRMED_DEFECT`
- Exploitability: `DIRECT_COUNTEREXAMPLE`
- Priority: `P1_REFERENCE_P0_IF_ADAPTER_DERIVED`
- Blocking checkpoint: `M5-P4B5D`
- Invariant: every publication after an authenticated checkpoint consumes the
  exact preceding successor under one sequence, version, and deployment.
- Minimal witness: create valid bundles `A: S0 -> S1` and `B: T0 -> T1`, where
  `S1 != T0`. A `ReferenceCommitStoreV1` containing `(A, B)` with visible state
  `T1` passes `_revalidate_store_v1`.
- Affected code:
  - `src/core/fcis_commit_reference.py::ReferenceCommitStoreV1`
  - `src/core/fcis_commit_reference.py::_revalidate_store_v1`
  - `src/core/fcis_commit_reference.py::_bundle_root_in_publications_v1`
  - `src/core/fcis_commit_reference.py::reference_commit_v1`
- Required repair: bind sequence, previous publication root, pre-root,
  next-root, snapshot version, and deployment identity. Validate every adjacent
  edge from an authenticated checkpoint or use a checked append-only
  accumulator.
- Required regressions: splice, reorder, middle deletion, truncation, fork
  insertion, ABA, cross-version substitution, restart, and retry.
- Nonclaim: this is an unmounted reference-model defect, not evidence of
  production datastore corruption.

### REPLAY-NULLIFIER-001: declared nullifiers are not enforced

- Status: `CONFIRMED_ENFORCEMENT_GAP`
- Exploitability: `ENFORCEMENT_GAP_WITHOUT_LIVE_EXPLOIT_CLAIM`
- Priority: `P1_CONDITIONAL_P0`
- Blocking checkpoint: `M5-P4B5D`
- Invariant: every replay atom in commit authority is atomically
  uniqueness-enforced or removed after a checked redundancy proof.
- Minimal witness: `_derive_replay_v1` creates a nullifier for every
  `(sender_pubkey, intent_id)`, and `ReplayUpdateV1` retains the records.
  `_apply_patch_atoms_v1` applies only nonce advances. The store has no
  nullifier state or duplicate-nullifier compare-and-replace.
- Affected code:
  - `src/core/fcis_transition_values.py::NullifierRecordV1`
  - `src/core/fcis_transition_values.py::ReplayUpdateV1`
  - `src/core/fcis_decision_derivation.py::_derive_replay_v1`
  - `src/core/fcis_commit_reference.py::_apply_patch_atoms_v1`
- Required repair: atomically persist and uniqueness-check nullifiers, or prove
  they are redundant in every supported profile and remove them from
  executable authority.
- Required regressions: concurrent duplicates, higher-nonce reuse,
  compatibility paths, proof-mediated paths, restart, truncation, restore, and
  retry.
- Nonclaim: a live exploit remains conditional because nonce semantics may make
  some duplicates unreachable; that redundancy is not proved.

### EVIDENCE-REVALIDATE-001: receipt evidence is not fully recomputed

- Status: `CONFIRMED_ENFORCEMENT_GAP`
- Exploitability: `CONDITIONAL_ON_MOUNT_OR_POLICY`
- Priority: `P1`
- Blocking checkpoint: `M5-P4B5C`
- Invariant: support and resource evidence is freshly derived from the exact
  retained inputs and traces at decision authority.
- Minimal witness: post-construction mutation of `support_root`,
  `support_set_commitment`, `state_read_count`, `context_read_count`,
  `canonical_input_bytes`, or `witness_bytes` is omitted by
  `_revalidate_evaluation_v1`. `_budget_violation_v1` trusts the retained
  counts.
- Affected code:
  - `src/core/fcis_step_evaluation_values.py::FCISStepEvaluationEvidenceV1`
  - `src/core/fcis_step_evaluator.py::_candidate_evidence_v1`
  - `src/core/fcis_decision_derivation.py::_revalidate_evaluation_v1`
  - `src/core/fcis_decision_derivation.py::_budget_violation_v1`
  - `src/core/fcis_support_profile_v5.py::compute_fcis_support_root_v5`
- Required repair: retain exact traces and support material, recompute all
  fields during decision derivation, and derive receipts/budget decisions only
  from the fresh result.
- Required regressions: independently rehashed mutation for every evidence
  field, support/version/trace substitution, and budget boundary-value tests.
- Nonclaim: the witness assumes hostile or compromised same-process mutation;
  it does not allege a remote constructor bypass.

### CONTEXT-PROVENANCE-001: canonical context lacks authenticated origin

- Status: `CONFIRMED_SECURITY_PREMISE_GAP`
- Exploitability: `CONDITIONAL_ON_MOUNT_OR_POLICY`
- Priority: `P0_AT_PRODUCTION_MOUNT`
- Blocking checkpoint: `M5-P4B5E`
- Invariant: consensus time, fee policy, deployment policy, settlement mode,
  and replay policy come from one authenticated ledger/deployment context that
  callers cannot construct.
- Minimal witness: `FCISSettlementExecutionContextV1` and
  `FCISStepExecutionContextV1` admit exact `now`, fee recipient/share, mode,
  quote policy, nonce policy, and snapshot version. They bind no verified
  ledger header, deployment identity, policy epoch, or configuration root.
- Affected code:
  - `src/state/fcis_execution_context_values.py::FCISSettlementExecutionContextV1`
  - `src/state/fcis_execution_context_values.py::FCISStepExecutionContextV1`
  - `src/state/fcis_execution_context.py::admit_fcis_step_execution_context_v1`
  - `src/state/fcis_execution_context_admission.py::_construct_step_v1`
  - `src/core/fcis_step_evaluator.py::evaluate_fcis_step_candidate_v1`
- Required repair: add a controlled authenticated context witness derived from
  a verified header, authenticated consensus time, deployment configuration
  root, policy epoch, chain/deployment ID, and authority proof. Receipt-bind
  its root and epoch.
- Required regressions: request-derived substitution, cross-deployment replay,
  unauthorized fee recipient/share, time rollback/forward jump, oracle
  freshness, and LP-age boundaries.
- Nonclaim: this is a missing production premise in an unmounted path.

### PROOF-RECOMPUTE-001: expected-valid proof recomputation fails

- Status: `CONFIRMED_GATE_FAILURE`
- Exploitability: `GATE_FAILURE_WITHOUT_UNSOUND_ACCEPTANCE_CLAIM`
- Priority: `P0_RELEASE_BLOCKER`
- Blocking checkpoint: `M5-P4B5E`
- Invariant: every expected-valid certificate recomputes and validates
  deterministically; stale or mismatched material rejects.
- Minimal witness: the recorded five-file settlement proof lane exits nonzero
  on expected-valid material. The demonstrated class is a crash or rejection,
  and the first packet still needs minimization.
- Affected code and evidence:
  - `tools/proof_verifiers/recompute_batch_v1.py::main`
  - `tests/integration/test_recompute_batch_proof_verifier.py::test_recompute_batch_proof_verifier_accepts_valid_certificate`
  - `tests/integration/test_settlement_certificate_runtime_gate.py`
  - `tests/integration/test_validation_uses_strong_settlement_gate.py`
  - `tools/stateful_scenario_bridge.py::settlement_proof_recompute_gate`
- Required repair: rerun the exact lane with `-x -vv`, preserve stdout/stderr,
  minimize the first expected-valid packet, classify the normalization or
  wrapper divergence, and retain positive and negative regression vectors.
- Required regressions: expected-valid corpus, command/pre/post/effect/event/
  batch/witness substitutions, stale proofs, and weak-versus-strong wrapper
  selection.
- Nonclaim: no unsound acceptance of stale or mismatched proof material has
  been demonstrated.

## M6 entry condition

An all-value M6 claim remains prohibited until:

```text
P4B4 exact validator reviewed and unmounted evidence green
AND P4B5A fee dimensions/custody closed
AND P4B5B production nonce policy closed
AND P4B5C evidence recomputation closed
AND P4B5D history/nullifier enforcement closed
AND P4B5E context/proof gate closed
AND ZUSD-P0 total-debt cap closed across promoted lanes
```

Even then, M6 must separately establish mounted-path exclusivity, production
datastore linearizability, crash recovery, idempotent outbox delivery,
Python/Rust/proof parity, migration, and all-value conservation. This ledger
does not certify any of those properties.
