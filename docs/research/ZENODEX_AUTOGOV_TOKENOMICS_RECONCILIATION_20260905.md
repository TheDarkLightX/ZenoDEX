# AutoGovNEXT as a tokenomics donor

Date: 2026-09-05. Status: `SOURCE_REVIEW_AND_SCOPED_REPLAY`. Authority: none.
This research recovers existing autogov work for the whole-program V3 service
budget. It selects no fee, reward, risk, token-rights or activation policy.

## Reusable architecture

The existing [policy implementation](../../src/integration/autonomous_governance_q_policy.py)
provides a finite action vocabulary, canonical policy hash, deterministic
selection and separate admission checks. Its surface includes fee rate,
buy/burn, staker, reserve and host fractions, collateral ratios, whale-defense
staker fraction and the funding cap. Policy tables rank candidates against
explicit observations. The composed governance gate rechecks allowed changes.
Cooldown, bounds, step limits, anti-oscillation and carried trajectory budgets
constrain movement. The authority-parameter denylist includes signer sets,
verifier images/keys, deployment profiles and governance authority hashes.

The [trajectory theorem](../../lean-mathlib/Proofs/AutogovNextTrajectoryBudget.lean)
supplies a useful universal arithmetic result. With nonnegative absolute
movements, a carried accumulator and the same limit at each admitted step:

```text
used_final = used_initial + sum(absolute_parameter_movements)
used_initial = 0 and every carried step fits the limit
  imply sum(absolute_parameter_movements) <= limit
```

This theorem deliberately leaves reset policy outside its model. The node
implementation and its tests retain a lifetime accumulator until a separately
authorized governance reset. A new tokenomics controller can reuse the
mathematical pattern only after its state acquisition, carry, reset authority
and publication behavior are bound to the V3 publisher.

The existing [live apply adapter](../../src/integration/autogov_live_apply_api.py)
and [node launcher](../../tools/zeno_ledger_node.py) are integration surfaces
to reconcile, rather than proof that all writers already use the V3 commit
port. A policy hash establishes which bytes were selected; authority to select
those bytes and authenticity of its observations require separate evidence.
Import-bound Python function aliases do not secure a compromised process.

## Mathematical and economic corrections

The [June mechanism note](../AUTOGOVNEXT_GAME_THEORY_AND_MECHANISM_DESIGN.md)
is explicitly historical, pre-promotion work. Its section 2.3 defines a
deviator's payoff through out-of-envelope admission, then describes honesty
as dominant when that payoff is prevented. That is a restricted safety game.
It does not establish dominance for the service-budget game, whose players
can benefit from different admitted allocations, Oracle reports, bidder
selection or timing. Its section 7 already identifies within-envelope Oracle
bias as an open issue. Its broader statements about poisoned rankings inherit
this restricted payoff definition.

For the proposed reward system, four obligations must remain distinct:

1. **Accounting:** each physical atom has one owner; outstanding earned claims,
   reserved service commitments, loss backing and designated burn budgets
   cannot be reallocated as free subsidy.
2. **Authority:** only an approved policy can award funds or change future
   envelopes, while exact committed claims retain their original terms.
3. **Service validity:** a claimant provided the agreed service under an
   authentic observation and occurrence. Nominal TVL, reported volume and
   holding a token do not establish this fact by themselves.
4. **Economic alignment:** with combined trader/LP/voter/reporter/provider
   positions, deviations do not produce the prohibited payoff in the stated
   game. Feasibility, hash equality and replay determinism do not imply this.

The existing trajectory proof closes an arithmetic sub-obligation. It neither
proves optimal allocation nor bounds the monetary loss of an admitted
parameter change. A monetary loss bound needs a separate relation between
parameter motion, accessible exposure and payoff, including units and market
assumptions. A learned score and a low replay regret do not supply that relation.

## Proposed reuse for funded services

Use autogov to propose future capped campaigns or procurement envelopes after
accounting ownership and service definitions are approved. The proposed
allocation should name its funding asset, already committed funding source,
duration, service units, eligibility, compensation cap, observation rule,
claimant, reserve requirement and terminal refund owner. Its deterministic
admission gate can enforce:

```text
new_commitments_per_asset <= authenticated_free_budget_per_asset
paid_claims <= earned_claims <= previously_reserved_commitment
no new authority, minting permission or old-claim reinterpretation
```

These are proposed contracts. The current nine-parameter surface does not
implement this service-award command. Adding it requires versioned ownership,
proof and integration work; renaming existing `stakers_bps` does not establish
equivalence to compensation for verified work.

Freeze eligibility and allocation terms before their measurement period.
Preserve pending claims, collateral, minimum reserves and burn commitments
across revisions. Keep proposal ranking observational until the complete
award/claim/cancel/recovery/terminal path is qualified. Zero free funds or
unavailable service evidence produces no new award, while existing claims
retain their disposition. Finite bootstrap funding supplies only a finite
runway; no control algorithm creates income during a revenue drought.

Measured liquidity procurement can be compared with the existing fee-first
baseline and funded campaigns. A cheapest-ask rule may solve a reported-cost
problem for identical units; bidder truthfulness, coalitions and service
verification remain different claims. Oracle, host and proof-service costs
also need explicit funding. Stability Pool principal and liquidation
collateral must retain their capital/risk interpretation.

## V3 lifecycle reconciliation

The legacy node intentionally appends some rejected policy decisions as
no-op receipts with equal pre/post economic roots. V3 logical precommit
rejection additionally excludes replay consumption, history and outbox effects.
Those outcome contracts differ. Preserve legacy interpretation for historical
verification, and give the successor explicit outcome classes. A committed
governance no-op must not be described as a V3 precommit rejection. No legacy
test or manifest was changed to conceal this difference.

The service-only versus profit-share conflict recovered in the
[comparative funding study](ZENODEX_LP_AND_SERVICE_REWARD_FUNDING_COMPARISON_20260905.md)
also applies here. A `stakers_bps` field and a revenue-vault draft do not approve
new passive fee rights. The proposed research leaves that policy unresolved.

## Replayed evidence and limits

The unchanged policy test module passed **37 tests in 11.09 seconds**:

```bash
python3 -m pytest -q tests/integration/test_autonomous_governance_q_policy.py
cd lean-mathlib
lean -DwarningAsError=true Proofs/AutogovNextTrajectoryBudget.lean
```

The direct Lean command passed under pinned Lean 4.27.0. An independent
temporary copy appended `#print axioms` for all four theorems and passed with
warnings treated as errors. `carriesBudget_final_used_le_limit` uses no axioms;
the other three list only `propext`. There is no `sorryAx` in that audit.
The temporary-copy audit does not add a runtime-refinement proof.

Three existing isolated node lifecycle tests also passed in 53.86 seconds:

```bash
python3 -m pytest -q \
  tests/integration/test_zeno_ledger_node_autogovnext.py::test_autogovnext_append_uses_node_owned_governance_state_for_next_update \
  tests/integration/test_zeno_ledger_node_autogovnext.py::test_autogovnext_append_duplicate_tx_id_returns_existing_report \
  tests/integration/test_zeno_ledger_node_autogovnext.py::test_autogovnext_append_includes_gate_rejected_noop_without_state_mutation
```

These exercise carried node state, exact retry and the legacy committed
policy-rejection outcome on temporary test state. They start no HTTP server.
The retained log `zenodex-v3-autogov-local-lifecycle01.log` has SHA-256
`0f789b3587be3ec9cb4938a1db3661ba9e91fae079c64233d85b7b9c3dd671bd`.

Retained policy log `zenodex-v3-autogov-policy-replay01.log` has SHA-256
`945e73ee0d4a39924cfd07e9ea7f3f71efa3bb8912cca606265a95542c1bd141`.
The axiom audit is retained as `zenodex-v3-autogov-axiom-audit01.log`, SHA-256
`95567668d915cfcc5ab6fd334830b14dc49b1ba1fa74d3a8438bd63b35e318b1`,
with its exact temporary source. The full autogov assurance gate, HTTP/follower fleet,
frontend/package installs, ESSO campaign, new RISC0 proofs, production reset
and release activation were not run for this donor study. The existing
assurance manifest retains `production_security_claim=false`.

### Inspected source identity

These are recovery anchors, not a promoted release manifest. SHA-256:

```text
d9c20574722aa9bf22ced7dc3188cdd4b7d70e23c6c98f91bd8032cc623b96e5  docs/AUTOGOVNEXT_GAME_THEORY_AND_MECHANISM_DESIGN.md
698d35917867714463ce67d769b394568d410dbf0a1d5e40da0fc4ef569e5118  docs/AUTOGOVNEXT_AND_ZENODEX_PRODUCTION_READINESS_PLAN_2026_06_10.md
eea1f7d2f80de87556931521aa462f1fda489ea31ba80c6a111f328adcc73f6d  src/integration/autonomous_governance_q_policy.py
99d81aac54d3f42fd52b6a7f145d835bb1baf8dc32238d67f8e25c35cd558b44  src/integration/autogov_live_apply_api.py
49f6b5b998dac35281074f2e5af12ef1e35d6566dda6f10a7feaabfd3fb114a9  tools/autogovnext_governance_lane_assurance_manifest.json
120003b811ff4e6508285c6e01113ffc82437151fd3475f31153045c38726b3d  lean-mathlib/Proofs/AutogovNextTrajectoryBudget.lean
cf45793c76ed10f7b82f0dd8a7a6bbf9b210a446e45f7c2d6af3be852c84a494  tests/integration/test_autonomous_governance_q_policy.py
0fd4db61b0a8240a09f83c6aa43cfd4bce2e13fbb708388dca30542a71e81c1b  tools/zeno_ledger_node.py
```
