# ZenoDEX Theorem-to-Runtime Matrix V1

This matrix maps the promoted Aristotle/Lean math into public runtime gates,
tests, and remaining production work for ZenoDEX, ZenoOracle, and ZenoProof.
It is an engineering assurance artifact. Legal classification, securities
status, tax treatment, oracle truth, cryptographic soundness, and live
governance behavior remain separate review lanes.

## Status Meanings

- `Implemented`: a public runtime gate or replay test enforces the theorem's
  runtime projection directly enough to treat the bridge as active evidence.
- `Partial`: public code covers part of the theorem, but a field projection,
  shared gate, or exact regression test is still missing.
- `Missing`: the theorem or note exists, but no public runtime gate currently
  enforces the shape.

## High-Value Claim

The promoted math is strongest where it turns broad disaster states into local
checkable gates:

```text
positive payout -> admitted source
positive payout -> reserve target met
positive payout -> payout <= realized surplus
same canonical work -> paid at most once
revoked verifier -> proof artifact rejected
```

These gates attack the highest-damage families: passive-yield leakage,
future-entrant funding, reserve starvation, duplicate proof rewards,
oracle-bridge spoofing, verifier spoofing, and burn-accounting drift.

## Runtime Matrix

| Lean theorem or formula | Runtime projection | Public evidence | Status | Next hardening step |
| --- | --- | --- | --- | --- |
| `admitted_source_blocks_bad_funding` | Admitted source must have `noPassiveYield = true` and `noFutureEntrant = true`. | `lean-mathlib/Proofs/ZenoDEXSTierDisasterMath.lean`; `docs/research/ZENODEX_YIELD_LIKE_FUNDING_SHAPES_V1.md` | Partial | Add a runtime `SourceGate` or `YieldSource` admission object with explicit `source_verified`, `source_bounded`, `no_guaranteed_return`, `no_profit_share`, `no_future_entrant`, `disclosure_met`, and `legal_capability` fields. |
| `passive_or_future_source_not_admitted` | Passive or future-entrant source flags reject before any payout math runs. | Lean proof only, with yield taxonomy note. | Missing | Add tests that each forbidden kind and each bad flag rejects in the runtime source-admission gate. |
| `positive_payout_implies_reserve_source_and_surplus_bound` | If a positive payout occurs, reserves have priority, the payout is bounded by realized surplus, and bad funding flags are closed. | Proof mining reward budget checks in `tools/zenoproof_verify.py` and `src/core/proof_mining_claimability_gate.py`; oracle reward budget checks in `tools/zenodex_oracle_reporter_economics_replay.py`. | Partial | Create a shared `WaterfallCert` runtime gate with `realized_surplus`, `reserve_topup`, `reserve_deficit`, `allocable_budget`, `work_budget`, `burn`, and `residual`, then require every yield-like payout to cite it. |
| `zero_surplus_forces_zero_outflow` | Zero realized surplus should force zero burn, zero work budget, and zero payment. | Reward-pool mismatch and overpay rejections exist in ZenoProof and ZenoOracle replays. | Partial | Add a zero-surplus regression across proof mining reward, oracle reporter reward, fee rebate, and burn receipt lanes. |
| `same_work_pay_once_under_canonicalizer` | Work identity is canonicalized over statement, assumptions, input, output, and public result, so nonce-only changes cannot trigger a second payout. | `tools/zenoproof_verify.py` rejects duplicate reward claims through `previously_rewarded_claim_ids`; `src/core/proof_mining_claims.py` binds proof, context, policy, nonce, and reward budget. | Partial | Add a canonical work id object over `statement_root`, `assumption_root`, `input_root`, `output_root`, and `public_result_root`, then test that changing only nonce or aux data still hits the consumed set. |
| `raw_inequality_is_not_work_uniqueness` | Artifact byte inequality is insufficient for work uniqueness. | Lean counterexample in `ZenoDEXSTierDisasterMath.lean`. | Missing | Add a negative regression where two artifacts differ in nonce or aux data but share the canonical work tuple; the second claim must reject. |
| `bridge_admission_exposes_all_settlement_gates` | Oracle bridge admission must preserve `claim_id`, `public_result_root`, consumer action, freshness window, and verified proof status. | `tools/zenoproof_verify.py` O4/O5 bridge checks; `tests/test_zenoproof_verify.py` wrong input binding, weak O5 independence, and dependency-cycle tests; `docs/claims_registry.yaml` claim `py:zenoproof:v0_artifact_verifier`. | Partial | Add explicit tests for `public_result_root`, consumer action, stale freshness, and unverified proof-result rejection in the O4/O5 bridge path. |
| `revoked_code_signing_record_not_admitted` | A registry record with `revoked = true` rejects even when the artifact otherwise matches policy. | `tools/zenoproof_verify.py` checks `verifier_revoked`; `tests/test_zenoproof_verify.py::test_revoked_verifier_rejects`. | Implemented | Extend the registry from revocation boolean to signed release records: verifier id, binary digest, toolchain id, release key, signature, revocation epoch, and revocation reason. |
| `admitted_kind_allowed` | Only whitelisted yield-like source kinds can enter. | Lean taxonomy in `ZenoDEXYieldLikeFundingSafety.lean`. | Missing | Implement the runtime enum for allowed and forbidden source kinds. |
| `admitted_source_is_bounded` | Every admitted source must be bounded to a measured source cap. | Fee split, reward pool, burn budget, and proof-mining pool checks cover specific cases. | Partial | Require `source_cap` in all payout certificates and bind it to the relevant source ledger. |
| `admitted_source_has_no_passive_return_right` | Admitted sources cannot grant guaranteed return, profit-share, or future-entrant dependency. | Lean proof and public yield-like funding note. | Missing | Add runtime flags and regression tests for `no_guaranteed_return`, `no_profit_share`, and `no_future_entrant`. |
| `required_work_source_is_earned` | Service-like sources require earned service evidence. | Proof-mining and oracle reporter paths require proof/report artifacts before reward. | Partial | Normalize service evidence into a shared `earned_by_service` certificate with claim id, task scope, proof result, value review, and anti-sybil result. |
| `liquid_staking_pass_through_requires_ministerial` | Liquid-staking pass-through receipts require a ministerial-only provider role. | Lean proof and design note. | Missing | Build a pass-through receipt verifier with underlying assets, protocol rewards, provider fees, slashing losses, ministerial flag, and no-guarantee flags. |
| `hold_to_earn_not_admitted`, `guaranteed_apy_kind_not_admitted`, `profit_share_kind_not_admitted`, `future_entrant_kind_not_admitted`, `discretionary_managerial_yield_kind_not_admitted` | Forbidden source kinds reject independently from payout arithmetic. | Lean proof only. | Missing | Add one test per forbidden kind in the runtime source-admission gate. |
| `positive_yield_like_payout_gate` | A positive yield-like payout requires allowed kind, bounded source, no guaranteed return, no profit share, no future entrant, reserve-first satisfaction, and payout bounded by realized surplus. | Public Lean proof plus partial runtime budget checks in proof mining, oracle reporter economics, burn receipts, and fee-rebate tests. | Partial | Make the source gate and waterfall gate mandatory inputs to each payout adapter. |
| `zero_allocable_budget_forces_zero_payment` | If allocable budget is zero, payment must be zero. | Reward-pool mismatch tests cover a narrower pool-specific version. | Partial | Add shared allocable-budget tests for all payout shapes. |
| `fee_rebate_bounded_by_own_fees` | `rebate <= fees_paid`. | `tests/core/test_perp_incentive_hazards.py::test_protocol_fee_rebate_capped_by_extracted_fees_not_profitable_under_bounds`; claim `py:cpmm:protocol_fee_rebate_capped_by_extracted_fees_unprofitable_under_bounds`. | Partial | Promote fee rebate into a reusable certificate object with `fees_paid`, `rebate`, and source-admission binding. |
| `fee_pool_distribution_source_bounded` | `sum(payouts) <= totalFees`. | ZenoOracle `fee_split_exceeds_fee_paid` rejection; CPMM LP fee recapture witness. | Partial | Add a generic fee pool distribution verifier used by LP, oracle, and treasury fee-split lanes. |
| `service_reward_source_bounded` | `reward + penalties <= base_reward + fee_share`, hence reward is source bounded. | ZenoOracle reward budget, dispute reward budget, and proof-mining reward-payout replays. | Partial | Bind penalties and fee shares into a reusable service reward certificate. |
| `pass_through_receipt_source_bounded` | `receipt_claim + provider_fees + slashing_losses <= underlying_assets + accrued_protocol_rewards`. | Lean proof and design note. | Missing | Build and test the liquid-staking pass-through receipt lane before exposing it in any UI or payout path. |
| `burn_amount_source_bounded` | `burn_amount <= allocable_budget`. | `src/core/burn_receipts.py` amount guard enforces `burn_budget >= burn_amount`; `tests/core/test_burn_receipts.py` covers replay, hash, amount mismatch, and no-burn preservation. | Partial | Bind `burn_budget` to the shared `allocable_budget` and `WaterfallCert` so burns cannot bypass reserve-first accounting. |

## Most Important Gaps

1. Unified source admission.

```text
Admitted(source) :=
  allowed_kind
  AND source_verified
  AND source_bounded
  AND no_guaranteed_return
  AND no_profit_share
  AND no_future_entrant
  AND disclosure_met
  AND work_required_implies_earned_by_service
  AND pass_through_implies_ministerial_only
```

This is the biggest missing runtime gate. It turns the yield taxonomy into an
executable reject surface.

2. Shared reserve-first waterfall.

```text
reserve_topup < reserve_deficit -> allocable_budget = 0
payment > 0 -> reserve_topup >= reserve_deficit
payment <= realized_surplus
```

Current proof-mining and oracle paths have pool-local budget checks. The next
step is a cross-lane waterfall certificate that every payout-like adapter must
cite.

3. Canonical work identity.

```text
sameWork(a, b) :=
  statement_root(a) = statement_root(b)
  AND assumption_root(a) = assumption_root(b)
  AND input_root(a) = input_root(b)
  AND output_root(a) = output_root(b)
  AND public_result_root(a) = public_result_root(b)
```

The runtime should pay this identity once. Raw artifact inequality, nonce
changes, or aux-data changes cannot define new work.

4. Bridge preservation tests.

The O4/O5 bridge has good structure already. The next test pack should mutate
each bridge-preservation field independently: claim id, public result root,
consumer action, epoch freshness, verified flag, input root, output root, and
O5 independence witness.

5. Verifier sandbox and code signing.

Current evidence covers registry schema, timeout rejection, revocation
rejection, policy-root freshness, and external verifier failures. Production
still needs a signed release manifest and a real sandbox boundary for
subprocess verifiers. WebAssembly is a strong candidate for deterministic,
low-syscall verifier execution, especially for public replay verifiers, but the
math only requires a verifier result with stable identity, bounded execution,
revocation handling, and input/output root binding.

## Next Implementation Order

1. Add `src/core/yield_source_admission.py` with the runtime taxonomy and
   admission result object.
2. Add tests covering every allowed kind, every forbidden kind, and each bad
   flag.
3. Add `src/core/waterfall_budget.py` with reserve-first accounting and
   zero-allocable rejection.
4. Bind proof-mining rewards, oracle reporter rewards, fee rebates, service
   rewards, burn receipts, and future pass-through receipts to the source gate
   and waterfall gate.
5. Add canonical-work duplicate tests for proof mining and ZenoProof reward
   gates.
6. Expand O4/O5 bridge mutation tests to cover every preservation field.
7. Promote the new runtime gates into `docs/claims_registry.yaml` only after
   deterministic tests replay locally.

## Production Blockers After This Matrix

- Source-admission runtime gate is missing.
- Shared reserve-first waterfall runtime gate is missing.
- Canonical same-work runtime id is incomplete.
- Pass-through receipt verifier is missing.
- O4/O5 bridge preservation tests need field-by-field coverage.
- Code-signing release records need real digest/signature/revocation metadata.
- Verifier subprocesses need a stronger sandbox boundary for production.
- Legal review must approve each live source, disclosure, interface, and
  marketing claim before launch.

