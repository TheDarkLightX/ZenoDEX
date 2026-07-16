---
title: ideas
type: note
permalink: autonomous-tau-dex-review/experiments/math-research-memory/ideas
---

# Ideas

## Adaptive Bernstein region compiler

- `failing_region_midpoint_refinement_v1`
  - exact `Rational{BigInt}` de Casteljau compiler that refines only a failing
    interval and emits an ordinary complete Bernstein cover.
  - bounded corpus: `240` Gegenbauer, `154` Jacobi envelope, and `378` oriented
    Jacobi Turan obligations, plus seven negative controls.
  - result: `772/772` positives accepted, `0/7` false accepts, `2928` total
    pieces, maximum `8` pieces, and `2663176` canonical bytes.
  - equal baseline: `3592` pieces, maximum `16`, and `4076028` bytes.
  - at six leaves, midpoint adaptive leaves `5` `UNKNOWN` versus `240` for
    equal subdivision.
  - Lean bridge: arbitrary-degree Bernstein-combination nonnegativity, exact
    power-basis conversion, recursive de Casteljau evaluation, affine
    left/right subdivision correctness, direct `[lo, hi]` restriction, and
    finite-cover lifting check in
    `Proofs/AdaptiveBernsteinRegionCertificates.lean`.
  - residual proof boundary: the exact Julia compiler has 12 differential
    binding checks; Julia-source binding to the Lean definitions remains
    differential evidence.

- `derivative_landmark_dispatch_negative_knowledge_v1`
  - uses exact derivative Bernstein sign variations to propose a critical
    landmark, snapped to a global `1/64` grid before splitting.
  - result: `2943` pieces and `4270358` bytes. This is worse than midpoint
    adaptive on both measures and worse than equal subdivision in encoded bytes.
  - a prior coefficient-interpolated landmark is dropped because exact
    recursive denominators grow with coefficient height.
  - acceptance never depends on the heuristic; only the emitted Bernstein
    cover can produce `ACCEPT`.

## Region-adaptive analytic certificate compiler

- `region_adaptive_analytic_certificate_v1`
  - paper source: Deift-Zhou nonlinear steepest descent, refined by the
    Wang-Ma dbar extension.
  - decomposes an analytic inequality into certified regular, critical-point,
    transition, and outer regions.
  - each region carries a model proof, residual bound, and overlap contract;
    global acceptance requires complete coverage and every model margin to
    dominate its typed error budget.
  - completed first experiment: normalized Jacobi/Gegenbauer corpus versus the
    equal-subdivision Bernstein lane; failing-region midpoint refinement wins,
    while derivative-landmark selection is retained as negative knowledge.
  - promotion metrics: zero false accepts, lower certificate-piece count or
    lower `UNKNOWN` rate, exact-rational replay, and a checked Lean gluing
    theorem.

- `approximation_defect_receipt_v1`
  - carries `region_id`, `model_id`, `model_certificate`, `defect_bound`,
    `interaction_bound`, `reconstruction_bound`, and `coverage_root`.
  - derives from the dbar split between a solvable local RHP and a separately
    bounded nonanalytic interpolation defect.
  - remains offchain and fail-closed. Numerical approximation may propose the
    receipt; a deterministic verifier checks rational bounds and otherwise
    returns `UNKNOWN`.
  - executable status: the v1 schema and checker now validate canonical
    rationals, typed certified-versus-allocated bounds, exact finite coverage,
    overlap agreement, and a receipt-body root.
  - Lean status: componentwise budget composition, local target
    nonnegativity, finite-cover lifting, and overlap mismatch bounds check in
    `Proofs.ApproximationDefectCertificates`.
  - remaining trust boundary: `certificate_id` values are opaque references;
    promotion requires replayable upstream model and error-bound verifiers.

## v197 proof-gated gamification budget

- `proof_gated_gamification_budget_v1`
  - separates token rewards from XP/status/non-token progress.
  - token reward law:
    `reward <= min(VerifiedValue, BudgetCap, SybilAdjustedCap, TreasuryCap)`
    plus `ProofOK`, `AntiSybilOK`, and `ReceiptScopeOK`.
  - bounded result: `12` quests, `5` accepted token rewards, `1` accepted
    XP-only quest, `6` rejected adversarial quests, and `0` invariant failures.
  - Lean bridge: `RevenueSurfaceSafety.lean` proves that a reward below the
    four-way meet is below each individual cap.
  - next frontier: use real proof-mining and disaster-witness receipts as quest
    inputs rather than hand-authored quest rows.

## v198 disaster potential chaos morphisms

- `disaster_potential_chaos_morphism_v1`
  - models chaos injections as morphisms over a weighted disaster-potential
    vector.
  - core law:
    `SafeTransition(s -> s') := Risk(s') <= Risk(s) OR RecoveryCertificate(s -> s')`.
  - bounded result: `108` cases, `54` accepted, `54` rejected, `12` direct
    repairs, `42` certified recoveries, `12` catastrophic rejections, and `0`
    invariant failures.
  - Lean bridge: `DisasterPotentialSafety.lean` proves that accepted
    risk-increasing transitions require the recovery certificate.
  - next frontier: wire the risk vector to actual disaster-state replay axes and
    fuzz campaign objectives.

## v195 assumption-change override packet language

- `assumption_change_override_packet_language_v1`
  - searches for the smallest exact witness language for v194 governance
    assumption-change overrides.
  - required atoms: `domain_ok`, `surface_binding_ok`, `cap_reference_ok`,
    `assumption_nonce_fresh`, `signer_threshold_ok`, `registry_root_ok`,
    `epoch_freshness_ok`, and `no_user_net_ack_ok`.
  - bounded result: `13` packets, `2` valid packets, `11` invalid packets,
    `8` forced atoms, `1` minimal exact language, and `0` invariant failures.
  - every atom has a private negative witness; dropping any atom false-accepts
    a concrete adversarial packet.
  - next frontier: concrete schema/checker design and replay-protection rules
    once governance signer semantics are fixed.

## v194 evidence-meet launch config guard

- `evidence_meet_launch_config_guard_v1`
  - compiles the v193 meet caps into a bounded launch/config lint relation:
    `fee_bps <= MeetCap(surface) OR AssumptionChangeOverride(surface)`.
  - under-meet configs can claim evidence compliance; over-meet or uncapped
    configs require an explicit governance assumption-change record and cannot
    inherit the user-net safety claim.
  - bounded result: `10` configs, `18` surface checks, `2` accepted without
    override, `3` accepted with override, `5` rejected, and `0` invariant
    failures.
  - Lean bridge: `RevenueSurfaceSafety.lean` proves that if an accepted fee is
    above the cap, the override branch must be present.
  - next frontier: adversarial override packets and replay safety for
    assumption-change records.

## v193 evidence-meet fee-cap lattice

- `evidence_meet_fee_cap_lattice_v1`
  - composes v190 fixture caps, v191 stress caps, and v192 execution-derived
    caps by taking the minimum available cap per surface.
  - core law: `MeetCap(surface) <= cap(source, surface)` for every source cap.
  - bounded result: `6` user-value meet caps, `2` execution-backed meet caps,
    `4` synthetic-only meet caps, and `0` invariant failures.
  - Lean bridge: `RevenueSurfaceSafety.lean` proves that charging below
    `min(capA, capB)` preserves user nonnegative net whenever either source
    cap is safe relative to measured value.
  - next frontier: use the meet cap as a config-lint boundary for launch
    parameters and require explicit assumption-change receipts for overrides.

## v192 execution-derived fee receipts

- `execution_derived_fee_receipt_bridge_v1`
  - connects FIRE fee calibration to actual ZenoDEX CPMM routing arithmetic.
  - exact-in receipt value:
    `best_route_amount_out - direct_route_amount_out`.
  - exact-out receipt value:
    `direct_route_amount_in - best_route_amount_in`.
  - bounded result: `18` accepted execution-derived receipts and `2`
    deliberately bad rows across `3` deterministic market fixtures.
  - current caps: route surplus `2500` bps of measured value and exact-out
    savings `2497` bps of measured value, both review-only.
  - next frontier: emit the same receipt shape from quote/API replay logs and
    compare live cap drift against synthetic and execution-fixture baselines.

## v191 fee-cap calibration stress corpus

- `fee_cap_calibration_stress_corpus_v1`
  - turns the v190 receipt-to-cap bridge into a regression-tested stress
    object rather than a singleton fixture.
  - bounded corpus: `32` rows, including `18` accepted user-paid rows, `6`
    accepted protocol-surplus rows, `3` accepted penalty rows, and `5`
    deliberately rejected adversarial rows.
  - adversarial coverage: extractive user fee, protocol surplus overcapture,
    primary penalty revenue, wash farming, and primary negative net revenue.
  - current result: `6` review caps survive, `5` bad rows reject for exact
    expected reasons, retail caps stay within hard rails, and
    `launch_parameter_claim_count = 0`.
  - next frontier: replace the synthetic stress corpus with real execution
    receipts and compare empirical cap drift against the synthetic regression
    oracle.

## v190 revenue surface atlas

- `revenue_surface_atlas_v1`
  - turns FIRE tokenomics into concrete fee surfaces rather than generic
    reward or staking language.
  - modeled surfaces: swap rake, route surplus capture, exact-out savings,
    COW/batch solver surplus, protection receipts, automation, pro
    certificates/API, integrator routing, treasury market-maker bot profit,
    arbitrage recapture auctions, LP loss-cover premium, and early-exit
    penalties.
  - key laws:
    `UserFee <= MeasuredUserValue`,
    `StakeRewards <= RevenueBackedRewardBudget + ExplicitSubsidy`,
    and `BurnBudget > SubsidyEmissions` for actual supply deflation.
  - bounded result: `155527` policies searched, `5510` survivors,
    `0` model-audit invariant failures.
  - named falsifiers: zero fee, extractive notional fees, wash rebate farming,
    penalty dependency, and subsidized passive yield are rejected.
  - receipt bridge: JSONL `fire-revenue-surface-receipt/v1` rows calibrate
    empirical value-density caps and reject unsafe rows before they enter the
    fee-surface model.
  - fee-cap recommendation bridge: accepted user-paid receipts can produce
    review-only caps bounded by measured value and hard rails; protocol-surplus
    captures and penalties are classified separately.
  - Lean skeleton: `lean-mathlib/Proofs/RevenueSurfaceSafety.lean`.
  - next frontier: replay real route/protection/automation/API receipts and
    mine empirical value-density caps per surface.

## v182 Bernstein certificate fast path for bounded Tau/FIRE polynomial QE

- `bernstein_interval_sign_certificate_v1`
  - compile a bounded univariate polynomial inequality
    `forall x in [a,b], p(x) >= 0` into exact rational Bernstein coefficients
    after normalizing to `[0,1]`.
  - if all Bernstein coefficients are nonnegative on every certified
    subinterval, the universal inequality is discharged without full QE.
  - intended Tau use: a conservative pre-QE fast path. Success proves the
    obligation; failure is `UNKNOWN` and falls back to the existing solver.
  - intended FIRE/ZenoDEX use: compress polynomial interval proof trees into
    proof-carrying coefficient certificates.
  - DLMF transfer: use the polynomial-basis and numerical-methods viewpoint as
    a certificate design pattern, not as a runtime dependency on special
    functions.
  - Julia role: exact `Rational{BigInt}` certificate generation and bounded
    corpus measurement.

## v182 negative knowledge

- `floating_special_functions_are_not_runtime_facts_v1`
  - DLMF special functions and Julia floating approximations are excellent
    discovery tools, but they should not become Tau/FIRE acceptance facts
    without rational error certificates.

- `bernstein_failure_is_unknown_v1`
  - nonnegative Bernstein coefficients are sufficient, not necessary.
    A failed certificate is not a counterexample to nonnegativity.

## v166 FIRE tokenomics value object

- `productive_deflation_allocation_frontier_v1`
  - first bounded FIRE tokenomics object for crypto-winter launch design.
  - replaces "maximize burn" with a constrained allocation frontier:
    burn + contributor entry + adopter entry + liquidity + treasury runway.
  - main falsification: pure burn fails under the no-outside-capital entry
    model because it leaves no non-cash path for builders or users.

- `fire_value_constraint_closure_v1`
  - value in post-AGI should be defined as scarce, verified
    constraint-satisfaction, not raw output, effort, token price, or hype.
  - formula surface:
    `FIREValue(x) > 0 only if Useful(x) and Scarce(x) and Verifiable(x)
    and Capturable(x) and NonExtractive(x)`.
  - next frontier: replace the cycle's scalar `value_per_contributor_units`
    surrogate with a component vector over revenue enabled, cost reduced,
    risk reduced, trust added, liquidity quality, and option value.

- `ponzi_pressure_classifier_v1`
  - define ponzi-shaped reward loops by funding-dependency geometry rather than
    by whether a loop exists.
  - core measure:
    `PonziPressure_t = max(0, LegacyRewards_t - VerifiedBacking_t) /
    max(1, NewEntrantInflow_t)`.
  - attention, mining, and contribution meaning can be FIRE value if they map to
    retained useful action, trust/risk reduction, security, proofs, cost
    reduction, availability, learning, or community trust.
  - next frontier: add this classifier to the bounded tokenomics cycle and mine
    policies that maximize contribution meaning while keeping PonziPressure at
    zero or explicitly budgeted.

## v167 credible hope value object

- `credible_hope_value_accumulation_frontier_v1`
  - first bounded model comparing USD, early Bitcoin, modern Bitcoin,
    ponzi-shaped yield tokens, and FIRE productive deflation as value objects
    rather than price charts.
  - key premise:
    Bitcoin's early psychological power came from scarcity plus meaningful
    permissionless contribution, not price alone.
  - FIRE target:
    preserve credible hope while adding verified productive backing, bounded
    rewards, and non-cash contribution paths.

- `fire_beats_bitcoin_value_object_v1`
  - bounded frontier design:
    `productive_deflation_floor + verified_work_and_fees +
    proof_work_usage_hybrid + capped_bounties_rebates + bounded_governance +
    fire_earned_hope`.
  - under the v167 scoring ontology, this beats `bitcoin_modern` on value
    accumulation and credible hope while keeping PonziPressure no greater.

## v168 participatory price object

- `participatory_price_appreciation_engine_v1`
  - restores price appreciation as an explicit objective.
  - price target is not rejected; instead it is decomposed into source quality:
    fee capture, productive demand, buyback sink, scarcity, trust, liquidity,
    option value, and human agency premium minus extraction risk.
  - adds `HumanParticipationInPrice` so an AI-owned cashflow object can score
    high on price pressure while still failing the FIRE human-agency target.

- `participatory_price_index_v1`
  - combined metric:
    `ParticipatoryPriceIndex = PriceAppreciationPressure *
    HumanParticipationInPrice`.
  - first bounded result: FIRE participatory appreciation beats modern Bitcoin
    on both price pressure and participatory price index while keeping
    PonziPressure at zero in the model.

## v169 trust economics object

- `trust_as_capacity_not_entitlement_v1`
  - trust should widen capacity, task size, finality, collateral efficiency, and
    attestation responsibility.
  - trust should not create free yield or automatic reward multipliers.
  - first bounded task-market result: `newcomer_lane_capacity` is the best
    FIRE-shaped mechanism, while `trust_entitlement_multiplier` and
    `stake_weighted_rewards` create measurable unearned premium.

- `newcomer_lane_capacity_v1`
  - protected low-risk newcomer lanes are necessary because trust-only scoring
    can leave newcomers with zero access even when the mechanism is otherwise
    value-backed.
  - next frontier: make newcomer lanes sybil-resistant without making entry
    impossible for cash-poor humans.

## v170 adversarial participatory economics

- `adversarial_participatory_economics_v1`
  - explicit attacker model over honest cash-poor humans, trusted builders,
    AI workers, whale operators, and bot farms.
  - compares naive newcomer lanes, capital gates, proof-only markets,
    receipt/rate-limit mechanisms, attested newcomer lanes, and hybrid FIRE
    guards.

- `hybrid_fire_guard_v1`
  - first bounded adversarial survivor:
    receipt quality + rate limits + human attestation + slashing +
    proof weighting + protected newcomer quota.
  - result: strongly reduces fake loss versus naive newcomer lanes while
    preserving human access.

## v171 float-liquidity price bridge

- `float_liquidity_buyback_price_bridge_v1`
  - first AMM-style bridge from FIRE economics to token price, float, and
    liquidity depth.
  - separates raw price return from participatory appreciation.
  - first falsification: the naive participatory score over-rewarded human
    rewards until reward overhang was added.

- `reward_overhang_discount_v1`
  - reward releases are positive for human ownership only when they remain
    bounded relative to burn/buyback pressure.
  - core measure:
    `RewardOverhang = reward_tokens_issued / max(1, tokens_burned)`.
  - next frontier: add whale sell shocks and liquidity withdrawal shocks.

## v172 liquidity shock recovery

- `liquidity_shock_recovery_fire_v1`
  - first bounded shock model over FIRE token designs.
  - combines LP withdrawal, whale selling, usage loss, lower organic demand,
    and reward-panic selling across 5 designs and 3 shocks.
  - best design is `fire_recovery_circuit`, which combines treasury defense,
    reward throttling, liquidity support, buyback/burn, and human ownership.

- `participatory_recovery_score_v1`
  - recovery score:
    `ValuePerFloat * RecoveryRatio * LiquidityDepth * HumanParticipation /
    (1 + Drawdown + RewardOverhang + TreasuryDepletion)`.
  - key separation: thin-liquidity hype can win headline price in quiet markets
    but collapses under shock; pure burn lacks recovery budget; over-rewarding
    weakens recovery through reward overhang.
  - next frontier: add governance abuse and calibration against real AMM depth,
    sell size, and protocol fee data.

## v173 guarded recovery governance

- `guarded_recovery_governance_abuse_v1`
  - bounded governance-abuse model for the v172 recovery circuit.
  - compares admin discretion, whale-token voting, slow multisig, guarded FIRE
    recovery governance, and frozen no-emergency posture across 4 scenarios.
  - best mechanism is `fire_guarded_recovery_governance`.

- `emergency_controls_need_receipts_v1`
  - recovery controls must prove both sides:
    no false emergency trigger and no missed legitimate shock.
  - current survivor uses evidence thresholds, public receipts, TWAP-style
    guards, spend caps, cooldowns, slashable authority, and human reward floors.
  - next frontier: define the exact recovery-governance receipt language and
    test collusive evidence providers.

## v174 recovery governance receipt language

- `recovery_governance_receipt_language_v1`
  - exact bounded receipt-language search over the 512-case Boolean cube formed
    by 9 raw emergency-governance fields.
  - best language is the three-macro conjunction:
    `trigger_ok and spend_policy_ok and authority_ok`.
  - no one- or two-atom candidate language is exact in the candidate library.

- `three_macro_recovery_receipt_v1`
  - `trigger_ok := drawdown_ok and severity_ok and twap_fresh`
  - `spend_policy_ok := spend_le_cap and cooldown_elapsed and
    human_floor_preserved`
  - `authority_ok := slashable_authority and public_receipt_hash and
    no_insider_override`
  - next frontier: make the upstream field truth assumptions slashable and test
    collusive evidence providers.

## v175 collusive recovery evidence quorum

- `collusive_recovery_evidence_quorum_v1`
  - bounded provider-collusion model for recovery-governance receipts.
  - with `n = 5` provider groups, `f = 2` colluding groups, and `h = 1` offline
    group, the viable quorum law is `f < q <= n - h`.
  - best policy is `q3_slash10000`: three independent provider groups with full
    slash coverage for each evidence domain.

- `quorum_interval_for_recovery_evidence_v1`
  - rejects three tempting baselines:
    single/two-provider evidence is forgeable, majority without slash has no
    accountability, and five-of-five full slash blocks liveness under one
    honest outage.
  - next frontier: model provider identity and common-control aliasing, because
    quorum math only helps if independence is real.

## v176 common-control provider independence

- `common_control_provider_independence_v1`
  - bounded common-control model over a three-provider quorum and five root
    fields: controller, beneficiary, infrastructure, signer operator, and slash
    pool.
  - best language is:
    `economic_identity_ok and operational_identity_ok and slash_pool_distinct`.
  - this is the unique minimal exact language in the candidate library over
    `3125` partition-product cases.

- `provider_independence_receipt_v1`
  - rejects nominal quorum-only evidence, controller-only checks, economic-only
    checks, and economic-plus-slash checks.
  - next frontier: privacy-preserving beneficial-ownership and
    operator-independence receipts, because exact identity checks may be costly
    or privacy-sensitive.

## v177 private provider independence receipt

- `private_provider_independence_receipt_v1`
  - bounded private-receipt language over 10 fields: hidden ZK independence
    relations, provider/epoch/domain binding, membership proof, nullifier
    freshness, root hiding, and domain unlinkability.
  - best language is:
    `zk_independence_ok and context_binding_ok and membership_freshness_ok and
    privacy_ok`.
  - this is the unique minimal exact language in the candidate library over
    `1024` Boolean cases.

- `privacy_is_part_of_safety_v1`
  - public root revelation, commitments-only receipts, unbound ZK proofs, stale
    nullifiers, and cross-domain-linkable proofs all false-accept some bounded
    bad cases.
  - next frontier: turn the symbolic private receipt into a concrete circuit
    interface and registry/nullifier design.

## v178 private provider receipt verifier interface

- `private_provider_receipt_verifier_interface_v1`
  - bounded verifier-interface language over 14 fields: circuit identity,
    verifying key, schema hash, registry root, provider key, epoch, domain,
    relation statement, nullifier scope/freshness, and canonical privacy output.
  - canonical best language is:
    `circuit_identity_ok and public_context_ok and relation_statement_ok and
    nullifier_binding_ok and privacy_output_ok`.
  - `minimal_exact_language_count = 2` because `relation_statement_ok` is an
    alias for the raw relation-binding field in this toy language.

- `proof_blob_is_not_receipt_v1`
  - rejected baselines include proof blob only, verifying-key without circuit
    id, unbound context, missing nullifier, nullifier without epoch, and privacy
    output without canonicalization.
  - next frontier: wire this interface into a runtime boundary and define the
    concrete verifier schema that an implementation must enforce.

## v179 FIRE reputation trust capacity

- `fire_reputation_trust_capacity_v1`
  - bounded reputation/trust task-market model that connects earlier trust
    economics to provider-independence and private-receipt work.
  - trust vector includes verified receipts, dispute accuracy, uptime, recent
    activity decay, slashing history, stake at risk, independence score, and
    domain expertise.
  - best mechanism is `fire_trust_capacity`.

- `trust_routes_risk_not_yield_v1`
  - trust controls capacity, finality, collateral efficiency, and evidence-role
    eligibility.
  - reward remains bounded by verified task value and task caps.
  - falsified alternatives: trust-yield multipliers, stake-weighted reputation,
    and flat receipt rewards without decay.
  - next frontier: governance-safe bounds for trust-vector weights.

## v180 reputation weight governance bounds

- `reputation_weight_governance_bounds_v1`
  - bounded governance-weight search over the v179 task market.
  - tests whether "trust as capacity" can still drift into oligarchy when
    governance changes the weight vector.
  - searches `8014` candidate policies: `6` named policies plus an `8008`
    point `1000` bps grid.

- `fire_reputation_weight_envelope_v1`
  - safe envelope:
    `stake_bps <= 1500`, `verified_receipts_bps <= 3000`,
    `recent_activity_bps >= 1000`, `independence_bps >= 1000`,
    `domain_expertise_bps >= 1000`, `slash_penalty_bps >= 4000`.
  - the grid finds `237` policies inside the envelope.
  - `fire_weight_bounds` is safe and beats the named capture baselines, while
    `grid_1541` is the best coarse-grid safe point in this bounded corpus.

- `oligarchic_drift_as_governance_weight_failure_v1`
  - stake capture, old receipt capture, weak independence, domain blindness,
    and no-decay receipt governance all fail in measurable ways.
  - next frontier: turn the envelope into an auditable runtime governance
    receipt for reputation parameter updates.

## v181 BPS revenue value flow frontier

- `bps_revenue_value_flow_frontier_v1`
  - first bounded token-unit search over FIRE fee parameters and net-revenue
    sink splits.
  - searches `194412` bps policies over swap improvement, exact-out savings,
    protection, automation, receipt, integrator, solver, stewardship, and sink
    split parameters.
  - finds `10782` survivors satisfying hard rails, no negative user actions,
    positive net protocol revenue, and positive burn.

- `value_density_fee_caps_v1`
  - important survivor object: notional-based fees must be capped by measured
    value density, not only broad launch rails.
  - bounded caps:
    protection `5` bps, automation `16` bps, integrator `10` bps, retail
    receipt `0` bps.
  - this suggests basic user receipts should be free, bundled, or charged only
    against measured surplus.

- `fee_on_improvement_survives_v1`
  - fee-on-improvement survives because it charges against demonstrated
    surplus rather than total notional.
  - zero fees fail to fund burn/security, notional-heavy fees create negative
    user actions, and pure burn starves productive budgets.
  - next frontier: replay this against real quote corpora and calibrate
    value-density distributions by action type.

## v133 AMM global budget object

- `global_cpmm_budget_object_v1`
  - strongest current AMM-theorem candidate from peer review:
  - compare candidate and CPMM at the same external price through a scalar
    original-HODL value budget, not through a pointwise global curvature
    identity.

- `homogeneous_to_normal_form_bridge_v1`
  - derive the paper normal form `L(m,d) = n*m + φ(d)` directly from smooth
    symmetric homogeneous invariants so the local/global theorem stack no
    longer keeps that step as a paper-only hypothesis.

- `same_price_value_ratio_object_v1`
  - make the global comparison object be
    `R_candidate(d) / R_cpmm(q_candidate(d))`, so the theorem is stated at the
    same external price rather than only at the same reserve coordinate.

- `symmetric_cubic_rescaling_bridge_v1`
  - if the implemented cubic kernel uses `x*y*(p*x + q*y)`, add the positive
    coordinate-rescaling bridge to the symmetric `X*Y*(X+Y)` form or restrict
    theorem claims explicitly to the symmetric slice.

## v71 bridge object

- `ratio_sheet_atlas_v1`
  - amount-only prefix floor-deficit profile plus reserve-normalized ratio sheet is nearly exact for anchored head code on the widened first-perturbed family.
- `reserve_decade_tiebreak_v1`
  - adding a coarse reserve-decade band resolves the last collision exactly.
  - treat this as a bridge object, not a breakthrough; compression is weak even though exactness is high.

## v72 fast-path object

- `dominant_easy_fan_v1`
  - direct amount-only arithmetic fan for the dominant easy mass on the widened first-perturbed family.
  - exact on its pure cells and covers about `93.7%` of total cases.
- `hybrid_fallback_mass_v1`
  - explicit quantitative split between exact fast path and symbolic fallback.
  - about `6.3%` of cases remain in ambiguous cells.

## v100 world-model contract object

- `shapeforge_contract_surface_v1`
  - typed world-model atlas over contract, gap, and evidence surfaces for ZenoDEX.
  - current strong slices: `exact_out_canonical_minimizer`, `settlement_strong_validation`, `kernel_abi_composition`, `perp_funding_epoch_gate`.
  - main use: queryable proposal -> counterexample -> proof backlog instead of free-form design notes.
  - next frontier: convert the exact-out minimizer, settlement bundle, composition mirror sync, and perps funding/oracle slices into replayable certificate lanes.

## v132 optimizer transfer atlas

- `mp215_optimizer_transfer_atlas_v1`
  - per-paper persistent loop for the useful *Mathematical Programming* volume 215 papers.
  - package each article as `ideas.md`, `insights.md`, and `plan.md`, then compile a deterministic report so later sessions can continue the same frontier.

- `optimization_duality_transfer_atlas_v2`
  - widened successor to the `mp215` loop.
  - extends the same deterministic paper-study shape to older optimization, duality, and market-design papers once they show a plausible ZenoDEX seam.

- `offchain_batch_qp_lane_v1`
  - current strongest transfer candidate from the paper study set.
  - treat large-scale convex QP as an offchain relaxation and candidate-generation lane, never as direct consensus execution.

- `local_velocity_projection_controller_v1`
  - strongest controller-search candidate from the paper study set.
  - use admissible-velocity local models for parameter search rather than full projection each step.

- `qp_candidate_handoff_boundary_v1`
  - explicit transfer law for convex solver lanes:
  - solver output is only advisory until a deterministic candidate/certificate layer admits it.

- `controller_search_handoff_boundary_v1`
  - explicit transfer law for constrained controller tuning:
  - optimizer output is only promotable after bounded replay and explicit guard certification.

- `bounded_certificate_ceiling_v1`
  - when a decision surface already has bounded enumeration plus a canonical certificate lane, external optimizers should be treated as advisory front-end shapers only.

- `shadow_controller_simplex_fragment_v1`
  - the current honest home for weighted-simplex-style controller tuning is the shell-side autotrader replay perimeter, not live decision certificates.

- `one_dimensional_monotone_ceiling_v1`
  - if the active repo surface is already a one-dimensional monotone decision with exact bounded search, complementarity reformulations should stay diagnostic rather than operational.

- `wasserstein_risk_envelope_v1`
  - use Wasserstein-ball DRO to shape shadow-side oracle and treasury risk envelopes when the ambiguity radius can be tied to a clear conservatism budget.

- `information_shadow_price_boundary_v1`
  - use shadow prices of information to quantify the value of fresher oracle, attestation, or external Tau information without pretending it is a live execution law.

- `wasserstein_perp_envelope_problem_v1`
  - robustify the existing replayable perps containment pack by optimizing threshold/buffer candidates against a Wasserstein ambiguity set over adverse replay scenarios.

- `oracle_attestation_shadow_problem_v1`
  - treat oracle freshness and attestation age as explicit information constraints whose shadow prices can be attached to audit-facing freshness boundaries.

- `bounded_experiment_beats_plausible_transfer_v1`
  - paper transfer candidates should clear a bounded measurable-baseline-improvement test before being treated as near-term prototypes.

- `attestation_age_first_anchor_v1`
  - on the first three-anchor information-shadow experiment, attestation age is the strongest initial audit-facing attachment point; oracle freshness is second, external Tau is too narrow to lead.

- `attestation_shadow_reporting_surface_v1`
  - a fixed-review-budget reporting surface that ranks cases by information-shadow pressure.
  - current honest result:
    - simple attestation-first scoring beats oracle-first scoring on shifted harmful-mass capture,
    - but the best learned surface is mixed oracle-plus-attestation rather than purely attestation-heavy.

- `illiquid_accounting_value_surface_v1`
  - use illiquid-market duality to derive accounting-value or indifference-value surfaces for treasury and insurance decisions under nonlinear costs and constraints.

- `duality_gap_honesty_gate_v1`
  - before trusting any stochastic controller or treasury dual object, require a no-duality-gap story rather than optimizing a mathematically elegant but operationally meaningless dual.

- `mconvex_route_exchange_certificate_v1`
  - use discrete convex exchange optimality to replace some bounded exact-out enumeration with a small local no-improving-transfer certificate.

- `breakpoint_dual_router_seed_v1`
  - treat two-pool and relaxed multi-pool splits as one-dimensional dual breakpoint problems before doing deterministic discrete correction.

- `breakpoint_plateau_canonicalizer_v1`
  - after a breakpoint-style seed recovers the right exact-in objective value, explicitly recover the leftmost equal-value plateau before treating it as a canonical solver.

- `breakpoint_canonical_scan_solver_v1`
  - on the bounded two-pool CPMM corpus, breakpoint seed plus explicit leftward equal-output scan is a real drop-in candidate because it preserved the canonical winner while staying materially cheaper than the current profile search.

- `breakpoint_widened_support_v1`
  - the same repaired breakpoint solver survived a widened CPMM corpus with larger reserves, wider fees, and larger stressed trade sizes while keeping exact support and a material quote-call advantage.

- `hot_started_knapsack_dual_v1`
  - exploit neighboring quote amounts with a hot-start Newton-style dual solve to reduce repeated routing effort.

- `hotstart_sequence_reuse_v1`
  - neighboring-amount reuse preserved the exact winner on the bounded two-pool CPMM sequence corpus, but only marginally beat the repaired breakpoint solver, so it currently belongs as a secondary amortization layer rather than a primary routing object.

- `spg_relaxation_seed_v1`
  - use projected-gradient relaxations to produce feasible continuous split seeds, then recover integer/canonical winners with local exchange cleanup.

- `generalized_flow_injection_oracle_v1`
  - for multi-hop routing, compute a node-level injection plan first and recover a canonical leg realization second, instead of searching directly over all leg flows.

- `lex_column_generation_batch_clearing_v1`
  - if the Tellache-style integer lex-program column-generation method really matches the `(A, B, lex_id)` batch objective, it is the strongest direct batch-clearing paper candidate because it targets the exact objective shape instead of an approximation surrogate.

- `knapsack_fptas_exact_out_v1`
  - if the Chen-style knapsack dynamic-programming compression can be adapted to exact-out multi-pool routing without breaking canonical tie recovery, it is a strong replacement candidate for bounded enumeration on at least the CPMM selected-domain surface.

- `exact_out_output_mass_dp_v1`
  - on the first bounded CPMM selected-domain corpus, exact-out canonical selection already collapsed to a direct DP over output mass with exact winner recovery.

- `selected_pool_allocation_dp_collapse_v1`
  - the same exact-out DP collapse survived widened CPMM and supported non-CPMM selected-domain corpora, suggesting that allocation inside a fixed selected pool set is not the main remaining bottleneck.

- `prefilter_completeness_is_the_real_exact_out_gap_v1`
  - after the selected-pool allocation problem collapses to DP, the honest unresolved difficulty becomes whether the selected candidate pool set is complete enough for the intended certificate notion, not automatically for winner correctness.

- `exact_out_dp_compression_ratio_v1`
  - the output-mass DP is not only exact on tested selected-domain corpora; it also keeps materially fewer states than the selected-domain candidate enumeration.

- `prefilter_gap_dominates_exact_out_v1`
  - random bounded audits show very low support-soundness rates for the current exact-out prefilter, but same-corpus repair checks show winner correctness and contraction can still survive; the main remaining exact-out problem is now a support/certificate gap, not inner allocation search.

- `exact_out_support_correctness_split_v1`
  - on the current bounded random corpus, poor prefilter support soundness coexists with exact canonical winner recovery and contraction; support completeness and winner correctness are different objects.

- `winner_cover_is_not_support_cover_v1`
  - the current bounded cover-search repair preserves the full-domain winner and contraction by selecting a minimal winner-support subset, but that same choice can drive support soundness to zero.

- `duplicate_pool_symmetry_support_gap_v1`
  - the smallest support-only exact-out gap already appears in a 4-pool fully symmetric CPMM family; early stopping can drop duplicate support while leaving the canonical winner unchanged.

- `benign_vs_threatening_support_gap_v1`
  - support gaps split into at least two classes:
    - benign duplicate-symmetry gaps that do not change the winner
    - heterogeneous gaps that can change the winner

- `heterogeneous_but_benign_support_gap_v1`
  - heterogeneity alone does not imply a winner gap; there is a large class of 4-pool heterogeneous support gaps that still preserve the canonical winner.

- `two_cluster_threatening_gap_v1`
  - the first threatening exact-out gaps arise in balanced two-cluster families with materially different pool quality, not merely from tiny heterogeneous perturbations.

- `quality_outlier_threat_pattern_v1`
  - winner-threatening exact-out gaps concentrate in quality-outlier patterns rather than in arbitrary mixed heterogeneity.

- `three_plus_one_outlier_gap_v1`
  - the strongest bounded threat class is a `3+1` family with one materially better outlier pool.

- `tied_cluster_completion_selector_v1`
  - a cheap selector that completes omitted tied cluster members repairs a meaningful fraction of threatening exact-out cases while preserving benign cases.

- `non_tied_outlier_second_ingredient_v1`
  - the remaining threatening cases are not fixed by tie completion; they need a second outlier-aware ingredient for omitted critical pools that are not tied to selected members.

- `partial_feasible_truth_audit_v1`
  - exact-out support and winner audits must range over pools feasible for some positive split up to `Q`, not only pools feasible at the full target.

- `small_probe_outlier_recall_v1`
  - a second smaller probe scale can recover omitted winner-critical pools that look bad at the full target but become attractive on smaller legs.
  - current bounded result:
    - meaningful partial repair on the corrected random corpus
    - while preserving benign cases

- `multi_probe_outlier_recall_v1`
  - one small secondary probe is not enough; a short family of probe scales repairs more threatening cases on the corrected corpus while preserving benign ones.

- `mid_scale_probe_ladder_v1`
  - some omitted critical pools are attractive only at intermediate split sizes, so the right selector object is a probe ladder rather than a pure small-scale recall rule.

- `slot_ceiling_last_miss_v1`
  - after truthful auditing plus a mid-scale probe ladder, the last bounded random-corpus exact-out miss is a candidate-slot ceiling rather than a ranking failure.

- `probe_ladder_cap5_exact_recovery_v1`
  - on the corrected random corpus, probe ladder plus `max_candidate_pools = 5` recovered the exact winner with no benign regressions.

- `dominant_pattern_probe_ladder_cap4_v1`
  - on the dominant structured threat-pattern families, probe ladder under the existing `4`-pool cap already achieved exact winner recovery with no benign regressions.

- `residual_random_slice_cap5_fallback_v1`
  - the cap-5 lift is currently justified only by the residual corrected random slice outside the dominant structured threat families.

- `anytime_feasible_mi_routing_v1`
  - an anytime-feasible mixed-integer method is attractive only if the intermediate feasible states are deterministic and certificate-friendly under fail-closed routing semantics.

- `anti_fragmentation_fee_axiom_v1`
  - a fee axiom paper that validates ZenoDEX's anti-fragmentation logic is valuable as a mechanism-proof object even if it does not improve a runtime solver.

- `decision_diagram_bilevel_fee_design_v1`
  - decision-diagram bilevel reformulations may be the first tractable exact path for fee design because fee setting is structurally leader-follower in ZenoDEX.

- `learned_mconvex_warmstart_v1`
  - learned acceleration for M-convex minimization becomes interesting only after a non-learned discrete-convex routing solver survives on ZenoDEX's bounded corpora.

- `nonlinear_dro_fee_tuning_v1`
  - nonlinear DRO is a stronger follow-on to Wasserstein-style robustness if fee or parameter losses are inherently nonlinear in the market distribution.

## Active frontier

1. `route_cover_sheaf_v1`
- Overlapping local route sections with explicit gluing quality.
- Main use: advisory routing confidence and local-to-global approximation control.

2. `route_defect_cocycle_v1`
- Overlap mismatch as a transport/obstruction norm.
- Main use: explain where local route approximations fail to glue.

3. `execution_braid_potential_v1`
- Canonical commuting rewrites act as an energy descent over admissible execution traces.
- Main use: collapse execution-order disorder into a monotone potential.

4. `normal_form_basin_v1`
- Admissible execution traces partition into normal-form basins with measurable compression and basin energy.
- Main use: summarize partially commuting execution spaces without enumerating all structure at runtime.
- Current note: useful, but coarse on the present corpus because all admissible orders collapse into one normal form.

5. `parallel_braid_depth_v1`
- Canonical rewrites admit a layered parallel normalization depth strictly smaller than sequential rewrite length.
- Main use: expose execution concurrency hidden inside the rewrite system.

6. `layer_skeleton_v1`
- Layered swap skeleton records independent rewrite work per round.
- Main use: schedule or price execution preprocessing by concurrency width rather than raw swap count.

7. `serial_fiber_shuffle_semiring_v1`
- Admissible execution traces factor exactly as shuffles of serial pool fibers.
- Main use: replace brute-force trace counting with an exact factorized law.

8. `prefix_progress_simplex_v1`
- Execution prefixes collapse to a small lattice of per-fiber progress counts.
- Main use: memoization, DP compression, and bounded search over execution states.

9. `simplex_dp_semiring_v1`
- Exact counts and aggregate braid energy can be computed by dynamic programming on the progress simplex.
- Main use: replace brute-force path summation with exact recursion on compressed states.

10. `simplex_occupancy_measure_v1`
- The progress simplex carries an exact occupancy measure for execution prefixes.
- Main use: path-integral style analysis over compressed execution states.

11. `simplex_flow_measure_v1`
- Exact execution mass moves along simplex edges with no schedule enumeration.
- Main use: edge-level transport analysis and structural bottleneck detection.

12. `simplex_cut_form_v1`
- Rank cuts in the simplex carry nonuniform edge concentration.
- Main use: identify bottleneck slices where execution mass concentrates.

13. `simplex_one_form_integral_v1`
- Additive path costs can be integrated exactly over simplex edge flow.
- Main use: exact aggregate cost computation on compressed execution geometry.

14. `simplex_divergence_law_v1`
- The compressed execution flow obeys an exact source-sink conservation law.
- Main use: correctness checks and transport-calculus style reasoning on execution space.

15. `simplex_bellman_potential_v1`
- Expected remaining braid energy is an exact Bellman potential on the progress simplex.
- Main use: exact future-value estimation on compressed execution states.

16. `simplex_branch_curvature_v1`
- Branch curvature measures where local execution choices materially change future cost.
- Main use: identify high-leverage decision states for scheduling or advisory control.

17. `simplex_policy_fan_v1`
- Best-next-step choices partition the progress simplex into a small number of policy regions.
- Main use: policy stratification over compressed execution states.

18. `simplex_boundary_mass_v1`
- Exact tie boundaries vanish, but near-boundary mass is substantial.
- Main use: quantify decision fragility when exact boundaries are too thin to matter.

19. `simplex_margin_field_v1`
- Near-optimal policy gaps form an exact scalar field over the simplex.
- Main use: track how decisively the control law prefers one move over another.

20. `simplex_instability_front_v1`
- Low-margin states cluster into a large instability front carrying significant occupancy mass.
- Main use: identify coherent fragile regions where control decisions are most sensitive.

21. `margin_shell_measure_v1`
- Fragility compresses into a tiny exact family of margin shells with large low-shell mass.
- Main use: coarse-grain the control geometry into quantized fragility levels.

22. `margin_shell_flux_v1`
- Execution transports mass across fragility shells with a measurable signed drift.
- Main use: determine whether execution tends to move into or out of fragile regimes.

23. `margin_shell_operator_v1`
- Margin shells support an exact quotient dynamic including terminal exit.
- Main use: tiny exact shell-level dynamics for fragility analysis.

24. `margin_shell_hazard_v1`
- Lower-margin shells have strictly higher exit hazard on the current corpus.
- Main use: hazard-based control and pricing around fragile execution regions.

25. `shuffle_inversion_kernel_v1`
- Pairwise inversion probability in a uniform interleaving has a closed negative-hypergeometric form.
- Main use: replace pairwise shuffle brute force with an exact kernel.

26. `pairwise_superposition_law_v1`
- Exact future inversion potential decomposes into deterministic backlog plus pairwise shuffle kernels over remaining commuting pairs.
- Main use: closed-form Bellman value on the execution simplex.

27. `min_key_policy_law_v1`
- The Bellman-optimal next action is exactly the available action with minimal canonical key on the current bounded corpus.
- Main use: exact greedy control without solving Bellman recursion online.

28. `key_margin_order_v1`
- Pairwise action-value order exactly matches canonical key order, with positive margins.
- Main use: certify that the greedy control law is not only optimal but strictly ordered.

29. `weighted_pairwise_superposition_v1`
- The pairwise kernel law survives arbitrary nonnegative lower-action weights as an exact uniform-schedule expected-cost law.
- Main use: weighted expected inversion analysis without brute-force schedule enumeration.

30. `weighted_min_key_invariance_v1`
- The min-key control law stayed invariant across the generated nonnegative weight family on the bounded corpus.
- Main use: robustness testing of the greedy law under weighted perturbations.

31. `abstract_weighted_merge_invariance_v1`
- The min-key control law survives an abstract bounded family of ordered-fiber execution shapes under nonnegative lower-action weight models.
- Main use: support a bounded universality claim that is not tied to one concrete corpus.

32. `pair_penalty_no_obstruction_v1`
- No counterexample appears on the same abstract family even under pair-specific nonnegative penalties.
- Main use: sharpen the boundary of where the greedy law still survives before searching for richer obstruction tensors.

33. `future_gate_obstruction_tensor_v1`
- Future-gated pair penalties are the first bounded family found to break the min-key law.
- Main use: expose the first genuine obstruction family and force a richer correction object.

34. `blocker_availability_correction_v1`
- Immediate future-gate debt plus blocker-availability suffix debt recovers most exact decisions in the future-gated family.
- Main use: first compact approximate correction score after the greedy law breaks.

35. `gate_feedback_value_law_v1`
- In the future-gated family, optimal future cost equals the minimum total gate weight that must be dropped to make the remaining precedence graph acyclic.
- Main use: exact value law replacing Bellman recursion with a feedback-style graph quantity.

36. `acyclic_completion_policy_law_v1`
- The optimal next action minimizes immediate violated gate weight plus acyclic completion cost of the remaining precedence graph.
- Main use: exact control law for the first true obstruction family.

37. `feedback_acyclicity_universality_v1`
- The gate-feedback value law survives a denser bounded family of unit-weight future-gate models with up to three active gates.
- Main use: show the exact graph law is not a sparse-model accident.

38. `feedback_policy_universality_v1`
- The acyclic-completion policy law survives the same denser family.
- Main use: strengthen the exact control law beyond the first obstruction search family.

39. `prefix_barrier_projection_v1`
- In bounded same-direction CPMM batches, exact optimal executed volume collapses to a one-dimensional cumulative-prefix barrier scheduling model.
- Main use: reduce batch volume optimization from permutation search to threshold scheduling.

40. `earliest_barrier_law_v1`
- Earliest-threshold-first is exact for executed volume in the bounded prefix-barrier batch model.
- Main use: exact greedy law for the volume component of batch clearing.

41. `barrier_surplus_gap_v1`
- After the exact volume collapse, earliest-barrier-first still preserves `A` and loses only a tiny amount of surplus `B` on the bounded corpus.
- Main use: isolate the residual surplus problem after quotienting the main volume geometry.

42. `barrier_surplus_cocycle_v1`
- The remaining surplus error after the barrier quotient behaves like a small bounded integer residual on the bounded CPMM corpus.
- Main use: first residual object for the `B`-component after exact `A` collapse.

43. `a_feasible_swap_graph_v1`
- In bounded same-direction CPMM batches, earliest-barrier order connects to an optimal order through a short sequence of adjacent swaps that preserves exact executed volume `A` at every step.
- Main use: constructive geometry for the residual search after quotienting by the volume model.

44. `unit_edge_cocycle_v1`
- Inside a barrier class, every `A`-preserving adjacent swap changes surplus by at most one unit on the bounded corpus.
- Main use: local residual law on the `A`-feasible swap graph.

45. `prefix_swap_curvature_form_v1`
- On regular `A`-preserving adjacent edges, the global surplus change equals an exact prefix-local two-swap CPMM output difference.
- Main use: exact local differential form for the residual `B` geometry on the `A`-feasible swap graph.

46. `quantized_curvature_v1`
- The prefix-local surplus differential on regular swap edges is unit-bounded and zero on most edges of the bounded corpus.
- Main use: sparse quantized local curvature law for the batch-clearing surplus residual.

47. `swap_cocycle_potential_v1`
- The regular-edge surplus cocycle on the bounded `A`-feasible swap graph integrates exactly to a global potential rooted at barrier order.
- Main use: global surplus potential on the regular residual graph after exact `A` collapse.

48. `swap_cycle_holonomy_v1`
- The regular-edge surplus differential is conservative on the bounded `A`-feasible swap graph, so cycle sums vanish on the connected component.
- Main use: zero-holonomy law for the regular residual surplus geometry.

49. `zero_plateau_quotient_v1`
- Collapsing zero-delta edges compresses the regular `A`-feasible swap graph into a tiny quotient that carries the real control obstruction.
- Main use: minimal control-state object above the exact regular-edge surplus potential.

50. `plateau_ascent_law_v1`
- After collapsing zero-delta plateaus, a max-surplus plateau is always reachable by positive-edge ascent on the bounded corpus.
- Main use: exact quotient-level ascent law for the residual batch-clearing surplus geometry.

51. `outlier_slot_potential_v1`
- In the fully permissive same-direction `3+1` batch family, the residual surplus potential depends only on the slot of the unique outlier, not on the permutation of the three equal peers.
- Main use: isolate the next rare obstruction family after plateau quotient ascent into a one-coordinate slot law.

52. `outlier_phase_atlas_v1`
- After additive normalization, the `3+1` outlier slot law collapses to a tiny finite atlas of phase signatures.
- Main use: finite classification object for the first rare post-quotient obstruction family.

53. `outlier_slot_universality_v1`
- On a broader zero-min `3+1` amount grid, the residual surplus still depends only on the slot of the unique outlier.
- Main use: demonstrate that the outlier-slot object survives scale broadening beyond the original bounded corpus.

54. `outlier_phase_plane_v1`
- Once the `3+1` slot law is widened in scale, the normalized phase atlas expands but remains finite.
- Main use: phase-diagram object for the first rare residual family under broader scale variation.

55. `outlier_phase_fan_v1`
- The broadened `3+1` slot law organizes into a finite phase fan on the amount plane rather than an unstructured cloud of signatures.
- Main use: cell decomposition object for the broader outlier residual family.

56. `phase_adjacency_graph_v1`
- The broader `3+1` phase fan has a small connected adjacency graph with low diameter and a highly central neutral phase.
- Main use: combinatorial skeleton of the broader phase-boundary geometry.

57. `outlier_gradient_field_v1`
- The broadened `3+1` slot law is more primitively carried by a finite adjacent-slot gradient field.
- Main use: differential carrier for the broader outlier phase geometry.

58. `gradient_phase_correspondence_v1`
- On the broadened `3+1` family, normalized slot phases and adjacent-slot gradient triples are in exact one-to-one correspondence.
- Main use: exact bridge between additive phase geometry and differential phase geometry.

59. `generator_defect_pocket_v1`
- In a denser high-load near-diagonal `3+1` window, the direct local prefix-gradient generator fails only on a sparse subset of cases.
- Main use: isolate the first real obstruction above the broader gradient-field law.

60. `generator_defect_alphabet_v1`
- The defect pocket of the direct local generator uses only a tiny finite alphabet of nonzero defect vectors.
- Main use: reduce generator failure geometry to a finite symbolic obstruction set.


61. `trailing_gradient_exactness_v1`
- On the widened zero-min `3+1` grid, the direct local generator gets the last adjacent-slot gradient exactly in every checked case.
- Main use: expose a causal/triangular exactness law in gradient coordinates before attempting a full local correction.

62. `front_gradient_filtration_v1`
- On the same widened grid, every remaining generator defect lives entirely in the first two gradient coordinates, with a tiny integer alphabet and `L1` mass at most `2`.
- Main use: compress generator failure into a front-supported defect filtration rather than a global phase failure.


63. `suffix_completion_law_v1`
- On the widened zero-min `3+1` grid, the true gradient equals the direct local gradient plus omitted-suffix completion corrections, with the trailing correction vanishing identically.
- Main use: exact triangular correction law for the local generator in gradient coordinates.

64. `suffix_correction_alphabet_v1`
- The nontrivial suffix corrections collapse to a tiny 7-symbol pair alphabet with coordinates in `{-1,0,1}`.
- Main use: reduce the correction problem to a finite low-mass suffix grammar rather than arbitrary front noise.


65. `suffix_carry_chain_v1`
- The first suffix correction factors exactly into first omitted-peer carry plus terminal omitted-peer carry.
- Main use: reduce the correction pair to a more primitive carry-chain object.

66. `terminal_carry_sparsity_v1`
- The terminal omitted-peer carry is nonzero only rarely and is always unit-valued.
- Main use: localize the last unresolved complexity of the widened `3+1` correction law.


67. `unit_reserve_gap_v1`
- At the terminal omitted-peer step, the two branch states always share the same input reserve and differ in output reserve by at most one unit on the widened grid.
- Main use: isolate the terminal correction to a one-unit reserve perturbation law.

68. `terminal_floor_crossing_v1`
- The rare terminal carry is exactly the one-unit floor-crossing event induced by that terminal reserve gap.
- Main use: reduce the last unresolved correction to a pure arithmetic threshold event.


69. `equal_fiber_trailing_exactness_v1`
- On widened equal-fiber `n+1` families with `n=4,5`, the direct local generator still gets the trailing gradient coordinate exactly.
- Main use: promote the `3+1` triangular law into a broader equal-fiber phenomenon.

70. `prefix_defect_cone_v1`
- Across the same widened equal-fiber families, remaining defects stay prefix-supported with tiny `L1` mass.
- Main use: expose a broader prefix-supported defect cone beyond the original `3+1` family.

## Deferred ideas

1. Patch sheaf over multi-route covers.
2. Tropical patch algebra for route + privacy + confidence.
3. Defect transport across batch-clearing rewrite steps.
4. Canonical rewrite/groupoid laws for multi-pool execution fragments.
5. Proof sheaf over DEX microkernels.

## Falsified or weakened

1. `extremal_dyadic_obstruction_tree_v1`
- The tested split rule lost to uniform sampling.
- Keep only as a falsified branch unless a stronger curvature-aware split law appears.

2. `execution_transport_defect_v1`
- The minimum-transport formulation collapsed: normalized space did not beat the raw optimum on the tested corpus.
- The useful lesson was to replace transport minimization with rewrite-energy descent and basin geometry.

71. `equal_fiber_tail_universality_v1`
- Across widened equal-fiber families `n=3..8`, the trailing defect coordinate stays exactly zero and defect amplitude stays unit-bounded on the dense 35k..55k window.
- Main use: isolate the universal part of equal-fiber correction geometry before support-shape complexity appears.

72. `interval_breakpoint_v1`
- The simple interval-support regime survives through `n=5` and breaks first at `n=6` with witness `(a,b)=(35000,42000)`, defect `(1,0,1,0,0,0)`.
- Main use: identify the first family-level phase transition in equal-fiber support geometry.

73. `single_crossing_suffix_law_v1`
- Across widened equal-fiber families `n=3..8`, each defect coordinate equals a suffix carry chain with at most one nonzero unit event.
- Main use: turn the family-level correction from a defect table into a tiny event process.

74. `monotone_unit_gap_walk_v1`
- The suffix carry event is generated by a monotone output-reserve gap walk with values in `{-1,0,1}` and unit step changes.
- Main use: explain the single-crossing law structurally via a unit-bounded state process.

75. `signed_block_gap_law_v1`
- Across widened equal-fiber families `n=3..8`, the reserve-gap process along each omitted suffix is always a signed block followed by zeros.
- Main use: collapse the family-level carry process to a tiny deterministic state law.

76. `last_nonzero_event_law_v1`
- The suffix carry chain is exactly the last nonzero event of that signed block gap walk.
- Main use: determine the entire correction chain from a single event index.

77. `equal_fiber_corrected_generator_v1`
- Local gradients plus the last-nonzero gap event reconstruct the exact widened equal-fiber signature.
- Main use: exact family-level corrected generator without brute-force order search.

78. `equal_fiber_signature_compiler_v1`
- The signed-block gap law compiles the exact equal-fiber signature directly.
- Main use: first direct algorithmic payoff from the widened equal-fiber object stack.

79. `single_perturbed_peer_transfer_v1`
- The exact equal-fiber compiler remains exact on a majority of one-perturbed-peer cases and leaves only a tiny residual alphabet elsewhere.
- Main use: first stability/transfer law beyond the exact equal-fiber family.

80. `dominant_prefix_tail_cone_v1`
- For the one-perturbed-peer family, almost all nonzero transfer residual mass lies in simple prefix or tail support cones.
- Main use: advisory residual model for near-equal-fiber transfer rather than brute-force recomputation.

81. `two_generator_transfer_cone_v1`
- The one-perturbed-peer transfer residual is mostly carried by the tail singleton and the full-prefix block.
- Main use: compress the first transfer residual into a tiny cone instead of a flat defect table.

82. `three_generator_near_exact_transfer_v1`
- Adding one mid-tail generator covers almost the entire one-perturbed-peer transfer family, leaving only 9 exceptional cases.
- Main use: near-exact transfer law just beyond the exact equal-fiber family.

83. `small_perturbation_cone_universality_v1`
- The 3-generator transfer law is exact on the bounded one-perturbed-peer family for perturbation magnitude at most 2000.
- Main use: exact transfer region immediately beyond the exact equal-fiber family.

84. `large_downshift_exception_pocket_v1`
- All remaining transfer failures lie at larger perturbations, with most in the downward-perturbation pocket.
- Main use: isolate the next correction search to a tiny exceptional regime.

85. `transfer_generator_tower_v1`
- The first perturbed-family transfer residual compresses into a hierarchical basis tower: 3 generators cover the exact small-perturbation region and 711/720 cases overall, 5 generators cover 718/720, and 7 generators span the full family.
- Main use: compact transfer-basis hierarchy immediately beyond the exact equal-fiber family.

86. `exact_perturbed_peer_basis_v1`
- Seven explicit generators span the entire one-perturbed-peer transfer residual family exactly.
- Main use: exact residual basis for the first non-equal family beyond the exact compiler.

87. `gradient_transfer_basis_v1`
- The first perturbed-family transfer residual closes exactly in gradient space with only 6 generators.
- Main use: cleaner exact residual basis than signature space for the first transfer family.

88. `gradient_signature_compression_v1`
- Gradient space compresses the first perturbed-family residual from 21 signature symbols to 17 gradient symbols, and the exact residual basis from 7 generators to 6.
- Main use: identify the right coordinates for further transfer-law search.

89. `interval_boundary_basis_v1`
- The first perturbed-family transfer residual has an exact semantic interval-boundary basis of size `6`: five prefix-drop generators and one head-tail bridge interval.
- Main use: semantic exact basis for the first transfer family, cleaner than an arbitrary vector basis.

90. `triple_interval_grammar_v1`
- Every gradient residual in the first perturbed-family transfer is representable as a sum of at most `3` interval-boundary generators.
- Main use: exact semantic grammar for transfer residuals beyond equal-fiber symmetry.

91. `interval_normal_form_v1`
- Every first perturbed-family gradient residual has an exact minimal interval decomposition; the mass splits into `428` zero cases, `279` one-interval cases, `12` two-interval cases, and only `1` three-interval case.
- Main use: near-canonical semantic normal form for the full transfer family.

92. `double_interval_dominance_v1`
- `719 / 720` first perturbed-family transfer cases are covered by at most two interval-boundary generators; only one pattern requires three.
- Main use: exact near-classification showing the residual is almost entirely two-interval.

93. `singleton_exception_pocket_v1`
- In the broadened downshift/outlier window, the strongest three-interval target-gradient defect remains a single witness: `(a,c,b) = (40000,35000,41000)`.
- Main use: isolate the sharpest residual pocket as a singleton rather than a diffuse exception family.

94. `two_interval_universality_v1`
- Across the broadened downshift/outlier window (`360` cases), all but `2` cases lie in the zero/one/two-interval regime.
- Main use: upgrade the interval normal-form claim from a corpus fact to a stronger near-universality law on a widened family.

95. `resonance_line_v1`
- In the first broadened downshift/outlier window, all >2-interval cases lie on the perturbation-gap line `delta - epsilon = 4000`.
- Main use: first boundary law for the remaining interval-grammar exceptions.

96. `spike_uniqueness_v1`
- On that resonance line, each feasible perturbation pair contributes exactly one exceptional spike in `a`.
- Main use: compress the boundary law from a diffuse line to isolated spikes.

97. `exception_gradient_atlas_v1`
- On a much wider lattice, the >2-interval tail still collapses to only `10` cases and `7` gradient symbols.
- Main use: widened exceptional atlas showing the interval grammar remains highly compressed beyond the near window.

98. `reserve_level_exception_atlas_v1`
- Those widened >2-interval exceptions concentrate on only `4` reserve levels.
- Main use: identify reserve-scale concentration as the next structural coordinate for the exception law.

99. `exception_motif_atlas_v1`
- On the widened lattice, the >2-interval tail collapses from 7 raw gradient symbols into 7 semantic interval motifs.
- Main use: replace symbol-level exception handling with motif-level exception handling.

100. `motif_family_collapse_v1`
- Those 7 widened motifs collapse exactly into 4 semantic families.
- Main use: exact family grammar for the far-field interval exceptions.

101. `tail_charge_classifier_v1`
- The 4 widened exceptional motif families are determined exactly by the last gradient coordinate.
- Main use: one-scalar classifier for the far-field exceptional atlas.

102. `tail_charge_universality_v1`
- The widened exceptional atlas collapses to only four tail-charge values: `1, 2, -2, -1`.
- Main use: identify tail charge as the right far-field coordinate for the next correction law.

103. `super_tail_ladder_v1`
- On the larger lattice, the only observed four-interval breach is the old three-interval target family with a unit lift in its final coordinate.
- Main use: first higher-order extension law beyond the three-interval grammar.

104. `four_interval_uniqueness_v1`
- On the larger lattice, only one gradient symbol needs more than three intervals: `(-1, 0, 1, -1, 2)`.
- Main use: prove the first higher-order breach is unique rather than a broad new regime.

105. `tail_floor_deficit_law_v1`
- On the enlarged one-perturbed-peer lattice (`24000` cases), the far-field tail charge equals the rounded terminal local floor-deficit difference exactly.
- Main use: first exact reserve-arithmetic law for the far-field exception classifier.

106. `subcritical_continuous_tail_v1`
- The continuous terminal local-swap residual stays strictly below `1/2` everywhere on that lattice, with maximum observed magnitude `0.1272411832765057`.
- Main use: stability margin proving the rounded floor-deficit classifier is robust.

107. `tail_ladder_quantization_v1`
- The old three-interval rung and the four-interval super-tail rung occupy disjoint floor-deficit bands near `1` and `2`.
- Main use: quantized ladder law for the first higher-order breach.

108. `super_tail_threshold_v1`
- A single threshold at `1.5` separates the three-interval and four-interval ladder branches exactly on the current larger lattice.
- Main use: exact bifurcation law for when the super-tail lift turns on.

## v62
- `tail_flux_floor_duality_v1`: on the widened one-perturbed-peer lattice, the tail exception coordinate is exactly the same scalar whether computed as interval-boundary tail flux or as the arithmetic terminal floor-deficit law.
- `head_tail_interval_factorization_v1`: every widened first-perturbed-family gradient residual factors exactly into a scalar tail charge plus a zero-tail head residue; on the 24k-case lattice the head atlas has finite size and the tail charge remains bounded by 2.

## v63
- `head_residue_interval_normal_form_v1`: after removing the exact scalar tail coordinate, the widened first-perturbed-family head residue still admits an exact bounded interval grammar.
- `unit_head_atlas_v1`: the widened head residue atlas is finite and unit-valued; every head coordinate lies in {-1,0,1}.

## v64
- `head_disjoint_interval_law_v1`: after removing the exact scalar tail coordinate, the minimal head interval decomposition is always pairwise disjoint on the widened first-perturbed family.
- `head_block_forest_v1`: the widened head residue is therefore a tiny disjoint block forest with at most three blocks.

## v65
- `head_semantic_forest_atlas_v1`: the exact 31-pattern widened head forest atlas collapses to 12 semantic families once only block types are retained.
- `head_forest_type_dominance_v1`: almost the entire widened head side lies in the zero / one-block / prefix-suffix semantic families.

## v66
- `head_boundary_word_atlas_v1`: the widened head semantic forest grammar collapses to a 9-word signed boundary language.
- `span_resolved_family_code_v1`: the only 3 ambiguous boundary words are resolved exactly by a simple span/gap code.

## v67
- `ambiguous_word_gap_law_v1`: the only three ambiguous widened head boundary words are resolved exactly by their internal gap pattern.
- `oriented_gap_comparison_v1`: for the nontrivial 3-boundary words, family type is decided by a simple oriented comparison of the two interior gaps.



97. `symbolic_head_compiler_v1`
- Head family type should be treated as a symbolic code object, not a raw forest atlas.
- Use: exact widened head-family compilation from boundary word plus tiny gap law.

98. `vectorized_gpu_proxy_v1`
- Test whether the best exact objects already have the right compute shape for GPU scaling.
- Result: yes for batched tail scalar and head-word kernels.

99. `compiler_kernel_factorization_v1`
- Treat the current perturbed-family compiler as a kernel stack: map / compact / tiny-branch.
- Use: bridge the math objects into a future advisory GPU/phone accelerator path.


100. `anchored_head_code_v1`
- After symbolic family classification, test whether adding one anchor coordinate reconstructs the exact head residue, not just the head family.

101. `perturbed_residual_compiler_v1`
- Combine exact anchored head reconstruction with the exact tail scalar law to obtain a full residual compiler on the first transfer family.

## v71-v74
- `ratio_sheet_atlas_v1`: exact amount-only bridge atlas for widened first-perturbed-family head state using prefix floor-deficit profile and reserve-normalized ratio sheet; useful as evidence that the head side is close, but not yet a compressed law.
- `reserve_decade_tiebreak_v1`: coarse reserve-decade band removes the final ambiguity in the v71 bridge atlas.
- `dominant_easy_fan_v1`: exact amount-only fast-path gate for the dominant easy mass on the widened first-perturbed family.
- `hybrid_fallback_mass_v1`: two-stage hybrid exactness is 99.025% on the widened first-perturbed family.
- `sheet_residue_exactifier_v1`: exact residual-stage amount-only exactifier on the remaining 234 ambiguous cases using reserve-sheet ratio plus terminal reserve residue.
- `three_stage_amount_compiler_v1`: exact three-stage amount-only compiler on the widened first-perturbed family.

## v75
- `three_stage_kernel_algebra_v1`: exact three-stage direct-amount compiler expressed explicitly as a kernel algebra over the widened first-perturbed family.
- `vectorized_three_stage_compiler_v1`: exact batched execution of the three-stage compiler; exact, but naive batching alone does not yet improve wall-clock speed.

## v76-v77
- `gap_pair_nonzero_word_law_v1`: within the stage-3 nonzero residual, head boundary word is almost determined by the simple amount-space coordinate `(a-c, b-a)`.
- `pocket_digit_tiebreak_v1`: the remaining five ambiguous gap-pair pockets can be resolved exactly by a tiny digit-level tiebreak.
- `gap_pair_decade_law_v1`: the cleaner formulation of the same effect: reserve decade `c // 10_000` resolves the five ambiguous nonzero pockets exactly.


## v78
- `gap_tail_resonance_pocket_v1`: on the stage-3 nonzero residual, `(gap_pair, tail_charge)` is exact on `76 / 78` cases and leaves only one ambiguous resonance pocket of mass `2`.
- `single_pocket_scale_threshold_v1`: that sole resonance pocket is resolved exactly by a coarse reserve-scale threshold on `c // 10_000`.

## v79
- `reserve_ratio_quantization_band_v1`: on the stage-3 nonzero residual, `gap_pair + round(S*c/a)` is exact across a wide quantization band (`203` exact scales in `1..300`).
- `minimal_exact_ratio_quantizer_v1`: the smallest exact scale is `S = 35`, and it improves the exact symbolic nonzero residual law from `78` keys down to `77` keys.

Interpretation:
- This is a cleaner exactifier than reserve decade because it is a reserve-normalized arithmetic coordinate rather than a coarse bucket.
- It is still a symbolic-state compiler, not yet the final compressed arithmetic head law.


## v80
- `stage3_ratio_digit_exactifier_v1`: the full `234`-case stage-3 residual is classified exactly by `fallback_key + round(53*c/a) + a_mod10`, reducing the exactifier key count from `234` to `226`.
- `stage3_exactifier_plateau_v1`: the same arithmetic exactifier shape is exact across a broad scale plateau (`234` exact scales in `1..300`), with best scale `S = 53`.

Interpretation:
- This is the first exact compression improvement on the full stage-3 residual, not just the nonzero slice.
- It is a better direct-amount exactifier than the old reserve-sheet bridge key, but it is still not yet the final compressed deep law for the head side.


## v81
- `tail_pressure_bit_carrier_v1`: the nonzero stage-3 residual is classified exactly by `(gap_pair, tail_charge, boundary_sign@0)` with `77` keys.
- `dual_boundary_sign_carrier_v1`: the same nonzero residual is classified exactly by `(gap_pair, boundary_sign@0, boundary_sign@3)` with `77` keys.

Interpretation:
- These are semantically cleaner than the old reserve-decade tiebreak for the nonzero stage-3 slice.
- They do not improve the best full stage-3 exactifier from `v80`; their value is explanatory and structural rather than a full-residual compression win.

## Next frontier after v84
- Try to explain `triadic_band_scalar(b)` from reserve-floor geometry rather than treat it as a pure quantization artifact.
- Search whether the scalar band is equivalent to a head-side interval-flux residue or a reserve-normalized pressure staircase.
- Revisit full staged acceleration using the cleaner scalar stage-3 exactifier instead of the older digit rule.

## Next frontier after v85
- Test whether `fallback_boundary_word` itself can be predicted from a smaller arithmetic carrier once `fallback_ratio_bucket`, `round(52*c/a)`, and `triadic_band_scalar(b)` are known.
- Search whether the residual ambiguity is controlled by a tiny head-side arithmetic flux or pressure-sign coordinate.
- Revisit acceleration after symbolic reduction: the reduced stage-3 law is a better kernel target than the older full fallback-key exactifier.

## Next frontier after v86
- Test whether `first_support(amount_profile)` itself has a direct arithmetic law from simpler reserve/floor coordinates.
- Search whether the scalar stage-3 exactifier can collapse from 4 scalars to 3 without losing the broad exact plateau.
- Revisit end-to-end vectorized/GPU scaling on the cleaner fully scalar exactifier.

## Next frontier after v87
- Test whether `first_support(amount_profile)` can be fused with one of the remaining two scalar coordinates.
- Search for a true 2-scalar exactifier, or prove a lower bound/irreducibility for the current 3-scalar law.
- Revisit end-to-end accelerated compilation now that the stage-3 exactifier is fully scalar and smaller.

- Next target after `v90`: characterize which exact one-scalar weights minimize key count and whether `208` is optimal by a collision-geometry argument rather than brute-force search.
- Try to derive the forbidden-weight spectrum directly from support-class interval separation to turn the v90 collision theorem into a geometric law.

## next after v97
- explain why the safe-merge optimum stops at 8 using collision geometry, not brute-force search
- classify which support-gap-1 same-label merges are admissible before the first cross-label pinch
- test whether the same chamber-pinch law appears in nearby families beyond the widened first-perturbed family

## next after v99
- classify admissible same-label support-gap-1 merges by support class and label, not just count
- test whether the four-class support atlas transfers to nearby perturbed families
- ask whether chamber optimality can be stated as: maximize unit-gap safe merges subject to first cross-label pinch

## next after v100
- test whether span-1 ladder optimality transfers to nearby perturbed families
- classify the 4 span-1 large-merge weights by support-class atlas and compare against 728
- search for a direct family transfer law for the support-ladder optimum

## next after v101
- search for a route-side support atlas or chamber law analogous to the batch scalar optimum line
- test whether the ternary overlap grammar transfers to larger reserve/fee grids and exact-out route families
- ask whether adaptive refinement can be driven purely by the interval grammar without brute-force interval search

## next after v104
- Batch line: test whether the support-class transfer code `(L,z01,n01)` extends beyond the exact large-merge weights to nearby exact-weight windows and nearby perturbed families.
- Routing line: search for a route-side chamber or support-atlas transfer law on top of the semantic star fan and axis-rigidity objects.

## next after v108
- Extend the transfer ladder beyond pure modulus lifts: for `merge>=2`, search for the first exact low-complexity lift beyond `(Omega, mod m)` and beyond `(Omega, mod m, merge/max_span)`.
- Test whether the phase-lattice interpretation has a support-class quotient explanation: `mod 4` as a genuinely 2-adic phase and `mod 18` as `(mod 9, parity)`.
- On the routing side, search for a chamber or transfer law on top of the `v103` semantic star fan.

## next after v109
- Determine whether the `merge>=2` composite phase `mod 91` has a direct collision-geometric explanation in terms of support-class families rather than as a bare arithmetic modulus.
- Test whether `merge>=1` admits a similar enriched support signature plus composite phase, or whether the transfer ladder breaks again there.
- For routing, search for a support-word transfer law across neighboring star-fan families.

## next after v110
- Search for the first exact `merge>=1` lift beyond one-extra-stat enrichment: likely a new support-class object, not just another modulus.
- Determine whether the transfer ladder `1,4,18,91` has a multiplicative/collision-family law rather than being a sequence of isolated moduli.
- On routing, continue from the star-fan by testing support-word transfer codes between neighboring semantic families.
## v113
- `no_one_interaction_crt_merge1_v1`: `merge>=1` still resists the next natural enrichment: full local support counts plus one interaction bit plus a curated CRT phase pair.
- `merge1_threshold_frontier_v1`: the transfer ladder is now sharp through `merge>=2`, and `merge>=1` remains beyond the one-extra-stat and one-interaction-CRT regimes.
## v114
- `route_neutral_incidence_code_v1`: neutral-incidence bitmasks are not enough to recover bounded route semantic families.
- `route_neutral_prefix_code_v1`: neutral-incidence plus a tiny symbolic prefix code on the two support words is exact on the bounded route family.
## v115
- `merge1_full_histogram_lift_v1`: `merge>=1` admits an exact lift once the full same-label support histogram is used, with exact phase `mod 821`.
- `merge1_minimal_modulus_v1`: `821` is the minimal exact single modulus for that full-histogram lift on the bounded family.
## v116
- `route_minimal_triad_code_v1`: bounded route semantic families are recovered exactly by neutral incidence plus a minimal 3-feature code.
- `route_triad_family_count_v1`: no 1- or 2-feature enrichment works, but there are 17 exact 3-feature triads.
## next after v118
- Search whether the `merge>=1` asymmetric quotient admits a semantic interpretation sharper than `zero-side (-1,0)` vs rest plus nonzero total mass.
- Test whether the `55`-signature quotient can be combined with a smaller modulus than `821` after refining the zero-side block semantics.
- Probe whether the route triad line admits an analogous asymmetric quotient between the two support words.
## next after v119
- Since support compression no longer reduces the minimal modulus, focus the next search on the phase side: look for a quotient of the `821`-phase space or a CRT/chamber decomposition of the merge>=1 exact regime.
- Test whether the routing triad code has an analogous phenomenon: support code compressed, phase complexity unchanged.
## next after v121
- Explain why the largest exact chamber is `[1737, 1769]`.
- Explain the monotone density ramp of exact moduli as modulus approaches the automatic exact regime.
- Search for a chamber law that predicts chamber starts and ends from divisor/collision geometry instead of enumerating the exact set.
## next after v123
- Explain which within-class differences are absent across `[1737, 1769]`, since upper-half exactness has collapsed to self-difference avoidance there.
- Search for a compressed law for upper-half chamber lengths using only the raw difference set, not the full divisor closure.
## next after v124
- Search for a grammar of upper-half gap lengths from the ordered raw difference set.
- Ask whether large upper-half chambers are controlled by local scarcity of difference values rather than global divisor structure.
## next after v125
- Search for a grammar of upper-half gap lengths, not just the chamber set.
- Explain why all upper-half chambers with length `> 8` localize in the upper half of the upper-half regime.
- Test whether the long-gap zone is controlled by a local scarcity measure on consecutive self-differences.

## v126-v127 next ideas

- Search for a chamber or divisor law behind the prime-rigid `821` merge-1 phase.
- Test whether the route triad factorization admits a smaller chamber/phase object on top of the 17 exact triads.
- Look for a route-side support-atlas transfer law analogous to the batch support-class ladder.
## v128
- `merge1_divisor_spectrum_law_v1`: exactness on the `merge>=1` asymmetric quotient is governed by the complement of within-class divisor collisions up to the maximal span.
- `merge1_upper_half_gap_run_law_v1`: above half the maximal span, exactness simplifies further to missing-run geometry in the ordered self-difference set.
- Next: derive a gap-length grammar and local scarcity law for the `merge>=1` upper-half chambers.
## v130
- Validated `record_gap_spine_v1`: long upper-half exact chambers form a monotone record spine with records `(1512,1520,9)`, `(1597,1608,12)`, `(1644,1667,24)`, `(1669,1695,27)`, `(1737,1769,33)`.
- Validated `threshold_tail_bands_v1`: long-gap thresholds activate in nested tail bands: `>12` starts at `1644`, `>24` starts at `1669`, `>28` and `>32` start at `1737`.
## v131 next ideas
- Measure how a liquidation penalty, SP dilution share, or commit-before-liquidate rule deforms or removes the pending-liquidation band.
- Turn the pending-liquidation band into a kernel-level acceptance test if liquidation is supposed to depend on committed prices only.
- Extend the full-SP band to partial SP ownership `s`, where profitability should collapse to `s * collateral * pending_price > debt`.

## exact-out next ideas
- `omitted_pair_slot_ceiling_fallback_v1`
  - threat-triggered `cap5` fallback for exact-out probe-ladder selection when the residual winner class is a two-pool omitted pair rather than a dominant outlier family already fixed by `cap4`.
- `omitted_pair_signature_v1`
  - detect whether a non-selected pool pair has complementary mid-scale exact-out quality strong enough to justify one extra slot before paying for a blanket cap lift.

## journal scan backlog
- `tellache_linear_lex_column_generation`
  - Transportation Science 2024: exact column generation for linear integer lexicographic optimization.
  - Best current fit for batch clearing / lex winner-selection objects.
- `maher_ronnberg_ip_column_generation`
  - Mathematical Programming Computation 2023: generate columns that are useful for high-quality integer solutions, not just LP relaxations.
  - Best current fit for bounded candidate-set growth control and certificate-friendly lex/batch search.
- `vasquez_lozano_van_hoeve_binary_bilevel_dd`
  - Mathematical Programming 2025: single-level reformulation of binary bilevel programs using decision diagrams.
  - Best current fit for fee-design / mechanism-design bilevel objects.
- `wirth_pena_pokutta_open_loop_fw`
  - Mathematical Programming 2025: accelerated affine-invariant Frank-Wolfe with open-loop step sizes.
  - Best current fit for continuous advisory relaxations and warm-started controller search.
- `luteberget_sartor_feasibility_jump`
  - Mathematical Programming Computation 2023: LP-free Lagrangian MIP heuristic.
  - Best current fit for anytime feasible advisory/bounded-search sidecars, not consensus runtime.
- `joswig_loho_scaling_over_polytope_vertices`
  - Mathematical Programming 2021: scaling algorithm for optimizing arbitrary functions over vertices of polytopes.
  - Best current fit for column-generation quality bounds and augmentation-style progress certificates.

## journal scan hidden gems

- `adjustability_robust_linear_optimization_v1`
  - *Mathematical Programming* 2024.
  - Hidden gem for ZenoDEX's oracle/attestation timing frontier because it turns the value of information and decision timing into a concrete optimization object, including a sharp zero-adjustability test.

- `integer_column_generation_high_quality_solution_v1`
  - *Mathematical Programming Computation* 2023.
  - Hidden gem for candidate-set growth because it explicitly uses pricing to improve integer feasible solutions, not only LP bounds.

- `tellache_lex_column_generation_v1`
  - *Transportation Science* 2024.
  - Strongest direct batch-clearing paper candidate because it is about exact linear lexicographic optimization via column generation, which is much closer to ZenoDEX's lex winner-selection story than generic MIP heuristics.

- `bilevel_decision_diagram_reformulation_v1`
  - *Mathematical Programming* 2025.
  - Strongest hidden gem for fee/mechanism design because it removes repeated follower solves through a single-level decision-diagram reformulation.

- `feasibility_jump_anytime_sidecar_v1`
  - *Mathematical Programming Computation* 2023.
  - Useful as an anytime feasible advisory sidecar only if intermediate feasible states can be made deterministic and certificate-friendly.

- `adjustable_information_timing_gate_v1`
  - New transfer law suggested by the robust-adjustability paper:
  - if zero adjustability can be certified for a bounded information-timing slice, then the static policy is already information-tight on that slice and no richer dynamic controller is justified.

## wide journal sweep additions

- `k_adaptability_policy_bundle_v1`
  - *Mathematical Programming*.
  - Hidden gem for bounded policy bundles and scenario-to-policy assignment because it gives an exact branch-and-price view of finite policy families.

- `resource_allocation_equilibrium_computation_v1`
  - *Mathematical Programming* 2022.
  - Hidden gem for exact equilibrium computation on splittable resource-allocation structures; potentially useful for offchain equilibrium or multimarket controller analysis.

- `fleet_assignment_decomposition_recipe_v1`
  - *Mathematical Programming* 1995.
  - Hidden gem as an industrial decomposition recipe: not directly a DEX paper, but strong for learning how to make very large integer programs operational through staged reformulation and engineering.

- `tseng_separable_coordinate_descent_v1`
  - *Mathematical Programming* 2009.
  - Hidden gem for shadow-side controller tuning over separable penalties and smooth-plus-separable objectives; likely theory/advisory only, not a routing winner object.

- `almost_linear_convex_flow_v1`
  - arXiv 2203.00671 / near-linear exact max-flow and min-cost-flow with extension to edge-separable convex flow.
  - Hidden gem for future multi-hop routing or offchain convex-flow relaxations, not a direct replacement for current canonical integer split-routing yet.

- `bounded_policy_bundle_kadapt_v2`
  - Small `K` policy bundles on the information-timing seam can deliver large bounded gains over the best static allocation; in the first mixed synthetic seam, `K = 3` already matched the full ex-post oracle.

- `single_lane_zero_adjustability_slice_v1`
  - On the bounded information-timing seam, pure oracle-only, attestation-only, and Tau-only families behave like zero-adjustable slices; only mixed families justify richer dynamic bundles.

- `integer_destroy_repair_selector_v1`
  - Start from the current `probe_ladder_cap4` exact-out selector and run a one-swap destroy-repair pass scored by the exact selected-domain canonical winner.
  - Strongest current use:
    - repair CPMM residual omitted-pair misses without widening the candidate-pool cap.

- `slot_replacement_beats_cap_lift_v1`
  - On the matched widened CPMM smoke slice, one-swap integrality-aware replacement repaired all threatening cases while `cap5` repaired only part of them.
  - Current honest role:
    - same-budget selector repair first,
    - cap-lift fallback second.

- `cheap_inversion_trigger_v1`
  - Best current balanced gate for the Maher repair lane:
    - `omitted_better_pool_count >= 1 and winner_leg_count >= 2`
  - On the widened CPMM corpus it caught `87.5%` of threatening cases while cutting amortized repair spend from about `10.21` to `1.125`.

- `trigger_family_stabilization_v1`
  - Extending the same cheap feature family from pair conjunctions to triple conjunctions gave no improvement; the best triple was just the current pair trigger plus a vacuous `omitted_count >= 1`.

- `singleton_residual_fallback_v1`
  - The remaining widened-CPMM Maher miss is a singleton-incumbent class with no cheap omitted-pool inversion signal.
  - Simple residual singleton fallbacks recover exact recall, but they are too blunt to promote because they fire on too much benign mass.

- `plateau_lex_column_bridge_v1`
  - After the exact `A` collapse and zero-delta plateau quotient in bounded same-direction CPMM batch clearing, residual plateaus act like an honest restricted lex master.
  - Positive-frontier plateau pricing recovered the exact lex winner on the first `200` nontrivial residual cases while pricing only about half the plateau set on average.

- `global_exact_out_dd_v1`
  - A layered decision diagram over all pools recovered the exact full-domain canonical exact-out winner on the first bounded wide corpora.
  - Current honest role:
    - stronger bounded reference oracle than selector-plus-fixed-set DP alone,
    - because the DD absorbs both support selection and allocation into one exact carrier.

- `decision_diagram_state_compression_v1`
  - On the same bounded wide corpora, the global exact-out DD kept materially fewer states than the truthful full-domain candidate enumeration:
    - about `12.4%` of candidates on `cpmm_wide`,
    - about `7.3%` of candidates on `supported_wide`,
    - with mean state-fraction ratios `0.409` and `0.221` respectively because the DD counts layered states rather than only terminal candidates.

- `exactness_first_global_dd_reference_v1`
  - On the matched bounded wide comparison, the global DD beat `probe_ladder_cap4 + fixed-set DP` on `cpmm_wide` exactness (`1.0` vs `0.9375`) at nearly the same total quote-call budget.
  - Honest role:
    - bounded exactness-first reference oracle,
    - not yet a blanket runtime replacement, because the fixed-set DP lane still uses fewer internal states.

- `dd_beats_guarded_maher_on_exactness_v1`
  - On the matched widened CPMM slice, the global DD stayed exact while the guarded Maher lane fell to `0.875`.
  - Honest role:
    - DD remains the strongest exact bounded oracle even after the best current local selector repair,
    - Maher remains the cheaper guarded runtime-side repair lane.

- `projected_relaxed_dd_objective_law_v1`
  - On the widened exact-out corpora tested so far, the out-mass-only relaxed DD already gives the exact objective value.
  - That means the remaining difficulty is not the primary objective but canonical tie recovery.

- `tiny_restricted_dd_canonical_lane_v1`
  - The exact canonical winner survives on very small restricted widths once enough tie memory is restored:
    - `cpmm_wide`: width `3`
    - `supported_wide`: width `6`
  - This is a stronger object than “DDs help”; it is a tiny bounded carrier law.

- `objective_frontier_projection_canonicalizer_v1`
  - On the widened exact-out corpora, once the exact objective frontier is isolated, even the out-mass-only frontier carrier recovers the exact canonical winner.
  - So the remaining DD frontier is not tie-memory recovery but cheap objective-frontier recovery.

- `relaxed_frontier_composed_dd_lane_v1`
  - On the widened exact-out DD seam, the exact relaxed objective table plus out-mass frontier projection recovered the exact canonical winner with no extra quote work beyond the relaxed table.
  - This shifts the promotion target from “objective certificate only” to a composed frontier-construction lane.

- `dd_frontier_residual_survival_v1`
  - The composed relaxed-objective plus frontier-projection DD lane also survives the omitted-pair CPMM residual family that previously justified special selector handling.
  - That makes it a harder-corpus exactness object, not just a broad random-corpus result.

- `supported_reserve_only_dd_boundary_v1`
  - The composed relaxed-objective plus frontier-projection DD lane is not universal across supported structured patterns.
  - It survives `2+1+1::multi_template`, but fails on supported `3+1::reserve_only` and `2+2::reserve_only` because the relaxed objective underestimates the true optimum.

- `legaware_relaxed_boundary_repair_v1`
  - The supported `reserve_only` DD boundary is explained by dropping the max-legs constraint from the relaxed objective carrier.
  - A leg-aware relaxed carrier repairs the boundary exactly, but appears too expensive to promote because it uses more than `2x` the exact-DD state mass with no quote savings.

- `dd_declared_domain_contract_v1`
  - The composed DD lane now has an explicit declared domain:
    - `cpmm_wide`
    - `cpmm_residual_omitted_pair`
    - supported `2+1+1::multi_template`
  - The supported `reserve_only` patterns are excluded and should fall back to exact DD.

- `dd_declared_domain_oracle_posture_v1`
  - On the declared included slices, the composed DD lane is best treated as a bounded exactness oracle, not as the default runtime lane.
  - Its unique exactness lift is concentrated in `cpmm_wide`; the strongest selector lanes already hit parity on the residual CPMM and supported multi-template slices.

- `dd_declared_domain_guard_v1`
  - The DD promotion contract can be encoded as a simple route policy:
    - composed DD on all-CPMM slices and supported `2+1+1::multi_template`,
    - exact DD fallback on supported `reserve_only`,
    - selector default elsewhere.

- `dd_guarded_oracle_shadow_lane_v1`
  - On the currently classified corpus, the guarded DD oracle lane is exact while the runtime selector lane lands at `0.996567`.
  - The DD lane's unique lift remains small but real and is isolated to the composed-DD route.

- `dd_mixed_replay_shadow_harness_v1`
  - A runtime-neutral mixed replay-style harness can log route choice, guarded answer, selector answer, and disagreement flags per case.
  - On the current replay mix, the guarded DD lane stays exact and the observed lift is concentrated in the composed-DD CPMM route.

- `dd_shadow_log_schema_v1`
  - The DD shadow lane now has an explicit per-case log contract:
    - route
    - reason
    - truth quote
    - guarded quote
    - selector quote
    - disagreement flag
    - route-specific work stats

- `composed_dd_cpmm_runtime_candidate_v1`
  - On the larger all-CPMM replay slice, the composed DD route is both more exact and cheaper in quote work than the selector lane.
  - That raises it from “oracle only” to a real bounded shadow/runtime candidate for the all-CPMM route.

- `cpmm_dd_runtime_bar_v1`
  - The CPMM composed-DD route now has an explicit replay-based promotion bar:
    - route fenced to all-CPMM only,
    - exactness `1.0` on maintained replay corpus,
    - mean guarded quote cost no worse than selector,
    - per-case JSONL disagreement review.

- `cpmm_dd_reusable_shadow_runner_v1`
  - The larger CPMM shadow pass is now a reusable CLI runner with configurable seed, corpus width, report path, and JSONL log path.

- `cpmm_dd_runtime_bar_check_v1`
  - The CPMM route promotion bar can now be checked mechanically from the replay report and JSONL log.
  - It returns criterion-level pass/fail plus a single overall status artifact.

- `dd_shadow_adapter_v1`
  - The guarded DD lane now has a non-core adapter surface in `src/integration/`.
  - It exposes:
    - route decision
    - guarded DD quote
    - selector quote
    - disagreement metadata under the canonical exact-out key
  - This is the right runtime-adjacent object to reuse before any core-facing promotion discussion.

- `dd_shadow_cli_v1`
  - The guarded DD lane now has a file-driven replay/shadow CLI in `tools/`.
  - It can evaluate JSON case bundles through the adapter and emit summary JSON plus per-case JSONL without depending on the experiment harness directly.

## v133 lookup-table semantic compiler

- `lookup_bao_compiler_v1`
  - finite compiler from symbolic unary lookup tables into exact BAO-valid operators on `P(W)`.
  - accepts the relation-induced / atom-image class and exposes nonadditive tables as semantic failures.

- `thresholded_q_operator_v1`
  - threshold a per-action Q-table at the atom level, then extend by union to get an exact unary operator.
  - current honest role: bounded symbolic-controller semantics, not consensus-critical runtime logic.

- `relation_image_acceptance_gate_v1`
  - use atom-image factorization as the admission test for new custom unary operators before allowing them into Tau-side semantics.

## v134 binary lookup-table semantic compiler

- `binary_lookup_bao_compiler_v1`
  - finite compiler from symbolic binary lookup tables into exact separately additive operators on `P(W)`.
  - accepts the ternary-relation / pair-atom class and exposes arbitrary pair tables as semantic failures.

- `ternary_relation_acceptance_gate_v1`
  - use pair-atom factorization as the admission test for new custom binary operators before allowing them into Tau-side semantics.

- `mixed_carrier_operator_compiler_v1`
  - next generalization target:
  - compile `P(S) x P(C) -> P(S')` symbolic tables for state/capability/target semantics once the same additivity story is formalized.

## v135 typed mixed-carrier semantic compiler

- `typed_lookup_bao_compiler_v1`
  - finite compiler from symbolic mixed-carrier lookup tables into exact separately additive operators on `P(S) x P(C) -> P(T)`.
  - accepts the typed ternary-relation / typed pair-atom class and exposes arbitrary mixed-carrier tables as semantic failures.

- `typed_operator_acceptance_gate_v1`
  - use typed pair-atom factorization plus separate additivity as the admission test for new Tau-side operators.

- `state_capability_target_operator_library_v1`
  - next library target:
  - build observation, capability, and transition operators on top of the same typed compiler pattern.

## v136 typed operator acceptance gate

- `typed_operator_acceptance_gate_v1`
  - deterministic checker for custom typed operators on `P(S) x P(C) -> P(T)`.
  - emits accepted or rejected plus explicit violated checks and canonical pair-atom images on success.

- `canonical_pair_atom_receipt_v1`
  - accepted operators should persist a canonical pair-atom image receipt, not just a yes or no verdict.

- `tau_operator_registry_gate_v1`
  - next integration target:
  - require every proposed Tau-side custom operator to pass the typed acceptance gate before registry admission.

## v137 typed operator registry gate

- `typed_operator_registry_gate_v1`
  - deterministic registry admission for custom typed operators on `P(S) x P(C) -> P(T)`.
  - accepts exactly when the typed semantic gate passes and the canonical semantic receipt is fresh for both operator id and semantic hash.

- `semantic_receipt_hash_v1`
  - canonical hash of operator dimensions plus canonical typed pair-atom images.
  - gives a stable identity for semantic duplicates independent of operator naming.

- `receipt_backed_tau_operator_manifest_v1`
  - next integration target:
  - persist admitted operators as a manifest of operator ids, semantic hashes, and canonical receipts so Tau-side custom operators are registry-backed rather than ad hoc.

## v138 receipt-backed Tau operator manifest

- `receipt_backed_tau_operator_manifest_v1`
  - canonical manifest for typed operators on `P(S) x P(C) -> P(T)`.
  - retains exactly one legal owner per semantic receipt hash and stores the replayable semantic receipt alongside the human-facing operator id.

- `manifest_verify_v1`
  - fail-closed verifier for manifest artifacts.
  - checks entry-hash consistency, uniqueness, canonical ordering, receipt replay, and manifest-hash correctness.

- `tau_operator_manifest_checker_v1`
  - next integration target:
  - a small file-oriented checker that validates manifest JSON without importing the experiment harness.

## v139 Tau operator manifest checker

- `tau_operator_manifest_checker_v1`
  - file-oriented checker for typed operator manifest JSON artifacts.
  - accepts exactly when parsing, schema checks, and semantic manifest verification all succeed.

- `manifest_file_receipt_v1`
  - compact checker receipt with path, parse result, schema result, semantic verification result, and final acceptance bit.

- `tools_check_typed_operator_manifest_v1`
  - next integration target:
  - extract the checker into a repo-level tool so manifest validation can run outside the experiment package.

## v140 Tau operator library bootstrap

- `tau_operator_library_bootstrap_v1`
  - tiny manifest-backed library bootstrap for typed Tau-style operators.
  - loads exactly when the manifest is accepted and the required role bindings are present.

- `manifest_checked_operator_roles_v1`
  - named role bindings such as `Obs_i`, `Can_a`, and `Next_a` resolved only through manifest-backed operator ids.

- `repo_level_operator_library_bootstrap_tool_v1`
  - next integration target:
  - extract the library bootstrap into a repo-level tool or loader over a checked manifest plus a role-binding config.


## v141 score-table typed operator compiler

- `score_table_typed_operator_compiler_v1`
  - bounded compiler from autotrader-shaped score tables into accepted typed operators on `P(S) x P(C) -> P(T)`.
  - accepts atom-local score families after typed pair-atom compilation and rejects direct full-table thresholding when separate additivity fails.

- `atom_local_score_semantics_v1`
  - if a score family is attached to typed pair atoms, thresholding plus union extension yields a lawful operator candidate that can go through the existing acceptance/manifest/library path.

- `direct_full_score_rejection_v1`
  - direct thresholding on full subset tables is not semantic by default; it must still survive the typed acceptance gate or remain heuristic metadata.

- `controller_surface_from_scores_v1`
  - a tiny `Obs_i/Can_a/Next_a` surface can already be compiled from bounded score families and matched against the current sample controller corpus.


## v142 score-table symbolic policy synthesizer

- `score_table_symbolic_policy_synthesizer_v1`
  - bounded synthesizer from score-compiled role outputs into symbolic source policies of the current `(decision_role, allow_mask)` grammar.
  - exposes representability, ambiguity, and impossibility on the bounded controller corpus.

- `bounded_policy_ambiguity_class_v1`
  - the current sample labels are representable by multiple policies in the bounded grammar.
  - canonical selection is possible, but semantic uniqueness still needs more corpus constraints.

- `canonical_policy_from_score_outputs_v1`
  - a deterministic representative can be chosen by a total key over `(decision_role, allow_mask)` and then pushed into the existing source-policy lane.


## v143 policy identifiability corpus search

- `policy_identifiability_corpus_search_v1`
  - bounded search for the smallest extra corpus that collapses symbolic-policy ambiguity under the current `(decision_role, allow_mask)` grammar.
  - shows that one extra case collapses the `Obs_i` ambiguity, but the residual `(Can_a,1)` vs `(Can_a,3)` class is structurally aliased on the full bounded domain.

- `residual_mask_alias_v1`
  - on the current bounded `Can_a` family, masks `1` and `3` induce the same boolean policy everywhere.
  - exact cause: `bit2(Can_a) -> bit1(Can_a)` on every bounded case.

## v144 policy equivalence quotient

- `policy_equivalence_quotient_v1`
  - bounded quotient of the current `9` syntactic `(decision_role, allow_mask)` policies by full bounded-domain boolean decision equivalence.
  - compresses the grammar to `8` semantic classes and isolates the only nontrivial alias class as `{(Can_a,1), (Can_a,3)}`.

- `quotient_level_policy_synthesis_v1`
  - the right synthesis target is the semantic class, not the raw syntactic policy.
  - at the quotient level, the original `3`-case corpus has `2` matching classes and the augmented corpus with case `2:2` has a unique matching class.

- `canonical_alias_class_metadata_v1`
  - use the lexicographically smallest policy as the administrative representative of a semantic class, while carrying the residual alias members as explicit metadata rather than pretending the class is syntactically unique.

## v145 quotient policy PCC bridge

- `quotient_policy_pcc_bridge_v1`
  - bounded bridge from the `v144` quotient winner into the existing non-core Tau operator artifact chain.
  - shows that the unique augmented quotient class can be represented by canonical policy `(Can_a,1)` and compiled through lowering, evidence, signing, deployment, and PCC-obligation layers.

- `quotient_alias_metadata_bridge_v1`
  - residual full-domain aliases should travel as explicit metadata alongside the canonical representative.
  - current surviving alias metadata is `{(Can_a,1), (Can_a,3)}` while the canonical representative remains `(Can_a,1)`.

- `pcc_reachable_from_quotient_policy_v1`
  - quotient-level symbolic synthesis is already strong enough to hit a current PCC obligation on the bounded non-core chain.
  - this closes the gap between the score-table/controller discovery line and the artifact-trust pipeline.

## v146 alias-aware symbolic policy lane

- `alias_aware_symbolic_policy_lane_v1`
  - bounded integration of quotient alias metadata into the non-core symbolic policy lane.
  - shows that alias-aware symbolic policies are first-class artifacts that still lower cleanly through evidence, signing, deployment, and PCC-obligation layers.

- `alias_metadata_first_class_policy_identity_v1`
  - adding quotient alias metadata changes the symbolic policy hash while leaving the bounded lowered artifact semantics unchanged.
  - provenance becomes explicit policy identity instead of an experiment-side sidecar only.

- `alias_metadata_survives_pcc_lane_v1`
  - the current residual alias class `{(Can_a,1), (Can_a,3)}` survives explicitly in source policy, lowering receipt, evidence bundle, and PCC obligation.
  - this closes the provenance gap between quotient synthesis and the artifact-trust pipeline.

## v147 direct alias policy synthesizer

- `direct_alias_policy_synthesizer_v1`
  - direct bounded emitter from the `v144` quotient winner into an alias-aware symbolic policy artifact using the repo-level symbolic-policy builder.
  - removes the experiment-side sidecar step while preserving the current residual alias class `{(Can_a,1), (Can_a,3)}` as first-class policy metadata.

- `exact_v146_artifact_reproduction_v1`
  - the direct emitter reproduces the `v146` alias-aware symbolic policy artifact exactly, including policy hash, rather than merely reproducing its lowered behavior.
  - this makes the builder path a canonical artifact constructor, not just a semantics-preserving alternative.

- `direct_alias_policy_reaches_current_pcc_lane_v1`
  - the directly emitted alias-aware symbolic policy still lowers cleanly through lowering receipt, evidence bundle, signed bundle, deployment receipt, and PCC obligation.
  - this closes the remaining gap between quotient synthesis and direct non-core artifact generation.

## v148 alias-aware replay corpus classifier

- `alias_aware_replay_corpus_classifier_v1`
  - bounded classifier for replay corpora at the quotient-class level using the alias-aware symbolic policy schema.
  - cleanly separates true multi-class ambiguity from residual in-class aliasing.

- `quotient_unique_alias_bearing_corpus_v1`
  - a corpus can be identification-ready even when the winning class has multiple syntactic members, as long as those members are carried as alias metadata inside one quotient class.
  - on the current grammar, both the augmented corpus and the full bounded domain are quotient-unique but alias-bearing through `{(Can_a,1), (Can_a,3)}`.

- `replay_hash_stability_for_unique_class_v1`
  - once a replay corpus isolates the same unique quotient class, the emitted alias-aware symbolic policy hash is stable across corpus sizes and matches the direct `v147` artifact.
  - this gives a replay-level criterion for when policy synthesis is stable enough to feed the artifact-trust lane.

## v149 two-literal controller family pressure

- `two_literal_controller_family_pressure_v1`
  - bounded quotient study of a richer monotone controller family with `atom`, `and`, and `or` over the current role outputs.
  - shows that widening the controller family from single literals to two-literal formulas materially increases replay pressure.

- `richer_family_augmented_corpus_failure_v1`
  - the current augmented replay corpus that isolates a unique class in the old role/mask grammar still leaves `4` quotient classes alive in the richer two-literal family.
  - grammar widening is therefore a replay-corpus problem before it is a schema problem.

- `simplicity_canonicalization_survives_widening_v1`
  - even in the richer two-literal family, the unique full-domain matching class has simplest canonical representative `atom(Can_a,1)`.
  - the richer family widens the frontier, but its full-domain winner still normalizes back to the current simple canonical policy.

## v150 minimal replay extension for richer family

- `minimal_replay_extension_for_richer_family_v1`
  - bounded minimal-witness search for the richer two-literal controller family starting from the current augmented replay corpus.
  - shows the current augmented corpus is close but not sufficient: no 1-case extension works, while a 2-case extension already recovers uniqueness.

- `targeted_replay_upgrade_pair_v1`
  - the first minimal witness pair is `{1:1, 1:2}`.
  - this turns “collect more replay cases” into a concrete next corpus upgrade for the richer family.

- `minimal_extension_preserves_simple_winner_v1`
  - the minimal replay extension still recovers the same canonical class `atom(Can_a,1)` with member count `13`.
  - richer-family replay upgrades can therefore strengthen identification without forcing immediate schema growth.

## v151 richer family replay upgrade bridge

- `richer_family_replay_upgrade_bridge_v1`
  - bounded bridge from the richer two-literal controller family, after the exact replay upgrade from `v150`, back into the current non-core artifact lane.
  - shows the upgraded richer family isolates one class and still reaches a current PCC obligation.

- `same_selector_richer_provenance_v1`
  - the upgraded richer-family winner preserves the same selector and atom-level alias members as `v147`.
  - the source-policy hash changes only because the richer family carries a different provenance object (`quotient_object_id`), not because the bounded policy meaning changed.

- `corpus_gap_not_schema_gap_v1`
  - the pressure seen in `v149` was a replay-corpus deficiency, not evidence that the symbolic policy schema must widen immediately.
  - once the minimal witness pair is added, the richer family normalizes back to the current simple artifact surface.

## v152 three-literal family upgrade stability

- `three_literal_family_upgrade_stability_v1`
  - bounded stability check for the replay-upgraded corpus under the next larger monotone controller family with formulas of up to three literals.
  - shows the exact replay upgrade from `v150` already isolates one quotient class in this larger family.

- `upgrade_generalizes_beyond_two_literals_v1`
  - the witness pair `{1:1,1:2}` is not narrowly fitted to the two-literal family.
  - it also collapses the three-literal family to the same unique class while the old augmented corpus still leaves `5` classes alive.

- `bounded_monotone_stability_of_atom_can_a_1_v1`
  - the unique upgraded/full-domain class in the three-literal family still canonicalizes to `atom(Can_a,1)` with member count `198`.
  - this is stronger bounded evidence that the current simple policy surface is stable under monotone family widening.

## v153 monotone closure saturation

- `monotone_closure_saturation_v1`
  - exact fixed-point closure of the current literal signatures under pointwise `and` and `or` on the bounded domain.
  - shows the full monotone closure has `26` semantic classes.

- `three_literal_family_already_saturates_closure_v1`
  - the bounded three-literal family from `v152` already reaches all `26` closure classes.
  - no larger monotone family over the same literals can add new semantic classes on this bounded domain.

- `upgraded_corpus_is_full_monotone_baseline_v1`
  - the replay-upgraded corpus still isolates one class in the full monotone closure, with canonical representative `atom(Can_a,1)`.
  - the upgraded replay corpus is therefore a full monotone baseline for the current literal set, not just a witness for one family size.

## v154 boolean atom partition closure

- `boolean_atom_partition_closure_v1`
  - exact Boolean closure of the current literal signatures, computed by taking the atom partition of the bounded `4x4` domain and then all unions of those atoms.
  - shows the current literals induce `9` Boolean atoms, so the full Boolean closure has `512` semantic classes.

- `non_monotone_frontier_opens_after_v153_v1`
  - `v153` closed the monotone lane at `26` classes, but the Boolean closure immediately jumps to `512` classes on the same literals.
  - this proves the non-monotone lane is a genuinely new frontier, not a restatement of the monotone closure.

- `upgraded_corpus_not_boolean_complete_v1`
  - the replay-upgraded corpus that isolates one class in the full monotone closure still leaves `8` Boolean classes alive, while the full bounded domain isolates one.
  - stronger replay baselines or new literals are now the honest next progress objects if Boolean expressivity matters.

## v155 Boolean-closure minimal replay extension

- `boolean_closure_minimal_replay_extension_v1`
  - exact minimal-witness search for the full Boolean closure frontier starting from the replay-upgraded corpus from `v150`.
  - shows the Boolean lane needs `3` extra cases, not `1` or `2`, to collapse from `8` surviving classes to a unique class.

- `three_free_atoms_explain_boolean_gap_v1`
  - the replay-upgraded corpus leaves exactly three Boolean atoms unconstrained: `[0,3,6]`.
  - the Boolean ambiguity is therefore structural and exact, not an artifact of the search procedure.

- `boolean_witness_family_has_atom_representative_form_v1`
  - every minimal Boolean witness has the same shape: one representative from the large all-false atom, plus `1:3` and `2:3`.
  - this turns the next replay upgrade into a simple atom-cover rule instead of a long case list.

## v156 Boolean atom basis corpus

- `boolean_atom_basis_corpus_v1`
  - minimal replay basis for the full Boolean closure induced by the current literals.
  - shows the exact reusable baseline is one representative per Boolean atom, so the minimal Boolean-complete corpus size is `9`.

- `minimal_boolean_complete_corpus_count_v1`
  - there are exactly `14` minimal Boolean-complete corpora, given by the product of the current atom multiplicities.
  - this turns the replay baseline into a combinatorial object rather than a single ad hoc case list.

- `current_literals_need_no_more_formula_growth_v1`
  - once the Boolean atom basis exists, every current-literal Boolean policy family is identified by labels on that basis.
  - future progress on expressivity now requires new literals or genuinely new operator families, not more formulas over the same literals.

## v157 input-test literal refinement

- `input_test_literal_refinement_v1`
  - bounded search over new input-side source/capability test primitives, quotienting them by semantic pattern on the current `4x4` domain.
  - shows the current candidate library has `16` raw primitives but only `14` distinct semantic classes.

- `best_single_input_refiners_v1`
  - the strongest single new tests raise the current `9`-atom basis to `11` atoms by splitting both residual multi-case atoms.
  - the best singleton quotient classes are represented by `src_bit1`, `src_eq_cap`, `src_full/src_pop_ge_2`, `src_gt_cap`, `src_subset_cap`, and `src_xor_cap_nonzero`.

- `coordinate_bit_basis_is_unique_v1`
  - the unique minimal basis that fully separates the bounded `4x4` domain is `{src_bit1, src_bit2, cap_bit1, cap_bit2}`.
  - this makes the next safe semantic extension direction explicit: guarded input-coordinate tests, not more formulas over the old literal set.

## v158 input-augmented monotone closure

- `input_augmented_monotone_closure_v1`
  - exact monotone closure on the bounded `4x4` domain after augmenting the old output-literal generators with the unique input-coordinate basis from `v157`.
  - shows the positive policy language jumps from `26` classes to `167` classes.

- `old_replay_basis_breaks_under_new_primitives_v1`
  - the old replay-upgraded corpus and the `v156` Boolean atom basis both still leave `4` matching classes alive under the enlarged monotone family.
  - this proves replay sufficiency is relative to the primitive set, not an absolute property of the corpus.

- `current_target_still_size_one_alias_v1`
  - even after the primitive expansion, the current target remains a size-1 generator alias carried by `Can_a:1` and `Can_a:3`.
  - the new primitives enlarge the language, but they do not yet change the current canonical target selector.

## v159 augmented monotone basis repair

- `augmented_monotone_basis_repair_v1`
  - exact minimal replay repair for the augmented monotone closure from `v158`, starting from the canonical Boolean atom basis from `v156`.
  - shows the enlarged primitive set needs only a 2-case repair, and that repair is unique.

- `unique_augmented_basis_repair_witness_v1`
  - the unique minimal witness is `{0:3, 3:0}`.
  - this turns the replay repair for the current primitive set into a deterministic baseline rather than a family of alternatives.

- `repaired_basis_for_current_primitive_set_v1`
  - the current repaired replay baseline is:
    - `v156` Boolean atom basis
    - plus `{0:3, 3:0}`
  - this is now the right corpus object for any further pressure tests over the current primitive set.

## v160 coordinate-basis monotone completeness

- `coordinate_basis_monotone_completeness_v1`
  - exact comparison between the closure generated by the four coordinate-bit primitives from `v157` and the full set of monotone Boolean functions on the bounded 4-bit input cube that vanish at zero.
  - shows those two sets are exactly equal, both of size `167`.

- `current_positive_language_is_complete_v1`
  - the current coordinate-bit basis already generates the full positive Boolean language available on the bounded input cube.
  - no additional positive-formula growth over these coordinates can add new semantic classes.

- `old_output_literals_are_positive_redundant_v1`
  - adding the old output literals does not enlarge the coordinate-bit monotone closure.
  - this means the current positive-language center of gravity has shifted fully onto the input-coordinate basis.

## v161 non-monotone adjoinability frontier

- `nonmonotone_adjoinability_frontier_v1`
  - exact bounded search over adjoining a six-primitive non-monotone relational library to the complete coordinate-bit positive basis from `v160`.
  - shows the base positive closure of size `167` can grow to at most `1176` in the current library, still far below the full Boolean algebra size `65536`.

- `current_nonmonotone_library_has_exact_growth_frontier_v1`
  - the best singleton, pair, and triple frontiers are `328`, `533`, and `966`, and the first maximal basis is `{src_subset_cap, cap_subset_src, src_lt_cap, src_gt_cap}`.
  - this turns the current non-monotone lane into an exact bounded frontier object instead of an open-ended formula-growth guess.

- `extra_relational_candidates_do_not_complete_boolean_lane_v1`
  - adding `src_eq_cap` and `src_xor_cap_nonzero` on top of the first maximal size-4 basis does not push beyond `1176`.
  - this means the next honest source of expressivity is new non-monotone primitives or guarded-action structure, not more reuse of the current six candidates.


## v162 Boolean algebra runtime posture

- `free_boolean_syntax_runtime_quotient_v1`
  - use the countable/free Boolean algebra only as the abstract syntax ceiling for pure tests.
  - runtime semantics should remain a finite executable quotient with canonical parity checks.

- `cantor_prefix_runtime_carrier_v1`
  - the current `CantorPrefixRegion` lane is better understood as a bounded clopen carrier, not as an approximation to a complete atomless runtime algebra.
  - this sharpens the engineering story for the existing Cantor-region assurance bundle work.

- `operator_enrichment_requires_new_receipts_v1`
  - BAO/KAT/GKAT style enrichment is the meaningful next algebraic frontier, but every enrichment should be treated as a fresh semantic object with explicit lowering/parity receipts.

## v163 disaster guard hitting quotient

- `disaster_guard_hitting_quotient_v1`
  - exact bounded quotient search over `18` named ZenoDEX disaster axes by required obligation atoms.
  - compresses the current corpus to `13` obligation classes and finds a unique minimal `7`-guard family covering every class and every named axis.

- `obligation_atom_frontier_v1`
  - turns the next disaster-state search into a sharper question: does a candidate state reuse an existing obligation class, or does it force a new obligation atom?
  - this is stronger than only adding more named scenarios because it separates duplicate examples from genuinely new safety language.

- `quotient_coverage_lean_bridge_v1`
  - adds a Lean-checked transfer law: if two axes require the same obligations, guard coverage of one representative transfers to the other.
  - the local proof library now has `156` checked theorem declarations in the concrete bridge project.

## v164 proof-carrying disaster antichain minimizer

- `proof_carrying_disaster_antichain_minimizer_v1`
  - strengthens the equality quotient from `v163` into a dominance-pruned antichain under obligation-set inclusion.
  - compresses the current frontier from `18` named axes to `13` equality classes, then to `10` subset-maximal representatives.

- `downward_coverage_invariant_v1`
  - proves and tests the core invariant: `Req(a) subset Req(b)` and coverage of `b` imply coverage of `a`.
  - this is the first paper-grade mathematical invariant from the disaster-state minimization lane.
  - the concrete bridge proof project now has `170` checked theorem declarations after adding the antichain-cover and novelty-classifier theorems.

- `candidate_axis_novelty_classifier_v1`
  - classifies candidate disaster axes as duplicate, dominated, new incomparable class over existing atoms, new dominating class, or new-atom required.
  - the strongest signal is `new_atom_required`, because it means the current witness language is incomplete rather than merely under-sampled.

## v165 private-obligation guard optimality certificate

- `private_obligation_guard_optimality_certificate_v1`
  - upgrades guard-cover optimality from exhaustive search to a checkable private-witness certificate.
  - proves the selected `7`-guard cover is forced because each selected guard has a required obligation that no other guard covers.

- `forced_guard_lower_bound_v1`
  - each private obligation supplies a local lower-bound witness: any valid cover must include the corresponding guard.
  - for the current corpus, the private witnesses cover all selected guards, so subset-minimality and cardinality optimality are certified without trusting combinatorial search.

- `mixed_lower_bound_certificate_frontier_v1`
  - the next frontier is a certificate language for cases without private atoms: private witnesses first, disjoint shared-obligation blocks second, bounded residual search last.
  - this points toward a proof-carrying set-cover lower-bound system specialized to disaster-state assurance.

- `proof_carrying_disaster_minimizer_compact_theorem_v1`
  - bundles antichain equivalence, selected-union full coverage, no uncovered full-axis obligation gaps, and selected-guard optimality into one Lean theorem.
  - theorem name: `proofCarryingDisasterMinimizer_sound_optimal`.

## v182 DLMF/Julia certificate menu for Tau/FIRE polynomial obligations

- `bernstein_interval_certificate_fast_path_v1`
  - exact Julia `Rational{BigInt}` experiments compile univariate rational polynomial sign obligations into Bernstein coefficient certificates over rational intervals.
  - the core corpus has `41/41` positive cases certified by 8 equal subdivisions, while monomial coefficient positivity certifies `0/41`.
  - false accepts on explicit negative controls remain `0` in the bounded corpus.

- `chebyshev_envelope_certificate_family_v1`
  - DLMF/Mathlib Chebyshev boundedness gives a separate certificate for obligations of the form `1 - T_n(2*x - 1)^2 >= 0` on `[0,1]`.
  - exact Julia stress cases show equal-subdivision Bernstein positivity certifies only `T_2` and `T_3` out to 128 pieces, while `T_4` through `T_8` remain `UNKNOWN`.
  - this is not a falsifier of nonnegativity; it is evidence that oscillatory special-function shapes need their own proof rule.

- `fragment_sensitive_qe_certificate_menu_v1`
  - the best Tau/FIRE optimization path is no longer a single universal QE replacement.
  - use a fail-closed menu: Bernstein interval certificates for ordinary polynomial sign obligations, Chebyshev boundedness certificates for recognized oscillatory envelope shapes, and fallback to QE or `UNKNOWN` otherwise.
  - both the Bernstein interval certificate surface and the Chebyshev envelope certificate surface now have local Lean proofs.
  - the reusable proof module is `Proofs.TauFragmentCertificates`, and the generated demo menu certifies `48/48` positive obligations with `0` explicit negative-control accepts in the bounded corpus.

- `standalone_fragment_menu_checker_v1`
  - `menu_checker.py` gives a replayable exact-rational JSON-in/JSON-out checker for the two proved fast paths.
  - the file demo has `3` accepts and `2` fail-closed `UNKNOWN` outcomes, including a negative control and a malformed Chebyshev interval.
  - this is the operational bridge from theorem menu to a future Tau patch or tutorial demo.

- `full_corpus_fragment_menu_replay_v1`
  - `build_menu_corpus.py` converts the generated Julia corpus into a replayable menu-checker spec and report.
  - full-corpus replay has `48/48` positive obligations accepted, `0/3` negative controls accepted, and all `3/3` negative controls left `UNKNOWN`.
  - this is stronger than the hand demo because it ties the executable checker to the same corpus used by the DLMF/Julia discovery cycle.

- `dlmf_agent_workflow_v1`
  - standardizes the loop as conjecture -> DLMF identities -> Lean/Tau/Rust/Python/Julia translation -> numerical/exact tests -> restricted theorem -> generalization.
  - the key guardrail is that DLMF and numerical testing produce candidate theorem shapes, while Lean proves the `ACCEPT` semantics.
  - the workflow is recorded in `experiments/math_object_innovation_v182/DLMF_AGENT_WORKFLOW.md`.

- `tau_checkout_fragment_certificate_sidecar_v1`
  - packages the exact-rational fragment menu into the local Tau checkout at `external/tau-lang/scripts/tau_fragment_certificate_menu.py`.
  - demo spec: `external/tau-lang/demos/demo_4.1-fragment_certificate_menu.json`.
  - documentation: `external/tau-lang/docs/fragment_certificate_menu.md`.
  - focused replay: `pytest -q tests/tau/test_tau_fragment_certificate_menu_sidecar.py`.
  - negative knowledge: this is a Tau-facing pre-solver hook, not a direct C++ QE optimization and not a Tau parser.

- `expanded_chebyshev_polynomial_recognizer_v1`
  - improves the fragment filter by recognizing expanded shifted Chebyshev envelope polynomials through exact recurrence-generated coefficient equality.
  - demo upgrade: `expanded_chebyshev_T4_envelope` is accepted as `CHEBYSHEV_POLY_MATCH` even though it is supplied as ordinary coefficients.
  - this reduces dependence on friendly source syntax and is closer to what a Tau/host extractor would emit.
  - negative knowledge: recognizer correctness is still checker-relative; a future Lean bridge should formalize the coefficient recurrence or emit a checkable equality certificate.

- `reference_adapter_tacticbook_v1`
  - records the broader DLMF/OEIS/mathlib/Wolfram/ProofWiki/LMFDB/nLab adapter strategy in `experiments/math_object_innovation_v182/DLMF_TACTICBOOK.md`.
  - machine-readable schema: `experiments/math_object_innovation_v182/reference_adapters.json`.
  - validation test: `experiments/math_object_innovation_v182/test_reference_adapters.py`.
  - the standard is formula source -> exact local checker -> Lean proof for `ACCEPT` semantics -> fail-closed Tau/host dispatch.

## v184 Legendre/Turan Bernstein certificate profile

- `legendre_turan_reference_adapter_v1`
  - applies the DLMF/reference-adapter workflow to shifted Legendre envelopes and Legendre Turan differences.
  - Julia exact `Rational{BigInt}` recurrence generation plus Bernstein certificate search certifies `64/64` positive obligations for `1 <= n <= 32`.
  - negative controls accepted: `0/4`.
  - max equal subintervals needed: `16` for both envelope and Turan families.

- `orthogonal_polynomial_dispatch_heuristic_v1`
  - Chebyshev envelopes from v182 are Bernstein-hostile enough to need a special theorem recognizer.
  - Legendre envelopes and Turan differences, in the v184 bounded range, are Bernstein-friendly.
  - this suggests a dispatch heuristic: try Bernstein first on smooth Legendre/Turan-style inequalities, but use special-function recognizers early on oscillatory Chebyshev envelopes.

- negative knowledge:
  - this is bounded evidence for `n <= 32`, not a general theorem for all Legendre inequalities.
  - local mathlib search did not expose a Legendre polynomial theorem surface analogous to the Chebyshev one already used.
  - the current formal route is generic Bernstein certificate soundness for emitted certificates, not a direct Lean proof of the DLMF Legendre/Turan inequalities.

## v185 Gegenbauer Bernstein certificate profile

- `gegenbauer_reference_adapter_v1`
  - extends the v184 Legendre/Turan profile to normalized Gegenbauer envelopes and normalized Gegenbauer Turan differences.
  - tested `lambda in {1/2, 1, 3/2, 2, 3}` and `1 <= n <= 24`.
  - Julia exact `Rational{BigInt}` recurrence generation plus Bernstein certificate search certifies `240/240` positive obligations.
  - negative controls accepted: `0/4`.
  - max pieces: `16` overall, `16` for envelopes, `8` for Turan differences.

- `gegenbauer_dispatch_profile_v1`
  - strengthens the dispatch heuristic from v184.
  - among tested orthogonal-polynomial profiles, Chebyshev remains the unusual Bernstein-hostile case; Legendre and Gegenbauer profiles are Bernstein-friendly.
  - normalized Turan differences are especially friendly, never needing more than `8` equal subintervals in this bounded profile.

- negative knowledge:
  - this is bounded evidence for the listed rational `lambda` values and `n <= 24`, not a general Gegenbauer theorem.
  - it does not remove the need for Chebyshev-specific recognition.
  - formal `ACCEPT` semantics still route through emitted Bernstein certificates rather than a direct Gegenbauer theorem.

## v186 asymmetric Jacobi boundary

- `asymmetric_jacobi_envelope_profile_v1`
  - tests endpoint-normalized shifted Jacobi envelopes for 11 rational `(alpha,beta)` pairs and `1 <= n <= 14`.
  - all `154/154` envelope obligations certify by Bernstein with max `8` equal subintervals.
  - this extends the envelope side of the Legendre/Gegenbauer dispatch heuristic to asymmetric Jacobi parameters in the bounded profile.

- `asymmetric_jacobi_turan_endpoint_falsifier_v1`
  - endpoint-normalized Jacobi Turan candidates fail sharply for asymmetric parameters.
  - `140/154` Turan assumed-positive obligations are exact endpoint counterexamples.
  - example: `(alpha,beta,n)=(1/2,0,1)` has value `-4/45` at `x=0` and `0` at `x=1`.
  - only the symmetric Legendre-style parameter `(0,0)` certifies all Turan cases in the tested grid.

- negative knowledge:
  - the claim "Legendre/Gegenbauer Turan friendliness extends to asymmetric Jacobi Turan under endpoint normalization" is falsified.
  - these are not mere `UNKNOWN` certificate failures; exact endpoint values are negative.
  - future Jacobi Turan work needs a corrected normalization, extra endpoint factors, or a different theorem statement.

## v187 certificate-carrying route interval graph

- `certificate_carrying_arbitrage_graph_v1`
  - combines a positive asset-potential certificate with exact integer CPMM edge semantics.
  - bounded corpus: 5 assets, complete directed graph, 160 no-arb graphs, 80 injected-arb graphs, simple routes from asset 1 to asset 5 with at most 3 edges.
  - Julia exact rational replay certifies `160/160` no-arb graphs and rejects `80/80` injected-arb graphs.
  - the route-prefix pruning rule prunes `522/1600` bounded no-arb route candidates with `0` false prunes.

- `integer_interval_cpmm_bridge_v1`
  - tests the local post-fee CPMM integer floor bridge:
    `q = net_in * reserve_out / (reserve_in + net_in)` and `out = floor(q)`.
  - bounded exact grid: `728000` reserve/input triples across discovery and holdout ranges.
  - observed `0` floor-interval violations; max exact errors were `158/159` and `276/277`, both below `1`.

- next theorem targets:
  - `potential_route_prefix_prune_sound`: a positive potential certificate makes continuation output upper-bounded by the prefix potential value. Promoted to Lean as `pathProduct_potential_bound` and `pathProduct_le_potential_ratio`.
  - `cpmm_post_fee_floor_error_lt_one`: the local integer floor bridge has exact error in `[0,1)`. Promoted to Lean as `cpmm_post_fee_floor_interval`.
  - `treasury_arbitrage_dual_guard`: treasury opportunities require both the opportunity certificate and the already proved budget guard.

- negative knowledge:
  - this is a `symbolic_state_compiler`, not a production router.
  - the result still depends on upstream certified potentials / upper-rate certificates.
  - it does not cover all graph sizes, live concurrent reserve mutation, or external venue execution.

## v188 Gasper-cone Jacobi Turan orientation

- `gasper_cone_jacobi_turan_oriented_recognizer_v1`
  - repairs the v186 asymmetric Jacobi Turan failure by using the cone-compatible endpoint normalization.
  - for shifted Jacobi `J_n(x) = P_n^(alpha,beta)(2*x-1)`, the right-normalized Turan profile is tested only in the `beta >= alpha` cone, and the left-normalized profile is the mirrored `alpha >= beta` cone.
  - the oriented recognizer chooses right endpoint when `beta >= alpha`, otherwise left endpoint.
  - bounded exact Julia scan over 21 rational `(alpha,beta)` pairs and `1 <= n <= 18` certifies `378/378` oriented obligations with max `8` Bernstein pieces.
  - total in-cone positive claims across right, left, and oriented rows certify `810/810`.

- `wrong_endpoint_jacobi_turan_falsifier_v1`
  - strict wrong-endpoint cases are not merely hard for Bernstein certificates.
  - all `648/648` outside-cone rows are exact endpoint counterexamples.
  - all `324/324` strict wrong-anchor rows are endpoint-falsified.
  - negative controls remain fail-closed with `0/4` accepted.

- theorem/search implications:
  - v186's failures were a parameter-cone/orientation signal, not random certificate weakness.
  - the practical Tau/FIRE dispatch rule is: check the Jacobi Turan cone first, orient the endpoint, emit a Bernstein certificate inside the cone, otherwise reject the theorem recognizer and fall back to ordinary handling.
  - the next proof target is the mirror lemma:
    left-normalized `(alpha,beta)` at `x=0` reduces to right-normalized `(beta,alpha)` at `1-x`.

- negative knowledge:
  - more subdivision is not a remedy for strict outside-cone Jacobi Turan formulas, because exact endpoint values are negative.
  - the result is a bounded recognizer/certificate profile, not a local proof of Gasper's full Jacobi Turan theorem.
  - the full theorem should remain reference-backed until a Lean proof or trusted theorem import exists.

## v189 Jacobi Turan endpoint obstruction formula

- `jacobi_turan_endpoint_obstruction_formula_v1`
  - extracts the exact endpoint formula explaining why the strict wrong endpoint in v188 is mathematically false.
  - exact Julia scan over `10368` rational rows found `0` mismatches between direct endpoint evaluation and the closed formula.
  - inside-cone endpoint rows were nonnegative: `5760/5760`.
  - outside-cone endpoint rows were negative: `4608/4608`.
  - equal-parameter boundary rows were zero: `1152`.

- closed formula:
  - right normalization at the opposite endpoint has sign controlled by `beta - alpha`.
  - left normalization at the opposite endpoint has sign controlled by `alpha - beta`.
  - in endpoint-ratio form, the obstruction factors as a square ratio times this signed parameter difference over a positive denominator.

- Lean promotion:
  - `lean-mathlib/Proofs/JacobiTuranEndpointObstruction.lean` proves the recurrence-defined endpoint coefficient ratio bridge and the algebraic endpoint-ratio skeleton for both orientations.
  - it now also proves the sign consequences: right endpoint nonnegative in `alpha <= beta`, right endpoint negative when `beta < alpha`, and the mirrored left endpoint statements.
  - proof receipt: `lean-mathlib/proof_receipts/jacobi_turan_endpoint_obstruction_v1.json`.

- negative knowledge:
  - the endpoint obstruction is a necessary cone filter, not a full Jacobi Turan positivity theorem.
  - the Lean theorem uses a recurrence-defined endpoint coefficient; it does not yet prove equality with Mathlib's generalized binomial/Jacobi endpoint definitions.
  - the next useful formal step is either a Pochhammer/binomial recurrence bridge or a trusted theorem import boundary for the full Gasper theorem.

## v196 derivative Bernstein monotonicity certificates

- `derivative_bernstein_monotonicity_certificate_v1`
  - tests a Tau-style fast path for obligations of the form
    `forall x y in [a,b], x <= y -> p(x) <= p(y)`.
  - exact Julia `Rational{BigInt}` replay over `[0,1]` checks Bernstein
    coefficients of `p'` over equal subdivisions in `{1,2,4,8}`.
  - bounded corpus: `33` polynomial cases, `29` true monotone cases, and `4`
    negative controls.
  - result: `27/29` true monotone cases accepted, `0/4` negative controls
    accepted, and `15147` exact grid pair comparisons avoided by accepted
    derivative certificates.
  - demo checker: `experiments/math_object_innovation_v196/derivative_menu_checker.py`
    accepts `2/3` built-in obligations and leaves the decreasing-line negative
    control as `UNKNOWN`.
  - Tau checkout sidecar:
    `external/tau-lang/scripts/tau_derivative_certificate_menu.py`,
    `external/tau-lang/demos/demo_4.2-derivative_certificate_menu.json`, and
    `external/tau-lang/docs/derivative_certificate_menu.md`.
  - Lean bridge: `TauFragmentCertificates.derivativeCertificate_monotoneOn`
    and `TauFragmentCertificates.derivativeCertificate_nonnegOn_of_leftEndpoint`
    check in `lean-mathlib/Proofs/TauFragmentCertificates.lean`.

- `derivative_sign_redundancy_negative_knowledge_v1`
  - the derivative certificate did not add new endpoint-based sign
    nonnegativity accepts when ordinary Bernstein used the same partition and
    `p(0)` was shifted nonnegative.
  - measured redundancy check: `27/27` accepted monotone cases were also
    ordinary Bernstein sign accepts on the same pieces after the endpoint
    shift, with `0` redundancy failures.
  - conclusion: derivative Bernstein is a monotonicity / two-variable-order
    reduction path, not a better plain sign certificate under matched
    partitions.

- next frontier:
  - add adaptive critical-point splitting for square-derivative shapes,
    because non-dyadic centered cubic cases are true monotone but remain
    `UNKNOWN` under equal dyadic subdivisions up to `8` pieces.
  - benchmark the Tau sidecar against extractor-shaped monotonicity obligations.
  - the result is now tutorial-ready if the tutorial states the non-claim that
    derivative Bernstein does not improve plain sign certificates under matched
    partitions.
