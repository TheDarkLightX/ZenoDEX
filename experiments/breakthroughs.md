---
title: breakthroughs
type: note
permalink: autonomous-tau-dex-review/experiments/math-research-memory/breakthroughs
---

# Breakthroughs

## Method promotion from critical-region dispatch v1

- `failing_region_midpoint_refinement_v1` is promoted as a bounded
  certificate-compiler optimization.
- Reason:
  - it reuses the existing exact Bernstein acceptance rule and complete-cover
    proof boundary,
  - it accepts `772/772` positive Jacobi/Gegenbauer obligations and `0/7`
    negative controls,
  - it saves `664` pieces (`1848` basis points) and `1412852` canonical bytes
    (`3466` basis points) relative to equal subdivision,
  - and its per-case piece and byte cost is lower on `322` obligations and
    equal on the remaining `450`.
  - Lean checks arbitrary-degree Bernstein-combination nonnegativity, exact
    recursive de Casteljau scalar evaluation, and the finite-cover acceptance
    spine.
- Practical consequence:
  - a Bernstein certificate generator should refine only failing leaves before
    increasing a global equal partition,
  - and a six-leaf budget leaves only `5` bounded positives `UNKNOWN` instead
    of `240` under equal subdivision.
- Non-promotion:
  - `derivative_landmark_dispatch_v1` uses `15` more pieces and `1607182` more
    bytes than midpoint refinement, so it remains negative knowledge,
  - coefficient-interpolated critical points are rejected because their exact
    denominator growth depends on input coefficient height,
  - and no runtime, Tau, settlement, or general special-function claim is
    promoted from this research compiler.
  - Lean now proves one-step and recursive de Casteljau evaluation identities,
    while power-to-Bernstein conversion and the full left/right affine
    subdivision identity remain differentially checked Julia obligations.

## Non-promotion note from the approximation-defect receipt bridge

- `approximation_defect_receipt_v1` survives as a proof-relevant executable
  bridge, but it is not promoted as a runtime certificate.
- Reason:
  - it gives the Deift-Zhou / Wang-Ma transfer an exact-rational receipt shape,
  - it fails closed on the four named composition attacks,
  - and Lean checks the local gluing and finite-cover theorem used by
    `ACCEPT`,
  - but upstream analytic certificate identifiers remain opaque assumptions.
- Current measured result:
  - focused checker tests: `11/11` pass
  - built-in replay: `1` accepted, `4` `UNKNOWN`
  - required adversarial witnesses: missing region, underestimated defect,
    omitted interaction, and overlap mismatch
  - runtime/Tau/settlement authority: none

## Non-promotion note from v197

- `proof_gated_gamification_budget_v1` survives as a useful mechanism-design
  object, but it is not promoted as a full breakthrough.
- Reason:
  - it gives gamification a cap-meet token reward law,
  - it rejects hype, wash-loop, missing-proof, over-budget, over-sybil, and
    stale-receipt quest shapes,
  - and Lean checks that the four-way reward meet implies every individual cap,
  - but it is not yet connected to live proof-mining or user receipts.

- Current measured result:
  - `quest_count = 12`
  - `accepted_count = 6`
  - `accepted_token_reward_count = 5`
  - `accepted_xp_only_count = 1`
  - `rejected_count = 6`
  - `total_gamification_budget_invariant_failures = 0`

## Non-promotion note from v198

- `disaster_potential_chaos_morphism_v1` survives as a useful chaos-engineering
  object, but it is not promoted as a full breakthrough.
- Reason:
  - it gives chaos campaigns a weighted potential and certificate rule,
  - it distinguishes direct repairs, certified recoveries, ordinary rejections,
    and catastrophic over-cap rejections,
  - and Lean checks that accepted risk increases require the certificate branch,
  - but the risk weights and morphism corpus are still research choices.

- Current measured result:
  - `case_count = 108`
  - `accepted_count = 54`
  - `rejected_count = 54`
  - `direct_repair_count = 12`
  - `certified_recovery_count = 42`
  - `catastrophic_rejection_count = 12`
  - `total_disaster_potential_invariant_failures = 0`

## Non-promotion note from v195

- `assumption_change_override_packet_language_v1` survives as a useful
  witness-language result, but it is not promoted as a full breakthrough.
- Reason:
  - it proves, over the bounded corpus, that all eight override atoms are
    forced by private negative witnesses,
  - it identifies the full packet guard as the unique minimal exact language,
  - and it falsifies tempting text-only and authority-only packet languages,
  - but it is not yet a cryptographic signature, governance registry, or
    production checker implementation.

- Current measured result:
  - `packet_count = 13`
  - `valid_packet_count = 2`
  - `invalid_packet_count = 11`
  - `atom_count = 8`
  - `forced_atom_count = 8`
  - `minimal_exact_language_count = 1`
  - `minimal_exact_atom_count = 8`
  - `total_override_language_invariant_failures = 0`

## Non-promotion note from v194

- `evidence_meet_launch_config_guard_v1` survives as a useful symbolic compiler
  from review caps to config-lint obligations, but it is not promoted as a full
  breakthrough.
- Reason:
  - it turns the v193 meet cap into an explicit fail-closed guard relation,
  - it rejects over-cap, uncapped, malformed-override, unsafe-claim, and
    redundant-override candidates in the bounded corpus,
  - and Lean checks that over-cap acceptance under the guard implies the
    override branch,
  - but accepted-with-override configs are assumption-change reviews, not
    evidence-backed safe fee schedules.

- Current measured result:
  - `config_count = 10`
  - `surface_check_count = 18`
  - `accepted_without_override_count = 2`
  - `accepted_with_override_count = 3`
  - `rejected_count = 5`
  - `evidence_compliant_config_count = 2`
  - `governance_assumption_change_count = 3`
  - `total_config_invariant_failures = 0`

## Non-promotion note from v193

- `evidence_meet_fee_cap_lattice_v1` survives as a useful symbolic compiler for
  composing fee-cap evidence, but it is not promoted as a full breakthrough.
- Reason:
  - it gives a clean lattice operation for fee-cap evidence,
  - it reduces execution-backed route caps to the tighter stress-backed meet,
  - it has a small Lean proof that the meet cannot loosen a safe source cap,
  - but the upstream caps are still oracle-dependent review artifacts.

- Current measured result:
  - `surface_count = 16`
  - `meet_cap_surface_count = 6`
  - `execution_backed_meet_count = 2`
  - `synthetic_meet_count = 4`
  - `single_source_cap_count = 0`
  - `no_user_value_cap_count = 10`
  - `total_meet_invariant_failures = 0`

## Non-promotion note from v192

- `execution_derived_fee_receipt_bridge_v1` survives as a useful bridge from
  runtime route arithmetic to FIRE revenue calibration, but it is not promoted
  as a breakthrough.
- Reason:
  - it replaces hand-authored measured value with actual router deltas in
    deterministic fixture markets,
  - it keeps review caps bounded by measured value and hard retail rails,
  - it rejects deliberately tampered over-fee and wash-risk rows,
  - but it is still fixture replay, not live market calibration.

- Current measured result:
  - `receipt_count = 20`
  - `accepted_count = 18`
  - `rejected_count = 2`
  - `route_receipt_count = 9`
  - `exact_out_receipt_count = 9`
  - `candidate_review_cap_count = 2`
  - `launch_parameter_claim_count = 0`
  - `total_execution_receipt_invariant_failures = 0`

## Non-promotion note from v191

- `fee_cap_calibration_stress_corpus_v1` survives as a useful model-bug
  control for FIRE revenue calibration, but it is not promoted as a
  breakthrough.
- Reason:
  - it gives the fee-cap bridge a multi-sample stress corpus,
  - it proves the current bridge rejects five declared bad revenue rows for the
    exact expected reasons,
  - it verifies strict sample thresholds fail closed and no launch parameter
    claim is emitted,
  - but it is still synthetic and descriptive, not live market calibration.

- Current measured result:
  - `receipt_count = 32`
  - `accepted_count = 27`
  - `rejected_count = 5`
  - `candidate_review_cap_count = 6`
  - `launch_parameter_claim_count = 0`
  - `total_stress_invariant_failures = 0`

## Non-promotion note from v190

- `revenue_surface_atlas_v1` survives as a useful FIRE tokenomics object, but
  it is not promoted as a breakthrough.
- Reason:
  - it gives an explicit fee-surface atlas rather than treating staking as a
    revenue source,
  - it searches `155527` bounded policies and finds `5510` survivors,
  - it keeps the launch-shaped policy alive while rejecting zero-fee,
    extractive-notional, wash-rebate, penalty-dependent, and passive-subsidy
    shapes,
  - and it now includes model-bug controls plus a small Lean algebra skeleton,
  - but it is still a bounded oracle over hand-authored scenarios, not a live
    calibrated fee engine.

- Current measured result:
  - `best_survivor = grid_090937_max_burn_guarded`
  - `best_survivor`: net protocol revenue `5322`, burn budget `4257`,
    deflation margin `4257`, penalty dependency `0` bps
  - `fee_surface_launch`: survivor `true`, net protocol revenue `2258`,
    total user net value `3669`, burn budget `1016`
  - `model_audit.total_model_invariant_failures = 0`
  - `mutation_receipt.detected_count = 5 / 5`
  - `report_integrity.passed_count = 11 / 11`
  - receipt calibration fixture: `receipt_count = 11`, `accepted_count = 9`,
    `rejected_count = 2`
  - fee-cap recommendation fixture: `candidate_review_cap_count = 6 / 11`,
    `launch_parameter_claim_count = 0`,
    `total_recommendation_invariant_failures = 0`

## Non-promotion note from v182

- `bernstein_interval_sign_certificate_v1` survives as a useful Tau/FIRE proof
  object, but it is not promoted as a full breakthrough yet.
- Reason:
  - it gives a proof-carrying symbolic fast path for bounded univariate
    polynomial nonnegativity obligations,
  - it uses exact Julia rational arithmetic, not floating-point sampling,
  - the bounded corpus found `0` monomial-positive hits, `24/41`
    one-interval Bernstein hits, and `41/41` hits after four or eight equal
    subdivisions, with no false accepts among the explicit negative controls,
  - and it produced an Aristotle proof packet for the soundness theorem,
  - but Aristotle has not returned the proof yet, and the method is a
    conservative sufficient certificate rather than complete QE.

- Current measured result:
  - `case_count = 44`
  - `positive_case_count = 41`
  - `monomial_positive_hits = 0`
  - `bernstein_1_positive_hits = 24`
  - `bernstein_4_positive_hits = 41`
  - `bernstein_8_positive_hits = 41`
  - `false_accepts = 0` for monomial, Bernstein-1, Bernstein-2,
    Bernstein-4, and Bernstein-8 on the explicit negative controls
  - Aristotle project: `7fb8a5e9-f2ac-4122-a07b-e9c05edccca6`

## Non-promotion note from v181

- `bps_revenue_value_flow_frontier_v1` survives as a useful FIRE revenue object,
  but it is not promoted as a breakthrough.
- Reason:
  - it turns the revenue design into an executable bps search over `194412`
    policies,
  - it finds `10782` survivor policies that keep users non-negative while
    funding protocol revenue and burn,
  - and it discovers the stronger value-density cap object for fees charged on
    notional,
  - but it is still a bounded toy action corpus rather than replayed live quote
    data or a production fee engine.

- Current measured result:
  - `best_survivor = grid_fee_31557__max_burn_guarded`
  - `best_survivor`: user net value `2443`, net protocol revenue `2435`, burn
    budget `2069`
  - `fire_launch__fire_balanced`: survives with user net value `3906`, net
    protocol revenue `952`, burn budget `476`
  - value-density caps: protection `5` bps, automation `16` bps, integrator
    `10` bps, retail receipt `0` bps
  - `zero_fee__fire_balanced`: gross protocol revenue `0`, survivor `false`
  - `notional_fee_extract__fire_balanced`: negative action count `6`

## Non-promotion note from v180

- `reputation_weight_governance_bounds_v1` survives as a useful FIRE
  governance object, but it is not promoted as a breakthrough.
- Reason:
  - it closes the immediate v179 gap by showing that reputation weights
    themselves need hard governance rails,
  - it searches `8014` bounded policies and finds `237` inside the safe
    envelope,
  - and it falsifies stake-capture, old-receipt-capture, independence-light,
    domain-blind, and no-decay governance shapes,
  - but it is still a bounded task-market oracle rather than a production
    reputation verifier or governance module.

- Current measured result:
  - `fire_weight_bounds`: envelope ok, score `70.548668`, independence failure
    `0`, newcomer access `4.884319`
  - `grid_1541`: best coarse-grid envelope score `84.408668`
  - `stake_capture_governance`: stake capture `197.484000`, oligarchy risk
    `39.050099`
  - `old_receipt_capture_governance`: old receipt capture `262.335360`
  - `independence_light_governance`: independence failure `32.923800`
  - `domain_blind_governance`: domain mismatch `22.848000`

## Non-promotion note from v179

- `fire_reputation_trust_capacity_v1` survives as a useful FIRE trust object,
  but it is not promoted as a breakthrough.
- Reason:
  - it connects task-market reputation, evidence-provider independence, decay,
    and slashing into one bounded model,
  - it shows trust-yield multipliers and stake-weighted reputation create
    unearned premium,
  - and it shows stale reputation is a real failure mode without decay,
  - but it is still a hand-authored bounded scenario oracle rather than a
    production reputation algorithm.

- Current measured result:
  - `fire_trust_capacity`: score `122.916105`, unearned premium `0`,
    newcomer access `4.884319`, independence failure `0`
  - `trust_yield_multiplier`: unearned premium `93.240000`
  - `stake_weighted_reputation`: unearned premium `72.793333`
  - `flat_receipt_rewards`: stale power `127.935360`

## Non-promotion note from v178

- `private_provider_receipt_verifier_interface_v1` survives as a useful
  symbolic FIRE verifier-interface object, but it is not promoted as a
  breakthrough.
- Reason:
  - it turns the v177 private receipt into a verifier-facing schema with
    circuit identity, public context, relation statement, nullifier binding, and
    canonical privacy output,
  - it falsifies proof-blob-only and partially bound verifier surfaces,
  - and it gives a concrete implementation checklist for the future runtime
    boundary,
  - but it is still symbolic and does not yet implement a cryptographic
    verifier.

- Current measured result:
  - `case_count = 16384`
  - `best_language = [circuit_identity_ok, public_context_ok, relation_statement_ok, nullifier_binding_ok, privacy_output_ok]`
  - `minimal_exact_language_count = 2`
  - `proof_blob_only`: false accepts `16383`
  - `unbound_context`: false accepts `15`

## Non-promotion note from v177

- `private_provider_independence_receipt_v1` survives as a useful symbolic FIRE
  privacy object, but it is not promoted as a breakthrough.
- Reason:
  - it makes privacy part of the recovery-evidence accept condition rather than
    a wrapper around public identity checks,
  - it finds a unique minimal exact four-macro receipt language over the
    bounded Boolean cube,
  - and it falsifies commitments-only, unbound-ZK, stale-nullifier, and
    cross-domain-linkable designs,
  - but it is still a symbolic receipt language, not a concrete ZK circuit or
    registry implementation.

- Current measured result:
  - `case_count = 1024`
  - `best_language = [zk_independence_ok, context_binding_ok, membership_freshness_ok, privacy_ok]`
  - `minimal_exact_language_count = 1`
  - `commitments_only`: false accepts `7`
  - `unbound_zk_proof`: false accepts `7`

## Non-promotion note from v176

- `common_control_provider_independence_v1` survives as a useful symbolic FIRE
  identity object, but it is not promoted as a breakthrough.
- Reason:
  - it closes the most immediate gap in v175 by showing how nominal providers
    can alias through shared control, beneficiary, infrastructure, operator, or
    slash pool roots,
  - it finds a unique minimal exact receipt language over the bounded
    three-provider partition product,
  - and it quantifies false accepts for weaker identity checks,
  - but it still assumes the roots themselves can be truthfully and privately
    witnessed.

- Current measured result:
  - `case_count = 3125`
  - `best_language = [economic_identity_ok, operational_identity_ok, slash_pool_distinct]`
  - `minimal_exact_language_count = 1`
  - `nominal_quorum_only`: false accepts `3124`
  - `economic_plus_slash`: false accepts `24`

## Non-promotion note from v175

- `collusive_recovery_evidence_quorum_v1` survives as a useful symbolic FIRE
  evidence object, but it is not promoted as a breakthrough.
- Reason:
  - it compiles the bounded provider assumptions `(n=5, f=2, h=1)` into the
    quorum interval `f < q <= n - h`,
  - it identifies `q3_slash10000` as the unique lowest-cost exact policy in the
    searched grid,
  - and it exposes why weak quorums, unslashable majorities, and unanimity are
    each wrong for recovery evidence,
  - but it still assumes that provider groups are genuinely independent.

- Current measured result:
  - `exact_policy_count = 6`
  - `minimal_exact_policy_count = 1`
  - `best_policy = q3_slash10000`
  - `two_of_five_no_slash`: false accepts `3`
  - `majority_no_slash`: accountability failures `3`
  - `five_of_five_full_slash`: liveness failures `3`

## Non-promotion note from v174

- `recovery_governance_receipt_language_v1` survives as a useful symbolic FIRE
  governance object, but it is not promoted as a breakthrough.
- Reason:
  - it gives an exact bounded compiler from 9 raw emergency obligations into a
    three-macro receipt language,
  - it proves by exhaustive bounded search that no one- or two-atom candidate
    language in the library is exact,
  - and it has a clean map/compact execution shape for future checker work,
  - but it still assumes the upstream drawdown, TWAP, authority, and receipt
    fields are truthful or slashable.

- Current measured result:
  - `case_count = 512`
  - `negative_case_count = 511`
  - `best_language = [trigger_ok, spend_policy_ok, authority_ok]`
  - `minimal_exact_language_count = 1`

## Non-promotion note from v173

- `guarded_recovery_governance_abuse_v1` survives as a useful FIRE governance
  stress object, but it is not promoted as a breakthrough.
- Reason:
  - it catches the next failure mode created by v172: emergency controls can
    become insider extraction controls,
  - it rejects both unbounded discretion and frozen no-emergency governance,
  - and it identifies a bounded survivor with evidence thresholds, public
    receipts, TWAP-style guards, spend caps, cooldowns, slashing, and human
    reward floors,
  - but it is still a hand-authored scenario oracle, not a formal governance
    theorem or empirically calibrated mechanism.

- Current measured result:
  - `fire_guarded_recovery_governance`: FIRE governance score `83.625742`,
    false triggers `0`, blocked legitimate responses `0`, legitimate triggers
    `3`
  - `frozen_no_emergency`: blocked legitimate responses `3`
  - `admin_discretion_unbounded`: false triggers `1`, average insider
    extraction `993.594726`

## Non-promotion note from v172

- `liquidity_shock_recovery_fire_v1` survives as a useful FIRE economics stress
  object, but it is not promoted as a breakthrough.
- Reason:
  - it extends the v171 AMM bridge with LP withdrawal, whale selling, usage
    loss, organic-demand loss, and reward panic selling,
  - it shows `fire_recovery_circuit` beats pure burn, thin-liquidity hype, and
    over-rewarded FIRE under bounded shock scenarios,
  - and it introduces a recovery score that charges drawdown, reward overhang,
    and treasury depletion,
  - but it is still a hand-authored deterministic scenario oracle, not
    empirical calibration or a theorem.

- Current measured result:
  - `fire_recovery_circuit`: participatory recovery `694.339654`, worst
    drawdown `36.5756`, min recovery ratio `0.931479`, recovered scenarios `3/3`
  - `fire_over_rewarded`: participatory recovery `365.663793`, reward overhang
    `0.163554`, recovered scenarios `2/3`
  - `thin_liquidity_hype`: participatory recovery `0.187481`, worst drawdown
    `97.3350`, recovered scenarios `0/3`

## Non-promotion note from v171

- `float_liquidity_buyback_price_bridge_v1` survives as a useful FIRE economics
  bridge, but it is not promoted as a breakthrough.
- Reason:
  - it mechanically ties price to AMM reserves, buyback, reward sells, vesting
    release, and circulating float,
  - it exposed an over-reward scoring bug and fixed it with reward overhang,
  - and it separates best raw price from best participatory appreciation,
  - but it is still a toy AMM model without adversarial liquidity shocks.

- Current measured result:
  - `thin_liquidity_hype`: price return `59.1952`, participatory score `1.6628`
  - `fire_participatory_buyback`: price return `22.0246`, participatory score
    `5.5922`
  - `fire_over_rewarded`: reward overhang `2.9997`, participatory score
    `3.6643`

## Non-promotion note from v170

- `adversarial_participatory_economics_v1` survives as a useful FIRE economics
  stress object, but it is not promoted as a breakthrough.
- Reason:
  - it exposes that naive newcomer rewards are captured by attackers,
  - it shows capital gates and proof-only markets can also suppress human access
    or favor AI/whales,
  - and it identifies a hybrid guard as the best bounded survivor,
  - but the adversary model is still hand-authored and small.

- Current measured result:
  - `naive_newcomer_lane`: attacker capture `75.6665`, fake loss `4861.0244`
  - `hybrid_fire_guard`: attacker capture `31.7118`, fake loss `31.3341`,
    human access `68.2882`, participatory economic security `66.0208`

## Non-promotion note from v169

- `trust_as_capacity_not_entitlement_v1` survives as a useful FIRE economics
  object, but it is not promoted as a breakthrough.
- Reason:
  - it clarifies how trusted accounts can earn more without entitlement:
    bigger tasks, faster finality, lower collateral, and more responsibility,
  - it falsifies a naive newcomer lane that did not actually assign work to
    newcomers,
  - and the corrected `newcomer_lane_capacity` mechanism wins the bounded
    participatory-price objective,
  - but it is still a small hand-authored task market.

- Current measured result:
  - `trust_entitlement_multiplier`: unearned premium `161.7600`
  - `stake_weighted_rewards`: unearned premium `89.5370`
  - `newcomer_lane_capacity`: unearned premium `0.0000`, newcomer access
    `9.5571`, human participation `80.6527`

## Non-promotion note from v168

- `participatory_price_appreciation_engine_v1` survives as a useful FIRE design
  object, but it is not promoted as a breakthrough.
- Reason:
  - it corrects the v167 framing by making price appreciation explicit,
  - it distinguishes price pressure from human participation in price,
  - and it cleanly separates FIRE from an AI-owned protocol that may appreciate
    without giving humans agency,
  - but it is still hand-scored `descriptive_oracle`, not empirical market
    evidence or a theorem.

- Current measured archetype scores:
  - `bitcoin_modern`: price pressure `36.7030`, participatory price `2.2572`
  - `ai_owned_protocol`: price pressure `58.8910`, participatory price `6.8215`
  - `fire_participatory_appreciation`: price pressure `72.7430`,
    participatory price `60.5343`

## Non-promotion note from v167

- `credible_hope_value_accumulation_frontier_v1` survives as a useful FIRE
  design object, but it is not promoted as a breakthrough.
- Reason:
  - it cleanly separates price performance from value accumulation and credible
    hope,
  - it shows the first FIRE-style frontier that dominates modern Bitcoin under
    the bounded scoring ontology,
  - but the scores are still model-dependent and hand-authored, so this is
    `descriptive_oracle`, not a theorem.

- Current measured archetype scores:
  - `bitcoin_modern`: value `59.0667`, hope `44.9333`, PonziPressure `16.6417`
  - `fire_productive_deflation`: value `76.1708`, hope `76.6500`,
    PonziPressure `0.0000`
  - `ponzi_yield_token`: PonziPressure `67.0250`

## Non-promotion note from v166

- `productive_deflation_allocation_frontier_v1` survives as a useful FIRE
  tokenomics object, but it is not promoted as a breakthrough.
- Reason:
  - it gives a concrete winter-launch feasibility frontier,
  - it falsifies pure-burn tokenomics under the declared entry model,
  - and it forces the missing value ontology into the docs,
  - but it is still `descriptive_oracle` with a simple bounded value surrogate,
    not a production tokenomics theorem.

- Current measured result:
  - `policy_count = 10626`
  - `survivor_count = 4845`
  - `frontier_count = 94`
  - `max_surviving_burn_bps = 8500`
  - `pure_burn_survives = false`

## Non-promotion note from v133

- `global_cpmm_budget_object_v1` survives as the strongest current AMM theorem
  target, but it is not promoted as a breakthrough.
- Reason:
  - it gives a clean global no-free-lunch route aligned with the current
    normalized-surface proof stack,
  - it would replace a weaker pointwise-curvature framing with an integrated
    original-HODL value budget against CPMM,
  - but it is still a source-level review object, not a Lean-checked theorem.

## Non-promotion note from v100

- `shapeforge_contract_surface_v1` survives as a useful object, but it is not promoted as a breakthrough.
- Reason:
  - it gives a typed, queryable atlas over ZenoDEX contract, gap, and evidence surfaces,
  - it materially improves exact-out, settlement, composition, and perps reasoning posture,
  - but it is still `descriptive_oracle`, not a direct runtime/compiler law.

## Non-promotion note from v132

- `optimization_duality_transfer_atlas_v2` survives as a useful object, but it is not promoted as a breakthrough.
- Reason:
  - it creates a persistent, replayable paper-study loop with per-article `ideas/insights/plan` state,
  - it improves cross-session research continuity and now widens cleanly beyond one journal issue,
  - but it is still a research-memory scaffold, not yet a new DEX law or mechanism object.

## Non-promotion note from v71

- `reserve_decade_tiebreak_v1` is exact, but it is not promoted as a breakthrough.
- Reason:
  - it resolves the direct amount-only head atlas exactly,
  - but the chart has near one-key-per-case complexity,
  - so it is a bridge object rather than a clean new law.

## Promotion from v72

- `dominant_easy_fan_v1` is promoted as a useful DEX object.
- Reason:
  - it is direct amount-only,
  - exact on its accepted cells,
  - and it covers the dominant easy mass (`~93.7%`) with an explicit fallback boundary.
- This is a better shipping shape than a weak universal chart: exact fast path plus principled residual path.

## Confirmed survivors

1. `fibered_defect_quotient_v1`
- Query-sensitive directional defect bound.
- Exact winner preserved on the bounded corpus with materially fewer exact evaluations.

2. `antichain_galois_frontier_v1`
- Concrete candidate sets collapse to tiny abstract antichains while preserving the maximal upper bound.

3. `residuated_confidential_semiring_v1`
- Confidential winner extraction should be planned in a residual budget algebra rather than protocol casework.

4. `quadratic_osculating_patch_v1`
- Three-point local patches carry curvature and nearly eliminate bounded CPMM approximation error at fixed sampling budget.

5. `quadratic_obstruction_basis_v1`
- Once curvature is carried locally, dense failure sets collapse to a sparse obstruction basis.

6. `route_patch_semiring_v1`
- Hop-local patches compose into a useful route-level approximation object.

7. `route_cover_sheaf_v1`
- Overlapping quadratic route sections glue far better than linear ones.

8. `route_defect_cocycle_v1`
- Overlap mismatches behave like a useful obstruction norm for local-to-global route quality.

9. `execution_braid_potential_v1`
- Canonical commuting rewrites define a monotone energy descent on admissible execution traces.

10. `normal_form_basin_v1`
- Normal-form fibers have measurable compression and basin geometry, turning execution-order disorder into a quotient object.
- Current note: on the present bounded corpus the basin count collapses to one, so the object is informative but coarse.

11. `parallel_braid_depth_v1`
- Canonical rewrites reveal a parallel normalization depth materially smaller than sequential rewrite length.

12. `layer_skeleton_v1`
- Independent swap layers expose reusable concurrency structure inside execution normalization.

13. `serial_fiber_shuffle_semiring_v1`
- Admissible traces factor exactly as shuffles of serial fibers, eliminating brute-force counting on the bounded semantics.

14. `prefix_progress_simplex_v1`
- Distinct execution prefixes collapse to a small progress lattice, turning huge prefix forests into compact state spaces.

15. `simplex_dp_semiring_v1`
- Exact schedule counts and aggregate braid energy can be computed on the compressed progress simplex without enumerating schedules.

16. `simplex_occupancy_measure_v1`
- The compressed simplex admits an exact occupancy measure, turning prefix forests into analyzable state mass distributions.

17. `simplex_flow_measure_v1`
- The compressed simplex carries exact edge-flow counts, replacing raw prefix-edge enumeration.

18. `simplex_cut_form_v1`
- Rank cuts have measurable nonuniform edge concentration, exposing structural bottlenecks in execution flow.

19. `simplex_one_form_integral_v1`
- Additive path costs can be integrated exactly over simplex edge flow, turning aggregate schedule costs into discrete integrals.

20. `simplex_divergence_law_v1`
- The compressed execution flow obeys an exact discrete conservation law with zero internal divergence and source/sink flux equal to schedule count.

21. `simplex_bellman_potential_v1`
- Expected remaining braid energy can be computed exactly as a Bellman potential on the compressed simplex.

22. `simplex_branch_curvature_v1`
- The simplex carries a nontrivial curvature signal showing where local branching materially affects future execution cost.

23. `simplex_policy_fan_v1`
- The simplex admits a small policy stratification under exact Bellman control.

24. `simplex_boundary_mass_v1`
- Exact policy ties disappear on the tested corpus, but near-boundary mass remains large; fragility lives in margins rather than exact boundaries.

25. `simplex_margin_field_v1`
- Policy margin is an exact scalar field on the simplex, turning ambiguity into geometry instead of a binary event.

26. `simplex_instability_front_v1`
- Low-margin states cluster into a single dominant instability front carrying a large share of occupancy mass.

27. `margin_shell_measure_v1`
- Fragility compresses from dozens of low-margin states to a tiny exact shell family while preserving most of the relevant mass structure.

28. `margin_shell_flux_v1`
- Shell-to-shell transport has a signed negative drift, so execution tends to move toward more fragile shells on the current corpus.

29. `margin_shell_operator_v1`
- The shell geometry closes into an exact quotient operator with two nonterminal shells plus terminal exit.

30. `margin_shell_hazard_v1`
- The lower shell has strictly higher exit hazard than the higher shell across the tested corpus.

31. `shuffle_inversion_kernel_v1`
- Pairwise inversion probability in an ordered two-fiber shuffle has an exact closed negative-hypergeometric form.

32. `pairwise_superposition_law_v1`
- Exact future inversion potential is not just DP-computable; it decomposes exactly into deterministic debt plus pairwise shuffle kernels over remaining commuting pairs.

33. `min_key_policy_law_v1`
- On the bounded execution corpus, the exact Bellman-optimal next action collapses to the available action with minimal canonical key.

34. `key_margin_order_v1`
- Pairwise action-value order exactly matches key order, with strictly positive margins.

35. `weighted_pairwise_superposition_v1`
- The pairwise shuffle kernel extends to an exact weighted expected-cost law for nonnegative lower-action penalties.

36. `weighted_min_key_invariance_v1`
- On the tested bounded family of nonnegative weight perturbations, the exact optimal policy still collapses to min-key order.

37. `abstract_weighted_merge_invariance_v1`
- Across 846 bounded abstract ordered-fiber cases and 20 generated weight models per case, the exact optimal action matched min-key order on all 329,928 checked nonterminal states.

38. `pair_penalty_no_obstruction_v1`
- No counterexample appeared in the same abstract family across 19,750 generated pair-penalty models, so nonnegative pair penalties are still inside the current invariance basin.

39. `future_gate_obstruction_tensor_v1`
- Future-gated penalties produced a counterexample in the smallest nontrivial case `((1,), (2,))` with model `{1->2: 1}`, proving that the min-key law does have a real bounded obstruction family.

40. `blocker_availability_correction_v1`
- A compact blocker-availability correction score recovered the exact optimal action on 51,740 of 52,764 checked states (`98.059%`) in the future-gated family.

41. `gate_feedback_value_law_v1`
- Across 244 bounded abstract cases, 3,828 future-gate models, and 56,592 states, optimal future cost matched exactly the minimum gate weight needed to make the remaining precedence graph acyclic.

42. `acyclic_completion_policy_law_v1`
- Across the same bounded family, the exact optimal action matched the score `immediate violated weight + remaining acyclic completion cost` on all 52,764 checked nonterminal states.

43. `feedback_acyclicity_universality_v1`
- The exact feedback-acyclicity value law stayed perfect on a denser unit-weight family with up to three active future gates: 5,286 models and 81,104 checked states with zero mismatches.

44. `feedback_policy_universality_v1`
- The exact acyclic-completion policy law stayed perfect on the same denser family: 5,286 models and 75,818 checked nonterminal states with zero mismatches.

45. `prefix_barrier_projection_v1`
- Across 104,976 bounded same-direction CPMM batch cases, exact optimal executed volume matched perfectly the best feasible schedule in a one-dimensional cumulative-prefix barrier model.

46. `earliest_barrier_law_v1`
- On the same 104,976-case corpus, earliest-threshold-first matched exact optimal executed volume with zero counterexamples.

47. `barrier_surplus_gap_v1`
- After the exact `A` collapse, earliest-barrier-first preserved `A` on all 104,976 cases and lost only `0.09924` surplus units on average, with worst-case gap `2`.

48. `barrier_surplus_cocycle_v1`
- The residual `B` error after the barrier quotient was nonzero on only `9.764%` of the bounded corpus and was always an integer gap of at most `2`.

49. `a_feasible_swap_graph_v1`
- Across all 104,976 bounded batch cases, earliest-barrier order connected to an exact optimal order through an adjacent-swap path that preserved exact executed volume `A` at every intermediate step; average path length was `1.598`, max `5`.

50. `unit_edge_cocycle_v1`
- Across 211,634 checked adjacent swaps inside barrier classes, every `A`-preserving swap changed surplus by at most one unit, with nonzero local change on `9.299%` of edges.

51. `prefix_swap_curvature_form_v1`
- Across 155,906 regular `A`-preserving adjacent swap edges, the global surplus change matched exactly a prefix-local two-swap CPMM output differential with zero mismatches.

52. `quantized_curvature_v1`
- On the same 155,906 regular edges, the local surplus differential was always in `{-1, 0, 1}` and was zero on `87.377%` of edges.

53. `swap_cocycle_potential_v1`
- Across all 104,976 bounded same-direction batch cases, the regular-edge surplus cocycle integrated exactly to a global potential on the `A`-feasible swap graph component rooted at barrier order; average component size was `6.349`, max `24`.

54. `swap_cycle_holonomy_v1`
- On the same corpus, the regular-edge surplus differential had zero holonomy on every checked connected component, with average cycle rank `2.176` and max `13`.

55. `zero_plateau_quotient_v1`
- On the same 104,976-case corpus, collapsing zero-delta edges compressed the regular swap component from `6.349` nodes on average to `1.328` plateaus, a `79.08%` reduction.

56. `plateau_ascent_law_v1`
- After quotienting by zero-delta plateaus, a max-surplus plateau was reachable by positive-edge ascent on every bounded case; average minimum ascent length was `0.0852` and the worst case required only `2` positive moves.

57. `outlier_slot_potential_v1`
- Across 5,472 fully permissive `3+1` batch cases, the residual surplus potential depended only on the slot of the unique outlier, with zero counterexamples.

58. `outlier_phase_atlas_v1`
- The same `3+1` family collapsed after additive normalization to just `4` phase signatures (from `7` raw signatures), and those phases aligned cleanly with unique-min/unique-max regimes and mild vs extreme size ratios on the bounded corpus.

59. `outlier_slot_universality_v1`
- Across a broader zero-min `3+1` amount grid of 72 unequal amount pairs, the residual surplus still depended only on the slot of the unique outlier, with zero counterexamples.

60. `outlier_phase_plane_v1`
- On the same broader grid, the normalized slot-phase atlas expanded from the bounded `4`-phase picture to a finite `17`-phase plane, showing that slot universality survives scale broadening even as the phase diagram becomes richer.

61. `outlier_phase_fan_v1`
- The broadened `3+1` slot law organized into a finite `17`-cell phase fan with a dominant neutral cell of mass `18`.

62. `phase_adjacency_graph_v1`
- The same broadened fan had a small connected adjacency graph with `17` nodes, `43` edges, diameter `3`, and neutral degree `11`, giving the phase geometry a compact combinatorial skeleton.

63. `outlier_gradient_field_v1`
- On the broadened `3+1` family, the slot law re-expressed exactly as a finite set of `17` adjacent-slot gradient triples.

64. `gradient_phase_correspondence_v1`
- On the same family, normalized slot phases and gradient triples were in exact one-to-one correspondence, confirming the gradient field as the cleaner primitive carrier of the broadened phase geometry.

65. `generator_defect_pocket_v1`
- On a denser high-load near-diagonal `3+1` window of 420 amount pairs, the direct prefix-gradient generator remained exact on 401 pairs and failed only on a sparse 19-pair pocket.

66. `generator_defect_alphabet_v1`
- Inside that defect pocket, the generator failure used only 4 nonzero defect vectors: `(-1,0,0,0)`, `(0,-1,-1,-1)`, `(-1,0,-1,-1)`, and `(0,-1,0,0)`.


67. `trailing_gradient_exactness_v1`
- Across the full zero-min `3+1` grid with amounts in `{1000, 2000, ..., 50000}`, the direct prefix-gradient generator matched the true last adjacent-slot gradient on all 2,450 unequal amount pairs.

68. `front_gradient_filtration_v1`
- On the same 2,450-case grid, every nonzero gradient defect was supported only in the first two coordinates; there were just 54 nonzero cases, 6 nonzero defect symbols, 3 support patterns, and the defect `L1` norm never exceeded `2`.


69. `suffix_completion_law_v1`
- Across the full widened zero-min `3+1` grid of 2,450 unequal amount pairs, the true adjacent-slot gradient matched exactly the direct local gradient plus explicit omitted-suffix completion corrections, and the trailing correction was zero in every case.

70. `suffix_correction_alphabet_v1`
- On the same 2,450-case grid, the two nontrivial suffix corrections collapsed to just 7 pair symbols with coordinate magnitudes at most `1`: `(0,0)`, `(-1,0)`, `(1,0)`, `(0,-1)`, `(1,-1)`, `(0,1)`, and `(-1,1)`.


71. `suffix_carry_chain_v1`
- Across the full widened zero-min `3+1` grid of 2,450 unequal amount pairs, the first suffix correction matched exactly the sum of first omitted-peer carry and terminal omitted-peer carry, with zero counterexamples.

72. `terminal_carry_sparsity_v1`
- On the same 2,450-case grid, the terminal omitted-peer carry was nonzero in only 20 cases, took values only in `{-1,0,1}`, and split evenly between `-1` and `1` when nonzero.


73. `unit_reserve_gap_v1`
- Across the full widened zero-min `3+1` grid of 2,450 unequal amount pairs, the two terminal omitted-peer states always shared the same input reserve and denominator/net parameters, and differed in output reserve by at most one unit.

74. `terminal_floor_crossing_v1`
- On the same 2,450-case grid, the sparse terminal carry matched exactly a one-unit floor-crossing law, with 20 nonzero cases and zero counterexamples.


75. `equal_fiber_trailing_exactness_v1`
- Across widened equal-fiber `n+1` families with `n=4,5` on the dense 35k..55k window (840 unequal amount pairs total), the direct local generator matched the trailing gradient coordinate exactly in every case.

76. `prefix_defect_cone_v1`
- On the same 840-case widened equal-fiber corpus, all remaining defects were prefix-supported, the trailing support coordinate was always zero, and the total defect `L1` mass never exceeded `2`.

## Working interpretation

The strongest pattern so far is not a single grand formula. It is a toolkit:
- directional defects
- antichain closures
- residual-budget algebras
- curvature-aware patches
- sparse obstruction bases
- local-to-global gluing objects
- monotone rewrite energies
- quotient basins over partially commuting traces

This is the current reusable language for deeper DEX math experiments.

The newest addition is a residual geometry for batch clearing. In bounded same-direction CPMM batch clearing, executed volume `A` collapses exactly to a one-dimensional cumulative-prefix barrier scheduling problem and earliest-barrier-first is exact for that component. The remaining `B` error after quotienting by this barrier model is small, sparse, and integer-valued, and it lives on a short `A`-feasible adjacent-swap graph with unit local cocycle. On regular edges, that cocycle collapses to an exact prefix-local two-swap differential form, and that differential integrates to a global potential with zero cycle holonomy on the bounded regular graph. The first true control obstruction above that potential is not a cycle defect but a zero-delta plateau quotient, and after collapsing those plateaus the positive-edge ascent problem becomes tiny and exact on the bounded corpus. The next rare residual family above that quotient is a fully permissive `3+1` outlier regime where the remaining potential depends only on outlier slot. That slot law survives a broader zero-min scale sweep exactly, but the normalized phase atlas expands from `4` bounded phases to a `17`-phase fan with a small connected adjacency skeleton. In differential form, those `17` broadened phases are exactly the same `17` adjacent-slot gradient triples. Above that line, the first true obstruction to a direct local generator is a sparse high-load near-diagonal defect pocket with a 4-symbol defect alphabet, so the next frontier is a boundary law for that obstruction set rather than more global phase enumeration.
A widening pass then showed a stronger triangular law: in gradient coordinates the direct local generator gets the trailing adjacent-slot differential exactly on the full widened zero-min `3+1` grid, and every remaining defect is front-supported in the first two coordinates with tiny integer mass. So the next frontier is not a new global carrier, but an exact correction law for this front-supported defect filtration.
That correction law now exists at the next layer: the front-supported defect is exactly the omitted suffix-completion pair for the first two gradients, and this pair takes only 7 unit-valued symbols on the widened grid. The next frontier is therefore a boundary grammar for those suffix symbols, not a search for another correction carrier.
A further factorization shows that the first suffix correction itself is a carry chain: first omitted-peer carry plus a much sparser terminal carry. So the next frontier is even narrower now: a boundary law for the rare terminal carry cases, not for the whole suffix pair.
That terminal carry now has an exact arithmetic form: the two terminal branches differ only by a one-unit output-reserve gap, and the carry sign is exactly the induced floor crossing on the last omitted peer. The next frontier is therefore a boundary law for when that floor crossing occurs in amount/remainder space.
A widening pass to equal-fiber `n+1` families with `n=4,5` then showed that the triangular law itself is broader: the trailing gradient coordinate stays exact and the defect remains prefix-supported with tiny mass. The next frontier is therefore an equal-fiber carry automaton or boundary grammar, not a one-off `3+1` patch.

77. `equal_fiber_tail_universality_v1`
- Across widened equal-fiber families `n=3..8` on the dense 35k..55k window (`2520` unequal amount pairs total), the trailing defect coordinate stayed exactly zero and defect amplitude stayed unit-bounded in every checked case.

78. `interval_breakpoint_v1`
- The simple interval-support regime for equal-fiber defects survived through `n=5` and broke first at `n=6` with minimal witness `(a,b)=(35000,42000)` and defect `(1,0,1,0,0,0)`.

79. `single_crossing_suffix_law_v1`
- Across widened equal-fiber families `n=3..8`, every defect coordinate matched exactly a suffix carry chain with support size at most `1`; the exact chain law held on all `13,860` checked family-coordinate states.

80. `monotone_unit_gap_walk_v1`
- On the same `13,860` family-coordinate states, the underlying output-reserve gap walk was monotone in every case, with gap magnitude and step changes never exceeding `1`.

The equal-fiber widening line is now stronger than a special-case correction patch. It has a family-level structure: exact trailing coordinate, unit amplitude, a first support-shape breakpoint at `n=6`, and then a single-crossing suffix-event law generated by a monotone unit-gap walk. That is a genuine process object, not just a bounded histogram.

81. `signed_block_gap_law_v1`
- Across widened equal-fiber families `n=3..8`, the reserve-gap walk on all `13,860` checked family-coordinate states was exactly a constant-sign block followed by zeros.

82. `last_nonzero_event_law_v1`
- On the same `13,860` family-coordinate states, the entire suffix carry chain matched exactly the last nonzero event of that signed-block gap walk.

83. `equal_fiber_corrected_generator_v1`
- Across widened equal-fiber families `n=3..8` (`2520` unequal amount pairs total), local gradients corrected by the last-nonzero event law reconstructed the exact family signature in every checked case.

84. `equal_fiber_signature_compiler_v1`
- The widened equal-fiber signature compiled exactly from the signed-block gap law and last-nonzero event law on all `2520` tested family cases, giving the first direct exact-by-family algorithm produced by the deeper object stack.

The equal-fiber line is now no longer just a family of structural observations. It has become a compiled algorithm: trailing exactness, unit amplitude, single-crossing suffix law, signed-block gap walk, and last-nonzero event law compose into an exact signature compiler on the widened family.

85. `single_perturbed_peer_transfer_v1`
- On the first one-perturbed-peer family (`720` bounded cases), the exact equal-fiber compiler remained exact on `59.44%` of cases and left only a `21`-symbol residual alphabet on the rest.

86. `dominant_prefix_tail_cone_v1`
- In the same transfer family, `96.92%` of all nonzero residual cases lay in simple prefix or tail support cones, showing that the equal-fiber compiler degrades in a concentrated way rather than collapsing diffusely.

The equal-fiber compiler is therefore not brittle. When symmetry is perturbed by one peer, it usually stays exact and otherwise fails inside a narrow residual cone. That makes it valuable for advisory transfer and for the next correction-law search.

87. `two_generator_transfer_cone_v1`
- On the one-perturbed-peer transfer family (`720` bounded cases), the residual lay in the 2-generator cone spanned by the pure tail singleton and full-prefix block in `695` cases (`96.53%`).

88. `three_generator_near_exact_transfer_v1`
- Adding one mid-tail generator expanded coverage to `711 / 720` cases (`98.75%`), leaving only `9` exceptional cases in the first transfer family beyond exact equal-fiber symmetry.

The first transfer residual is therefore not just small; it is highly compressible. That makes the equal-fiber compiler a strong base object for advisory transfer and suggests the next correction law should target only the remaining 9 exceptional cases.

89. `small_perturbation_cone_universality_v1`
- On the one-perturbed-peer transfer family, the 3-generator transfer law was exact on all `342` bounded cases with perturbation magnitude at most `2000`.

90. `large_downshift_exception_pocket_v1`
- The remaining transfer failures formed a `9`-case large-perturbation pocket; all had perturbation magnitude at least `3000`, and `7/9` were downward perturbations.

The transfer line now has a proper phase diagram: exact equal-fiber family, exact small-perturbation extension, near-exact broader transfer cone, and then a tiny large-perturbation exception pocket.

91. `transfer_generator_tower_v1`
- On the first one-perturbed-peer transfer family (`720` bounded cases), a hierarchical residual basis tower achieved coverage `711/720` with `3` generators, `718/720` with `5`, and exact `720/720` coverage with `7` generators.

92. `exact_perturbed_peer_basis_v1`
- Seven explicit generators spanned all `21` residual symbols of the one-perturbed-peer transfer family exactly, giving the first exact residual basis beyond the equal-fiber compiler.

The transfer line now has a real algebraic hierarchy: exact equal-fiber compiler, exact small-perturbation extension, near-exact 3-generator transfer cone, and an exact 7-generator basis for the full first perturbed family.

93. `gradient_transfer_basis_v1`
- On the first one-perturbed-peer transfer family (`720` bounded cases), the residual closed exactly in gradient space with a 6-generator basis.

94. `gradient_signature_compression_v1`
- For the same transfer family, changing from signature space to gradient space reduced residual variety from `21` to `17` symbols and exact basis size from `7` to `6` generators.

The transfer line is now cleaner in gradient coordinates than in signature coordinates. That is the current best representation-level breakthrough in this batch-clearing program.

95. `interval_boundary_basis_v1`
- The first perturbed-family transfer residual closes exactly with a semantic 6-generator interval-boundary basis: five prefix-drop generators plus one head-tail bridge interval.

96. `triple_interval_grammar_v1`
- Every first perturbed-family gradient residual is representable exactly as a sum of at most three interval-boundary generators.

97. `interval_normal_form_v1`
- The first perturbed-family transfer residual has an exact minimal interval normal form: `428` zero cases, `279` one-interval cases, `12` two-interval cases, and a single three-interval case.

98. `double_interval_dominance_v1`
- `719 / 720` first perturbed-family transfer cases lie in the zero/one/two-interval regime; only one residual pattern needs three intervals.

The transfer line is now best understood semantically as an interval grammar. Gradient space gave the right coordinates; interval-boundary grammar gave the right objects. This is the cleanest transfer refinement beyond the equal-fiber compiler so far.

99. `singleton_exception_pocket_v1`
- The strongest three-interval target-gradient defect in the broadened downshift/outlier window is still a singleton witness: `(40000, 35000, 41000)`.

100. `two_interval_universality_v1`
- On the broadened downshift/outlier window (`360` cases), the interval grammar is zero/one/two-interval exact except for only `2` cases (`99.444%` coverage).

The transfer line is now close to a finished interval grammar: exact equal-fiber compiler, exact interval normal form on the first perturbed family, and broadened two-interval near-universality with only a microscopic exception pocket.

101. `resonance_line_v1`
- In the first broadened downshift/outlier window, all >2-interval exceptions lie on the single perturbation-gap line `delta - epsilon = 4000`.

102. `spike_uniqueness_v1`
- Each feasible perturbation pair on that resonance line contributes exactly one exceptional spike in `a`.

103. `exception_gradient_atlas_v1`
- On a much wider lattice, the >2-interval transfer tail still collapses to only `10` cases and `7` gradient symbols.

104. `reserve_level_exception_atlas_v1`
- Those widened exceptions concentrate on only `4` reserve levels, with maximum mass `3` on any one level.

The interval grammar is now strong in two senses: near the base family it is almost universally zero/one/two-interval, and far beyond that it still fails only in a tiny gradient/reserve-scale atlas.

105. `exception_motif_atlas_v1`
- The widened >2-interval tail compresses from 10 cases / 7 raw gradient symbols into 7 semantic interval motifs.

106. `motif_family_collapse_v1`
- Those 7 widened motifs collapse exactly into 4 semantic families.

107. `tail_charge_classifier_v1`
- The 4 widened exceptional motif families are determined exactly by the last gradient coordinate.

108. `tail_charge_universality_v1`
- The widened far-field exceptional atlas collapses to the four tail-charge values `{1, 2, -2, -1}`.

The far-field exception theory is now materially cleaner: the widened >2-interval tail compresses from raw symbols to motifs, from motifs to families, and from families to a one-scalar tail-charge classifier.

109. `super_tail_ladder_v1`
- Beyond the three-interval regime, the only observed four-interval family is a one-step tail-amplitude lift of the old singleton target pattern.

110. `four_interval_uniqueness_v1`
- On the larger lattice, only one gradient symbol requires more than three intervals, and it appears in only `5` cases.

The interval grammar now has a higher-order extension law: the first breach beyond three intervals is not a new family explosion, but a unique super-tail lift of an existing family.

111. `tail_floor_deficit_law_v1`
- On the enlarged one-perturbed-peer lattice (`24000` cases), tail charge equals the rounded terminal local floor-deficit difference exactly.

112. `subcritical_continuous_tail_v1`
- The continuous terminal local-swap residual remains uniformly subcritical (`< 1/2`) everywhere on that lattice, with maximum observed magnitude `0.1272411832765057`.

This is the first exact arithmetic explanation of the far-field exception law: the symbolic tail-charge classifier is not just descriptive, it is a rounded floor-deficit law with a global stability margin.

113. `tail_ladder_quantization_v1`
- The three-interval ladder branch lives in the floor-deficit band `[0.9716, 1.0817]`, while the four-interval super-tail branch lives in `[2.0211, 2.0513]`.

114. `super_tail_threshold_v1`
- A single threshold at `1.5` separates the three-interval and four-interval ladder branches exactly (`28 / 28` cases) on the current larger lattice.

The higher-order breach is now substantially cleaner: it is not only a unique super-tail lift, but a one-dimensional bifurcation in the floor-deficit coordinate.

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


134. `symbolic_head_compiler_v1`
- The widened head side compiles exactly from a small symbolic code: boundary word plus a tiny gap law.

135. `vectorized_gpu_proxy_v1`
- The dominant exact stages in the current perturbed-family compiler admit exact batched vectorized kernels, with measured speedups of about `110.67x` on the tail scalar kernel and `11.71x` on the head-word kernel across 24,000 cases.

136. `vectorized_symbolic_family_compiler_v1`
- The widened head-side symbolic family compiler is exact under batched vectorization and runs about `1.56x` faster than the scalar symbolic compiler on the 24,000-case family.

137. `compiler_kernel_factorization_v1`
- The current perturbed-family batch-order compiler factors into `map_tail_scalar`, `compact_head_boundary_word`, and `tiny_gap_branch` kernels instead of brute-force order search.


138. `anchored_head_code_v1`
- On the widened first-perturbed family, the exact head residue is determined by a compact anchored code: boundary word, gap tuple, and first support index.

139. `perturbed_residual_compiler_v1`
- Combining the exact anchored head code with the exact tail scalar law yields an exact full gradient compiler on all 24,000 widened first-perturbed-family cases.

## v71-v74
- `dominant_easy_fan_v1`: first exact direct-amount fast path on the widened first-perturbed family, covering 93.70416666666667% of all cases.
- `hybrid_fallback_mass_v1`: adding the v73 fallback zero/nonzero gate raises direct exactness to 99.025% globally.
- `three_stage_amount_compiler_v1`: the widened first-perturbed family now has an exact direct-amount three-stage compiler.

Interpretation:
- `ratio_sheet_atlas_v1` and `reserve_decade_tiebreak_v1` are bridge exactifiers, not compressed laws.
- `dominant_easy_fan_v1` and `three_stage_amount_compiler_v1` are the real DEX-facing advances from this slice.

## v75
- `three_stage_kernel_algebra_v1`: the widened first-perturbed family now has an exact direct-amount compiler with explicit kernel factorization across all three stages.

Caveat:
- `vectorized_three_stage_compiler_v1` is exact but not yet a speed breakthrough (`speedup ~= 0.993x`). This is execution-shape evidence, not a promotion-quality accelerator result.

## v76-v77
- `gap_pair_nonzero_word_law_v1`: on the stage-3 nonzero residual (`78` cases), `gap_pair` alone is exact on `72 / 78` cases and leaves only `5` ambiguous pockets of total mass `10`.
- `gap_pair_decade_law_v1`: adding reserve decade resolves those `5` pockets exactly, giving an exact symbolic compiler for the nonzero stage-3 residual.

Interpretation:
- This is a sharper symbolic residual law than the generic digit tiebreak from `v76`.
- It is still a symbolic-state compiler, not yet the compressed direct arithmetic head law.


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

## v82
- `out_reserve_triadic_exactifier_v1`: the full 234-case stage-3 residual is classified exactly by `fallback_key + round(53*c/a) + ((b mod 3), floor(b/20000))`, improving the prior exactifier from 226 keys to 223.
- `out_reserve_triadic_plateau_v1`: this out-reserve triadic-band exactifier remains exact across the same broad scale plateau, with best scale `S = 53`.

## v83
- `three_stage_triadic_compiler_v1`: replacing the older stage-3 ratio-digit exactifier with the out-reserve triadic-band law preserves exact direct-amount compilation on the widened first-perturbed family.
- `three_stage_triadic_kernel_algebra_v1`: the staged compiler kernel stack improves its stage-3 table from 226 to 223 exact states.

## v84
- `triadic_band_scalar_v1`: the out-reserve triadic-band pair collapses further to a single scalar band index `3 * floor(b / 20000) + ((b // 1000) % 3)`, keeping exact full stage-3 classification with 223 keys.
- `triadic_band_plateau_v1`: the scalar-band exactifier remains exact across the broad scale plateau, again with best scale `S = 53`.

## v85
- `reduced_fallback_triadic_exactifier_v1`: the exact full stage-3 law does not need the full fallback key; it only needs the fallback ratio bucket and fallback boundary word, plus `round(S*c/a)` and the triadic reserve-band scalar.
- `reduced_fallback_triadic_plateau_v1`: after this symbolic reduction, the broad exact plateau remains, and the best exact scale shifts from `S = 53` to `S = 52` while keeping `223` exact keys.

## v86
- `scalar_stage3_exactifier_v1`: the full 234-case stage-3 residual is classified exactly by four scalar amount-derived coordinates: fallback ratio bucket, `round(52*c/a)`, the triadic reserve-band scalar, and the amount-profile first-support index.
- `scalar_stage3_plateau_v1`: this fully scalar exactifier remains exact across a broad scale plateau, with `224` exact scales in `1..300` and best scale `S = 52`.

## v87
- `fused_scalar_stage3_exactifier_v1`: the full stage-3 residual collapses from 4 exact scalars to 3 exact scalars by fusing the fallback ratio bucket with the triadic reserve-band scalar via `r100 + 16 * triadic_band_scalar(b)`.
- `fused_scalar_stage3_plateau_v1`: the fused 3-scalar exactifier remains exact across a broad scale plateau, with best scale `S = 52`, `224` exact scales in `1..300`, and `220` exact keys.

- `v88`: exact 2-scalar stage-3 law with `216` keys and broad exact plateau (`224` exact scales, best at `S=52`).
- `v89`: exact 1-scalar stage-3 law with `208` keys; best embedding `r100 + 16*triadic + 87*round(52*c/a) + 728*first_support`.
- `v90`: theorem-shaped compression: exact one-scalar weights are precisely the complement of a finite forbidden collision set; all weights above `2299` are exact.

## v97
- `global_optimal_merge_law_v1`: within exact weights up to 2300, weight 728 is the unique exact weight with maximum safe same-label merges; 216 affine forms collapse to 208 keys via exactly 8 safe merges.
- `chamber_pinch_triptych_v1`: the optimal chamber `{726,727,728}` is locally pinched by exactly one cross-label collision on each side, and key counts descend as safe merges rise: `211 -> 210 -> 208`.

## v98
- `unit_gap_admissibility_peak_v1`: among exact weights, `728` uniquely maximizes admissible same-label support-gap-1 collisions with count `8`; nearby exact weights only realize `4` (`726`) and `5` (`727`), while `729` is blocked by cross-label collision.
- `unit_gap_merge_rigidity_v1`: the optimal merge pattern at `728` is entirely unit-gap; neighboring exact weights already contain non-unit-gap same-label edges.

## v99
- `optimal_support_pair_atlas_v1`: the eight optimal same-label merges at `728` live in only four support classes: zero `(-1,0)` x3, zero `(0,1)` x2, zero `(1,2)` x1, nonzero `(0,1)` x2.
- `neighbor_span_break_v1`: `728` is span-minimal; neighboring exact weights `726` and `727` already admit longer support spans.

## v100
- `span1_ladder_optimality_v1`: among the `1161` exact one-scalar weights up to `2300`, `1125` are span-1, and `728` is the unique span-1 weight attaining the maximal merge count `8`.
- `large_merge_pattern_atlas_v1`: among exact large-merge weights (`merge >= 5`), only `4/10` stay span-1; `728` is the unique maximal large-merge pattern.

## v101
- `route_ternary_overlap_code_v1`: on a bounded two-hop CPMM family, quadratic overlap defects live in the ternary alphabet `{0,1,2}` exactly.
- `route_interval_deviation_grammar_v1`: zeros appear in at most one run and twos in at most two runs; `87.5%` of the family lies in the simplest `<=1 zero-run, <=1 two-run` regime.

## v102
- `route_support_word_atlas_v1`: the support of route overlap entries equal to `2` collapses from `20` exact support sets to `8` semantic support words.
- `route_semantic_family_dominance_v1`: combining two-support words with zero-run words collapses the `30` exact route families to `13` semantic families; `87.5%` of cases lie in empty or single-word two-support regimes and `85.9375%` are zero-free.

## v103
- `route_semantic_star_fan_v1`: the `13` semantic route families form a star fan around the neutral family; the neutral node has degree `12`, radius `1`, and the family graph has diameter `2`.
- `route_axis_rigidity_v1`: `11/12` non-neutral route families are hub-adjacent through at least five primitive parameter axes; exactly one family is axis-rigid with support on only two axes.

## v104
- `large_merge_transfer_code_v1`: the exact large-merge one-scalar weights (`merge >= 5`, up to `2300`) admit a small support-class transfer code `Omega(w) = (L(w), z01(w), n01(w))`, exact on all `10` such weights.
- `chamber_local_peak_code_v1`: the local optimal chamber weights `{726,727,728}` are exactly separated by the tiny local code `(L(w), n01(w))`.

## v105
- `merge4_mod4_transfer_code_v1`: the exact large-merge support-class transfer code extends from `merge>=5` to `merge>=4` after adjoining only `weight mod 4`.
- `merge3_mod18_transfer_code_v1`: the same support-class code extends further to `merge>=3` after adjoining `weight mod 18`.

## v106
- `modulus_transfer_ladder_v1`: the large-merge transfer code has a discrete modulus ladder: no modulus for `merge>=5`, `mod 4` for `merge>=4`, and `mod 18` for `merge>=3`.
- `no_small_modulus_low_merge_v1`: no modulus up to `64` resolves the same support-class code for `merge>=2`, `merge>=1`, or the full exact-weight set.

## v107
- `merge3_phase_lattice_v1`: the `merge>=3` widening is best interpreted as a phase lattice: `mod 9` and parity are individually insufficient, but exact together.
- `merge4_two_adic_phase_v1`: the `merge>=4` widening is genuinely 2-adic: `mod 2` is insufficient, `mod 4` is exact.

## v108
- `no_simple_phase_lift_merge2_v1`: the `merge>=2` widening does not admit any exact code of the form `Omega + (weight mod m) + merge/max_span` for `m <= 64`.
- `threshold_break_law_v1`: the low-modulus transfer ladder breaks sharply after `merge>=3`: no modulus at `merge>=5`, `mod 4` at `merge>=4`, `mod 18` at `merge>=3`, and no simple lift at `merge>=2`.

## v109
- `merge2_composite_phase_lift_v1`: the `merge>=2` threshold does admit an exact transfer lift after enriching the support signature to `(merge, max_span, long_classes, z01, n01)` and adjoining a composite phase `mod 91`.
- `crt_phase_factorization_v1`: this `mod 91` phase factors exactly as `(mod 7, mod 13)`; neither factor alone is sufficient.

## v110
- `no_one_extra_stat_lift_merge1_v1`: the `merge>=1` threshold still resists the `merge>=2` recovery pattern; no exact code of the form `(base support signature + one extra simple support count + weight mod m)` exists for the tested moduli.
- `threshold_ladder_sharpness_v1`: the transfer ladder is now `1, 4, 18, 91`, and then a sharp break at `merge>=1` for the next simple enrichment level.
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
## v117
- `merge1_anchor_rest_quotient_v1`: the exact `merge>=1` full-histogram carrier compresses to `57` support signatures by isolating zero-side support `(-1,0)` and merging the rest.
- `merge1_minimal_partition_trichotomy_v1`: among same-partition quotient lifts, the minimal exact support-signature count `57` is achieved by exactly `3` partitions, and every minimizer separates `(-1,0)` from the central/right cluster.

## v118
- `merge1_asymmetric_histogram_quotient_v1`: the exact `merge>=1` histogram carrier compresses further to `55` support signatures when zero and nonzero sides are allowed different quotients; the simplest exact form isolates zero-side `(-1,0)` and collapses the full nonzero side.
- `merge1_asymmetric_minimality_v1`: among asymmetric zero/nonzero partition quotients, the minimal exact support-signature count is `55`, attained with a `2`-block zero partition and a `1`-block nonzero partition.
## v119
- `asymmetric_modulus_rigidity_v1`: compressing the exact `merge>=1` carrier from `72` support signatures to the asymmetric `55`-signature quotient does not lower the minimal exact modulus; the phase complexity remains rigid at `821`.
## v120
- `asymmetric_divisor_spectrum_v1`: exact moduli up to `1000` are exactly the complement of the forbidden divisor spectrum of within-class differences for the asymmetric `merge>=1` quotient.
- `asymmetric_span_law_v1`: once the modulus exceeds the maximal within-class span `1916`, exactness becomes automatic.
## v121
- `forbidden_divisor_prefix_cover_v1`: the forbidden divisor spectrum covers every modulus `1..820`, so `821` is the first exact modulus.
- `exact_chamber_cover_v1`: the exact subspan moduli up to `1916` form `118` chambers with `500` exact moduli, and those chambers are exactly the complement of the forbidden divisor spectrum below the automatic exact regime.
## v123
- `upper_half_self_divisor_law_v1`: above half the maximal span (`959..1916`), an asymmetric `merge>=1` modulus is exact iff it is not itself a within-class difference.
- `upper_half_boundary_law_v1`: all upper-half exact chambers are flanked by self-hit forbidden moduli, and the largest upper-half chamber is `[1737, 1769]`.
## v124
- `upper_half_gap_run_law_v1`: above half the maximal span, the exact chambers are exactly the consecutive missing runs of the raw within-class difference set.
- `largest_gap_witness_v1`: the largest upper-half chamber `[1737, 1769]` is flanked tightly by self-hit forbidden differences `1736` and `1770`.
## v125
- `upper_half_spacing_law_v1`: above half the maximal span, exact chambers are exactly the positive spacings between consecutive ordered self-differences, once the augmented boundary points `upper_half_start - 1` and `span` are included.
- `upper_half_long_gap_zone_v1`: every long upper-half chamber (length `> 8`) lies in the upper half of the upper-half regime.

## v126-v127 additions

- `phase_regime_ladder_v1`
  - The batch transfer ladder now has a clean arithmetic regime sequence: `1, 4, 18, 91, 821`.
- `prime_rigidity_break_v1`
  - Support compression from `72` to `55` signatures does not lower the `merge>=1` exact phase modulus; the phase remains rigid at prime `821`.
- `route_triad_star_factorization_v1`
  - The validated route star-fan and minimal triad code combine into a clean factorization: every family is hub-adjacent to neutral and three added features suffice for exact recovery.
- `route_rigid_exception_law_v1`
  - There is exactly one low-axis rigid route family; the rest are high-support perturbations of the neutral hub.
## v128
- `merge1_divisor_spectrum_law_v1`: on the exact `merge>=1` asymmetric quotient, moduli up to the maximal class span are exact iff they avoid the forbidden divisor spectrum of within-class differences.
- `merge1_upper_half_gap_run_law_v1`: above half the maximal class span, exact `merge>=1` moduli are exactly the missing runs in the ordered self-difference set, with largest upper-half chamber `[1737, 1769]`.
## v130
- Validated `record_gap_spine_v1`: long upper-half exact chambers form a monotone record spine with records `(1512,1520,9)`, `(1597,1608,12)`, `(1644,1667,24)`, `(1669,1695,27)`, `(1737,1769,33)`.
- Validated `threshold_tail_bands_v1`: long-gap thresholds activate in nested tail bands: `>12` starts at `1644`, `>24` starts at `1669`, `>28` and `>32` start at `1737`.
## v131
- `pending_liquidation_band_v1`: on the live zUSD core, `oracle_commit` blocking and `liquidate` enabling share the same pending-price MCR threshold, so the guard gap is exactly zero. In the zero-penalty full-SP regime, the profitable liquidation band is exactly `floor(debt * 1e8 / collateral) + 1 <= pending_price <= ceil(debt * mcr * 1e8 / (collateral * 10000)) - 1`. Bounded replay matched the closed form on 500 random single-vault and 500 random multi-vault probes with zero mismatches.

## v132 wider-scan additions
- `kadapt_information_bundle_v1`: on the bounded mixed information-timing seam, a `K = 3` freshness-allocation bundle matches the full scenario-oracle upper bound and materially improves both mean utility and robust minimum group mean over the best static policy.
- `single_lane_zero_adjustability_slice_v1`: on the bounded information-timing seam, pure oracle-only, attestation-only, and Tau-only families show zero measurable gain from `K = 3` over the best static policy, while mixed families show large positive gain.
- `integer_destroy_repair_selector_v1`: on the bounded exact-out CPMM frontier, a one-swap integrality-aware destroy-repair pass repairs the residual omitted-pair cap-4 misses without widening the candidate-pool budget.
- `slot_replacement_beats_cap_lift_v1`: on the matched widened CPMM smoke slice, one-swap integrality-aware slot replacement repaired every threatening case while the cap-5 fallback repaired only `57.1%`, with no benign regressions.
- `cheap_inversion_trigger_v1`: on the widened CPMM selector corpus, the trigger `omitted_better_pool_count >= 1 and winner_leg_count >= 2` caught `87.5%` of threatening cases while reducing amortized destroy-repair spend by about `89%` relative to always repairing.
- `trigger_family_stabilization_v1`: extending the same cheap trigger family to triple conjunctions produced no gain; the best triple trigger was the same pair gate plus a vacuous condition.

- `singleton_residual_fallback_v1`
  - The remaining widened-CPMM Maher miss is structurally real, but the obvious singleton residual fallbacks are not promotion-worthy.
  - Best tested rule `singleton_pool7_paircover` recovered exact recall, but with residual benign fire `0.386364` and amortized swap cost `6.25` versus `1.125` for the current guarded trigger lane.
- `global_exact_out_dd_v1`
  - On the first bounded wide exact-out corpora, a layered decision diagram over all pools recovered the exact full-domain canonical winner with zero counterexamples on both `cpmm_wide` and `supported_wide`.
  - The same carrier compressed search materially versus truthful full-domain enumeration:
    - `190.91` mean DD states versus `1534.38` mean candidates on `cpmm_wide`,
    - `212.56` mean DD states versus `2908.38` mean candidates on `supported_wide`.
  - This is the first paper-derived exact-out object in the loop that jointly absorbs support selection and allocation into one exact bounded solver/reference lane.
- `exactness_first_global_dd_reference_v1`
  - On the matched bounded wide comparison, the global exact-out DD stayed exact on `cpmm_wide` where `probe_ladder_cap4 + fixed-set DP` fell to `0.9375`, while using nearly the same mean quote-call budget (`81.09` vs `81.41`).
  - The DD did not beat the fixed-set lane on internal state count, so its current honest role is an exactness-first bounded reference oracle, not yet a blanket runtime replacement.
- `dd_beats_guarded_maher_on_exactness_v1`
  - On the matched widened CPMM slice, the global exact-out DD stayed exact while the current guarded Maher lane fell to `0.875`, with no Maher-only repairs and `12.5%` DD-only repairs.
  - This keeps the DD branch alive as the strongest exact bounded oracle even after the best current local selector repair is applied.
- `projected_relaxed_dd_objective_law_v1`
  - On the widened `cpmm_wide` and `supported_wide` exact-out corpora, the out-mass-only relaxed DD lower bound matched the exact objective on every tested case.
  - This means the DD gap lane is already an exact objective certificate lane on the claimed bounded domain.
- `tiny_restricted_dd_canonical_lane_v1`
  - After the objective collapse, the remaining carrier for exact canonical recovery is tiny:
    - width `3` on `cpmm_wide`,
    - width `6` on `supported_wide`.
  - This turns the DD branch from a generic exact oracle into a compact canonicalization lane on the claimed bounded slice.
- `objective_frontier_projection_canonicalizer_v1`
  - On the widened `cpmm_wide` and `supported_wide` exact-out corpora, once the exact objective frontier is isolated, even the out-mass-only frontier carrier recovers the exact canonical winner.
  - This shows the residual DD problem is not missing tie-memory state; it is cheap recovery or certification of the exact objective frontier.
- `relaxed_frontier_composed_dd_lane_v1`
  - On the widened exact-out DD corpora, the relaxed objective table plus out-mass frontier projection recovered the exact canonical winner on every tested case.
  - The composed lane used materially fewer states than the full exact DD while spending no extra quote calls beyond the relaxed table:
    - `cpmm_wide`: `106.75` combined states vs `197.56` exact-DD states, with identical mean quote calls `80.0`.
    - `supported_wide`: `106.88` combined states vs `214.53` exact-DD states, with identical mean quote calls `86.875`.
  - Honest role:
    - strongest current DD promotion target is a cheap objective-frontier constructor plus trivial canonical projection, not only an objective certificate lane.
- `dd_frontier_residual_survival_v1`
  - On the omitted-pair CPMM residual family, where `probe_ladder_cap4` only matched truth on `55.56%` of cases, the composed relaxed-objective plus frontier-projection DD lane stayed exact on all `27` witness-centered cases.
  - It preserved the same pattern as on the widened corpora:
    - `99.56` combined states vs `208.0` exact-DD states,
    - identical mean quote calls `84.0`,
    - and `0.0` extra frontier quote calls.
- `supported_reserve_only_dd_boundary_v1`
  - The composed DD lane has a real supported-family boundary.
  - On structured supported patterns:
    - `2+1+1::multi_template` stayed exact with `relaxed_objective_exact_rate = 1.0`.
    - `3+1::reserve_only` and `2+2::reserve_only` fell to `0.857143`.
  - First failure shape:
    - `amount_out_total = 8`
    - true optimum `21`
    - relaxed lower bound `20`
    - no frontier state at the false relaxed objective
  - Honest implication:
    - the composed relaxed-objective plus frontier-projection lane must either exclude the supported `reserve_only` boundary or repair the relaxed objective there.
- `legaware_relaxed_boundary_repair_v1`
  - The supported `reserve_only` boundary is caused by omitting the `max_legs` constraint from the relaxed objective carrier.
  - A leg-aware relaxed carrier repaired all tested supported targeted patterns back to exactness:
    - `2+1+1::multi_template`
    - `2+2::reserve_only`
    - `3+1::reserve_only`
  - But the repair is not a good compression object:
    - state fraction versus exact DD was `2.23`, `2.18`, and `2.17` respectively,
    - quote fraction stayed `1.0`.
  - Honest implication:
    - the boundary is repairable, but the current repair is worse than exact DD on carrier size, so narrowing the composed lane's domain is cleaner than promoting this repair.

- `dd_declared_domain_contract_v1`
  - The composed DD lane now has an explicit bounded promotion contract.
  - Included:
    - `cpmm_wide`
    - `cpmm_residual_omitted_pair`
    - supported `2+1+1::multi_template`
  - Excluded:
    - supported `2+2::reserve_only`
    - supported `3+1::reserve_only`
  - Weighted comparison on the included slices:
    - DD match rate `1.0`
    - strongest selector-lane match rate `0.996251`
  - Unique DD lift remains concentrated in `cpmm_wide`.

- `dd_declared_domain_oracle_posture_v1`
  - The right promotion for the composed DD lane is a stronger bounded exactness oracle, not a blanket runtime-default lane.
  - On the other included slices, the strongest selector lanes already reach parity.

- `dd_declared_domain_guard_v1`
  - The DD promotion contract is now executable as an experiment-side guard:
    - composed DD on all-CPMM cases and supported `2+1+1::multi_template`,
    - exact DD fallback on supported `reserve_only`,
    - selector default elsewhere.

- `dd_guarded_oracle_shadow_lane_v1`
  - On the classified corpus of `1165` cases, the guarded DD oracle lane was exact while the runtime selector lane reached `0.996567`.
  - Route split:
    - composed DD on `1067` cases with selector parity gap still present,
    - exact DD fallback on `98` supported boundary cases where selector already matched.
  - Honest implication:
    - the guarded DD lane is a clean shadow/oracle object, not yet a runtime-default replacement.

- `dd_mixed_replay_shadow_harness_v1`
  - On a mixed replay-style corpus of `53` cases:
    - guarded DD lane match rate was `1.0`
    - selector lane match rate was `0.924528`
    - disagreement rate was `0.075472`
  - All observed lift came from the composed-DD route:
    - `45` cases
    - guarded match `1.0`
    - selector match `0.911111`
  - Exact-DD fallback and selector-default routes both stayed at parity.

- `dd_shadow_log_schema_v1`
  - The guarded DD lane now has a lightweight per-case shadow log schema and JSONL artifact format.
  - This makes disagreement review deterministic and replayable instead of summary-only.

- `composed_dd_cpmm_runtime_candidate_v1`
  - On a larger all-CPMM replay corpus of `123` cases:
    - guarded match rate was `1.0`
    - selector match rate was `0.967480`
    - guarded lift rate was `0.032520`
    - mean guarded quote calls were `84.63`
    - mean selector quote calls were `116.97`
  - Honest implication:
    - the composed-DD CPMM route is now a real bounded shadow/runtime candidate, not merely an oracle lane.

- `cpmm_dd_runtime_bar_v1`
  - The CPMM composed-DD route now has an explicit acceptance bar for bounded runtime candidacy.
  - Required:
    - CPMM-only route fence
    - guarded exactness `1.0`
    - mean quote cost no worse than selector
    - replayable JSONL disagreement log

- `cpmm_dd_reusable_shadow_runner_v1`
  - The larger CPMM shadow pass is now a reusable CLI artifact, not a one-off experiment script.
  - That makes repeated replay sweeps and receipt regeneration cheap enough to treat as a standing promotion gate.

- `cpmm_dd_runtime_bar_check_v1`
  - The CPMM runtime promotion bar is now executable.
  - Current status:
    - route fence pass
    - guarded exactness pass
    - quote cost pass
    - replay log pass
    - disagreement cleanliness pass
    - case-level evidence pass
    - overall pass `true`

- `dd_shadow_adapter_v1`
  - The DD research lane is now packaged as a non-core adapter-backed shadow contract:
    - declared-domain route decision
    - guarded DD quote
    - selector quote
    - disagreement metadata
  - The mixed replay and large CPMM shadow receipts were regenerated through the adapter with no metric drift.
  - Honest implication:
    - this is the reusable integration object for replay/shadow work,
    - not a reason to move DD logic into `src/core/`.

- `dd_shadow_cli_v1`
  - The DD shadow lane now has a file-driven replay entrypoint in `tools/exact_out_dd_shadow.py`.
  - It reads JSON cases, runs them through the adapter, and emits summary JSON plus JSONL logs.
  - Honest implication:
    - replay/shadow usage is now operational outside the experiment loop,
    - while still staying entirely outside `src/core/`.

## Non-promotion note from v133

- `lookup_bao_compiler_v1` survives as a useful object, but it is not promoted as a breakthrough.
- Reason:
  - it proves a clean bounded theorem: on finite powerset carriers, unary BAO-valid lookup operators are exactly the relation-induced / atom-image operators,
  - and the toy thresholded Q-action operators compile into that class exactly,
  - but it is still a semantic compiler and acceptance gate, not yet a new DEX mechanism law or runtime-core theorem.

## Non-promotion note from v134

- `binary_lookup_bao_compiler_v1` survives as a useful object, but it is not promoted as a breakthrough.
- Reason:
  - it proves a clean bounded theorem: on finite powerset carriers, separately additive binary lookup operators are exactly the ternary-relation / pair-atom operators,
  - and the toy thresholded pair-score operators compile into that class exactly,
  - but it is still a semantic compiler and acceptance gate, not yet a new DEX mechanism law or runtime-core theorem.

## Non-promotion note from v135

- `typed_lookup_bao_compiler_v1` survives as a useful object, but it is not promoted as a breakthrough.
- Reason:
  - it proves a clean bounded theorem: on finite typed powerset carriers, separately additive mixed-carrier lookup operators are exactly the typed ternary-relation / typed pair-atom operators,
  - and the toy typed pair-score operators compile into that class exactly,
  - but it is still a semantic compiler and admission gate, not yet a new DEX mechanism law or runtime-core theorem.

## Non-promotion note from v136

- `typed_operator_acceptance_gate_v1` survives as a useful object, but it is not promoted as a breakthrough.
- Reason:
  - it turns the typed semantic theorem into a deterministic acceptance checker with explicit rejection reasons and canonical receipts,
  - and it accepts exactly the typed relation-shaped operators on the bounded exhaustive domain,
  - but it is still an admission gate and compiler-side object, not yet a new DEX mechanism law or runtime-core theorem.

## Non-promotion note from v137

- `typed_operator_registry_gate_v1` survives as a useful object, but it is not promoted as a breakthrough.
- Reason:
  - it turns the typed semantic gate into a deterministic registry discipline with idempotence and duplicate-semantic / duplicate-id protections,
  - and on the bounded exhaustive domain it inserts exactly the four lawful typed semantics and nothing extra,
  - but it is still a registry and compiler-side object, not yet a new DEX mechanism law or runtime-core theorem.

## Non-promotion note from v138

- `receipt_backed_tau_operator_manifest_v1` survives as a useful object, but it is not promoted as a breakthrough.
- Reason:
  - it turns registry discipline into a canonical, replayable, order-invariant file artifact with explicit tamper detection,
  - and on the bounded exhaustive domain it emits exactly the four lawful typed semantics and nothing extra,
  - but it is still a manifest and compiler-side object, not yet a new DEX mechanism law or runtime-core theorem.

## Non-promotion note from v139

- `tau_operator_manifest_checker_v1` survives as a useful object, but it is not promoted as a breakthrough.
- Reason:
  - it turns the manifest into a direct file-validation boundary with explicit parse/schema/semantic failure surfaces,
  - and it rejects tampered hashes, unsorted entries, duplicate ids, and real receipt replay failures on the bounded corpus,
  - but it is still a checker and compiler-side object, not yet a new DEX mechanism law or runtime-core theorem.

## Non-promotion note from v140

- `tau_operator_library_bootstrap_v1` survives as a useful object, but it is not promoted as a breakthrough.
- Reason:
  - it proves that a checked manifest can carry a small named operator library with deterministic application semantics,
  - and it rejects tampered manifests and missing required role bindings on the bounded corpus,
  - but it is still a bootstrap and compiler-side object, not yet a new DEX mechanism law or runtime-core theorem.


## Non-promotion note from v141

- `score_table_typed_operator_compiler_v1` survives as a useful object, but it is not promoted as a breakthrough.
- Reason:
  - it provides the first explicit bridge from bounded score tables into the accepted typed-operator lane,
  - it shows that atom-local score families compile cleanly while direct full-table thresholding can fail separate additivity,
  - but it is still a semantic compiler and controller-side bridge object, not yet a new DEX mechanism law or runtime-core theorem.


## Non-promotion note from v142

- `score_table_symbolic_policy_synthesizer_v1` survives as a useful object, but it is not promoted as a breakthrough.
- Reason:
  - it proves the first bounded bridge from score-compiled role outputs into the symbolic source-policy grammar,
  - it surfaces an important ambiguity fact: the current bounded corpus does not uniquely determine the policy,
  - but it is still a bounded synthesis and ambiguity-atlas object, not yet a new DEX mechanism law or runtime-core theorem.


## Non-promotion note from v143

- `policy_identifiability_corpus_search_v1` survives as a useful object, but it is not promoted as a breakthrough.
- Reason:
  - it cleanly separates removable corpus ambiguity from structural full-domain aliasing,
  - it shows one extra case removes the `Obs_i` ambiguity while `(Can_a,1)` and `(Can_a,3)` remain equivalent on the full bounded domain,
  - but it is still an identifiability and ambiguity-structure result, not yet a new DEX mechanism law or runtime-core theorem.

## Non-promotion note from v144

- `policy_equivalence_quotient_v1` survives as a useful object, but it is not promoted as a breakthrough.
- Reason:
  - it compresses the current `9` syntactic policies into `8` semantic classes and shows the only nontrivial full-domain alias class is `{(Can_a,1), (Can_a,3)}`,
  - it restores uniqueness at the quotient level for the augmented bounded corpus without pretending the raw syntax is unique,
  - but it is still a bounded quotient and alias-compression result, not yet a new DEX mechanism law or runtime-core theorem.

## Non-promotion note from v145

- `quotient_policy_pcc_bridge_v1` survives as a useful object, but it is not promoted as a breakthrough.
- Reason:
  - it proves the unique augmented quotient class can be compiled through the current non-core Tau operator artifact chain all the way to a current PCC obligation,
  - it preserves the residual `(Can_a,1)` / `(Can_a,3)` alias as explicit metadata instead of pretending raw syntax is unique,
  - but it is still a bounded quotient-to-artifact bridge object, not yet a new DEX mechanism law or runtime-core theorem.

## Non-promotion note from v146

- `alias_aware_symbolic_policy_lane_v1` survives as a useful object, but it is not promoted as a breakthrough.
- Reason:
  - it turns quotient alias provenance into a first-class non-core symbolic policy artifact and proves that provenance survives through the current bounded PCC lane,
  - it shows alias metadata changes source-policy identity without changing the bounded lowered semantics,
  - but it is still a bounded integration/provenance result, not yet a new DEX mechanism law or runtime-core theorem.

## Non-promotion note from v147

- `direct_alias_policy_synthesizer_v1` survives as a useful object, but it is not promoted as a breakthrough.
- Reason:
  - it turns quotient-level alias-aware policy synthesis into a direct artifact constructor with no sidecar file,
  - it reproduces the `v146` alias-aware policy artifact exactly and still reaches a current PCC obligation,
  - but it is still a bounded artifact-construction bridge, not yet a new DEX mechanism law or runtime-core theorem.

## Non-promotion note from v148

- `alias_aware_replay_corpus_classifier_v1` survives as a useful object, but it is not promoted as a breakthrough.
- Reason:
  - it turns quotient-level replay-corpus quality into an explicit classifier and shows the alias-aware schema can separate multi-class ambiguity from in-class aliasing,
  - it proves the augmented and full-domain corpora emit the same canonical alias-aware policy hash as `v147`,
  - but it is still a bounded replay-classification and stability result, not yet a new DEX mechanism law or runtime-core theorem.

## Non-promotion note from v149

- `two_literal_controller_family_pressure_v1` survives as a useful object, but it is not promoted as a breakthrough.
- Reason:
  - it gives the first bounded replay-pressure measurement for a richer controller family and shows the current augmented corpus is insufficient under grammar widening,
  - it also shows the unique full-domain winner still simplifies back to `atom(Can_a,1)`, which is valuable normalization evidence,
  - but it is still a bounded grammar-pressure and replay-classification result, not yet a new DEX mechanism law or runtime-core theorem.

## Non-promotion note from v150

- `minimal_replay_extension_for_richer_family_v1` survives as a useful object, but it is not promoted as a breakthrough.
- Reason:
  - it turns the richer-family replay gap into an exact minimal witness result and produces a concrete 2-case corpus upgrade,
  - it shows uniqueness can be recovered without changing the canonical winner,
  - but it is still a bounded replay-extension search result, not yet a new DEX mechanism law or runtime-core theorem.

## Non-promotion note from v151

- `richer_family_replay_upgrade_bridge_v1` survives as a useful object, but it is not promoted as a breakthrough.
- Reason:
  - it closes the loop from richer-family replay upgrade back into the existing PCC-facing artifact lane,
  - it cleanly separates provenance-sensitive source-policy identity from unchanged lowered behavior and unchanged case decisions,
  - but it is still a bounded replay-upgrade bridge result, not yet a new DEX mechanism law or runtime-core theorem.

## Non-promotion note from v152

- `three_literal_family_upgrade_stability_v1` survives as a useful object, but it is not promoted as a breakthrough.
- Reason:
  - it shows the replay upgrade from `v150` already stabilizes a strictly larger monotone controller family,
  - it strengthens confidence that the current simple policy surface is robust under bounded monotone widening,
  - but it is still a bounded family-pressure and corpus-stability result, not yet a new DEX mechanism law or runtime-core theorem.

## Non-promotion note from v153

- `monotone_closure_saturation_v1` survives as a useful object, but it is not promoted as a breakthrough.
- Reason:
  - it closes the monotone-family widening loop by showing `v152` already saturates the full monotone closure on the bounded domain,
  - it strongly stabilizes the current simple policy surface against any further monotone widening over the same literals,
  - but it is still a bounded closure/saturation result, not yet a new DEX mechanism law or runtime-core theorem.

## Non-promotion note from v154

- `boolean_atom_partition_closure_v1` survives as a useful object, but it is not promoted as a breakthrough.
- Reason:
  - it gives the first exact bounded Boolean-closure count for the current literal set and proves the non-monotone lane is much larger than the exhausted monotone lane (`512` vs `26`),
  - it also shows the current replay-upgraded corpus is no longer sufficient once full Boolean expressivity is allowed,
  - but it is still a bounded closure/frontier measurement, not yet a new DEX mechanism law or runtime-core theorem.

## Non-promotion note from v155

- `boolean_closure_minimal_replay_extension_v1` survives as a useful object, but it is not promoted as a breakthrough.
- Reason:
  - it gives the first exact minimal replay witness for the non-monotone Boolean lane and shows the gap is exactly three unconstrained atoms,
  - it also compresses the witness family into a clean structural rule rather than an arbitrary case list,
  - but it is still a bounded replay-extension result, not yet a new DEX mechanism law or runtime-core theorem.

## Non-promotion note from v156

- `boolean_atom_basis_corpus_v1` survives as a useful object, but it is not promoted as a breakthrough.
- Reason:
  - it packages the current literal frontier into an exact minimal replay basis and proves any smaller corpus is incomplete,
  - it also converts replay-baseline design into a clean combinatorial object with exact multiplicity `14`,
  - but it is still a bounded basis/construction result, not yet a new DEX mechanism law or runtime-core theorem.

## Non-promotion note from v157

- `input_test_literal_refinement_v1` survives as a useful object, but it is not promoted as a breakthrough.
- Reason:
  - it is the first exact bounded answer to which new primitives actually enlarge the current Boolean basis,
  - it also identifies the unique minimal full-separating basis and cleanly quotients redundant candidate tests,
  - but it is still a bounded primitive-search and refinement result, not yet a new DEX mechanism law or runtime-core theorem.

## Non-promotion note from v158

- `input_augmented_monotone_closure_v1` survives as a useful object, but it is not promoted as a breakthrough.
- Reason:
  - it gives the first exact closure-size measurement after adding genuinely new primitives and shows the positive language expands sharply (`26` to `167`),
  - it also proves the old replay basis is insufficient for the enlarged primitive set,
  - but it is still a bounded closure/frontier measurement, not yet a new DEX mechanism law or runtime-core theorem.

## Non-promotion note from v159

- `augmented_monotone_basis_repair_v1` survives as a useful object, but it is not promoted as a breakthrough.
- Reason:
  - it gives an exact and unique replay repair for the enlarged primitive set from `v158`,
  - it converts replay-baseline maintenance into a deterministic bounded object rather than a heuristic data-gathering task,
  - but it is still a bounded replay-repair result, not yet a new DEX mechanism law or runtime-core theorem.

## Non-promotion note from v160

- `coordinate_basis_monotone_completeness_v1` survives as a useful object, but it is not promoted as a breakthrough.
- Reason:
  - it gives an exact closure-completeness result for the current coordinate-bit basis and cleanly closes the positive-language frontier,
  - it also proves the old output literals are redundant for positive expressivity on the bounded domain,
  - but it is still a bounded closure-completeness result, not yet a new DEX mechanism law or runtime-core theorem.

## Non-promotion note from v161

- `nonmonotone_adjoinability_frontier_v1` survives as a useful object, but it is not promoted as a breakthrough.
- Reason:
  - it gives the first exact bounded growth frontier for adjoining a non-monotone relational primitive library to the complete coordinate-bit positive basis,
  - it also isolates a first maximal basis and shows the current six-candidate library saturates at `1176`, still far below the full Boolean algebra size `65536`,
  - but it is still a bounded primitive-frontier measurement, not yet a new DEX mechanism law or runtime-core theorem.


## Non-promotion note from v162

- `free_boolean_syntax_runtime_quotient_v1` survives as a useful object, but it is not promoted as a breakthrough.
- Reason:
  - it sharpens the abstract-vs-executable boundary for Boolean-algebra reasoning in ZenoDEX,
  - it strengthens the existing finite Cantor-prefix / BDD runtime posture,
  - but it is still a semantic guardrail and design clarification, not a new DEX mechanism law or runtime-core theorem.

## Method-promotion note from v163

- `disaster_guard_hitting_quotient_v1` is promoted as a search-method object, not as a new runtime mechanism.
- Reason:
  - it gives the first exact bounded bridge from named disaster-axis enumeration to obligation-class minimization,
  - it proves, with a local Lean transfer theorem, why covering quotient representatives is enough for every axis mapped to those representatives,
  - and it identifies a unique minimal `7`-guard cover for the current bounded corpus.
- Scope limit:
  - this does not prove all possible disaster states unreachable,
  - a future axis that needs a new obligation atom must expand the language and rerun the quotient search.

## Method-promotion note from v164

- `proof_carrying_disaster_antichain_minimizer_v1` is promoted as a paper-candidate method object.
- Reason:
  - it upgrades the disaster minimizer from equality quotienting to dominance pruning,
  - it exposes the downward-coverage invariant as the main theorem shape,
  - and it preserves the minimal guard cover while reducing the current proof frontier from `13` quotient classes to `10` antichain representatives.
- Scope limit:
  - the obligation extractor is still a finite symbolic model,
  - new obligation atoms still require a new corpus/proof cycle,
  - and the result is not yet a full end-to-end proof that every implementation-level bug maps into the obligation language.

## Breakthrough note from v165

- `private_obligation_guard_optimality_certificate_v1` is promoted as the current strongest paper-candidate result.
- Reason:
  - it removes exhaustive set-cover search from the current guard-cover optimality claim,
  - it supplies one local private-obligation witness per selected guard,
  - and the Lean bridge proves why a private required obligation forces guard membership in every valid cover.
- Practical consequence:
  - the current `7`-guard disaster cover is not just search-minimal; it is certificate-minimal.
- Compact theorem:
  - `proofCarryingDisasterMinimizer_sound_optimal` now packages the full minimizer result into one checked theorem surface.
- Scope limit:
  - this private-witness method is complete for the current bounded corpus,
  - but future corpora with no private atoms will require a mixed lower-bound certificate or bounded residual search.

## Method-promotion note from v182

- `fragment_sensitive_qe_certificate_menu_v1` is promoted as a Tau/FIRE optimization method object, not as a complete QE replacement.
- Reason:
  - the Bernstein fast path is exact-rational and proof-carrying, and it certifies all positive examples in the core bounded corpus by 8 subdivisions,
  - DLMF/Chebyshev stress cases reveal a second exact certificate family that Bernstein equal subdivision does not handle well,
  - and the combined result turns "try to make QE faster" into a fragment-sensitive compiler menu with explicit `UNKNOWN` fallbacks.
- Practical consequence:
  - Tau can plausibly skip expensive QE on recognized polynomial sign fragments while preserving fail-closed behavior.
  - the reusable Lean module `Proofs.TauFragmentCertificates` now makes the theorem surface citeable outside the experiment packet.
  - `menu_checker.py` makes the same menu replayable as an exact-rational JSON checker suitable for a future tutorial or Tau patch experiment.
  - the full-corpus menu replay accepts `48/48` positive obligations and leaves all `3/3` explicit negative controls `UNKNOWN`.
- Scope limit:
  - both local Lean proof packets now check, with Aristotle still queued as an independent review lane,
  - and neither result proves global Tau quantifier elimination is optimized for arbitrary formulas.

## Integration note from v182

- `tau_checkout_fragment_certificate_sidecar_v1` is promoted as an integration
  artifact, not as a core Tau solver patch.
- Reason:
  - it moves the exact-rational certificate menu from an experiment-only script
    into the local Tau checkout,
  - it gives a Tau-facing demo spec and documentation,
  - and it has a focused replay test proving the sidecar accepts only the three
    intended demo obligations while leaving the two controls `UNKNOWN`.
- Scope limit:
  - Tau's current core syntax and C++ QE pipeline do not expose this real
    polynomial certificate surface directly,
  - so the correct near-term integration is host extraction plus fail-closed
    fallback, not a claimed universal Tau QE acceleration.

## Method note from v184

- `legendre_turan_reference_adapter_v1` is promoted as a dispatch-method object,
  not as a new general theorem.
- Reason:
  - it shows the DLMF/reference-adapter loop can classify neighboring
    orthogonal-polynomial families by certificate profile,
  - shifted Legendre envelopes and Turan differences certify `64/64` positives
    for `1 <= n <= 32` with `0/4` negative-control accepts,
  - and the worst accepted cases need only `16` equal Bernstein subintervals.
- Practical consequence:
  - the certificate menu should not treat all special-function-looking
    polynomials as Chebyshev-like hard cases.
  - smooth Legendre/Turan-style obligations can try generic Bernstein first,
    while Chebyshev envelopes should use the exact special recognizer early.
- Scope limit:
  - this is bounded evidence, not a theorem for all `n`,
  - and local mathlib does not currently provide the general Legendre theorem
    surface needed for a direct proof-rule promotion.

## Method note from v185

- `gegenbauer_reference_adapter_v1` is promoted as a dispatch-method object, not
  as a direct theorem rule.
- Reason:
  - it widens v184 from Legendre to normalized Gegenbauer profiles over five
    rational `lambda` values,
  - it certifies `240/240` positive obligations for `1 <= n <= 24`,
  - and it accepts `0/4` negative controls.
- Practical consequence:
  - the current evidence says "try Bernstein first" is a good default for
    tested normalized Legendre/Gegenbauer envelope and Turan profiles.
  - Chebyshev-specific recognition remains justified because Chebyshev was the
    bounded outlier.
- Scope limit:
  - the result is bounded to the tested `lambda` values and `n <= 24`,
  - and generic Bernstein certificate soundness, not a direct Gegenbauer theorem,
    is still the formal acceptance route.

## Falsification note from v186

- `asymmetric_jacobi_turan_endpoint_falsifier_v1` is promoted as negative
  knowledge.
- Reason:
  - it falsifies the tempting extension from Legendre/Gegenbauer Turan
    friendliness to asymmetric endpoint-normalized Jacobi Turan candidates,
  - it finds exact endpoint counterexamples, not just failed certificates,
  - and it preserves a positive sub-result: asymmetric Jacobi envelopes certify
    `154/154` with max `8` Bernstein pieces.
- Practical consequence:
  - the certificate menu can try Bernstein first for Jacobi envelopes,
  - but it must not add an asymmetric Jacobi Turan proof rule under this
    endpoint normalization.
- Scope limit:
  - this falsifies the tested normalization and parameter grid,
  - not every possible Jacobi Turan theorem.

## Method note from v187

- `certificate_carrying_arbitrage_graph_v1` is promoted as a high-ROI theorem
  target, not as a finished runtime router.
- Reason:
  - it connects exact integer CPMM route semantics to a classical potential
    certificate shape,
  - it rejects `80/80` injected arbitrage graphs in the bounded corpus,
  - and it safely prunes `522/1600` bounded no-arb route candidates with `0`
    false prunes.
- Practical consequence:
  - ZenoDEX can pursue proof-backed route pruning and treasury arbitrage
    admission without trusting floating-point prices or heuristic graph search.
  - the same object can become a dual guard: opportunity certificate first,
    budget-safety guard second.
- Proof promotion:
  - `lean-mathlib/Proofs/RouteIntervalGraph.lean` closes the CPMM integer
    floor interval theorem and the abstract potential-ratio route-product
    theorem with no placeholders.
- Scope limit:
  - the Lean packet proves the reusable abstract certificate shape,
  - not production route optimality or live execution under reserve mutation.

## Method note from v188

- `gasper_cone_jacobi_turan_oriented_recognizer_v1` is promoted as a
  high-value dispatch-method object, not as a finished general theorem.
- Reason:
  - it explains the v186 asymmetric Jacobi Turan failures as wrong endpoint /
    wrong parameter-cone cases,
  - it certifies `810/810` in-cone positive rows and `378/378` oriented rows
    in the bounded exact-rational corpus,
  - it endpoint-falsifies `648/648` outside-cone rows, including `324/324`
    deliberate strict wrong-anchor cases,
  - and it accepts `0/4` negative controls.
- Practical consequence:
  - the Tau/FIRE certificate menu can treat Jacobi Turan as fragment-sensitive:
    recognize the cone, orient the endpoint, emit a Bernstein certificate only
    inside that cone, and avoid wasting QE/subdivision on endpoint-false cases.
  - this is the clearest current example of DLMF/reference guidance turning a
    failed special-function conjecture into a sharper recognizer.
- Proof target:
  - formalize the mirror equivalence from left-normalized `(alpha,beta)` on
    `[0,1]` to right-normalized `(beta,alpha)` under `x -> 1-x`.
  - keep Gasper's full cone theorem as an external theorem target until there
    is a local Lean proof or trusted theorem import.
- Scope limit:
  - the experiment proves bounded exact certificates and exact endpoint
    falsifiers,
  - not the unbounded Jacobi Turan theorem.

## Method note from v189

- `jacobi_turan_endpoint_obstruction_formula_v1` is promoted as a proof-shaped
  obstruction lemma.
- Reason:
  - it converts v188's endpoint falsifiers into a closed formula,
  - it checks `10368/10368` exact-rational rows with `0` formula mismatches,
  - and the recurrence-defined endpoint ratio bridge plus sign consequences are
    now Lean-checked for both endpoint orientations.
- Practical consequence:
  - the recognizer can reject strict wrong-cone endpoint choices before running
    Bernstein subdivision or Tau QE.
  - this is stronger than a bounded counterexample table because the sign source
    is now explicit: `beta - alpha` or `alpha - beta`.
- Scope limit:
  - the proof is a recurrence-defined endpoint-ratio skeleton plus
    cone/wrong-cone sign theorem,
  - not a proof of full Jacobi interval positivity or the full Gasper theorem.

## Method note from v196

- `derivative_bernstein_monotonicity_certificate_v1` is promoted as a useful
  Tau optimization target for monotonicity obligations, not as a new generic
  sign prover.
- Reason:
  - it accepts `27/29` true monotone polynomial cases in the bounded exact
    corpus,
  - accepts `0/4` negative controls,
  - and replaces accepted two-variable order obligations with one derivative
    sign certificate.
- Practical consequence:
  - the local Lean bridge now packages Mathlib's
    `monotoneOn_of_deriv_nonneg` with the interval-cover Bernstein certificate
    surface as `TauFragmentCertificates.derivativeCertificate_monotoneOn`.
  - the demo checker and Tau checkout sidecar now exist and are fail-closed;
    the remaining improvement is benchmarking against extractor-shaped
    obligations.
- Negative knowledge:
  - endpoint-based sign nonnegativity did not improve: `27/27` derivative
    accepts were also direct Bernstein sign accepts on the same pieces after
    shifting the left endpoint nonnegative.
  - derivative Bernstein should be sold as a monotonicity/QE-fragment
    reduction, not as a replacement for the existing sign menu.
  - non-dyadic square-derivative roots show that equal dyadic subdivision is
    incomplete, so adaptive root/critical-point splitting is the next
    certificate-family frontier.
