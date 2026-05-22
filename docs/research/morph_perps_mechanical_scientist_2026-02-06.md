# Morph Mechanical Scientist on Perps: Deep Insights (2026-02-06)

This report captures the deepest operational and algorithmic insights from iterative Morph scientist runs on perps domains.

## Scope

Domains exercised:
- `perp_oracle_manipulation`
- `perp_oracle_manipulation_reward_subsidy`
- `perp_funding_rate_gaming`
- `perp_settlement_bounty_farming`

Primary objective:
- sustained measurable lift (matched A/B with portals enabled vs disabled)
- then durable long-campaign improvement behavior (archive growth across campaigns and difficulty levels)

## Core Results

### 1) Sustained lift achieved on reward-subsidy domain

Artifact:
- `runs/mech_sci_iter/postfix_v2/reward_ab_sweep_manual.json`

10-seed aggregate:
- `has_lift_rate = 1.0` (10/10)
- `avg_seconds_reduction = 0.02413690673232243`
- `with_portals.avg_seconds = 0.1778269872122918`
- `without_portals.avg_seconds = 0.20196389394461423`
- `solved_rate_delta = 0.0` (quality preserved, speed improved)

Interpretation:
- Portal guidance is consistently useful in this domain.
- The speedup is robust while solved quality is unchanged.

### 2) Long campaigns now sustain archive growth

Artifacts:
- `runs/mech_sci_iter/improve/reward_long/improvement_log.jsonl`
- `runs/mech_sci_iter/improve/reward_long_partial_summary.json`

Observed over 6 completed campaigns:
- `campaigns_completed = 6`
- `total_archived_added = 42`
- `avg_archived_per_campaign = 7.0`
- `min_archived_per_campaign = 7`
- difficulty progression: `[4,8] -> [8,20] -> [16,50]`
- each campaign retained `best_solved=40`, `best_avg_expanded=1.0`

Interpretation:
- Workflow no longer stalls early from candidate exhaustion.
- Promotions and archive harvesting remain stable under increasing difficulty.

### 3) Bounty domain moved from zero-signal to solvable, but not yet positive-lift

Artifacts:
- pre-fix: `runs/mech_sci_iter/bounty_v1/ab_sweep.json`
- post-fix: `runs/mech_sci_iter/bounty_v2/ab_sweep.json`

Post-fix 10-seed aggregate:
- `solved_rate = 1.0` both arms
- `has_lift_rate = 0.4`
- `avg_seconds_reduction = -0.0006430848129336184` (portals slightly slower)

Interpretation:
- Domain is now operational (solves and holdout traces exist).
- Portal policy for bounty still needs retuning to produce positive sustained lift.

## Highest-Impact Technical Insights

### A) Candidate diversity collapse can mimic "hardness"

Symptom:
- campaigns ended with `no_new_candidates`
- improvement loop hit `archive_stalled:*`

Root causes found:
1. Composer filter regex bug rejected almost all non-`Try*` composed perps candidates.
2. Generation budget was tied directly to evaluation budget, shrinking exploration breadth per round.

Fixes that mattered:
- regex boundary corrected in perps composed filter (`\b...\b` intended literal word boundary in regex source string)
- decouple generation pool from evaluation cap (`generation_pool_cap = bounded multiple of eval cap`)
- ensure each round includes non-composed template anchors + ranked exploratory candidates

Effect:
- perps campaigns stopped prematurely much less often
- long-loop archive accumulation became stable and repeatable

### B) Checker invariants must match mutable tactic surfaces

Critical bounty finding:
- Domain exposed tactics `IncBountyMin`/`DecBountyMin`, but checker enforced `bounty_min_quote` as static between sigma0 and witness.
- This made any strategy using bounty mutation structurally fail despite valid witness math.

Fix:
- remove `bounty_min_quote` from static-fields lock in `check` and `check2` for bounty domain.

Effect:
- domain moved from holdout-zero to holdout-solvable behavior.

Design rule:
- If a field is intentionally mutated by tactics, do not lock it as static in checker invariants.
- Keep static locks only for true global bounds and immutable policy parameters.

### C) Depth budgets dominate strategy realizability

Finding:
- Long `repeat(IncBountyMin, N) ; TrySolve` sequences can be unreachable under campaign depth limits.

Action:
- switched bounty templates toward depth-aware short increment chains with early `TrySolve` branches.

Rule:
- Template depth should be calibrated against campaign `max_depth`; otherwise strategy quality is overestimated offline and under-realized online.

## Practical Workflow That Worked

1. Use quick 1-seed matched diagnostics across all perps domains to classify domain state:
   - positive lift
   - neutral
   - negative
   - zero-signal (no holdout solves)
2. Focus innovation budget on one stable positive-lift domain as control (`reward_subsidy`).
3. Fix structural blockers before tuning portals:
   - candidate generation bugs
   - gating collapse
   - checker/tactic mismatches
4. Validate with multi-seed A/B (>=10 seeds for claims of sustained lift).
5. Only then run long `scientist improve` campaigns and track:
   - archive growth per campaign
   - difficulty progression
   - promotion stability

## Open Problems

- `perp_oracle_manipulation`: noisy/near-neutral lift under current settings.
- `perp_funding_rate_gaming`: slight negative timing delta in quick diagnostics.
- `perp_settlement_bounty_farming`: now solvable, but portal guidance not yet net-positive on timing.

## Signature

- `sig: 0xmech_sci_perps_2026_02_06 @codex`


## Continuation Addendum (2026-02-06, later pass)

### 4) Bounty domain unlocked into sustained long-campaign growth

Artifacts:
- `runs/mech_sci_iter/bounty_v3/ab_sweep_manual.json`
- `runs/mech_sci_iter/improve/bounty_long/improvement_log.jsonl`
- `runs/mech_sci_iter/bounty_summary_from_skill.json`

Observed:
- Matched 10-seed A/B for bounty now has full solved coverage on both arms (`solved_rate=1.0`) and improved per-seed lift incidence (`has_lift_rate=0.6`), but still fails default sustained timing-lift gate due small negative mean seconds delta.
- Long improvement loop on bounty is strongly positive:
  - `campaigns_completed=5`
  - `total_archived_added=59`
  - `avg_archived_per_campaign=11.8`
  - `min_archived_per_campaign=11`
  - difficulty progression reached `[16,50]`

Interpretation:
- Portal-guided runtime speedup is still not sustained for bounty under current portal policy.
- Mechanism innovation and scientist-loop durability are now strong in bounty through archive/promotion throughput.

### 5) Cross-domain performance insight: portal overhead vs search benefit

When average expanded nodes are already minimal (`~1.0`), portal scoring overhead can dominate and make with-portals slightly slower even with equal quality.

Design implication:
- For near-trivial solve regimes, optimize for either:
  - harder instance generation where portal guidance can reduce search work, or
  - cheaper portal computation and/or selective portal use.

### 6) Secondary engineering improvement

Added cached state JSON parsing for perps portal scoring in `external/Morph/morph/scientist_domain.py` using LRU cache to reduce repeated decode overhead. This improves runtime efficiency while preserving semantics.

## Continuation Addendum 2 (2026-02-06, automation + sustained loop)

### 7) Perps self-improvement loop automated end-to-end

New orchestrator:
- `tools/perps_scientist_self_improve_loop.py`

What it does:
1. Runs `scientist ab-sweep` per domain.
2. Applies sustained-lift gates (`has_lift_rate >= 0.8`, `solved_rate_delta >= 0` by default).
3. Runs long `scientist improve` only for gated domains.
4. Emits one machine-readable summary JSON.

Smoke validation artifact:
- `runs/mech_sci_iter/loop_smoke_summary.json`

### 8) Multi-domain gated loop result

Artifact:
- `runs/mech_sci_iter/loop_summary_r1.json`

Domains evaluated:
- `perp_oracle_manipulation_reward_subsidy`
- `perp_settlement_bounty_farming`
- `perp_funding_rate_gaming`

Gate outcomes:
- `reward_subsidy`: **passed** (`has_lift_rate=1.0`, `solved_rate_delta=0.0`)
- `bounty`: not selected (`has_lift_rate=0.4`, `solved_rate_delta=0.0`)
- `funding`: not selected (`has_lift_rate=0.4`, `solved_rate_delta=0.0`)

Key implication:
- Domain gating prevents spending long-campaign budget on neutral/negative-lift domains.

### 9) Sustained long-campaign performance (selected domain)

Artifacts:
- `runs/mech_sci_iter/reward_summary_v4.json`
- `runs/mech_sci_iter/improve/reward_long_v2/improvement_log.jsonl`
- `runs/mech_sci_iter/loop_improve_r1/perp_oracle_manipulation_reward_subsidy/improvement_log.jsonl`

Observed (latest long pass):
- A/B (10 seeds): `has_lift_rate=1.0`, `avg_seconds_reduction=0.02709720097927857`, solved non-regression.
- Improve (8 campaigns): `total_archived_added=32`, `min_archived_per_campaign=4`, difficulty progressed to `[28,100]`.

Interpretation:
- The workflow now demonstrates both sustained portal lift and sustained archive-growth durability under increasing difficulty.

## Continuation Addendum 3 (2026-02-06, bounded long loop + signal triage)

### 10) Fresh A/B status after workflow retuning (`r5`)

Artifacts:
- `runs/mech_sci_iter/funding_summary_r5.json`
- `runs/mech_sci_iter/bounty_summary_r5.json`
- `runs/mech_sci_iter/loop_ab_r5/perp_funding_rate_gaming/ab_sweep.json`
- `runs/mech_sci_iter/loop_ab_r5/perp_settlement_bounty_farming/ab_sweep.json`

Observed:
- Funding (`perp_funding_rate_gaming`):
  - `has_lift_rate=0.0`
  - `avg_seconds_reduction=-5.852750021707225e-05`
  - solved-rate non-regression holds, but sustained-lift gate fails.
- Bounty (`perp_settlement_bounty_farming`):
  - `has_lift_rate=0.6`
  - `avg_seconds_reduction=0.0003735699437735697`
  - solved-rate non-regression holds, but sustained-lift gate still fails (`< 0.8`).

Interpretation:
- Funding remains low-signal/no-lift under current portal policy.
- Bounty is improving but still below sustained-lift threshold; treat as exploratory, not promotion-grade.

### 11) Bounded long-campaign loop stays durable on reward domain (`r5b`)

Artifacts:
- `runs/mech_sci_iter/loop_improve_r5b/improvement_report.json`
- `runs/mech_sci_iter/loop_improve_r5b/improvement_log.jsonl`
- `runs/mech_sci_iter/reward_improve_summary_r5b.json`

Configuration highlights:
- explicit global/campaign wall limits (`max_wall_seconds=240`, `max_wall_seconds_per_campaign=45`)
- 6 campaigns, increasing difficulty schedule retained

Observed:
- `campaigns_completed=6`
- `total_archived_added=12`
- `min_archived_per_campaign=2`
- `avg_archived_per_campaign=2.0`
- `total_promoted=12`
- `stopped_reason=max_campaigns_reached`
- total wall time ~147.5s

Interpretation:
- Even with tighter budgets, reward domain retains non-zero archive growth every campaign and clean difficulty progression.
- Bounded loops are practical for continuous self-improvement without multi-hour runs.

### 12) Operational decision rule (updated)

Use three bands for perps scientist domains:
- **Promotion-grade**: sustained gate pass (`has_lift_rate >= 0.8` + solved non-regression) + durable long-campaign growth.
- **Exploratory**: positive or mixed lift but below sustained threshold (`0 < has_lift_rate < 0.8`).
- **Hold/diagnose**: no-lift (`has_lift_rate == 0`) or clear negative timing deltas.

Current classification:
- Promotion-grade: `perp_oracle_manipulation_reward_subsidy`
- Exploratory: `perp_settlement_bounty_farming`
- Hold/diagnose: `perp_funding_rate_gaming`

## Continuation Addendum 4 (2026-02-06, long `r8` pass + code promotion)

### 13) New long loop (`r8`) confirms sustained lift and promotion readiness

Artifacts:
- `runs/mech_sci_iter/loop_summary_r8.json`
- `runs/mech_sci_iter/loop_ab_r8/perp_oracle_manipulation_reward_subsidy/ab_sweep.json`
- `runs/mech_sci_iter/loop_improve_r8/perp_oracle_manipulation_reward_subsidy/improvement_log.jsonl`

Observed (`perp_oracle_manipulation_reward_subsidy`):
- A/B (10 seeds):
  - `has_lift_rate=1.0`
  - `avg_seconds_reduction=0.026138451745904002`
  - solved-rate non-regression (`solved_rate_delta=0.0`)
- Improve (8 campaigns):
  - `campaigns_completed=8`
  - `total_archived_added=32`
  - `min_archived_per_campaign=4`
  - `avg_archived_per_campaign=4.0`
  - `total_promoted=32`
  - `meets_long_gate=true`

Gate result:
- `code_update_candidates[0].status = ready_for_implementation`

Cross-domain status in same run:
- `perp_settlement_bounty_farming`: `has_lift_rate=0.5` (exploratory)
- `perp_oracle_manipulation`: `has_lift_rate=0.3` (exploratory)
- `perp_funding_rate_gaming`: `has_lift_rate=0.2` with slight negative mean time delta (hold/diagnose)

### 14) Code promotion updates applied from validated lift themes

A) Canonical perps adapter entrypoint hardening
- Change: `src/integration/perps/engine.py` is now a strict re-export shim to `src/integration/perp_engine.py`.
- Why: remove duplicate-engine drift risk where package users could hit weaker semantics than the canonical adapter.
- Regression lock: `tests/integration/test_perps_engine_alias.py` asserts symbol identity for config/types/functions.

B) Settlement oracle-usable guard hardening (with bootstrap allowance)
- Changes:
  - `src/core/perp_v2/math.py`: added `is_settle_oracle_usable(...)`.
  - `src/core/perp_v2/guards.py`: `guard_settle_epoch` now fail-closes on malformed/stale oracle snapshots.
  - Deterministic bootstrap exception retained: first settle is allowed only when oracle is unseen, index is zero, and position is flat.
- Why: aligns with reward-subsidy anti-manipulation posture by preventing settlement against stale/invalid oracle state while preserving safe market bootstrap.
- Regression locks:
  - `tests/core/test_perp_v2/test_math.py` (new oracle-usable tests)
  - `tests/core/test_perp_v2/test_engine.py` (stale/not-seen reject + bootstrap-allowed test)

### 15) Verified test outcomes after promotion patches

Executed:
- `pytest -q tests/core/test_perp_v2/test_math.py tests/core/test_perp_v2/test_engine.py tests/integration/test_perps_engine_alias.py tests/integration/test_perp_engine.py`
- `pytest -q tests/core/test_perp_v2`

Results:
- Focused run: `145 passed`
- Full `perp_v2` suite: `183 passed, 3 skipped`

### 16) Updated operational insight

When a domain is `promotion-grade`, promotion should not stop at “candidate JSON”.
Required next step is explicit runtime hardening or architecture de-risking patches (plus regression tests), then re-run evidence gates.

sig: 0xmech_sci_perps_2026_02_06_add4 @codex

## Continuation Addendum 5 (2026-02-06, CPU scaling benchmark)

### 17) Parallel A/B launcher + CPU scaling benchmark

New utility:
- `tools/perps_scientist_parallel_benchmark.py`

Benchmark artifact:
- `runs/mech_sci_iter/parallel_bench/cpu_scale_r1_summary.json`

Workload (identical across worker counts):
- domains: reward-subsidy, bounty, funding, oracle-manipulation
- seeds per domain: `2`
- A/B budget: `train=12`, `holdout=24`, `max_rounds=2`, `max_eval_instances=128`

Measured wall-clock:
- `workers=1`: `324.2267s` (baseline)
- `workers=2`: `178.3154s` (`1.818x` speedup)
- `workers=4`: `143.9250s` (`2.253x` speedup)

Interpretation:
- More CPU delivers substantial throughput gains for multi-domain/multi-seed sweeps.
- Diminishing returns appear beyond 2 workers on this mixed-domain workload because long-tail domains (`perp_oracle_manipulation`, reward-subsidy) dominate the critical path.
- Recommendation: default `workers=2..4` for local productive runs; scale seeds/campaign count rather than chasing very high worker counts for the same 4-domain set.

### 18) Practical longest productive run guidance (current evidence)

Given observed stability and throughput, the best long productive profile remains:
- promotion-grade domain only (`perp_oracle_manipulation_reward_subsidy`),
- `8` campaigns per improve pass, with non-zero archive growth gate,
- and parallelized A/B triage before improve.

sig: 0xmech_sci_perps_2026_02_06_add5 @codex

## Continuation Addendum 6 (2026-02-06, expanded perps domains + stability check)

### 19) Mechanical-scientist domain expansion (Morph registry + CLI)

New scientist domains integrated:
- `perp_oracle_manipulation_lp`
- `perp_collateral_depeg`

Code updates:
- `external/Morph/morph/scientist_domain.py`
  - added adapters, seed-state builders, and portal scores for both domains.
- `external/Morph/morph/scientist_generator.py`
  - added per-domain hypothesis generators for both domains.
- `external/Morph/morph/cli.py`
  - added both ids to `_SCIENTIST_DOMAIN_CHOICES`.
- `external/Morph/tests/*`
  - updated domain-choice and adapter/generator coverage.
- `tools/perps_scientist_self_improve_loop.py`
  - default domain set extended to include both new perps domains.

Validation:
- `python3 -m py_compile` for modified Morph + tooling files.
- `PYTHONPATH=external/Morph pytest -q external/Morph/tests/test_scientist_generator.py external/Morph/tests/test_scientist_domain_adapters.py`
  - `16 passed, 2 skipped`
- `PYTHONPATH=external/Morph pytest -q external/Morph/tests/test_cli.py -k scientist_domain_choices_include_perps`
  - `1 passed`

### 20) Cross-seed A/B evidence on new domains

Artifacts:
- `runs/mech_sci_iter/loop_ab_r9/perp_collateral_depeg/ab_sweep.json`
- `runs/mech_sci_iter/loop_ab_r9_confirm/perp_collateral_depeg/ab_sweep.json`
- `runs/mech_sci_iter/loop_ab_r9_confirm/perp_oracle_manipulation_lp/ab_sweep.json`
- `runs/mech_sci_iter/loop_ab_r10/perp_oracle_manipulation_lp/ab_sweep.json`
- `runs/mech_sci_iter/loop_summary_r9_smoke.json`

Observed:
- `perp_collateral_depeg`:
  - 6-seed confirm: `has_lift_rate=0.0`, slight negative mean timing delta.
  - classification: **hold/diagnose**.
- `perp_oracle_manipulation_lp`:
  - 6-seed confirm: `has_lift_rate=0.8333333333333334`, positive mean timing delta.
  - 10-seed confirm: `has_lift_rate=0.6`, positive mean timing delta but below sustained gate.
  - classification: **exploratory** (not promotion-grade yet).

### 21) Deepest operational insights from this expansion

1. Low-seed lift can be a false positive:
   - a 2-seed smoke pass showed `has_lift_rate=1.0` for LP, but 10-seed confirmation dropped to `0.6`.
   - gate promotion only after >=10 seeds.

2. Domain utility depends on portal leverage:
   - depeg domain solves trivially with current strategy budget; portals produce near-zero expansion delta, so timing noise dominates.
   - this domain is useful as a safety refuter/checker domain, not currently as a lift domain.

3. Expanded-domain loops should remain gated:
   - keep reward-subsidy as primary promotion lane.
   - run LP/depeg in exploratory triage lanes, then only promote if sustained gate + long-campaign durability both pass.

sig: 0xmech_sci_perps_2026_02_06_add6 @codex

## Continuation Addendum 7 (2026-02-06, promotion-lane long pass + runtime hardening)

### 22) Fresh sustained A/B confirmation on promotion lane (`r12b`)

Artifact:
- `runs/mech_sci_iter/loop_ab_r12b/perp_oracle_manipulation_reward_subsidy/ab_sweep.json`

Observed (`perp_oracle_manipulation_reward_subsidy`, 10 seeds):
- `has_lift_rate=1.0` (10/10)
- `avg_seconds_reduction=0.02638658151195159`
- `solved_rate_delta=0.0`

Interpretation:
- Promotion lane remains robust under fresh seeds and bounded campaign settings.
- Runtime speed lift remains consistent and non-regressing on solved quality.

### 23) Bounded long-campaign pass remains durable (`r12b`)

Artifact:
- `runs/mech_sci_iter/loop_improve_r12b/improvement_log.jsonl`

Observed:
- `campaigns_completed=8`
- `total_archived_added=16`
- `min_archived_per_campaign=2`
- `avg_archived_per_campaign=2.0`
- `total_promoted=16`
- difficulty progressed and sustained at `[28,100]`
- loop summary: `stopped_reason=max_campaigns_reached`, total wall ~`199.76s`

Interpretation:
- Long-run self-improvement remains stable with non-zero archive growth every campaign.
- Bounded campaign budgets are sufficient for sustained iterative gains on the promotion-grade domain.

### 24) Runtime hardening promoted from exploratory safety signal

Changes:
- `src/integration/perp_engine.py`
  - `_apply_isolated_market_params` now rejects `depeg_buffer_bps <= 0`:
    - error: `"invalid params: require depeg_buffer_bps > 0"`
- `tests/integration/test_perp_engine.py`
  - added regression in `test_set_market_params_mid_epoch_guard_and_margin_safety` asserting depeg-buffer fail-close.
  - existing stale-oracle funding guard regression retained (`test_apply_funding_auto_rejects_stale_oracle`).

Validation:
- `pytest -q tests/integration/test_perp_engine.py -k 'funding_auto or set_market_params_mid_epoch_guard'`
  - `5 passed`

Why this promotion:
- Collateral/depeg exploratory domains continue to show low lift but high safety signal.
- Converting that signal into fail-closed parameter constraints is a direct code-level ROI path even when portal lift is weak.

### 25) LP domain tactic-generation experiment outcome

Experiment:
- added richer LP mutation tactics in domain + generator.
- result: search cost rose sharply and practical campaign throughput degraded under bounded budgets.
- reverted LP tactic expansion; retained stable `TrySolve` profile.

Operational insight:
- For LP exploratory lanes, throughput-dominant simple tactic sets currently outperform richer tactic grammars on end-to-end ROI.
- Keep LP as exploratory (cross-seed variable lift) until a bounded non-trivial grammar beats baseline on 10-seed sustained gate.

sig: 0xmech_sci_perps_2026_02_06_add7 @codex

## Continuation Addendum 8 (2026-02-07, reward-lane durability + zero-price hardening)

### 26) Fresh 10-seed sustained A/B on reward lane (`r13_reward_focus`)

Artifacts:
- `runs/mech_sci_iter/loop_ab_r13_reward/perp_oracle_manipulation_reward_subsidy/ab_sweep.json`
- `runs/mech_sci_iter/loop_reward_summary_r13.json`

Observed (`perp_oracle_manipulation_reward_subsidy`, 10 seeds):
- `has_lift_rate=1.0` (10/10)
- `avg_seconds_reduction=0.030217092218178254`
- `solved_rate_delta=0.0`

Interpretation:
- Promotion lane remains stable under fresh seed block.
- Portal guidance keeps producing timing lift without solved-quality regression.

### 27) Longer promotion campaign pass (`r13_reward_focus`)

Artifacts:
- `runs/mech_sci_iter/loop_improve_r13_reward/improvement_log.jsonl`
- `runs/mech_sci_iter/loop_reward_summary_r13.json`

Observed:
- `campaigns_completed=12`
- `total_archived_added=36`
- `min_archived_per_campaign=3`
- `avg_archived_per_campaign=3.0`
- `total_promoted=36`
- `stopped_reason=max_campaigns_reached`
- difficulty progression held through:
  - `[4,8] -> [8,20] -> [16,50] -> [28,100] -> [50,200] -> [100,400]`

Interpretation:
- Long-loop self-improvement remains productive at higher campaign counts.
- Archive throughput stayed strictly positive across all campaigns (no stall episodes).

### 28) Code promotion from sustained lane: reject zero clearing prices

Changes:
- `src/integration/perp_engine.py`
  - `publish_clearing_price` now fail-closes when `price_e8 <= 0` for:
    - isolated markets
    - clearinghouse 2p
    - clearinghouse 3p transfer
  - error: `"publish_clearing_price requires price_e8 > 0"`

Tests:
- `tests/integration/test_perp_engine.py`
  - added `test_publish_clearing_price_rejects_zero_price`
- `tests/integration/test_perp_engine_clearinghouse_2p.py`
  - added `test_publish_price_2p_rejects_zero_price`
- `tests/integration/test_perp_engine_clearinghouse_3p_transfer.py`
  - added `test_publish_price_3p_rejects_zero_price`

Validation:
- `pytest -q tests/integration/test_perp_engine.py tests/integration/test_perp_engine_clearinghouse_2p.py tests/integration/test_perp_engine_clearinghouse_3p_transfer.py -k 'zero_price or rejects_zero_price'`
  - `3 passed`
- `pytest -q tests/integration/test_perp_engine.py tests/integration/test_perp_engine_clearinghouse_2p.py tests/integration/test_perp_engine_clearinghouse_3p_transfer.py`
  - `27 passed`

Why this promotion:
- Mechanical-scientist reward-lane runs continue to emphasize oracle-manipulation pathways.
- Rejecting zero clearing prices removes a malformed-price edge case across all perps publication paths and keeps settlement/funding surfaces strictly positive-price anchored.

sig: 0xmech_sci_perps_2026_02_07_add8 @codex
