---
title: Verifier-Preserving Learned Candidate Ordering for UPBA v2 Settlement Search
type: research-paper
status: draft
date: 2026-05-18
---

# Verifier-Preserving Learned Candidate Ordering for UPBA v2 Settlement Search

ZenoDEX Research Paper, draft v0.4
Date: May 18, 2026

## Abstract

ZenoEnergy v0 studies whether a tiny learned energy scorer can reduce the cost
of searching UPBA v2 partial-fill exact-in settlement candidates while preserving
deterministic verification. The scorer is advisory: it ranks candidates before
the verifier checks them, and it has no authority over settlement validity,
ledger state, state roots, or replay.

The experiment trains a 97-parameter CPU-only linear energy ranker on synthetic,
verifier-labeled UPBA v2 candidate data. On a held-out synthetic corpus with
1,983 winner-bearing batches and about 20 candidates per batch, learned ordering
placed the exact verifier winner first in 98.3% of batches, in the top 5 in
100.0%, and in the top 10 in 100.0% with the current gap-weighted checkpoint.
The measured mean position of the winner fell from 19.99 under exhaustive order
to 1.017 under gap-weighted learned order. The deterministic verifier accepted
zero invalid candidates.

This is optimization research: the optimized quantity is verifier search work
over a finite candidate set. Correctness comes from deterministic verification,
certified candidate generation, dominance-pruning contracts, and deterministic
fallback.

The current production-adjacent path is an evidence bundle rather than a release
claim. The bundle assembles source-manifested and coverage-profiled UPBA and
AutoTrader real replay reports, then runs a fail-closed advisory ranking
promotion gate. The gate currently blocks promotion because real replay coverage
is still missing.

## 1. Research Classification

This work is a learning-to-rank optimization for a bounded combinatorial search
problem.

For a settlement context `x`, let:

```text
C(x) = finite candidate set
V_x(c) = deterministic verifier result for candidate c
J_x(c) = deterministic objective, ordered by volume then surplus
```

The exhaustive winner is:

```text
c*(x) := argmax { J_x(c) | c in C(x) ∧ V_x(c) = accept }
```

ZenoEnergy learns a scoring function:

```text
E_theta(x, c) -> scalar
```

Lower energy means earlier verifier priority. The optimization target is:

```text
minimize E_x[position_{sort(E_theta)}(c*(x))]
```

The settlement rule remains:

```text
accepted(c) := V_x(c)
```

The model optimizes order. The verifier controls validity.

## 2. Safety Boundary

The core safety rule is:

```text
LowEnergy_theta(x, c) ∧ V_x(c) = reject -> SettlementRejected
```

The implementation enforces this boundary by keeping dependencies one-way:

```text
src.energy -> src.core.uniform_batch_clearing
src.core.uniform_batch_clearing -/-> src.energy
```

Energy code may import verifier code for offline labels, evaluation, and safety
tests. Consensus-critical verifier code does not import `src.energy`.

The scorer may:

- compute advisory features;
- rank candidates;
- reduce the expected position of high-quality candidates;
- feed benchmark and research tooling.

The scorer may not:

- authorize settlement;
- replace deterministic certificate verification;
- mutate ledger state;
- enter state roots;
- change validity predicates;
- use private live order data for training.

## 3. Reasoning-Energy Framing

Logical Intelligence's EBRM article frames reasoning as adaptive planning over
states, constraints, objectives, and trajectories. Its most useful lesson for
ZenoEnergy is that an energy score should apply before the final answer and help
identify which constraint is broken.

ZenoEnergy maps that idea to UPBA v2 candidate search:

```text
reasoning state  -> partial or complete settlement candidate
constraint       -> verifier obligation
trajectory       -> candidate generation, pruning, and ranking path
energy           -> advisory priority plus failure localization
```

The current implementation keeps the final settlement authority in the verifier,
then uses energy to prioritize and explain candidates. The hand scorer therefore
returns both a scalar energy and a named component breakdown.

Reference: <https://logicalintelligence.com/blog/energy-based-models-for-reasoning>

## 4. Candidate Generation and Formal Contracts

Synthetic candidate generation is useful for research when generated candidates
are verifier-labeled and treated as a bounded experiment. A stronger mathematical
claim needs exact generation.

The in-repo Lean layer records this contract as:

```text
GeneratedCorpusExact(generated, Feasible) :=
  CompleteAuditSet(generated, Feasible) ∧ SoundAuditSet(generated, Feasible)
```

This means every feasible candidate is represented, and every generated
candidate is feasible for the bounded family under discussion.

The second proof layer is dominance pruning:

```text
DominanceCover(pruned, full) :=
  forall candidate in full,
    exists representative in pruned,
      WeaklyDominates(representative, candidate)
```

If every removed candidate is weakly dominated by a retained representative, the
pruned set can support the same bounded optimum claim when paired with the
proper upper-bound certificate. The Lean theorem
`upba_v2_dominance_pruned_partial_fill_bounded_grid_certificate_implies_global_weak_optimal`
formalizes this proof path.

The intended ordering is:

```text
exact generation -> certified dominance pruning -> learned ranking -> deterministic verification
```

Learned ranking is the final search-order accelerator. It is not the source of
the optimality claim.

## 5. Energy Models

ZenoEnergy v0 includes a deterministic hand-coded energy:

```text
E(candidate) =
  + 1_000_000 * invalid_balance_count
  + 1_000_000 * limit_price_violation_count
  + 1_000_000 * negative_reserve_flag
  + 1_000_000 * aggregate_cpmm_invariant_violation_flag
  + 100_000   * noncanonical_fill_vector_flag
  + 100_000   * schema_policy_mismatch_flag
  + 100_000   * price_objective_violation_flag
  + 100_000   * output_mismatch_count
  + 100_000   * fill_coverage_violation_flag
  + 100_000   * duplicate_fill_id_flag
  + 100_000   * unknown_fill_id_count
  + 100_000   * executed_input_over_amount_count
  + 100_000   * output_without_input_count
  + 50_000    * price_ratio_unreduced_flag
  + 10_000    * zero_net_input_count
  + 100       * dust_penalty
  + 10        * imbalance_penalty
  - 10        * normalized_executed_volume
  - 1         * normalized_surplus
```

It also includes a no-dependency learned linear ranker with 96 feature weights
and one bias:

```text
E_theta(x, c) = w · features(x, c) + b
```

Training uses pairwise hinge loss over candidates from the same batch:

```text
loss = max(0, margin + E_theta(good) - E_theta(bad))
```

The current preferred checkpoint uses weighted pair updates:

```text
pair_weight =
  winner_pair_weight when good candidate is the batch winner, otherwise 1
+ objective_gap_weight * normalized_volume_gap for valid-vs-valid pairs
+ same_volume_surplus_gap_weight * normalized_surplus_gap when volume ties
```

The update weight is clipped. This pushes the model toward the remaining error
class observed in hard-case mining: valid candidates ranked ahead of slightly
better valid winners.

The optional PyTorch MLP path supports:

```text
96 -> 64 -> 1
```

with 6,273 parameters. PyTorch was unavailable in the measured local run, so the
reported benchmark uses the 97-parameter linear model.

## 6. Dataset

The synthetic generator builds single-pool CPMM exact-in UPBA v2 batches. It
samples pool reserves, fees, users, balances, exact-in intents, candidate prices,
and partial-fill vectors. Candidate classes include valid candidates, suboptimal
valid candidates, invalid balance candidates, limit-price violations,
negative-reserve cases, invariant violations, noncanonical fill vectors,
all-zero candidates, noisy random candidates, near-miss adversarial candidates,
attractive output mismatches, unreduced price ratios, and schema/policy
mismatches.

Every row stores:

- normalized 96-dimensional feature vector;
- candidate hash;
- candidate type;
- verifier validity label;
- objective volume and surplus;
- hand energy;
- target energy;
- winner label.

The generated corpora are:

```text
train:
  batches: 10,000
  requested candidates per batch: 20
  rows: 199,860
  seed: 20260517
  sha256: 0x0643670a460dc05efc688af9f8dad4e8fafd44d5dba1928ffdd69d0aa689f46f

holdout:
  batches: 2,000
  requested candidates per batch: 20
  rows: 39,979
  seed: 20260518
  sha256: 0xbcf06a210d591f5ab02e05a105db4af6c26d02782f91080e517cb3fb4d634cb7
```

The holdout set has 1,983 batches with at least one verifier-valid candidate.
Metrics below are computed over those winner-bearing batches.

Hard candidate coverage:

```text
train:
  hard_attractive_output_mismatch: 10,000
  hard_unreduced_price: 10,000
  hard_schema_policy_mismatch: 10,000

holdout:
  hard_attractive_output_mismatch: 2,000
  hard_unreduced_price: 2,000
  hard_schema_policy_mismatch: 2,000
```

## 7. Evaluation Protocol

The benchmark compares four candidate orders:

- exhaustive original order;
- deterministic pseudo-random order;
- hand-coded energy order;
- learned energy order.

The primary measured quantity is the position of the exact verifier winner in
the proposed order. This is a candidate-priority metric. In an online system,
early stopping also needs either an optimality certificate for the checked
candidate or a deterministic fallback that eventually checks the remaining
candidates.

The reported `mean_verifier_calls` should therefore be read as:

```text
calls_until_known_winner_is_reached
```

It is the relevant metric for a verifier that can stop once the exact winner's
certificate is checked. With fallback that verifies the full suffix, accepted
output remains exhaustive-equivalent, and the cost reduction depends on when the
system can prove that no unchecked candidate can beat the current winner.

## 8. Results

Current benchmark command:

```bash
python3 tools/benchmark_upba_energy_search.py \
  --batches 2000 \
  --candidates-per-batch 20 \
  --seed 20260518 \
  --model data/upba_energy/upba_v2_energy_linear_gap_weighted_seed20260517.json \
  --top-k 10
```

| mode | batches | candidate_count_mean | top_1 | top_5 | top_10 | top_25 | mean winner position | p95 | p99 | invalid accepts |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| exhaustive | 1,983 | 19.99 | n/a | n/a | n/a | 1.000 | 19.99 | 20 | 20 | 0 |
| random | 1,983 | 19.99 | 0.048 | 0.258 | 0.527 | 1.000 | 10.21 | 19 | 20 | 0 |
| hand energy | 1,983 | 19.99 | 0.763 | 0.996 | 1.000 | 1.000 | 1.36 | 3 | 4 | 0 |
| gap-weighted learned | 1,983 | 19.99 | 0.983 | 1.000 | 1.000 | 1.000 | 1.017 | 1 | 2 | 0 |

The gap-weighted ranker reduced mean winner position by 94.9% versus exhaustive
order and by 25.3% versus hand energy in this harder bounded synthetic
benchmark.

The cross-seed stress harness then streamed additional generated data without
storing every row:

```text
seeds: 20260518, 20260519, 20260520
candidate_counts: 20, 32, 50
batches_per_config: 250
synthetic_batches_requested: 2,250
synthetic_candidates_requested: 76,500
```

Across the nine configurations, gap-weighted learned ordering had mean top-1
recall 98.2%, minimum top-1 recall 96.8%, top-5 recall 100.0%, top-10 recall
100.0% in every configuration, mean winner position 1.018, max mean winner
position 1.032, p99 winner position at most 2, and zero invalid accepts.

Hard-case mining then streamed a larger objective-ordering run:

```text
seeds: 20260521, 20260522, 20260523
candidate_counts: 50, 75, 100
batches_per_config: 1,000
synthetic_batches_requested: 9,000
synthetic_candidates_requested: 675,000
```

Across 8,920 winner-bearing batches, learned ordering had top-1 recall 98.3%,
top-5 recall 99.9%, top-10 recall 100.0%, mean winner position 1.028, max mean
winner position 1.045, p99 winner position at most 2, and zero top-10 misses.
The 150 top-1 misses were valid-vs-valid ordering cases: the top ranked
candidate was verifier-valid in every miss, and the exact winner was also valid
in every miss. This shifts the next model-improvement target from invalid
rejection to objective ordering among valid partial-fill candidates.

An objective-tuned linear variant used the same features and architecture but
trained for 8 epochs at learning rate 0.02. On the held-out dataset it improved
top-1 recall from 97.9% to 98.3%, top-5 recall from 99.9% to 100.0%, and mean
winner position from 1.031 to 1.019. On the nine-configuration cross-seed stress
matrix it kept top-10 recall at 100.0%, raised top-5 recall to 100.0%, reduced
mean winner position from 1.026 to 1.019, reduced the worst mean winner position
from 1.065 to 1.040, and kept p99 winner position at 2.

A gap-weighted linear variant then weighted winner pairs and valid-vs-valid
objective gaps during the same 8-epoch training schedule. On the held-out
dataset it kept top-1 recall at 98.3%, top-5 recall at 100.0%, top-10 recall at
100.0%, and reduced mean winner position to 1.017. On the nine-configuration
cross-seed stress matrix it kept top-10 recall at 100.0%, kept top-5 recall at
100.0%, reduced mean winner position to 1.018, reduced the worst mean winner
position to 1.032, and kept p99 winner position at 2.

A data-scaling probe then trained the same gap-weighted setup over 999, 1,999,
4,996, 9,996, 19,990, 49,969, 99,940, and 199,860 same-generator synthetic
rows. Mean verifier calls improved from 1.0736 at 999 rows to 1.0177 at
199,860 rows, with zero invalid accepts and top-10 recall 100.0% throughout.
The full-volume run remained slightly behind the current gap-weighted checkpoint
at 1.0166 mean calls. This points toward targeted coverage quality, hard
negative generation, and replay-shaped distributions as the next data axis.

A follow-up quality-selection probe filtered out the 84 no-winner training
batches and compared raw winner-bearing sampling against batches ranked by
current-model winner position, hand-energy winner position, hard-family density,
and valid-count variety. Quality selection reduced mean verifier calls relative
to raw sampling on four of six budgets, including 1.0388 versus 1.0610 at 250
training batches and 1.0217 versus 1.0247 at 2,500 batches, with zero invalid
accepts. The smallest 100-batch quality run was worse than raw sampling
(1.0620 versus 1.0439), showing that hard examples need distribution balance.

The best-model registry retains the current UPBA gap-weighted checkpoint and
three deterministic AutoTrader hard synthetic cross-seed models under
`data/upba_energy/best_models/`, with sha256 hashes in
`data/upba_energy/zenoenergy_best_model_registry.json`. These retained files are
stable advisory baselines for follow-up replay and shadow experiments.

The gap-weighted medium hard-case mine requested 4,500 batches and 337,500
candidate slots. Across 4,466 winner-bearing batches, it had top-1 recall
98.54%, top-5 recall 100.0%, top-10 recall 100.0%, mean winner position 1.017,
max p99 winner position 2, and zero invalid accepts. It had zero top-5 misses in
that run, so it is the current preferred research artifact.

The model audit found no forbidden label-like feature names and no nonzero
reserved-feature weights. The largest positive weights are hard verifier-shaped
penalties inherited from the hand initialization. The largest negative weights
favor executed volume, surplus, and related input/output flow features. This
matches the intended search policy: keep malformed candidates expensive, then
prefer higher-objective valid-looking candidates.

A hard-barrier hybrid ablation uses the order key:

```text
sort_key(c) := (B(c), E_theta(x, c), hash(c))
```

where `B(c)` is the deterministic hard-violation part of the hand energy. The
barrier includes malformed or verifier-shaped failures and excludes soft
imbalance, dust, volume, and surplus terms. On the held-out JSONL corpus, the
hybrid tied the gap-weighted learned ranker: top-1 98.3%, top-5 100.0%, top-10
100.0%, mean winner position 1.017, p99 winner position 2, and zero invalid
accepts. A 200-batch live-generator sanity run also tied learned ordering. The
hybrid remains an ablation. The gap-weighted learned checkpoint remains the
preferred artifact.

The Lean theorem
`upba_v2_hard_barrier_hybrid_reordered_partial_fill_bounded_grid_certificate_implies_global_weak_optimal`
records the formal safety surface: if the hybrid order is a permutation of the
exact bounded-grid candidate set, a deterministic verifier certificate over that
order proves the same bounded global weak optimum.

The theorems `full_fallback_equivalent_order_preserves_membership_iff` and
`full_fallback_equivalent_order_preserves_weak_optimality_iff` record the
fallback surface:

```text
ordered.Perm(candidates)
-> (winner in ordered <-> winner in candidates)
-> (WeaklyOptimalIn(winner, ordered) <-> WeaklyOptimalIn(winner, candidates))
```

This is the mathematical reason full fallback remains exhaustive-equivalent:
once every candidate is checked, ranking only changes the schedule. The audited
candidate set is unchanged. The runtime helper
`candidate_orders_are_hash_permutation` checks the hash-multiset version of this
obligation in benchmark receipts.

Early stop before full fallback has a stronger contract. The definition
`CheckedStopCertificate` requires the winner to be in the checked set and to
weakly dominate both checked candidates and the unchecked suffix. The theorem
`checked_stop_certificate_with_exact_full_implies_global_weak_optimal` lifts
that certificate to global weak optimality when the full finite candidate list
is exact and `checked ++ suffix` is a permutation of the full list. The runtime
helper `verified_checked_stop_certificate_holds` audits this condition over
already verified results for evidence receipts. Benchmark receipts report
`checked_stop_top_k_rate` and `checked_stop_at_winner_rate` as certificate-shaped
offline audit metrics.

The suffix-bound refinement adds a maximization theorem in
`ZenoEnergyAdvisoryBoundary.lean`:

```text
score(candidate) <= upperBound(candidate) for every suffix candidate
upperBound(candidate) <= score(winner) for every suffix candidate
winner weakly maximal over checked prefix
-> winner weakly maximal over checked ++ suffix
```

`suffix_upper_bound_checked_stop_with_exact_coverage_implies_global` then lifts
the finite-list certificate to a scoped feasible predicate when the full list
has exact coverage.

The same Lean boundary also records the negative theorem that energy order
alone is insufficient:

```text
energy_order_alone_does_not_imply_true_weakly_best
energy_order_alone_does_not_imply_true_weakly_max
```

These two counterexamples cover minimization-style verifier cost and
maximization-style verifier score. They formalize the research rule that low
energy may set priority, while deterministic verification or a checked-stop
certificate supplies settlement authority.

The holdout top-k sweep separates exact winner recall from checked-stop audit
success. On the 39,979-row holdout dataset, learned and hybrid ordering reached
checked-stop audit success of 100.0% by `k = 2`. Hand energy reached 99.6% at
`k = 5` and 100.0% at `k = 10`. Random ordering reached 50.7% at `k = 10`.

A later suffix-bound benchmark replaces the offline checked-stop audit with a
deterministic early-stop certificate over the unchecked suffix. A checked
verifier winner may stop only when it dominates the checked prefix and every
unchecked candidate has a deterministic objective upper bound no better than
the winner. On the committed bounded synthetic run
`seed=20260541`, learned and hybrid ordering each achieved mean verifier calls
of 1.0084, p99 verifier calls of 1, zero invalid accepts, and zero full fallback
cases across 119 evaluated batches. Hand energy averaged 1.4202 verifier calls,
and random ordering averaged 13.1849.

The suffix-bound stress harness then repeated the experiment across seeds
20260541, 20260542, and 20260543 with 20, 32, and 50 candidates per batch. The
learned and hybrid rankers kept objective-equivalent acceptance, suffix-stop,
and certificate-ok rates at 1.0 across all nine configs, with zero invalid
accepts and mean verifier calls of 1.0132. Hand energy averaged 1.3935 calls
and random ordering averaged 17.1010 calls. This strengthens the bounded
synthetic utility claim while leaving the same coverage and replay obligations.

The adversarial suffix stress then injected high-declared-output invalid
candidates into the unchecked suffix after the verifier winner was checked.
Across 119 evaluated bounded synthetic batches, deterministic disqualifiers
closed all 119 certificates, and the same certificates failed in all 119 cases
when only declared-output bounds were used. This supports a sharper design
lesson: suffix certificates need verifier-derived deterministic invalidity
signals. Raw declared outputs are too weak against attractive invalid suffixes.

The follow-up adversarial family stress generated 944 verifier-invalid suffix
cases across 8 invalidity families. Every case was deterministically
disqualified, every with-disqualifier suffix certificate passed, and
high-declared-output cases still failed under declared-output-only bounds. This
turns the disqualifier result from a single hard-negative family into broader
bounded synthetic evidence over schema/policy, fill coverage, all-zero,
limit-price, price-objective, reserve/invariant, and output-mismatch failures.

This result changes the interpretation of ranking utility. The model still has
no authority over settlement validity, but it can place the first verifier call
where a deterministic suffix-bound certificate is likely to close the finite
candidate list. The remaining production obligations are candidate-family
coverage and real replay.

## 9. Interpretation

The result supports the research hypothesis:

```text
tiny learned ranker -> lower expected winner position
```

The strongest signal is that a 97-parameter model improves over the deterministic
hand energy while preserving zero invalid accepts. The model is small enough for
CPU inference and artifact inspection.

The result does not establish production UPBA v2 optimality. The experiment uses
synthetic bounded data and an offline winner label. Production use needs one of
these additional supports:

- a certified exact candidate generator for the relevant bounded family;
- a v2 bounded-grid optimality verifier;
- dominance-pruning certificates that preserve the optimum;
- a privacy-approved replay corpus that reflects real orderflow distribution;
- deterministic fallback whenever early stopping proof is unavailable.

## 10. Real Data and Distribution Shift

Real data would make the learning problem more representative when it captures
the production distribution of pools, balances, intent sizes, limit prices,
partial fills, and adversarial near-misses. It would not change the safety rule.
Verifier labels would still define validity, and the model would still only rank.

The safe route for real data is:

```text
private live data -> redaction/aggregation policy -> replay corpus -> verifier labels -> offline training
```

Training should avoid secrets, raw private orderflow, and any data that would
change deterministic replay.

## 11. Production Gate and Evidence Bundle

ZenoEnergy now has a production-adjacent evidence path:

```text
tools/build_zenoenergy_production_evidence_bundle.py
```

The bundle composes five deterministic artifacts:

```text
zenodex/energy/upba_real_replay_report/v1
zenodex/energy/autotrader_real_shadow_report/v1
zenodex/energy/replay_source_manifest_check/v1
zenodex/energy/replay_coverage_profile_check/v1
zenodex/energy/production_promotion_gate/v1
```

The bundle itself uses:

```text
zenodex/energy/production_evidence_bundle/v1
```

Operators build the source manifests with:

```text
tools/build_zenoenergy_replay_source_manifest.py
```

That command computes canonical source-report hashes, attaches deterministic
replay and no-live-secrets attestations, records the secret-scan result, runs
the manifest checker, and writes the manifest only when the check passes.
Operators can generate the secret-scan report with:

```text
tools/check_zenoenergy_replay_secret_scan.py
```

The scanner writes `zenodex/energy/replay_secret_scan/v1`, catches obvious key
material and sensitive JSON keys, and can be supplied to the manifest builder
with `--secret-scan-report`. Dirty scans and source-count mismatches fail
closed. A clean scan is a packaging guardrail; production promotion still
requires the production gate and source-manifested real replay reports.

The coverage-profile checker writes
`zenodex/energy/replay_coverage_profile_check/v1`. It requires UPBA replay
breadth across pools, intent-size buckets, candidate families, hard-negative
families, and market days. It requires AutoTrader shadow replay breadth across
strategy, guard, and decision families. The profile is a breadth guard against
aggregate-count-only promotion; it does not prove representativeness of future
traffic.

The release predicate is:

```text
ProductionEvidenceBundle :=
  UPBARealReplayReport
  and AutoTraderRealShadowReport
  and ReplaySourceManifestChecks
  and ReplayCoverageProfileChecks
  and ProductionPromotionGate
```

The production gate requires at least 1,000 real UPBA replay batches, 20,000
real UPBA candidates, 500 real AutoTrader shadow contexts, 5,000 AutoTrader
shadow rows, seven market days, top-25 recall at least 0.99, zero invalid
accepts, deterministic replay, no live secrets, source manifest checks, and
coverage profile checks. It also requires learned mean verifier or guard calls
below hand energy.

Malformed evidence fails closed. Well-formed but insufficient evidence produces
`decision: blocked`. A passing bundle can only support advisory ranking:

```text
LowEnergy(candidate) ∧ VerifierRejects(candidate) -> SettlementRejected
```

The current gate remains blocked because the repo contains synthetic and fixture
evidence, plus the tooling needed to evaluate real evidence, while the required
real replay reports have not yet been supplied.

## 12. Reproducibility

Dataset generation:

```bash
python3 tools/generate_upba_energy_dataset.py \
  --batches 10000 \
  --candidates-per-batch 20 \
  --seed 20260517 \
  --output data/upba_energy/upba_v2_energy_synthetic_seed20260517.jsonl \
  --metadata-output data/upba_energy/upba_v2_energy_synthetic_seed20260517.meta.json

python3 tools/generate_upba_energy_dataset.py \
  --batches 2000 \
  --candidates-per-batch 20 \
  --seed 20260518 \
  --output data/upba_energy/upba_v2_energy_holdout_seed20260518.jsonl \
  --metadata-output data/upba_energy/upba_v2_energy_holdout_seed20260518.meta.json
```

Training:

```bash
python3 tools/train_upba_energy.py \
  --dataset data/upba_energy/upba_v2_energy_synthetic_seed20260517.jsonl \
  --output-model data/upba_energy/upba_v2_energy_linear_seed20260517.json \
  --epochs 3 \
  --learning-rate 0.01 \
  --seed 20260517 \
  --init hand
```

Current preferred gap-weighted training:

```bash
python3 tools/train_upba_energy.py \
  --dataset data/upba_energy/upba_v2_energy_synthetic_seed20260517.jsonl \
  --output-model data/upba_energy/upba_v2_energy_linear_gap_weighted_seed20260517.json \
  --epochs 8 \
  --learning-rate 0.02 \
  --seed 20260517 \
  --init hand \
  --winner-pair-weight 2.0 \
  --objective-gap-weight 4.0 \
  --same-volume-surplus-gap-weight 1.0 \
  --max-pair-weight 8.0
```

Evaluation:

```bash
python3 tools/benchmark_upba_energy_search.py \
  --batches 2000 \
  --candidates-per-batch 20 \
  --seed 20260518 \
  --model data/upba_energy/upba_v2_energy_linear_gap_weighted_seed20260517.json \
  --top-k 10
```

Formal checks:

```bash
cd lean-mathlib && lake env lean Proofs/UniformBatchOptimality.lean
cd lean-mathlib && lake build Proofs.UniformBatchOptimality
python3 ~/.codex/skills/proof-engineering/scripts/scan_proof_placeholders.py \
  lean-mathlib/Proofs/UniformBatchOptimality.lean
pytest -q tests/formal/test_lean_uniform_batch_optimality.py
```

Production evidence bundle replay:

```bash
python3 tools/build_zenoenergy_production_evidence_bundle.py \
  --upba-benchmark-report data/private/upba_replay_benchmark.json \
  --upba-source-manifest data/private/upba_replay_source_manifest.json \
  --upba-coverage-profile data/private/upba_replay_coverage_profile.json \
  --upba-source-kind production-shadow \
  --upba-source-descriptor prod-shadow:2026-05-01..2026-05-09 \
  --upba-market-day-count 9 \
  --autotrader-shadow-bridge-report data/private/autotrader_shadow_bridge.json \
  --autotrader-source-manifest data/private/autotrader_replay_source_manifest.json \
  --autotrader-coverage-profile data/private/autotrader_replay_coverage_profile.json \
  --autotrader-source-kind production-shadow \
  --autotrader-source-descriptor prod-shadow:autotrader:2026-05-01..2026-05-09 \
  --autotrader-market-day-count 9 \
  --deterministic-replay-ok \
  --no-live-secrets \
  --operator-release-enable
```

Committed research evidence replay:

```bash
PYTHONPATH=external/PopperPad/src python3 tools/check_zenoenergy_research_evidence.py
```

## 13. Recommendation

Keep ZenoEnergy v0 as an isolated research accelerator. The next high-value
work is mathematical first. Larger models are lower priority:

- finalize the v2 bounded-grid optimality verifier;
- strengthen exact candidate generation certificates;
- implement certified dominance-pruning witnesses;
- add source-manifested non-private or privacy-approved real corpora;
- replay suffix-bound early-stop on real or production-shadow candidate sets;
- extend adversarial family stress with real replay and candidate-coverage evidence;
- train the optional tiny MLP and compare it against the current linear ranker.

The current evidence says the search-order signal is strong enough to continue.
The release boundary remains deterministic verification, certified fallback, and
the production evidence bundle gate.
