---
title: Verifier-Preserving Learned Candidate Ordering for UPBA v2 Settlement Search
type: research-paper
status: draft
date: 2026-05-19
---

# Verifier-Preserving Learned Candidate Ordering for UPBA v2 Settlement Search

ZenoDEX Research Paper, draft v0.7
Date: May 20, 2026

## Abstract

ZenoEnergy v0 studies whether learned energy scorers can reduce the cost of
searching UPBA v2 partial-fill exact-in settlement candidates while preserving
deterministic verification. The scorer is advisory: it ranks candidates before
the verifier checks them, and it has no authority over settlement validity,
ledger state, state roots, or replay.

The first stable checkpoint was a 97-parameter CPU-only linear ranker trained on
synthetic, verifier-labeled UPBA v2 candidate data. The current preferred
research checkpoint is `gemini_mlp_v6_seed20260519`, a 6,273-parameter
pure-Python MLP over the same verifier-shaped feature surface. On the held-out
synthetic corpus with 1,983 winner-bearing batches and about 20 candidates per
batch, v6 placed the exact verifier winner first in 99.75% of batches, in the
top 5 in 100.0%, and in the top 10 in 100.0%. Mean winner position fell from
19.99 under exhaustive order to 1.0025 under v6 learned order. The deterministic
verifier accepted zero invalid candidates.

The leaderboard now compares seven UPBA v2 advisory rankers. It promotes v6 as
the current research checkpoint because it has the best holdout mean verifier
calls, best holdout top-1 recall, best cross-seed mean verifier calls, best
cross-seed worst top-1 recall, best hard-case top-1 recall, and fewest hard-case
top-1 misses among the full three-lane candidates. Gemini v5 is recorded as
negative evidence because it underperformed the retained gap-weighted baseline.

This is optimization research: the optimized quantity is verifier search work
over a finite candidate set. Correctness comes from deterministic verification,
certified candidate generation, dominance-pruning contracts, deterministic
suffix certificates, and deterministic fallback.

The current production-adjacent path is an evidence bundle rather than a release
claim. The bundle assembles source-manifested and coverage-profiled UPBA and
AutoTrader real replay reports, then runs a fail-closed advisory ranking
promotion gate. The gate currently blocks promotion because real replay coverage
is still missing.

The current AutoTraderEnergy lane is promising but less mature than UPBA. Its
hard synthetic cross-seed receipt records learned mean guard calls of 1.010
versus 4.312 for hand energy and 8.393 for random ordering, with zero invalid
accepts across three seed pairs. That is synthetic transfer evidence. The next
AutoTrader milestone is source-manifested real shadow replay.

The generative AutoTrader and ZenoJEPA additions are now recorded as bounded
proposal-search and UX evidence. The checked refiner baseline improved the
selected synthetic objective by 12.00 mean units across 160 generated contexts,
and the preconditioned refiner replay improves that to 13.01 mean units while
selecting zero policy-invalid refinements. Source-level ZenoJEPA now scores
future tension for AutoTrader proposals, and the UX receipt turns policy labels,
future-tension diagnostics, and suggested controls into user-facing advisory
cards. The useful JEPA claim is future-risk and UX quality: future tension
predicts synthetic later policy failures with AUC 0.8144, correlates with
slippage, budget, and drawdown stress at 0.6133, 0.5592, and 0.5556, and every
suggested-control card in the receipt has a future-tension-reducing control.
The same receipt records zero invalid accepts over 96 generated contexts and
explicit `model_authorizes_trade = false` / `ux_card_authorizes_trade = false`
authority fields. Deterministic policy guards and verifiers remain
authoritative.

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

The preferred linear checkpoint uses weighted pair updates:

```text
pair_weight =
  winner_pair_weight when good candidate is the batch winner, otherwise 1
+ objective_gap_weight * normalized_volume_gap for valid-vs-valid pairs
+ same_volume_surplus_gap_weight * normalized_surplus_gap when volume ties
```

The update weight is clipped. This pushes the model toward the remaining error
class observed in hard-case mining: valid candidates ranked ahead of slightly
better valid winners.

The promoted v6 research checkpoint uses a pure-Python MLP adapter:

```text
96 -> 64 -> 1
```

with 6,273 parameters. The MLP remains an advisory ranker. It uses the same
deterministic verifier labels, the same full-fallback boundary, and the same
rule that model output does not authorize settlement or enter state roots.

The corrected Gemini evaluation path matters. The holdout comparison already
used crossed Gemini features, but the streaming cross-seed and hard-case tools
had to be repaired to apply each model's declared feature surface before
scoring. The replay gate now checks the corrected path and promotes only the
models evaluated through that feature adapter.

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

Current v6 holdout comparison command:

```bash
python3 tools/compare_upba_energy_gemini.py \
  --dataset data/upba_energy/upba_v2_energy_holdout_seed20260518.jsonl \
  --gap-model data/upba_energy/best_models/upba_v2_linear_gap_weighted_seed20260517.json \
  --gemini-model internal/Gemini/gemini_mlp_v6_final.json \
  --output-json data/upba_energy/upba_v2_energy_gemini_v6_holdout_compare.json \
  --output-markdown docs/ZENO_ENERGY_GEMINI_V6_HOLDOUT_COMPARE.md
```

Current model leaderboard command:

```bash
python3 tools/build_upba_energy_model_leaderboard.py \
  --output-json data/upba_energy/upba_v2_energy_model_leaderboard.json \
  --output-markdown docs/ZENO_ENERGY_UPBA_V2_MODEL_LEADERBOARD.md
```

| model | holdout mean calls | holdout top-1 | cross mean calls | cross worst top-1 | hard top-1 | hard top-1 misses | invalid accepts |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| gemini MLP v6 | 1.0025 | 0.9975 | 1.0036 | 0.9839 | 0.9940 | 9 | 0 |
| gemini highwinner linear | 1.0066 | 0.9934 | 1.0076 | 0.9839 | 0.9919 | 12 | 0 |
| gap-weighted linear | 1.0166 | 0.9834 | 1.0175 | 0.9677 | 0.9854 | 65 | 0 |
| gemini linear v5 | 1.0217 | 0.9788 | 1.0202 | 0.9637 | 0.9839 | 24 | 0 |

The v6 checkpoint is the current preferred UPBA v2 research artifact. It beats
the retained linear checkpoints on the selected verifier-facing metrics used by
the leaderboard. Its absolute remaining headroom is small on this bounded
synthetic distribution: top-5 and top-10 are already complete, p99 holdout calls
are 1, and hard-case top-1 misses are down to 9 across 1,489 winner-bearing hard
batches. Further UPBA gains should target those residual valid-vs-valid misses,
real replay distribution shift, and suffix-certificate utility rather than raw
parameter scaling.

Historical gap-weighted linear benchmark command:

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
The full-volume run remained slightly behind the then-current gap-weighted checkpoint
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

A tiny ensemble probe then trained five diversified linear members and combined
them with the then-current gap-weighted checkpoint. Ensemble mean-energy and
rank-consensus orderings kept top-10 recall at 100.0% and invalid accepts at
zero, but the best ensemble mean verifier-call count was 1.0237 versus 1.0166
for the gap-weighted checkpoint. Rank disagreement had moderate top-1 miss signal
(AUC 0.6819), so the ensemble is useful as diagnostic coverage evidence rather
than as the promoted UPBA ranker.

The best-model registry now retains v6 as the preferred UPBA research
checkpoint, keeps the strongest linear UPBA checkpoints as superseded baselines,
and keeps three deterministic AutoTrader hard synthetic cross-seed models under
`data/upba_energy/best_models/`, with sha256 hashes in
`data/upba_energy/zenoenergy_best_model_registry.json`. These retained files are
stable advisory artifacts for follow-up replay and shadow experiments.

The gap-weighted medium hard-case mine requested 4,500 batches and 337,500
candidate slots. Across 4,466 winner-bearing batches, it had top-1 recall
98.54%, top-5 recall 100.0%, top-10 recall 100.0%, mean winner position 1.017,
max p99 winner position 2, and zero invalid accepts. It had zero top-5 misses in
that run, so it became the preferred linear research artifact before v6.

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
hybrid remains an ablation over the linear checkpoint. The v6 MLP now supersedes
the gap-weighted learned checkpoint as the preferred UPBA research artifact.

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

## 8.1 Langevin Discovery Boundary

The internal Gemini work also introduced Langevin-style candidate refinement:

```text
x_{t+1} = x_t - eta * grad E(x_t) + sqrt(2 * eta) * epsilon
```

This is proposal search. It can lower learned energy, but lower learned energy
does not imply verifier acceptance. The committed receipt records the critical
negative example:

```text
seed_verifier_ok: true
refined_verifier_ok: false
accepted_refinement: false
fallback_to_seed: true
selected_verifier_ok: true
```

The implementation therefore selects a refined proposal only when deterministic
verification accepts it and the learned energy improves. Otherwise it falls back
to the verifier-backed seed when the seed is valid. `ZenoGuard` remains a soft
advisory prior; it is not a validity proof, a settlement authorization rule, or
a replacement for the UPBA verifier.

## 8.2 AutoTrader Refiner And JEPA Boundary

The AutoTrader refiner applies bounded Langevin-style proposal search to
adjustable execution features:

```text
refiner proposal
-> canonicalize feature map
-> deterministic policy label
-> select only if valid and deterministic objective does not regress
```

The committed boundary receipt records:

```text
evaluated_contexts: 160
accepted_refinement_count: 160
selected_invalid_count: 0
baseline_objective_delta_mean: 12.003534
baseline_energy_delta_mean: -4.622400
preconditioned_objective_delta_mean: 13.008661
preconditioned_energy_delta_mean: -4.685220
optimized_config: precondition_decay=0.9, lr=0.04
decision: research_only_policy_checked_refinement
```

This is hard synthetic evidence. It is useful because it shows the correct
shape for generative AutoTrader search: model proposes feature changes, policy
labels decide selection, and real shadow replay remains required before
promotion.

ZenoJEPA and ZenoLogic are also bounded advisory surfaces. The JEPA receipt
shows that a latent future-tension score can rank a balanced action ahead of a
draining action:

```text
balanced_action_tension: 0.309388
draining_action_tension: 1.351591
future_tension_prefers_balanced: true
```

The same receipt records a ZenoLogic hazard:

```text
EnergyNot(hard_barrier)(invalid) < EnergyNot(hard_barrier)(valid)
```

That is expected for a mathematical complement, but it is dangerous if applied
to safety barriers. ZenoLogic can compose advisory energies. It does not create
a formal verifier, and `EnergyNot` must not be used over hard safety predicates.

The source-level JEPA/UX pass moves the useful part of the idea into
`src.energy`. The default AutoTrader JEPA model projects candidate features into
a small latent fragility state:

```text
state:
  liquidity_gap, drawdown_risk, price_deviation,
  position_pressure, budget_used, nonce_age

action:
  edge_gap, execution_urgency, slippage,
  budget_used, price_deviation, position_pressure
```

The model returns a future-tension score. The AutoTrader UX layer then builds a
card with:

```text
status
risk_level
badges
blocked_reasons
reasons
suggested_controls
scores
authority
display
```

The committed source-level UX receipt records:

```text
contexts: 96
future_weight: 0.1
later_policy_failure_auc: 0.814429
slippage_stress_correlation: 0.613327
budget_stress_correlation: 0.559229
drawdown_stress_correlation: 0.555595
suggested_control_best_reduction_rate: 1.000000
blocked_status_match_rate: 1.000000
future_warning_match_rate: 1.000000
mean_guard_calls: 1.062500
top_1_recall: 0.937500
top_5_recall: 1.000000
invalid_accept_count: 0
balanced_future_tension: 0.910303
fragile_future_tension: 4.764275
decision: research_only_future_aware_autotrader_ux
```

The old JEPA-over-hand ordering is now recorded as negative evidence. On this
receipt, hand+JEPA top-5 recall is 0.8021, while learned+JEPA top-5 recall is
1.0000. Future tension is best used as a risk explanation, warning signal, and
counterfactual-control score layered behind learned AutoTraderEnergy.

This improves UX in three concrete ways. First, blocked actions can tell the
user which deterministic policy guard failed, such as stale quote, slippage
limit, route binding, wallet capability, budget, or nonce freshness. Second,
policy-valid but fragile actions can be shown as risk-review candidates instead
of looking identical to low-risk proposals. Third, the interface can recommend
controls such as refreshing quote receipts, reducing notional, tightening route
selection, or waiting for budget recovery. The card is not an approval. It is a
deterministic explanation wrapper around advisory scores and policy labels.

## 9. Interpretation

The result supports the research hypothesis:

```text
learned advisory ranker -> lower expected winner position
```

The strongest signal is that multiple small learned scorers improve over the
deterministic hand energy while preserving zero invalid accepts, and that v6 now
also improves over the retained linear checkpoints. The v6 MLP is still small
enough for CPU inference and artifact inspection.

The UPBA v2 advisory ranker is approaching a synthetic-distribution plateau for
the current candidate family. The evidence does not show that no better scorer
exists. It shows that simple extensions already face diminishing returns:
same-generator data scaling saturated, the first set-aware and listwise probes
did not beat the strongest pairwise baseline, ensemble aggregation did not beat
the retained default, and v5 underperformed. The profitable UPBA direction is
now targeted: mine the remaining valid-vs-valid misses, replay on real or
production-shadow candidate sets, and measure whether suffix certificates close
earlier on representative traffic.

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
python3 tools/check_zenoenergy_research_evidence.py
```

## 13. Recommendation

Keep ZenoEnergy v0 as an isolated research accelerator. For UPBA, the next
high-value work is targeted and evidence-driven. Larger models are lower
priority unless they are trained against new residual families:

- finalize the v2 bounded-grid optimality verifier;
- strengthen exact candidate generation certificates;
- implement certified dominance-pruning witnesses;
- add source-manifested non-private or privacy-approved real corpora;
- replay suffix-bound early-stop on real or production-shadow candidate sets;
- extend adversarial family stress with real replay and candidate-coverage evidence;
- keep ensemble disagreement as a diagnostic signal until it beats the retained default;
- mine and retrain on the nine current v6 hard-case top-1 misses;
- keep v6 as the preferred UPBA research checkpoint until a challenger beats it
  across holdout, cross-seed, hard-case, and safety obligations.

AutoTraderEnergy should now receive the larger share of modeling effort. The
hard synthetic AutoTraderEnergy scorer already reduces guard calls sharply, and
the checked refiner shows a bounded synthetic objective gain while preserving
deterministic policy authority. The next AutoTrader work should build
source-manifested shadow corpora, add coverage profiles over strategy, guard,
decision, and UX-warning families, and train against real policy-gate labels.
The UX milestone is to replay actual AutoTrader decisions and verify that the
cards surface the correct guard reason, risk level, future-tension warning, and
operator control without hiding the deterministic authority boundary.

The current evidence says the search-order signal is strong enough to continue.
The release boundary remains deterministic verification, certified fallback, and
the production evidence bundle gate.
