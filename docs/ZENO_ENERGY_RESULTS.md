# ZenoEnergy v0 Results

Measured on May 17, 2026, using the in-repo synthetic generator and CPU-only
linear ranker. PyTorch was not installed in this environment, so the optional
MLP builder was not trained.

This refresh adds harder adversarial candidates inspired by energy-based
reasoning work: attractive output mismatches, unreduced price ratios, and
schema/policy mismatches. The hand energy now exposes named components so the
largest failure term can be inspected instead of treating the score as opaque.
The current preferred research checkpoint is the gap-weighted linear ranker,
which uses the same 97-parameter architecture and puts more training pressure on
winner pairs plus valid-vs-valid objective gaps.

## Dataset

```text
train:
  batches: 10,000
  requested candidates per batch: 20
  rows: 199,860
  feature_dim: 96
  seed: 20260517
  sha256: 0x0643670a460dc05efc688af9f8dad4e8fafd44d5dba1928ffdd69d0aa689f46f
  path: data/upba_energy/upba_v2_energy_synthetic_seed20260517.jsonl

holdout:
  batches: 2,000
  requested candidates per batch: 20
  rows: 39,979
  feature_dim: 96
  seed: 20260518
  sha256: 0xbcf06a210d591f5ab02e05a105db4af6c26d02782f91080e517cb3fb4d634cb7
  path: data/upba_energy/upba_v2_energy_holdout_seed20260518.jsonl
```

The holdout set contains 1,983 batches with at least one verifier-valid
candidate and 17 all-negative sampled batches. Recall and verifier-call metrics
are computed on the 1,983 batches where a winner exists.

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

Training command:

```bash
python3 tools/train_upba_energy.py \
  --dataset data/upba_energy/upba_v2_energy_synthetic_seed20260517.jsonl \
  --output-model data/upba_energy/upba_v2_energy_linear_seed20260517.json \
  --epochs 3 \
  --learning-rate 0.01 \
  --seed 20260517 \
  --init hand
```

Model:

```text
backend: linear_pairwise_hinge
feature_dim: 96
parameters: 97
```

## Benchmark

Command:

```bash
python3 tools/benchmark_upba_energy_search.py \
  --batches 2000 \
  --candidates-per-batch 20 \
  --seed 20260518 \
  --model data/upba_energy/upba_v2_energy_linear_gap_weighted_seed20260517.json \
  --top-k 10
```

| mode | batches | candidate_count_mean | top_1 | top_5 | top_10 | top_25 | mean_calls | p95 | p99 | invalid_accept |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| exhaustive | 1,983 | 19.99 | 0.000 | 0.000 | 0.000 | 1.000 | 19.99 | 20 | 20 | 0 |
| random | 1,983 | 19.99 | 0.048 | 0.258 | 0.527 | 1.000 | 10.21 | 19 | 20 | 0 |
| hand energy | 1,983 | 19.99 | 0.763 | 0.996 | 1.000 | 1.000 | 1.36 | 3 | 4 | 0 |
| gap-weighted learned | 1,983 | 19.99 | 0.983 | 1.000 | 1.000 | 1.000 | 1.017 | 1 | 2 | 0 |

The gap-weighted ranker reduced mean verifier-winner position by 94.9% versus
exhaustive order and by 25.3% versus hand energy in this harder bounded
synthetic benchmark.

## Cross-Seed Stress

Receipt: [ZENO_ENERGY_CROSS_SEED_STRESS.md](./ZENO_ENERGY_CROSS_SEED_STRESS.md)

Command:

```bash
python3 tools/stress_upba_energy_cross_seed.py \
  --batches 250 \
  --seeds 20260518,20260519,20260520 \
  --candidate-counts 20,32,50 \
  --model data/upba_energy/upba_v2_energy_linear_seed20260517.json \
  --top-k 10 \
  --output-json data/upba_energy/upba_v2_energy_cross_seed_stress_250x3x3.json \
  --output-markdown docs/ZENO_ENERGY_CROSS_SEED_STRESS.md
```

This streaming stress run requested 2,250 synthetic batches and 76,500 candidate
slots without storing the generated rows.

| mode | configs | top1_mean | top1_min | top5_mean | top10_mean | top10_min | mean_calls | max_mean_calls | p99_max | invalid_accepts |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| hand energy | 9 | 0.782 | 0.752 | 0.996 | 1.000 | 1.000 | 1.326 | 1.373 | 5 | 0 |
| learned linear | 9 | 0.982 | 0.964 | 0.999 | 1.000 | 1.000 | 1.026 | 1.065 | 2 | 0 |
| random | 9 | 0.032 | 0.012 | 0.164 | 0.340 | 0.213 | 17.401 | 25.480 | 50 | 0 |

## Hard-Case Mining

Receipt: [ZENO_ENERGY_HARD_CASES.md](./ZENO_ENERGY_HARD_CASES.md)

Command:

```bash
python3 tools/mine_upba_energy_hard_cases.py \
  --batches 1000 \
  --seeds 20260521,20260522,20260523 \
  --candidate-counts 50,75,100 \
  --model data/upba_energy/upba_v2_energy_linear_seed20260517.json \
  --max-examples 50 \
  --output-json data/upba_energy/upba_v2_energy_hard_case_mining_1000x3x3.json \
  --output-markdown docs/ZENO_ENERGY_HARD_CASES.md
```

This streaming mine requested 9,000 synthetic batches and 675,000 candidate
slots, then saved only compact miss summaries and examples.

```text
batches_with_winner: 8,920
top_1_recall: 98.3%
top_5_recall: 99.9%
top_10_recall: 100.0%
mean_winner_position_mean: 1.028
max_mean_winner_position: 1.045
max_p99_winner_position: 2
top1_miss_count: 150
top5_miss_count: 12
top10_miss_count: 0
```

Top-1 misses were valid-vs-valid ordering cases. The top ranked candidate was
verifier-valid in all 150 misses, and the exact winner was also valid in all
150. The next useful modeling improvement is objective ordering among valid
partial-fill candidates, especially around imbalance and dust terms.
`candidate_type` in the hard-case receipt records generator provenance; verifier
validity remains the authoritative label.

## Objective-Tuned Variant

The objective-tuned linear model keeps the same 97-parameter architecture and
feature schema, but trains longer on the same generated corpus:

```bash
python3 tools/train_upba_energy.py \
  --dataset data/upba_energy/upba_v2_energy_synthetic_seed20260517.jsonl \
  --output-model data/upba_energy/upba_v2_energy_linear_objective_tuned_seed20260517.json \
  --epochs 8 \
  --learning-rate 0.02 \
  --seed 20260517 \
  --init hand
```

Held-out dataset comparison:

| model | top_1 | top_5 | top_10 | mean_calls | p95 | p99 | invalid_accept |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| learned linear | 0.979 | 0.999 | 1.000 | 1.031 | 1 | 2 | 0 |
| objective-tuned linear | 0.983 | 1.000 | 1.000 | 1.019 | 1 | 2 | 0 |

Cross-seed stress receipt:
[ZENO_ENERGY_OBJECTIVE_TUNED_STRESS.md](./ZENO_ENERGY_OBJECTIVE_TUNED_STRESS.md)

| model | configs | top1_mean | top1_min | top5_mean | top10_min | mean_calls | max_mean_calls | p99_max | invalid_accepts |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| learned linear | 9 | 0.982 | 0.964 | 0.999 | 1.000 | 1.026 | 1.065 | 2 | 0 |
| objective-tuned linear | 9 | 0.982 | 0.968 | 1.000 | 1.000 | 1.019 | 1.040 | 2 | 0 |

Objective-tuned hard-case receipt:
[ZENO_ENERGY_OBJECTIVE_TUNED_HARD_CASES.md](./ZENO_ENERGY_OBJECTIVE_TUNED_HARD_CASES.md)

The tuned model's medium hard-case mine requested 4,500 batches and 337,500
candidate slots. It had top-10 recall 100.0%, top-5 recall 99.98%, mean winner
position 1.021, p99 winner position at most 2, and 0 invalid accepts. This
made the objective-tuned model a useful baseline for valid-vs-valid ordering
experiments.

## Gap-Weighted Variant

The gap-weighted model keeps the same 96-feature schema and 97-parameter linear
architecture. It changes the training update weight for each violated pair:

```text
pair_weight =
  winner_pair_weight when good candidate is the batch winner, otherwise 1
+ objective_gap_weight * normalized_volume_gap for valid-vs-valid pairs
+ same_volume_surplus_gap_weight * normalized_surplus_gap when volume ties
```

The weight is clipped to `max_pair_weight`. This targets the hard-case pattern
seen after the first runs: most remaining misses were valid candidates ranked
ahead of slightly better valid winners.

Objective-equivalent training hygiene is now available for the same pairwise
trainer. New research runs can pass `--positive-class objective-equivalent` so
`winner_pair_weight` applies to every verifier-accepted candidate in the tied
maximum `(objective_volume, objective_surplus)` class. The legacy default
`--positive-class hash-winner` remains available to reproduce earlier
checkpoints.

Training command:

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
  --max-pair-weight 8.0 \
  --positive-class hash-winner
```

Held-out dataset comparison:

| model | top_1 | top_5 | top_10 | mean_calls | p95 | p99 | invalid_accept |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| learned linear | 0.979 | 0.999 | 1.000 | 1.031 | 1 | 2 | 0 |
| objective-tuned linear | 0.983 | 1.000 | 1.000 | 1.019 | 1 | 2 | 0 |
| gap-weighted linear | 0.983 | 1.000 | 1.000 | 1.017 | 1 | 2 | 0 |

Gap-weighted cross-seed stress receipt:
[ZENO_ENERGY_GAP_WEIGHTED_STRESS.md](./ZENO_ENERGY_GAP_WEIGHTED_STRESS.md)

| model | configs | top1_mean | top1_min | top5_mean | top10_min | mean_calls | max_mean_calls | p99_max | invalid_accepts |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| learned linear | 9 | 0.982 | 0.964 | 0.999 | 1.000 | 1.026 | 1.065 | 2 | 0 |
| objective-tuned linear | 9 | 0.982 | 0.968 | 1.000 | 1.000 | 1.019 | 1.040 | 2 | 0 |
| gap-weighted linear | 9 | 0.982 | 0.968 | 1.000 | 1.000 | 1.018 | 1.032 | 2 | 0 |

Gap-weighted hard-case receipt:
[ZENO_ENERGY_GAP_WEIGHTED_HARD_CASES.md](./ZENO_ENERGY_GAP_WEIGHTED_HARD_CASES.md)

The gap-weighted medium hard-case mine requested 4,500 batches and 337,500
candidate slots. It had 4,466 winner-bearing batches, top-1 recall 98.54%,
top-5 recall 100.0%, top-10 recall 100.0%, mean winner position 1.017, p99
winner position at most 2, and 0 invalid accepts. The top-5 miss count fell to
0 in this run, so the gap-weighted model is the current preferred research
checkpoint.

## Listwise Set Ranker

Receipt: [ZENO_ENERGY_LISTWISE_SET_RANKER.md](./ZENO_ENERGY_LISTWISE_SET_RANKER.md)

The first listwise set-context experiment adds deterministic candidate-list
rank and interaction features, then trains a 237-feature linear energy model
with top-one listwise softmax loss.

Command:

```bash
python3 tools/compare_upba_energy_listwise_set_ranker.py \
  --train-batches 120 \
  --holdout-batches 80 \
  --candidates-per-batch 24 \
  --train-seed 20260532 \
  --holdout-seed 20260533 \
  --pairwise-epochs 6 \
  --listwise-epochs 10 \
  --pairwise-learning-rate 0.03 \
  --listwise-learning-rate 0.08 \
  --l2 0.0001 \
  --output-json data/upba_energy/upba_v2_energy_listwise_set_ranker_seed20260532_20260533.json \
  --output-markdown docs/ZENO_ENERGY_LISTWISE_SET_RANKER.md \
  --output-model-dir data/upba_energy
```

| mode | top1 | top5 | top10 | mean calls | p95 | p99 | invalid accepts |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| aggregate pairwise | 0.987 | 1.000 | 1.000 | 1.026 | 1 | 1 | 0 |
| set-aware pairwise | 0.987 | 1.000 | 1.000 | 1.026 | 1 | 1 | 0 |
| listwise set | 0.947 | 1.000 | 1.000 | 1.066 | 1 | 2 | 0 |

The listwise ranker preserved top-10 recall, had zero invalid accepts, zero
permutation violations, and `checked_stop_at_winner_rate = 1.0`. It did not
improve mean verifier calls against the strongest pairwise baseline on this
bounded synthetic split. Keep it as negative knowledge until a nonlinear or
outcome-weighted variant shows a measured win.

### Listwise Cross-Seed Stress

Receipt:
[ZENO_ENERGY_LISTWISE_SET_RANKER_CROSS_SEED.md](./ZENO_ENERGY_LISTWISE_SET_RANKER_CROSS_SEED.md)

Command:

```bash
python3 tools/stress_upba_energy_listwise_set_ranker.py \
  --train-batches 80 \
  --holdout-batches 60 \
  --candidates-per-batch 24 \
  --pairwise-epochs 6 \
  --listwise-epochs 10 \
  --pairwise-learning-rate 0.03 \
  --listwise-learning-rate 0.08 \
  --l2 0.0001 \
  --seed-pairs 20260532:20260533,20260534:20260535,20260536:20260537 \
  --output-json data/upba_energy/upba_v2_energy_listwise_set_ranker_cross_seed_seed20260532_20260537.json \
  --output-markdown docs/ZENO_ENERGY_LISTWISE_SET_RANKER_CROSS_SEED.md
```

| mode | top1 mean | top10 mean | mean calls | p99 mean |
| --- | ---: | ---: | ---: | ---: |
| aggregate pairwise | 0.9828 | 1.0000 | 1.0172 | 1.0000 |
| set-aware pairwise | 0.9259 | 1.0000 | 1.0741 | 2.0000 |
| listwise set | 0.9319 | 1.0000 | 1.0681 | 2.0000 |

The cross-seed stress preserved top-10 recall and checked-stop-at-winner audits
on all 3 seed pairs with 0 invalid accepts and 0 permutation violations. It also
reinforces the negative result: strict improvement over the strongest pairwise
baseline occurred on 0 of 3 seed pairs, and mean verifier calls were worse than
the aggregate pairwise baseline.

## Model Audit

Receipt: [ZENO_ENERGY_MODEL_AUDIT.md](./ZENO_ENERGY_MODEL_AUDIT.md)

The gap-weighted checkpoint audit reports:

```text
parameters: 97
feature_dim: 96
nonzero_weight_count: 38
reserved_nonzero_count: 0
forbidden_feature_names: none
```

The largest positive weights are the hard verifier-shaped penalties inherited
from the hand initialization: negative reserves, CPMM invariant failures,
limit-price violations, balance violations, malformed fills, schema/policy
mismatches, and output mismatches. These raise energy and push candidates later.

The largest negative weights reward candidate quality signals:

```text
candidate_normalized_executed_volume: -58.0118
candidate_normalized_surplus: -28.7780
candidate_volume_log1p: -9.7421
candidate_surplus_signed: -7.6317
```

Negative weights lower energy and move candidates earlier. This audit supports
the intended interpretation: the trained model keeps hard invalidity barriers
large, then learns to prefer higher-volume and higher-surplus candidates among
valid-looking alternatives.

## Hard-Barrier Hybrid Ablation

The benchmark tooling now supports a hard-barrier hybrid order:

```text
sort_key(candidate) := (
  deterministic_hard_barrier_energy(candidate),
  learned_energy(candidate),
  candidate_hash(candidate)
)
```

The hard barrier includes verifier-shaped violations such as balance failures,
limit-price failures, negative reserves, CPMM invariant failures, malformed fill
vectors, schema/policy mismatches, output mismatches, and zero-net-input
candidates. It excludes soft hand-energy terms such as dust, imbalance,
executed-volume reward, and surplus reward.

Held-out JSONL comparison against the current gap-weighted model:

| mode | top_1 | top_5 | top_10 | mean_calls | p95 | p99 | invalid_accept |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| learned | 0.983 | 1.000 | 1.000 | 1.017 | 1 | 2 | 0 |
| hard-barrier hybrid | 0.983 | 1.000 | 1.000 | 1.017 | 1 | 2 | 0 |

A 200-batch live-generator sanity benchmark also tied learned ordering:
top-1 95.96%, top-5 100.0%, top-10 100.0%, mean winner position 1.040, p99 2,
and 0 invalid accepts for both modes.

Receipt:
[ZENO_ENERGY_FALLBACK_PERMUTATION_AUDIT.md](./ZENO_ENERGY_FALLBACK_PERMUTATION_AUDIT.md)

The updated 200-batch receipt also reports checked-stop audit rates. Learned and
hybrid ordering both had `stop_top_k = 1.000` at `top_k = 10`; random ordering
had `stop_top_k = 0.480`. This is an offline audit after suffix verification,
so it measures whether a deterministic suffix certificate would have justified
top-k stopping in those cases.

Top-k sweep receipt:
[ZENO_ENERGY_TOPK_SWEEP.md](./ZENO_ENERGY_TOPK_SWEEP.md)

On the 39,979-row holdout dataset, learned and hybrid ordering reached
`checked_stop_top_k = 1.000` by `k = 2`. Hand energy reached `0.996` at `k = 5`
and `1.000` at `k = 10`. Random ordering reached only `0.507` at `k = 10`.

Interpretation: the hard-barrier hybrid is a useful ablation and a conservative
order-key option. The current synthetic distribution shows no measured gain over
the gap-weighted learned score alone.

## Repair Selector

The deterministic neighborhood benchmark showed that local repair proposals
improve objective quality but add verifier work. The first repair selector tests
whether a tiny proposal scorer can keep the useful repairs while adding fewer
candidates.

Receipt:
[ZENO_ENERGY_REPAIR_SELECTOR.md](./ZENO_ENERGY_REPAIR_SELECTOR.md)

Cross-seed receipt:
[ZENO_ENERGY_REPAIR_SELECTOR_CROSS_SEED.md](./ZENO_ENERGY_REPAIR_SELECTOR_CROSS_SEED.md)

Held-out synthetic run, 120 train batches, 80 holdout batches, 35-parameter
linear selector:

| mode | candidates | added | best dominates full winner | mean calls to dominance | mean volume regret | invalid accepts |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| limited | 6.000 | 0.000 | 0.225 | 4.875 | 271.475 | 0 |
| full neighborhood | 16.275 | 10.275 | 0.963 | 1.675 | 3.200 | 0 |
| hand selected | 8.000 | 2.000 | 0.963 | 1.350 | 3.200 | 0 |
| learned selected | 8.000 | 2.000 | 0.963 | 1.312 | 3.200 | 0 |

The learned selector compresses full neighborhood expansion in this run, but it
does not beat the hand-selected two-proposal subset on mean volume regret. This
is useful negative knowledge: the current deterministic repair recipes are
simple enough that hand energy remains a strong proposal selector.

The three-seed stress run used 80 train batches and 60 holdout batches per seed
pair. Compression held on every seed pair:

```text
compression_pass_count: 3
compression_fail_count: 0
strict_hand_win_count: 1
strict_hand_win_fail_count: 2
invalid_accept_count: 0
original_subset_violation_count: 0
```

Aggregate learned-selected regret matched full neighborhood mean regret
(`5.937`) while reducing mean candidate count from `16.321` to `8.000`.

## AutoTrader Transfer

Receipt:
[AUTOTRADER_ENERGY_HARD_CROSS_SEED.md](./AUTOTRADER_ENERGY_HARD_CROSS_SEED.md)

The AutoTraderEnergy hard-profile benchmark uses synthetic candidate trading
plans and deterministic policy-guard labels. The scorer ranks candidates only.
Execution remains gated by budget, nonce, authorization, risk, provenance, and
route checks.

Three train/holdout seed pairs used 2,500 training contexts, 1,000 holdout
contexts, and 16 candidates per context. The trained model is a 21-parameter
linear energy scorer initialized from the hand-coded guard energy.

| mode | mean guard calls | top-1 recall | top-5 recall | invalid accepts |
| --- | ---: | ---: | ---: | ---: |
| random | 8.393 | 0.066 | 0.318 | 0 |
| hand energy | 4.312 | 0.217 | 0.694 | 0 |
| learned energy | 1.010 | 0.990 | 1.000 | 0 |

The learned ordering beat hand energy on every evaluated seed pair and kept
`invalid_accept_count_total = 0`. This is a transfer result for the advisory
pattern. Production-shadow observations are still required before treating the
AutoTrader utility estimate as release evidence.

### AutoTrader Shadow Bridge

Receipt:
[AUTOTRADER_ENERGY_SHADOW_BRIDGE.md](./AUTOTRADER_ENERGY_SHADOW_BRIDGE.md)

The shadow bridge converts recorded ZenoGraph AutoTrader shadow observations
into the same advisory energy row schema used by the synthetic AutoTraderEnergy
benchmark. The deterministic controller tag remains the validity label. The
ZenoGraph advisory and model score affect ordering and objectives only.

Command:

```bash
python3 tools/evaluate_autotrader_energy_shadow_bridge.py \
  --synthetic-train-contexts 1500 \
  --candidates-per-context 16 \
  --train-seed 20260528 \
  --epochs 5 \
  --learning-rate 0.001 \
  --margin 1.0 \
  --output-json data/upba_energy/autotrader_energy_shadow_bridge_baseline_seed20260528.json \
  --output-markdown docs/AUTOTRADER_ENERGY_SHADOW_BRIDGE.md
```

The built-in deterministic fixture produced 4 contexts, 20 rows, 12 valid
controller-submit candidates, and 8 deterministic rejections or skips.

| mode | mean guard calls | objective guard calls | exact top-1 | objective top-1 | top-5 | invalid accepts |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| random | 3.250 | 2.000 | 0.250 | 0.500 | 1.000 | 0 |
| hand energy | 2.000 | 1.000 | 0.000 | 1.000 | 1.000 | 0 |
| learned energy | 2.000 | 1.000 | 0.000 | 1.000 | 1.000 | 0 |

The bridge is nonvacuous as a schema and boundary replay: it includes both
valid and invalid controller outcomes, and `invalid_accept_count_total = 0`.
It also records useful metric knowledge. Exact top-1 recall is zero for hand
and learned ordering because the fixture has tied valid objective maxima and
the exact winner is selected by hash among equivalent argmax candidates.
Objective-equivalent top-1 recall is 1.000 for both hand and learned ordering.
The built-in fixture is not live production distribution evidence.

## Fallback And Checked Stop

Receipt:
[ZENO_ENERGY_FALLBACK_CHECKED_STOP_FORMAL.md](./ZENO_ENERGY_FALLBACK_CHECKED_STOP_FORMAL.md)

The formal boundary now records Lean-checked names for full-fallback
permutation equivalence, checked-stop certificates, and objective-equivalent
argmax representatives. The corresponding runtime receipts show zero
permutation violations in the fallback audit and top-k sweep.

```text
fallback audit learned top_10_recall: 1.0
fallback audit learned top_10_objective_recall: 1.0
fallback audit learned mean_calls_to_objective_winner: 1.01
fallback audit learned checked_stop_top_k_rate: 1.0
fallback audit learned permutation_violation_count: 0
top-k sweep learned k=2 checked_stop_top_k_rate: 1.0
top-k sweep learned k=2 false_exclusion_rate: 0.0
top-k sweep learned k=2 objective_false_exclusion_rate: 0.0
top-k sweep learned mean_objective_winner_position: 1.0166414523449319
top-k sweep objective_tie_batch_count: 1
```

These are finite-candidate-family results. Online early stop still requires a
deterministic suffix-bound certificate or full fallback.
The objective-equivalent metrics apply the formal tied-maxima boundary to the
runtime receipts without changing the exact verifier winner or validity
predicate.

## Objective-Equivalent Training Hygiene

Artifact:
[ZENO_ENERGY_OBJECTIVE_EQUIV_TRAINING_HYGIENE.md](./ZENO_ENERGY_OBJECTIVE_EQUIV_TRAINING_HYGIENE.md)

Static JSON:
`data/upba_energy/upba_v2_objective_equiv_training_hygiene_receipt.json`

The trainer now has an explicit positive-class switch:

```text
--positive-class hash-winner
--positive-class objective-equivalent
```

The second mode treats every verifier-accepted tied maximum-objective candidate
as positive for winner-pair weighting. Equal-objective tied pairs are still
skipped by the pairwise loss, so the learner avoids a spurious preference among
objective-equivalent candidates.

This is a training-target hygiene receipt. It does not claim a new benchmark
improvement until a new model artifact is trained and evaluated with this mode.

## Production Promotion Gate

Artifact:
[ZENO_ENERGY_PRODUCTION_GATE.md](./ZENO_ENERGY_PRODUCTION_GATE.md)

Static JSON:
`data/upba_energy/zenoenergy_production_promotion_gate_receipt.json`

Real-report builder:
[ZENO_ENERGY_REAL_REPLAY_REPORTS.md](./ZENO_ENERGY_REAL_REPLAY_REPORTS.md)

Replay source manifest:
[ZENO_ENERGY_REPLAY_SOURCE_MANIFEST.md](./ZENO_ENERGY_REPLAY_SOURCE_MANIFEST.md)

Replay source manifest builder:
[ZENO_ENERGY_REPLAY_SOURCE_MANIFEST_BUILDER.md](./ZENO_ENERGY_REPLAY_SOURCE_MANIFEST_BUILDER.md)

Production evidence bundle:
[ZENO_ENERGY_PRODUCTION_EVIDENCE_BUNDLE.md](./ZENO_ENERGY_PRODUCTION_EVIDENCE_BUNDLE.md)

Builder receipt:
`data/upba_energy/zenoenergy_real_replay_report_builder_receipt.json`

Manifest receipt:
`data/upba_energy/zenoenergy_replay_source_manifest_receipt.json`

Manifest builder receipt:
`data/upba_energy/zenoenergy_replay_source_manifest_builder_receipt.json`

Bundle receipt:
`data/upba_energy/zenoenergy_production_evidence_bundle_receipt.json`

The production gate currently reports:

```text
decision: blocked
promotion_allowed: false
blocked: missing real UPBA replay report
blocked: missing real AutoTrader shadow report
blocked: operator must explicitly enable advisory ranking-only promotion
```

The positive result is that the research replay obligation passes: current
fallback, invalid-accept, and PopperPad evidence is clean. The negative result
is now explicit and replayed: synthetic and fixture evidence cannot promote the
scorer to production ranking. Promotion requires broad real replay/shadow
reports with zero invalid accepts, deterministic replay, no live secrets, top-25
recall above threshold, and lower mean calls than hand energy.

The real-report builder converts replay outputs into the exact schemas consumed
by the gate, records source report hashes, and rejects obvious fixture or
synthetic source descriptors. It does not prove source custody by itself, so
replay provenance and secret-scrubbing evidence remain required.

The replay source manifest checker makes those provenance assertions replayable
inside the repo: real reports must carry a passing manifest check that binds
source kind, descriptor, market-day coverage, source-report hashes,
deterministic replay, and a clean secret scan.

The replay source manifest builder removes manual hash handling from operator
intake. It computes canonical source-report hashes, attaches replay and
secret-scan attestations, runs the checker, and writes the manifest only when
the check passes.

The production evidence bundle command composes the real-report builder, source
manifest checker, and promotion gate. It emits a single
`zenodex/energy/production_evidence_bundle/v1` artifact for operator review.
A malformed source manifest or missing attestation fails closed. Insufficient
but well-formed evidence still produces `decision: blocked`.

The replay gate
[ZENO_ENERGY_RESEARCH_EVIDENCE_REPLAY.md](./ZENO_ENERGY_RESEARCH_EVIDENCE_REPLAY.md)
checks the set-aware comparison, listwise set-ranker comparison, neighborhood
benchmark, repair selector, listwise cross-seed stress, gap-weighted default,
cross-seed stress, AutoTraderEnergy hard cross-seed transfer, AutoTraderEnergy
shadow bridge, objective-equivalence formal boundary, fallback/top-k receipts,
objective-equivalent training hygiene, the production promotion gate, the replay
source manifest checker, the replay source manifest builder, the real replay
report builder, the production evidence bundle, and PopperPad status ledger. It
also checks
the SOTA decision-map receipt:
[ZENO_ENERGY_SOTA_DECISION_MAP.md](./ZENO_ENERGY_SOTA_DECISION_MAP.md).
The current receipt reports 131 passing checks and 0 failed checks, including
the PopperPad doctor check.

## Accuracy

With deterministic fallback enabled, ranked search returns the same verifier
winner as exhaustive search. The model only changes candidate order.

```text
accepted(candidate) := deterministic_verifier(candidate)
```

The Lean theorems
`full_fallback_equivalent_order_preserves_membership_iff` and
`full_fallback_equivalent_order_preserves_weak_optimality_iff` formalize the
order-only claim for full fallback:

```text
ordered.Perm(candidates)
-> (winner in ordered <-> winner in candidates)
-> (WeaklyOptimalIn(winner, ordered) <-> WeaklyOptimalIn(winner, candidates))
```

If the fallback path checks every original candidate exactly as a permutation,
the ranked order and exhaustive order have the same audited weak-optimality
surface.

The benchmark report now includes `permutation_violation_count` for each order
mode so this Lean premise is checked during empirical runs. The shared runtime
helper is `candidate_orders_are_hash_permutation`.

A low energy score never authorizes a settlement. If the top-k ranked prefix
misses the winner, the harness continues into deterministic fallback and checks
the remaining candidates.

Safe early stop has a separate proof boundary. The Lean definition
`CheckedStopCertificate` requires the current winner to dominate both the
checked candidates and a certified unchecked suffix bound. The theorem
`checked_stop_certificate_with_exact_full_implies_global_weak_optimal` proves
that such a certificate is enough to stop before full fallback when the full
candidate list remains exact. The helper
`verified_checked_stop_certificate_holds` audits this condition over already
verified results, which is useful for receipts and regression tests.

Top-k without fallback is an empirical accelerator. On this holdout set,
top-10 recall was 100%. That is benchmark evidence, and it does not prove
top-k completeness.

The benchmark's `mean_verifier_calls` metric is the position of the known
verifier winner in the proposed order. Online early stopping needs either an
optimality certificate for the checked candidate or a deterministic fallback that
checks the remaining candidates.

## Acceptance Check

```text
gap_weighted_top_10_recall >= 95%: pass (100%)
gap_weighted_mean_verifier_calls <= 50% of exhaustive: pass (1.017 <= 10.00 on heldout)
gap_weighted beats hand-coded energy by >= 10%: pass (about 25% on heldout mean calls)
invalid_accept_count = 0: pass
fallback recovers exact winner when top_k fails: pass in benchmark harness
```

## Caveats

The result is synthetic and bounded. It supports keeping ZenoEnergy v0 as a
research-only search accelerator. It does not establish production optimality
for UPBA v2, and it does not add a consensus claim.

Recommendation: keep the isolated scorer and benchmark harness, with the
gap-weighted checkpoint as the current research default. Next work should train
the listwise set ranker, train the repair selector on outcome-level labels,
refresh hard negatives, prototype a dominance-cover certificate, and compare
against a finalized v2 bounded-grid optimality verifier.
