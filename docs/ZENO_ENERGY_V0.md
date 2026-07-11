# ZenoEnergy v0

ZenoEnergy v0 is an isolated research scorer for UPBA v2 partial-fill exact-in
candidate search. It ranks candidate certificates before deterministic checking.
The deterministic UPBA verifier remains the settlement authority.

Research paper: [Verifier-Preserving Learned Candidate Ordering for UPBA v2 Settlement Search](./papers/zenoenergy-v0/paper.md)

Academic PDF: [ZenoEnergy: Verifier-Preserving Learned Candidate Ordering for UPBA v2 Settlement Search](./papers/zenoenergy-v0/zenoenergy-v0.pdf)

Academic state-of-the-art notes: [ZenoEnergy State Of The Art Notes](./ZENO_ENERGY_STATE_OF_THE_ART.md)

SOTA decision map: [ZenoEnergy SOTA Decision Map](./ZENO_ENERGY_SOTA_DECISION_MAP.md)

Set-aware ranker extension: [ZenoEnergy Set-Aware Ranker](./ZENO_ENERGY_SET_AWARE_RANKER.md)

Listwise set-ranker experiment: [ZenoEnergy Listwise Set Ranker](./ZENO_ENERGY_LISTWISE_SET_RANKER.md)

Listwise cross-seed stress: [ZenoEnergy Listwise Set Ranker Cross-Seed Stress](./ZENO_ENERGY_LISTWISE_SET_RANKER_CROSS_SEED.md)

Synthetic candidate coverage audit: [ZenoEnergy Synthetic Candidate Coverage](./ZENO_ENERGY_SYNTHETIC_CANDIDATE_COVERAGE.md)

Neighborhood repair benchmark: [ZenoEnergy Neighborhood Repair](./ZENO_ENERGY_NEIGHBORHOOD_REPAIR.md)

Learned repair-selector benchmark: [ZenoEnergy Repair Selector](./ZENO_ENERGY_REPAIR_SELECTOR.md)

Repair-selector cross-seed stress: [ZenoEnergy Repair Selector Cross-Seed Stress](./ZENO_ENERGY_REPAIR_SELECTOR_CROSS_SEED.md)

AutoTrader transfer receipt: [AutoTraderEnergy Hard Cross-Seed Receipt](./AUTOTRADER_ENERGY_HARD_CROSS_SEED.md)

AutoTrader shadow bridge receipt: [AutoTraderEnergy Shadow Bridge Receipt](./AUTOTRADER_ENERGY_SHADOW_BRIDGE.md)

Fallback and checked-stop formal boundary: [ZenoEnergy Fallback And Checked-Stop Formal Boundary](./ZENO_ENERGY_FALLBACK_CHECKED_STOP_FORMAL.md)

Dominance-cover runtime prototype: [ZenoEnergy Dominance Cover](./ZENO_ENERGY_DOMINANCE_COVER.md)

WES dominance search bridge: [ZenoEnergy WES Dominance Search](./ZENO_ENERGY_WES_DOMINANCE_SEARCH.md)

Dominance-prefix audit: [ZenoEnergy Dominance-Prefix Cover](./ZENO_ENERGY_DOMINANCE_PREFIX.md)

Suffix-bound early stop: [ZenoEnergy Suffix-Bound Early Stop](./ZENO_ENERGY_SUFFIX_BOUND.md)

Suffix-bound cross-seed stress: [ZenoEnergy Suffix-Bound Cross-Seed Stress](./ZENO_ENERGY_SUFFIX_BOUND_CROSS_SEED.md)

Suffix-bound adversarial stress: [ZenoEnergy Suffix-Bound Adversarial Stress](./ZENO_ENERGY_SUFFIX_BOUND_ADVERSARIAL_STRESS.md)

Suffix-bound adversarial family stress: [ZenoEnergy Suffix-Bound Adversarial Family Stress](./ZENO_ENERGY_SUFFIX_BOUND_ADVERSARIAL_FAMILY_STRESS.md)

Negative curriculum and epiplexity proxy: [ZenoEnergy Negative Curriculum](./ZENO_ENERGY_NEGATIVE_CURRICULUM.md)

Negative-curriculum ranker probe: [ZenoEnergy Curriculum Ranker](./ZENO_ENERGY_CURRICULUM_RANKER.md)

Synthetic data scaling: [ZenoEnergy Synthetic Data Scaling](./ZENO_ENERGY_DATA_SCALING.md)

Synthetic quality selection: [ZenoEnergy Quality Selection](./ZENO_ENERGY_QUALITY_SELECTION.md)

Best retained models: [ZenoEnergy Best Model Registry](./ZENO_ENERGY_BEST_MODELS.md)

Epiplexity literature boundary: [ZenoEnergy Epiplexity Literature Note](./ZENO_ENERGY_EPIPLEXITY_LITERATURE.md)

Energy-order-alone formal boundary: [ZenoEnergy Energy-Order-Alone Formal Boundary](./ZENO_ENERGY_ENERGY_ORDER_ALONE_FORMAL.md)

Research evidence replay gate: [ZenoEnergy Research Evidence Replay](./ZENO_ENERGY_RESEARCH_EVIDENCE_REPLAY.md)

Replay source manifest: [ZenoEnergy Replay Source Manifest](./ZENO_ENERGY_REPLAY_SOURCE_MANIFEST.md)

Replay source manifest builder: [ZenoEnergy Replay Source Manifest Builder](./ZENO_ENERGY_REPLAY_SOURCE_MANIFEST_BUILDER.md)

Replay secret scan: [ZenoEnergy Replay Secret Scan](./ZENO_ENERGY_REPLAY_SECRET_SCAN.md)

Replay coverage profile: [ZenoEnergy Replay Coverage Profile](./ZENO_ENERGY_REPLAY_COVERAGE_PROFILE.md)

Real replay report builder: [ZenoEnergy Real Replay Reports](./ZENO_ENERGY_REAL_REPLAY_REPORTS.md)

Production evidence bundle: [ZenoEnergy Production Evidence Bundle](./ZENO_ENERGY_PRODUCTION_EVIDENCE_BUNDLE.md)

Research log and evidence refs: [ZenoEnergy Research Log](./ZENO_ENERGY_RESEARCH_LOG.md)

```text
Model proposes; verifier decides.
```

The scorer may change candidate order. It may not authorize settlement, mutate
ledger state, enter state roots, replace certificate verification, or change
validity predicates.

## Boundary

The dependency direction is one-way:

```text
src.energy -> src.core.uniform_batch_clearing
src.core.uniform_batch_clearing -/-> src.energy
```

Energy code may import UPBA verifier APIs for labels, safety tests, and
benchmarks. UPBA verifier modules do not import `src.energy`.

Feature extraction defaults to `include_verifier_label=False`, so ranking does
not require an exact verifier call. Dataset generation explicitly enables
verifier labels for offline training and evaluation.

## Modules

- `src/energy/upba_v2_features.py`: fixed 96-dimensional normalized feature schema plus raw advisory diagnostics.
- `src/energy/upba_v2_hand_energy.py`: deterministic hand-coded energy baseline.
- `src/energy/upba_v2_energy_model.py`: optional PyTorch MLP builder and no-dependency linear ranker.
- `src/energy/upba_v2_ensemble.py`: tiny linear-model ensemble helpers for rank consensus and disagreement diagnostics.
- `src/energy/upba_v2_listwise_set_ranker.py`: deterministic candidate-list context features and top-one listwise softmax training helper.
- `src/energy/upba_v2_ranker.py`: ranking, verifier-backed search reports, and deterministic fallback helpers.
- `src/energy/upba_v2_dominance_cover.py`: runtime dominance-cover certificates and ranked-prefix dominance audits for verified finite candidate lists.
- `src/energy/upba_v2_suffix_bound.py`: deterministic suffix-bound certificates for advisory early stop over finite ranked candidate lists.
- `src/energy/upba_v2_neighborhood.py`: deterministic repair and neighborhood proposal helpers.
- `src/energy/upba_v2_repair_selector.py`: tiny advisory selector features and ranking for deterministic neighborhood proposals.
- `src/energy/autotrader_energy.py`: synthetic AutoTrader advisory energy rows, hand scorer, linear ranker, and guard-call evaluator.

## Tools

- `tools/generate_upba_energy_dataset.py`: synthetic batch generator with verifier-backed labels.
- `tools/audit_upba_energy_synthetic_coverage.py`: deterministic coverage audit for synthetic candidate classes, hard negatives, feature dimensions, and synthetic-only provenance.
- `tools/train_upba_energy.py`: pairwise hinge training for the no-dependency linear ranker.
- `tools/evaluate_upba_energy.py`: dataset-level top-k, objective-equivalent top-k, and verifier-call evaluation.
- `tools/benchmark_upba_energy_search.py`: compares exhaustive, deterministic hash ordering, hand energy, and learned energy with exact and objective-equivalent winner metrics.
- `tools/check_zenoenergy_replay_source_manifest.py`: validates replay source manifests, source hashes, deterministic replay attestations, and clean secret scans for real evidence.
- `tools/check_zenoenergy_replay_secret_scan.py`: scans replay reports for obvious key material and sensitive JSON keys before manifest packaging.
- `tools/check_zenoenergy_replay_coverage_profile.py`: validates real replay breadth across UPBA and AutoTrader coverage families before promotion.
- `tools/build_zenoenergy_replay_source_manifest.py`: computes source report hashes and writes replay source manifests only after validation passes.
- `tools/build_zenoenergy_real_replay_report.py`: validates real replay/shadow receipts and emits the schemas consumed by the production promotion gate.
- `tools/build_zenoenergy_production_evidence_bundle.py`: assembles source-manifested and coverage-profiled UPBA and AutoTrader real reports, then runs the production promotion gate in one fail-closed review command.
- `tools/stress_upba_energy_cross_seed.py`: streams cross-seed, multi-candidate-count stress benchmarks without storing every generated row.
- `tools/mine_upba_energy_hard_cases.py`: streams larger synthetic runs and records compact examples where learned ordering misses top-1/top-5/top-10.
- `tools/inspect_upba_energy_model.py`: audits trained linear checkpoints for top weights, reserved-feature use, and label-like feature names.
- `tools/sweep_upba_energy_topk.py`: sweeps top-k recall, objective-equivalent top-k recall, and offline checked-stop audit rates over stored dataset rows.
- `tools/compare_upba_energy_set_aware.py`: compares aggregate and set-aware rankers on fresh synthetic train/holdout splits and emits a small evidence report.
- `tools/compare_upba_energy_listwise_set_ranker.py`: compares a listwise set-context ranker against pairwise linear baselines.
- `tools/stress_upba_energy_listwise_set_ranker.py`: retrains and evaluates the listwise set-context ranker across train/holdout seed pairs.
- `tools/benchmark_upba_energy_neighborhood.py`: compares limited candidate budgets against deterministic neighborhood-expanded budgets.
- `tools/check_upba_v2_dominance_cover.py`: checks dominance-cover receipts over bounded synthetic verified full lists.
- `tools/check_upba_v2_dominance_prefix.py`: audits how many ranked verifier calls are needed before a dominance-cover certificate exists.
- `tools/check_upba_v2_suffix_bound.py`: benchmarks deterministic early stop with checked-prefix dominance and unchecked-suffix objective bounds.
- `tools/stress_upba_v2_suffix_bound.py`: reruns suffix-bound early stop across seeds and candidate-count grids.
- `tools/stress_upba_v2_suffix_bound_adversarial.py`: injects high-declared-output invalid unchecked suffix candidates and compares deterministic disqualifiers against declared-output-only bounds.
- `tools/stress_upba_v2_suffix_bound_adversarial_families.py`: injects multiple verifier-invalid unchecked suffix families and checks deterministic disqualifier coverage.
- `tools/zenoenergy_negative_curriculum.jl`: turns adversarial-family stress into hard-negative sampling weights plus a bounded epiplexity proxy for training-data steering.
- `tools/benchmark_upba_energy_curriculum.py`: trains a bounded rare-disqualifier curriculum ranker and compares it against the gap-weighted default.
- `tools/benchmark_upba_energy_data_scaling.py`: trains the same gap-weighted setup over increasing same-generator synthetic batch budgets and records saturation.
- `tools/benchmark_upba_energy_quality_selection.py`: compares raw winner-bearing synthetic batches against current-model-hard winner-bearing batches at matched budgets.
- `tools/benchmark_upba_energy_ensemble.py`: trains small diversified advisory rankers and compares mean-energy and rank-consensus ensemble orderings.
- `tools/preserve_zenoenergy_best_models.py`: copies or deterministically regenerates the retained advisory checkpoints and writes the best-model registry with sha256 hashes.
- `tools/check_zenoenergy_epiplexity_literature.py`: checks the epiplexity literature note, required sources, task-relevance gate, and proxy boundary.
- `tools/run_zenoenergy_wes_dominance_search.py`: feeds dominance-cover candidate claims into WES while UPBA verification supplies labels.
- `tools/benchmark_upba_repair_selector.py`: trains and benchmarks a 35-parameter linear proposal selector over deterministic neighborhood repairs.
- `tools/stress_upba_repair_selector.py`: retrains and evaluates the repair selector across train/holdout seed pairs.
- `tools/benchmark_autotrader_energy_cross_seed.py`: trains and evaluates a tiny AutoTraderEnergy scorer across synthetic train/holdout seed pairs.
- `tools/evaluate_autotrader_energy_shadow_bridge.py`: converts ZenoGraph AutoTrader shadow observations into advisory energy rows and evaluates hand/learned ordering while deterministic policy guards remain authoritative.
- `tools/check_zenoenergy_research_evidence.py`: replays committed ZenoEnergy research receipts, failing closed on missing evidence or drift.
- `tools/check_zenoenergy_production_promotion.py`: fail-closed advisory ranking promotion gate requiring clean research replay, real UPBA replay, real AutoTrader shadow coverage, and explicit operator enablement.

## Hand Energy

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

Lower energy means the candidate should be checked earlier. The formula is
advisory and has no settlement authority.

The hand scorer also exposes a named energy breakdown and a primary failure
term. This follows the reasoning-energy principle that a useful energy should
help locate which constraint is broken while assigning a scalar priority.

## Model

The repository can build the requested MLP shape when PyTorch is installed:

```text
96 -> 64 -> 1
```

The correct parameter count is:

```text
96*64 + 64 + 64*1 + 1 = 6_273
```

The no-dependency default path trains a 96-weight linear energy model with one
bias parameter. This keeps the default experiment CPU-only and dependency-light.
The trainer also supports gap-weighted pairwise updates, which give extra weight
to batch winners and to larger valid-vs-valid objective gaps. New research runs
can select `--positive-class objective-equivalent` so all verifier-accepted
tied maximum-objective candidates receive winner-pair pressure against lower
candidates. The default `hash-winner` mode remains for artifact replay.

Evaluation and benchmark tools also support a hard-barrier hybrid order:

```text
hard verifier-shaped barrier -> learned energy -> candidate hash
```

The hybrid barrier excludes soft hand-energy objective terms, so it preserves a
deterministic malformed-candidate barrier while letting the learned model order
valid-looking candidates.

The current research artifacts include three linear checkpoints:

- `data/upba_energy/upba_v2_energy_linear_seed20260517.json`: first hard-negative run.
- `data/upba_energy/upba_v2_energy_linear_objective_tuned_seed20260517.json`: longer training run with replay-gated safety and hand-baseline improvement, but no strict win over gap-weighted.
- `data/upba_energy/upba_v2_energy_linear_gap_weighted_seed20260517.json`: current preferred research checkpoint, with winner-pair and objective-gap weighting.

Model audit receipt:
[ZENO_ENERGY_MODEL_AUDIT.md](./ZENO_ENERGY_MODEL_AUDIT.md)

## Safety Contract

```text
LowEnergy(candidate) ∧ ¬VerifierAccepts(candidate) -> SettlementRejected
```

A low model energy never creates an accepted settlement. The implementation
tests adversarial low-energy invalid candidates, missing-model fallback,
state-root independence, dependency direction, and order-only behavior.

## Candidate Generation

Synthetic candidate generation is valid for research when it is treated as a
finite candidate-domain generator, then every generated candidate is labeled by
the deterministic verifier. It becomes a mathematical optimality claim only when
the generated candidate list is exact for the family under discussion:

```text
GeneratedCorpusExact(generated, Feasible) :=
  CompleteAuditSet(generated, Feasible) ∧ SoundAuditSet(generated, Feasible)
```

The Lean theorem
`generated_corpus_exact_upper_bound_certificate_implies_global_weak_optimal`
formalizes that contract. The theorem
`upba_v2_advisory_reordered_partial_fill_bounded_grid_certificate_implies_global_weak_optimal`
formalizes the advisory-order rule: an energy scorer may permute an exact UPBA
v2 bounded-grid partial-fill candidate set, and the deterministic verifier
certificate still proves the same bounded optimum.

The theorem
`upba_v2_hard_barrier_hybrid_reordered_partial_fill_bounded_grid_certificate_implies_global_weak_optimal`
records the same proof surface for the hard-barrier hybrid order. Its only
ordering obligation is still permutation of the exact candidate set.

The repair-selector theorem
`advisory_selected_repair_set_upper_bound_certificate_implies_base_weak_optimal`
records the smaller proposal-set boundary: a selected repair set may shrink the
neighborhood, but if it preserves the base candidate list and the deterministic
verifier supplies an upper-bound certificate over the selected set, the winner
is weakly optimal over the preserved base list.

The theorem
`full_fallback_equivalent_order_preserves_membership_iff` captures winner
presence under full fallback, and
`full_fallback_equivalent_order_preserves_weak_optimality_iff` captures audited
weak optimality under the same fallback rule used in the benchmark harness:

```text
FullFallbackEquivalentOrder(candidates, ordered) := ordered.Perm candidates
```

If fallback checks a permutation of the original finite candidate list, audited
weak optimality is identical in the ranked order and the original exhaustive
order. The runtime helper `candidate_orders_are_hash_permutation` checks the
hash-multiset version of this obligation.

Tied maxima have a quotient-style boundary. `ObjectiveEquivalent` means two
candidates have the same volume and surplus. The theorem
`objective_equivalent_reordered_exact_upper_bound_certificate_implies_global_weak_optimal`
proves that if a deterministic certificate selects one representative of the
tied objective class, another verifier-accepted candidate with the same
objective is also globally weakly optimal over the exact finite candidate
family.

Early stopping has a stronger proof obligation. The Lean definition
`CheckedStopCertificate` requires:

```text
winner in checked
WeaklyOptimalIn(winner, checked)
WeaklyOptimalIn(winner, unchecked_suffix)
```

The theorem
`checked_stop_certificate_with_exact_full_implies_global_weak_optimal` then
lifts this checked-stop certificate to global weak optimality when the full
candidate list is an exact audit set and `checked ++ unchecked_suffix` is a
permutation of that full list. This is the math boundary for stopping before
full fallback. The runtime helper
`verified_checked_stop_certificate_holds` audits the same dominance condition
over already verified results for offline receipts. Benchmark receipts expose
this as `checked_stop_top_k_rate` and `checked_stop_at_winner_rate`.

## Dominance Pruning

Dominance pruning is now represented by a runtime research certificate over a
verified finite full list. A pruned list may replace the full bounded candidate
list when every full-domain candidate has a retained representative that is
weakly at least as good by volume first and surplus second:

```text
DominanceCover(pruned, full) :=
  forall candidate in full,
    exists representative in pruned,
      WeaklyDominates(representative, candidate)
```

The theorem
`upba_v2_dominance_pruned_partial_fill_bounded_grid_certificate_implies_global_weak_optimal`
formalizes the UPBA v2 contract:

```text
full bounded-grid coverage
∧ pruned candidates are feasible
∧ pruned dominates full
∧ verifier upper-bound certificate over pruned
-> bounded global weak optimum over the original UPBA v2 candidate family
```

This gives a proof path for reducing verifier work before applying any learned
ranking. The current runtime prototype checks the finite-list premise and
records the remaining bounded-grid obligation explicitly.

Current bounded synthetic receipt:

```text
winner_only: 79 / 79 dominance-cover certificates pass
weak_pruned: 75 / 75 weak-pruning negative controls fail
hand_top1:   56 / 79 hand-energy top-1 pruning attempts pass
```

The WES bridge imports `external/WitnessEnergySearch` as an external research
tool and ranks dominance-cover candidate claims. WES can change checker order,
while UPBA verification and the dominance-cover checker decide labels. The
static WES receipt used WES commit
`5a26bcc1d97c90503bb66e67c7c2a2cf40d41bb6`, checked 60 of 120 candidates, and
put a useful dominance-cover result in the first checked slot for the learned,
frozen, declared-priority, cheap-first, and input-order policies. Random seeded
ordering reached its first useful result on the second checked slot.

The result is a search and certificate-format prototype. A production or
bounded-grid claim still needs a separate proof that the supplied full list is
complete for the intended UPBA v2 candidate family.

The dominance-prefix audit connects the certificate to ranked search cost. On
the committed bounded synthetic run, learned and hybrid orderings reached a
dominance-cover certificate after the first checked candidate in all 119
evaluated batches. Hand energy averaged 1.445 checked candidates, while random
ordering averaged 12.882 and reached full fallback in 5 batches.

This is still an offline audit over verified finite lists. It supports the
ranking objective and certificate plumbing, while live early stop still needs a
verifier-facing unchecked-suffix bound or deterministic full fallback.

The suffix-bound early-stop prototype closes that specific runtime gap for a
finite generated list. A checked verifier winner may stop before full fallback
only when it dominates the checked prefix and every unchecked candidate has a
deterministic objective upper bound no better than the winner. The committed
bounded synthetic benchmark reports learned and hybrid mean verifier calls of
1.0084, p99 of 1, zero invalid accepts, and zero full fallback cases over 119
evaluated batches.

The cross-seed suffix-bound stress extends this to nine bounded synthetic
configs, 3 seeds by 3 candidate counts. Learned and hybrid orderings keep
objective-equivalent acceptance and suffix-stop rates at 1.0, with zero invalid
accepts and mean verifier calls of 1.0132. This is stronger distribution
evidence for the current synthetic generator, while the candidate-family
coverage and real replay requirements still stand.

The adversarial suffix stress injects high-declared-output invalid candidates
into the unchecked suffix after the verifier winner is checked. With
deterministic disqualifiers, all 119 evaluated certificates pass. With
declared-output-only bounds, all 119 certificates fail. This records a concrete
negative result: suffix bounds need verifier-derived deterministic invalidity
signals, not raw declared outputs alone.

The adversarial family stress extends that check to 944 verifier-invalid cases
across 8 invalidity families: high declared output, negative reserve, limit
violation, fill coverage, all-zero fill vector, price objective, schema/policy,
and output mismatch. Every case is deterministically disqualified and every
with-disqualifier suffix certificate passes. High-declared-output cases still
fail under declared-output-only bounds.

This remains scoped to the supplied finite candidate family. Production
bounded-grid claims still require candidate-family coverage, and real replay is
still required before promotion.

## Neighborhood Repair

Deterministic repair proposals can expand a limited search budget by
canonicalizing, clamping, snapping, and locally stepping fill vectors around
seed candidates:

```text
limited candidates subset-of neighborhood-augmented candidates
```

The Lean definition `CandidateSubset` records this proof surface, and
`augmented_superset_upper_bound_certificate_implies_base_weak_optimal` proves
that a verifier upper-bound certificate over the augmented list also dominates
the preserved base list. This is a base-list dominance guarantee. It becomes a
bounded-grid optimality guarantee only when the augmented list is exact for the
full feasibility family or carries a dominance-cover certificate.
