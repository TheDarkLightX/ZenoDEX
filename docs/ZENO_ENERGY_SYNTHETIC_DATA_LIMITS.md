# ZenoEnergy Synthetic Data Limits

Date: 2026-05-19

This note records the academic boundary for using synthetic verifier-labeled
data in ZenoEnergy. It is a research and promotion-gate guide. It does not make
a production, settlement, consensus, or correctness claim.

## Core Claim

Synthetic data is useful for ZenoEnergy when it expands coverage over the formal
candidate family and every label is produced by the deterministic verifier or
policy gate. It is weak evidence when it repeats one generator, replaces real
replay, or recycles model outputs without independent checks.

For ZenoDEX:

```text
SyntheticCandidate(ctx) + VerifierLabel(ctx, candidate)
-> usable_training_row
```

The training row is useful for ranking research. It does not authorize a
settlement, prove bounded-grid completeness, or establish production
distribution coverage.

## Literature Lessons

### Recursive Synthetic Data Can Collapse

Shumailov et al. show that training on recursively generated data can produce
model collapse, with tails of the original distribution disappearing. The key
ZenoEnergy rule is to avoid self-consuming loops where the ranker creates the
training distribution and its own outputs replace verifier-labeled or replayed
data.

Alemohammad et al. reach a similar warning for self-consuming generative image
loops: without enough fresh real data, later models lose quality or diversity.
Seddik et al. give a statistical analysis in language-model settings and argue
that synthetic-only recursion cannot avoid collapse, while bounded mixes of real
and synthetic data can avoid it under some assumptions.

### Accumulation And Mixing Help

Gerstgrasser et al. refine the collapse story: replacing original data with
synthetic generations tends toward collapse, while accumulating real data and
successive synthetic data can avoid unbounded collapse in their analyzed and
empirical settings.

For ZenoEnergy, the practical rule is:

```text
real_replay_retained
and synthetic_data_has_source_family_tags
and verifier_labels_are_fresh
and heldout_metrics_improve
-> synthetic_curriculum_supported_for_research
```

Synthetic data may grow the corpus, but the old replay and seed families should
remain available for regression checks.

### Simulation Helps When Coverage Is Designed

Domain randomization shows that synthetic or simulated data can transfer when
the generator deliberately covers relevant variation. Learned optimization
work also supports the same shape: learned policies can guide solver search,
while exact solvers preserve validity.

ZenoEnergy should therefore use synthetic data to cover:

- balance cliffs;
- limit-price cliffs;
- invariant and reserve cliffs;
- noncanonical fill vectors;
- near-tie valid candidates;
- valid high-volume candidates with adverse surplus;
- output-mismatch and suffix-bound adversaries;
- live-like market regimes from replay summaries.

The generator should be treated as a hypothesis about deployment conditions,
then challenged by cross-seed, hard-case, adversarial-family, and real-replay
gates.

## Operational Rules

1. Never use model outputs as authoritative labels. Labels come from the
   verifier, policy gate, or replayed deterministic artifact.
2. Do not replace real replay with synthetic data. Synthetic evidence remains
   research-grade until source manifests, coverage profiles, and real replay
   gates pass.
3. Require seed and regime separation. Training and holdout corpora must differ
   by seed, candidate count, and hard-negative families.
4. Track rare-tail coverage. Report family counts and miss counts, not only
   aggregate accuracy.
5. Reject proxy-only promotion. Epiplexity, compression gain, and diversity
   scores can steer data selection, but heldout verifier-call and top-k metrics
   decide whether a curriculum helped.
6. Preserve deterministic fallback. A better ranker changes check order only;
   validity and accepted settlement remain verifier decisions.

## ZenoEnergy Gate

```text
SyntheticResearchSupported :=
  verifier_labels_fresh
  and cross_seed_top10_recall_min = 1
  and invalid_accept_count_total = 0
  and permutation_violation_count_total = 0
  and hard_case_top5_miss_count = 0
  and promoted_default_beaten_on_mean_calls
```

Production-adjacent promotion requires real replay on top:

```text
ProductionPromotionAllowed :=
  SyntheticResearchSupported
  and real_upba_replay_report_ok
  and real_autotrader_shadow_report_ok
  and source_manifest_ok
  and secret_scan_ok
  and coverage_profile_ok
```

Current v6 evidence satisfies the research-ranker promotion gate against the
retained linear checkpoints. It does not satisfy the production promotion gate
because real-replay evidence is still missing.

## Sources

- Ilia Shumailov, Zakhar Shumaylov, Yiren Zhao, Yarin Gal, Nicolas Papernot,
  and Ross Anderson. [The Curse of Recursion: Training on Generated Data Makes
  Models Forget](https://arxiv.org/abs/2305.17493), arXiv 2305.17493, 2023.
- Ilia Shumailov et al. [AI models collapse when trained on recursively
  generated data](https://www.nature.com/articles/s41586-024-07566-y),
  Nature 631, 755-759, 2024.
- Sina Alemohammad et al. [Self-Consuming Generative Models Go
  MAD](https://arxiv.org/abs/2307.01850), arXiv 2307.01850, 2023.
- Mohamed El Amine Seddik, Suei-Wen Chen, Soufiane Hayou, Pierre Youssef, and
  Merouane Debbah. [How Bad is Training on Synthetic Data? A Statistical
  Analysis of Language Model Collapse](https://arxiv.org/abs/2404.05090),
  arXiv 2404.05090, 2024.
- Matthias Gerstgrasser et al. [Is Model Collapse Inevitable? Breaking the
  Curse of Recursion by Accumulating Real and Synthetic
  Data](https://arxiv.org/abs/2404.01413), arXiv 2404.01413, 2024.
- Josh Tobin et al. [Domain Randomization for Transferring Deep Neural Networks
  from Simulation to the Real World](https://arxiv.org/abs/1703.06907), arXiv
  1703.06907, 2017.
- Yoshua Bengio, Andrea Lodi, and Antoine Prouvost. [Machine Learning for
  Combinatorial Optimization: a Methodological Tour
  d'Horizon](https://arxiv.org/abs/1811.06128), arXiv 1811.06128, 2018.
- Yang Song and Diederik P. Kingma. [How to Train Your Energy-Based
  Models](https://arxiv.org/abs/2101.03288), arXiv 2101.03288, 2021.
