# ZenoEnergy Epiplexity Literature Note

Date: 2026-05-19

This note records how the new epiplexity literature should affect
ZenoEnergy. It is a research guide for data selection and curriculum design.
It does not create a verifier, settlement, production, or consensus claim.

## Core Reading

Finzi, Qiu, Jiang, Izmailov, Kolter, and Wilson introduce epiplexity as
learnable structural information for computationally bounded observers:

```text
epiplexity := structure a bounded observer can extract
time-bounded entropy := residual content the observer cannot predict or compress
```

For ZenoEnergy, the bounded observer is the advisory ranker plus its feature
schema, training budget, and candidate generator. The data is the candidate
corpus with verifier labels and disqualifier families.

## Transfer To ZenoEnergy

The useful mapping is:

```text
observer T       := tiny ranker + feature extractor + bounded training loop
data X           := verifier-labeled candidate batches
structure S_T(X) := features and labels that reduce verifier calls out of sample
entropy H_T(X)   := noise, random tie-breaking, or structure outside the feature class
```

This makes epiplexity a data-selection tool. It helps decide whether synthetic
or replay corpora contain enough structured, learnable failure modes to justify
training another scorer.

## Current Proxy

The committed Julia curriculum lane reports:

```text
source: data/upba_energy/zenoenergy_negative_curriculum_seed20260545.json
classification: measurable_bounded_structure
score: 0.358265
label_entropy_bits: 2.866122
policy_separation: 0.375000
rare_label_headroom: 0.900498
```

This is a bounded proxy over one adversarial-family corpus. It combines label
diversity with separation between certificates that include deterministic
disqualifiers and certificates that omit them.

The proxy is useful because `output_mismatch_count` is rare in the current
hard-negative receipt and receives the strongest sampling weight. The next
curriculum-trained model should oversample rare deterministic disqualifiers,
then prove usefulness with cross-seed verifier-call reduction and top-k recall.

## Task-Relevance Gate

The strongest literature caveat is that total learned structure can separate
from task-relevant structure. The May 2026 controlled counterexample to strong
proxy-based explanations shows that a structure proxy need not agree with OOD
probe performance.

ZenoEnergy therefore uses this gate:

```text
EpiProxy(D) high
∧ task_metric_improves(D, heldout)
∧ safety_boundary_clean
-> curriculum_supported_for_research
```

The proxy alone cannot support a model promotion. The task metric must be
ZenoEnergy-specific: mean verifier calls, p95/p99 verifier calls, top-k recall,
regret before fallback, invalid accepts, and deterministic fallback recovery.

## Operational Rules

- Use epiplexity proxies to select, transform, and order training corpora.
- Report the observer budget: feature schema, model family, training budget,
  candidate generator, and seed set.
- Separate general structure from task-relevant structure.
- Require heldout and cross-seed ranking metrics before treating a curriculum
  as useful.
- Keep deterministic UPBA verification and suffix-bound certificates as the
  safety boundary.
- Treat compression-gain or MDL-style quantities as companion diagnostics when
  true latent structure is unavailable.

## Negative Knowledge

```text
epiplexity_proxy -> training_signal
epiplexity_proxy -/-> correctness_certificate
epiplexity_proxy -/-> production_readiness
epiplexity_proxy -/-> bounded_grid_completeness
```

The proxy says where training signal may exist. It does not say which
candidate is valid, optimal, or safe to accept.

## Next Experiment

Train a curriculum-weighted advisory ranker:

```text
positive set: verifier winners and objective-equivalent tied winners
negative set: adversarial-family candidates weighted by disqualifier rarity
loss: pairwise or listwise ranking
acceptance: cross-seed mean verifier calls beats gap-weighted default
safety: invalid_accept_count = 0 and fallback/certificate remains deterministic
```

The experiment should report both the epiplexity proxy and the actual ranking
metrics. If the proxy rises but ranking metrics do not improve, record that as
negative knowledge and keep the current gap-weighted ranker.

## Sources

- Marc Finzi, Shikai Qiu, Yiding Jiang, Pavel Izmailov, J. Zico Kolter, and Andrew Gordon Wilson. [From Entropy to Epiplexity: Rethinking Information for Computationally Bounded Intelligence](https://arxiv.org/abs/2601.03220), arXiv 2601.03220, submitted 2026-01-06 and revised 2026-03-16.
- Hongmin Li. [A Controlled Counterexample to Strong Proxy-Based Explanations of OOD Performance](https://arxiv.org/abs/2605.11554), arXiv 2605.11554, submitted 2026-05-12.
- Koichi Takahashi and Yusuke Hayashi. [Thermodynamic Limits of Physical Intelligence](https://arxiv.org/abs/2602.05463), arXiv 2602.05463, submitted 2026-02-05.
- Yang Song and Diederik P. Kingma. [How to Train Your Energy-Based Models](https://arxiv.org/abs/2101.03288), arXiv 2101.03288, 2021.
- Maxime Gasse, Didier Chetelat, Nicola Ferroni, Laurent Charlin, and Andrea Lodi. [Exact Combinatorial Optimization with Graph Convolutional Neural Networks](https://arxiv.org/abs/1906.01629), arXiv 1906.01629, 2019.
- Rui Wang, Zhiming Zhou, Tao Zhang, Ling Wang, Xin Xu, Xiangke Liao, and Kaiwen Li. [Learning to Branch in Combinatorial Optimization with Graph Pointer Networks](https://arxiv.org/abs/2307.01434), arXiv 2307.01434, 2023.
