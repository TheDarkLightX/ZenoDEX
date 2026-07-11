# ZenoEnergy Negative Curriculum

This Julia-generated receipt turns recorded negative knowledge into sampling guidance for the next advisory ranker.

```text
source_report: data/upba_energy/upba_v2_suffix_bound_adversarial_family_stress_seed20260545.json
evaluated_batches: 118
family_count: 8
total_cases: 944
with_disqualifiers_certificate_ok_count: 944
without_disqualifiers_certificate_ok_count: 590
```

## Bounded Epiplexity Proxy

```text
schema: zenodex/energy/bounded_epiplexity_proxy/v1
classification: measurable_bounded_structure
score: 0.358265
label_entropy_bits: 2.866122
normalized_label_entropy: 0.955374
policy_separation: 0.375000
rare_label_headroom: 0.900498
```

Diagnostic proxy only; it is not a correctness certificate and does not prove model accuracy, grid completeness, or production readiness.

## Curriculum Weights

| disqualifier | count | sample weight |
| --- | ---: | ---: |
| `all_zero_fill_vector_flag` | 118 | 1.305 |
| `fill_coverage_violation_flag` | 118 | 1.305 |
| `invariant_violation_flag` | 201 | 1.000 |
| `limit_violation_count` | 117 | 1.311 |
| `negative_reserve_flag` | 134 | 1.225 |
| `output_mismatch_count` | 20 | 3.170 |
| `price_objective_violation_flag` | 118 | 1.305 |
| `schema_policy_mismatch_flag` | 118 | 1.305 |

## Recommendations

- Oversample rare deterministic disqualifiers during candidate generation, especially output_mismatch_count.
- Use the bounded epiplexity proxy as a pre-training data-quality check; measurable structure means the corpus has label diversity and policy separation worth training against.
- Keep the current gap-weighted linear ranker as the default until a curriculum-trained model beats it on cross-seed mean verifier calls.
- Train advisory scorers with pairwise or listwise contrastive losses over verifier-labeled candidates instead of generative EBM likelihood.
- Use Julia for bounded adversarial-family search and feature-coverage sweeps, then replay all proposed candidates through the Python verifier.
- Treat hard-negative mining as model-training data only; deterministic verifier and suffix certificates remain the safety boundary.

## Negative Knowledge

- Epiplexity telemetry is a steering signal, not a correctness certificate.
- Declared-output-only suffix bounds are insufficient for attractive invalid candidates.
- Multi-family adversarial stress does not prove v2 bounded-grid completeness.
- Synthetic hard negatives can improve training coverage, but real replay is still required before production-adjacent promotion.

## Academic Hooks

- LeCun's EBM framing supports discriminative energy ranking over structured outputs, where inference compares candidate energies and chooses low-energy configurations: https://cs.nyu.edu/~yann/research/ebm/
- Song and Kingma's EBM training survey argues that full likelihood training faces an unknown normalizing constant and often needs MCMC, score matching, or NCE; ZenoEnergy should keep ranking and contrastive losses for v0: https://arxiv.org/abs/2101.03288
- Learned branch-and-bound work trains policies from strong solver rules and graph/state features; the ZenoEnergy analogue is verifier-imitation with deterministic fallback and no model authority: https://arxiv.org/abs/1906.01629
- Graph pointer branching adds top-k imitation losses over solver decisions; the ZenoEnergy analogue is top-k verifier-call reduction with checked suffix certificates: https://arxiv.org/abs/2307.01434
