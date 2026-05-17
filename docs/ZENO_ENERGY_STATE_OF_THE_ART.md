# ZenoEnergy State Of The Art Notes

Date: 2026-05-17

This note maps academic energy-based and learned-search research onto the next
ZenoEnergy work. The main conclusion is pragmatic:

```text
learned model chooses candidate order
deterministic verifier chooses acceptance
```

That is the same safety shape used by learned branch-and-bound, learned large
neighborhood search, and other solver-guidance methods. The model improves the
search policy. The verifier or solver remains the authority.

## Core EBM Lineage

LeCun and Huang's discriminative EBM work frames training as shaping energies so
good configurations receive lower energy than bad configurations. LeCun,
Chopra, Hadsell, Ranzato, and Huang then present EBMs as a general structured
prediction framework: inference is energy minimization over output
configurations, and training shapes the energy landscape so low-energy decisions
are good decisions.

For ZenoEnergy, the corresponding object is:

```text
E(context, candidate) -> scalar
```

Lower energy means "check this candidate earlier." Acceptance remains:

```text
accepted(candidate) := deterministic_verifier(context, candidate)
```

This is closest to the structured-output and discriminative EBM tradition. Full
generative density modeling is unnecessary for the default ZenoEnergy path.

## Modern EBM Training Limits

Song and Kingma summarize the main technical cost of probabilistic EBMs:
probabilities are specified up to an unknown normalizing constant. Likelihood
training then needs MCMC or alternatives such as score matching and
noise-contrastive estimation. Grathwohl et al. show that classifier logits can be
interpreted as an EBM, and their joint EBM training still uses sampling machinery
for the unnormalized density component.

ZenoEnergy should avoid expensive probabilistic EBM training in the default
path. Ranking and verifier-labeled regression are enough for the current
objective:

```text
arg sort candidates by E(context, candidate)
```

The research risk is distribution shift. Probabilistic normalization is outside
the core objective.

## Learned Search State Of The Art

The closest production-relevant literature is learned combinatorial
optimization, especially learned heuristics embedded inside exact or
solver-backed pipelines.

Gasse et al. train graph convolutional networks to guide branch-and-bound
variable selection for mixed-integer linear programs. The important pattern is
that learned branching improves search while the solver keeps exactness.

Bengio, Lodi, and Prouvost survey machine learning for combinatorial
optimization and emphasize that optimization instances themselves are the data
distribution. That directly matches the ZenoEnergy question: synthetic batches
are useful when they approximate the candidate-search distribution, and real
replay matters because it defines the distribution actually seen by the system.

Sonnerat et al. learn large-neighborhood search for MIPs by combining neural
assignment and neighborhood policies with an off-the-shelf solver. This suggests
a ZenoEnergy v1 direction: learn candidate repair or neighborhood expansion,
while preserving deterministic fallback over the full finite candidate family.

## GFlowNets

GFlowNets are relevant when candidate generation becomes the bottleneck. Bengio
et al. describe GFlowNets as learning a stochastic policy that samples
compositional objects with probability approximately proportional to a reward.
They explicitly connect reward to energy:

```text
E(x) = -log R(x)
```

For ZenoEnergy, a GFlowNet would be a candidate sampler over price/fill
construction steps. It could generate diverse high-reward settlement candidates
without enumerating every price/fill vector. Safety would require one of these
bridges:

```text
full fallback checks the exact finite family
```

or

```text
pruned/generated family has a deterministic dominance-cover certificate
```

That makes GFlowNets a good research extension after the current ranker. They
should remain candidate generators outside the verifier.

## Diffusion And Score Models For Discrete Optimization

Recent diffusion work for combinatorial optimization treats solution search as
sampling over hard discrete sets. Sanokowski, Hochreiter, and Lehner report a
data-free diffusion framework for neural combinatorial optimization accepted at
ICML 2024. This is academically important. It is heavier than the current
ZenoEnergy need.

Diffusion becomes attractive if UPBA candidate generation moves from tens of
candidates to thousands or millions and the candidate family has a structured
repair geometry. For the current bounded candidate ranker, diffusion is likely
overkill.

## Best Next ZenoEnergy Models

Priority order:

1. **Hard-barrier linear or MLP ranker.** Keep verifier-shaped invalidity
features as dominant penalties, train listwise or pairwise ranking, and keep the
model tiny.
2. **Regularized set-aware MLP or listwise ranker.** Replace hand-compressed
intent summaries with permutation-invariant intent-set encoding when intent
heterogeneity becomes important. The first linear set-aware feature block is
recorded in [ZenoEnergy Set-Aware Ranker](./ZENO_ENERGY_SET_AWARE_RANKER.md),
and the first comparison run is recorded in
[ZenoEnergy Research Log](./ZENO_ENERGY_RESEARCH_LOG.md).
3. **Learned repair or neighborhood model.** Given a bad candidate, suggest a
nearby price/fill adjustment. The verifier still checks every proposed repair.
The deterministic baseline in
[ZenoEnergy Neighborhood Repair](./ZENO_ENERGY_NEIGHBORHOOD_REPAIR.md) is the
control experiment before training a repair policy. The first tiny selector in
[ZenoEnergy Repair Selector](./ZENO_ENERGY_REPAIR_SELECTOR.md) compresses the
full neighborhood from 16.275 mean candidates to 8.000 on one held-out synthetic
seed while matching the full-neighborhood mean volume regret. It does not
strictly beat the hand-selected proposal subset on regret, so the immediate
research lesson is that the current proposal recipes are simple enough for a
hand selector to remain a strong baseline. The cross-seed stress receipt in
[ZenoEnergy Repair Selector Cross-Seed Stress](./ZENO_ENERGY_REPAIR_SELECTOR_CROSS_SEED.md)
keeps the same shape over three train/holdout seed pairs: compression succeeds
on all three, strict hand-selector improvement succeeds on one of three.
4. **GFlowNet candidate sampler.** Generate diverse high-reward candidates over
large price/fill spaces, then verify and fall back deterministically.
5. **Diffusion or score model.** Reserve this for large structured candidate
spaces where local denoising or continuous relaxation gives measurable search
benefit.

The current 97-parameter ranker remains a strong baseline because it is cheap,
auditable, and already moves the verifier winner to the first or second checked
candidate on the held-out synthetic distribution.

## AutoTrader Transfer

AutoTrader should use the same pattern:

```text
E(trading_state, candidate_plan) -> scalar
executable(candidate_plan) := deterministic_policy_gate(candidate_plan)
```

The best academic analogues are learned solver heuristics and learned
neighborhood search. AutoTrader can rank candidate strategies, repairs, hedge
adjustments, and route plans. Execution still requires deterministic budget,
nonce, authorization, risk, provenance, and settlement gates.

## Research Implications

1. Synthetic data is legitimate for bounded search research when the generator
matches the formal candidate family.
2. Real replay data is required to estimate production distribution shift.
3. The strongest SOTA analogy is learned solver guidance with deterministic
settlement authorization.
4. The next math target is a deterministic dominance-cover certificate for
neighborhood-augmented candidate families.
5. The next model targets are cross-seed testing of nonlinear or listwise
set-aware rankers and learned repair-policy selection before moving to heavier
generative samplers.

## Sources

- Yann LeCun and Fu Jie Huang, "Loss Functions for Discriminative Training of
  Energy-Based Models," AISTATS/PMLR, 2005:
  <https://proceedings.mlr.press/r5/lecun05a.html>
- Yann LeCun, Sumit Chopra, Raia Hadsell, Marc'Aurelio Ranzato, and Fu Jie
  Huang, "A Tutorial on Energy-Based Learning," 2006:
  <https://yann.lecun.org/exdb/publis/pdf/lecun-06.pdf>
- NeurIPS 2006 tutorial page, "Energy-Based Models: Structured Learning Beyond
  Likelihoods":
  <https://neurips.cc/virtual/2006/tutorial/3>
- Yang Song and Diederik P. Kingma, "How to Train Your Energy-Based Models,"
  arXiv:2101.03288:
  <https://arxiv.org/abs/2101.03288>
- Will Grathwohl et al., "Your Classifier is Secretly an Energy Based Model and
  You Should Treat it Like One," ICLR 2020:
  <https://openreview.net/pdf/df53e66f00cddbec2fc54bd79e0e5d84a31eaf9a.pdf>
- Maxime Gasse et al., "Exact Combinatorial Optimization with Graph
  Convolutional Neural Networks," NeurIPS 2019:
  <https://papers.neurips.cc/paper/9690-exact-combinatorial-optimization-with-graph-convolutional-neural-networks>
- Yoshua Bengio, Andrea Lodi, and Antoine Prouvost, "Machine Learning for
  Combinatorial Optimization: a Methodological Tour d'Horizon,"
  arXiv:1811.06128:
  <https://arxiv.org/abs/1811.06128>
- Yoshua Bengio et al., "GFlowNet Foundations," JMLR 2023:
  <https://jmlr.org/papers/volume24/22-0364/22-0364.pdf>
- Nicolas Sonnerat et al., "Learning a Large Neighborhood Search Algorithm for
  Mixed Integer Programs," arXiv:2107.10201:
  <https://arxiv.org/abs/2107.10201>
- Sebastian Sanokowski, Sepp Hochreiter, and Sebastian Lehner, "A Diffusion
  Model Framework for Unsupervised Neural Combinatorial Optimization," ICML
  2024:
  <https://arxiv.org/abs/2406.01661>
- Eve Bodnia and Boris Hanin, "Energy-Based Models for Reasoning, LLMs for the
  Interface," Logical Intelligence, 2026:
  <https://logicalintelligence.com/blog/energy-based-models-for-reasoning>
