# ZenoEnergy SOTA Decision Map

Date: 2026-05-18

This note maps current academic solver-learning and energy-model guidance onto
the ZenoEnergy research path. It is a decision aid for what to test next. It
does not create a consensus or settlement claim.

## Standing Rule

```text
model proposes
verifier decides
fallback or certificate preserves exactness
```

The model can reduce search cost only by changing proposal order or proposal
budget. Validity, state roots, and accepted settlement remain deterministic.

## Source Map

| source | relevant idea | ZenoEnergy decision |
| --- | --- | --- |
| LeCun et al., energy-based learning | Energy compares candidate configurations by scalar score, avoiding normalized probabilities for decision problems. | Keep energy as an advisory candidate score. |
| Song and Kingma, EBM training | General generative EBMs face unknown normalizing constants and often need MCMC, score matching, or NCE. | Avoid full generative EBM training for v0; use ranking or regression losses over verified candidates. |
| Logical Intelligence EBRM essay | Energy can score partial candidate states and localize broken constraints. | Treat as inspiration for repair diagnostics, but keep academic decisions grounded in primary literature and in-repo verifier evidence. |
| Deep Sets | Permutation-invariant set functions have a structured representation. | Candidate-set context should use set-safe pooling rather than order-sensitive summaries. |
| Set Transformer | Attention can model interactions inside unordered sets. | Test a tiny set-attention/listwise ranker only after linear baselines and replay gates remain stable. |
| ListNet / listwise ranking | Ranking losses should use whole lists when the task is ordering a list. | Replace pair-only updates in the next ranker with listwise top-one or top-k loss over each candidate batch. |
| Learning to Branch in MIP | Learn cheap ranking surrogates for expensive exact solver choices. | ZenoEnergy’s scorer should imitate verifier-backed winners and hard solver calls, then defer to the verifier. |
| GNN branch-and-bound | Structural encoders can generalize search policies across larger combinatorial instances. | A graph/set encoder is a v1 direction if simple listwise rankers saturate. |
| Learned Large Neighborhood Search | Learned policies can select neighborhoods while an exact solver evaluates repairs. | The repair selector is the right model family to keep extending, but only with fallback and dominance certificates. |

## Evidence Already In Repo

| topic | current evidence | status |
| --- | --- | --- |
| aggregate learned ranker | gap-weighted 97-parameter linear ranker reaches top-10 recall 1.0 on heldout synthetic data | supported as research default |
| set-aware linear ranker | extra set moments did not beat aggregate learned baseline | negative knowledge |
| deterministic neighborhood repair | improves regret sharply but increases verifier work | mixed evidence |
| learned repair selector | compresses full neighborhood on three seed pairs while preserving aggregate regret | supported as proposal-budget tool |
| learned vs hand repair selector | learned selector strictly beats hand-selected repairs on only one of three seed pairs | negative knowledge |
| fallback equivalence | Lean and runtime receipts cover permutation-preserving full fallback | supported boundary |
| checked stop | Lean receipt names certificate premises; runtime sweep audits suffix labels offline | supported boundary with online caveat |

## Next Experiments

1. **Listwise Set Ranker**

   Train a small no-GPU ranker on complete candidate lists:

   ```text
   context encoder: DeepSets-style pooled candidate features
   per-candidate score: MLP([candidate_features, pooled_context])
   loss: ListNet top-one cross entropy or top-k weighted listwise loss
   fallback: deterministic full candidate check
   ```

   Acceptance bar:

   ```text
   learned listwise mean verifier calls < gap-weighted linear mean calls
   learned top_2 or top_5 checked-stop audit remains 1.0 on holdout
   invalid_accept_count = 0
   permutation_violation_count = 0
   ```

2. **Repair Selector With Outcome-Level Labels**

   Current selector scores proposals individually. Train on the outcome of the
   selected proposal subset:

   ```text
   label(proposal subset) := best valid objective after adding subset
   loss := rank subset by regret reduction per added candidate
   ```

   This directly targets the hand-selected baseline.

3. **Hard-Negative Generator Refresh**

   Add adversarial examples where a candidate has attractive local energy but
   fails a certificate premise:

   ```text
   valid-looking suffix bound violation
   duplicate fill id with high volume
   dominance-cover miss
   set-context distribution shift
   near-tie valid candidates with surplus reversal
   ```

4. **Dominance-Cover Certificate Prototype**

   Status: first runtime prototype exists in
   [ZENO_ENERGY_DOMINANCE_COVER.md](./ZENO_ENERGY_DOMINANCE_COVER.md), with a
   WES search bridge in
   [ZENO_ENERGY_WES_DOMINANCE_SEARCH.md](./ZENO_ENERGY_WES_DOMINANCE_SEARCH.md).
   The follow-up prefix audit in
   [ZENO_ENERGY_DOMINANCE_PREFIX.md](./ZENO_ENERGY_DOMINANCE_PREFIX.md) shows
   that the learned and hybrid rankers reach the finite-list dominance-cover
   certificate at the first checked candidate on the committed bounded run. The
   suffix-bound early-stop certificate in
   [ZENO_ENERGY_SUFFIX_BOUND.md](./ZENO_ENERGY_SUFFIX_BOUND.md) adds a
   deterministic unchecked-suffix objective bound and stops after mean 1.008
   verifier calls on the committed bounded run. The cross-seed stress in
   [ZENO_ENERGY_SUFFIX_BOUND_CROSS_SEED.md](./ZENO_ENERGY_SUFFIX_BOUND_CROSS_SEED.md)
   keeps learned and hybrid mean calls at 1.013 across nine bounded synthetic
   configs with zero invalid accepts. The adversarial suffix stress in
   [ZENO_ENERGY_SUFFIX_BOUND_ADVERSARIAL_STRESS.md](./ZENO_ENERGY_SUFFIX_BOUND_ADVERSARIAL_STRESS.md)
   shows declared-output-only bounds fail on injected high-output invalid
   suffix candidates, while deterministic disqualifiers close the certificate.
   The useful next step is a full-list completeness argument for:

   ```text
   DominanceCover(pruned, full)
   ∧ UpperBoundCertificateChecksWithWinner(winner, pruned)
   -> GloballyWeaklyOptimal(winner, Feasible)
   ```

   The Lean theorem exists, the finite-list runtime receipt exists, the
   ranked-prefix audit exists, and the suffix-bound runtime certificate has
   one-seed, cross-seed, and adversarial-suffix synthetic receipts. The
   production gap is completeness for the generated full family plus real
   replay showing the bound remains useful on representative market data.

## Decisions

| candidate direction | decision | reason |
| --- | --- | --- |
| full generative EBM | defer | adds training and sampling complexity without improving verifier boundary |
| pairwise linear ranking | keep as baseline | cheap and already strong |
| listwise set ranker | test next | matches ranking task and set-structured candidate family |
| larger transformer | defer | data and evidence bottleneck comes before model capacity |
| learned repair selector | continue | strongest alignment with LNS and solver-guidance literature |
| top-k without fallback | reject | empirical recall cannot replace certificate or fallback |
| online checked stop | prototype only with suffix-bound certificate | current checked-stop rates are offline audits |

## References

- Yann LeCun, Sumit Chopra, Raia Hadsell, Marc'Aurelio Ranzato, and Fu Jie Huang. [A Tutorial on Energy-Based Learning](https://cs.nyu.edu/~yann/research/ebm/), 2006.
- Yann LeCun. [Energy-Based Models: Structured Learning Beyond Likelihoods](https://neurips.cc/virtual/2006/tutorial/3), NeurIPS tutorial, 2006.
- Yang Song and Diederik P. Kingma. [How to Train Your Energy-Based Models](https://arxiv.org/abs/2101.03288), 2021.
- Eve Bodnia and Boris Hanin. [Energy-Based Models for Reasoning, LLMs for the Interface](https://logicalintelligence.com/blog/energy-based-models-for-reasoning), 2026.
- Manzil Zaheer et al. [Deep Sets](https://papers.nips.cc/paper/6931-deep-sets), NeurIPS 2017.
- Juho Lee et al. [Set Transformer](https://proceedings.mlr.press/v97/lee19d.html), ICML 2019.
- Zhe Cao et al. [Learning to Rank: From Pairwise Approach to Listwise Approach](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/tr-2007-40.pdf), ICML 2007.
- Elias Khalil et al. [Learning to Branch in Mixed Integer Programming](https://ojs.aaai.org/index.php/AAAI/article/view/10080), AAAI 2016.
- Maxime Gasse et al. [Exact Combinatorial Optimization with Graph Convolutional Neural Networks](https://papers.neurips.cc/paper/9690-exact-combinatorial-optimization-with-graph-convolutional-neural-networks), NeurIPS 2019.
- Nicolas Sonnerat et al. [Learning a Large Neighborhood Search Algorithm for Mixed Integer Programs](https://arxiv.org/abs/2107.10201), 2021.
