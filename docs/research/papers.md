---
title: papers
type: note
permalink: autonomous-tau-dex-review/docs/research/papers
---

# Research Corpus: DEX Math, Routing, and Fairness (papers-first)

Date: 2026-01-24

This file is a *text-format research corpus* for ZenoDex: we collect high-signal academic papers (plus a few widely cited
technical reports) and record the actionable math/algorithm takeaways.

Policy note:
- We do **not** paste full paper text here.
- We keep to short summaries, keywords, and implementation-oriented notes.

---

## 1) CFMM / AMM foundations (math + mechanism)

### Replicating Market Makers: The Geometry of Automated Market Makers
- Link: https://arxiv.org/abs/2103.14769
- Why it matters:
  - Formalizes AMMs as payoffs/geometry; useful for reasoning about invariants and “what curve means”.
  - Bridges AMMs ↔ replicating portfolios; clarifies assumptions behind “market making without order books”.
- ZenoDex hooks:
  - Treat “curve family choice” as a *typed module* with explicit obligations: monotonicity, minimality under rounding,
    bounded error, and conservation in base units.

### Replicating Monotonic Payoffs Without Oracles
- Link: https://arxiv.org/abs/2111.13740
- Why it matters:
  - Shows what payoff families can be replicated *without* external price oracles under monotonicity constraints.
  - Helps separate what must be oracle-driven vs what can be endogenous to the AMM.
- ZenoDex hooks:
  - Design “oracle-optional” products (bounded, monotone) that remain verifiable in Tau without trusting price feeds.

### Constant Function Market Makers: Multi-Asset Trades via Convex Optimization
- Link: https://arxiv.org/abs/2107.12484
- Why it matters:
  - Frames multi-asset CFMM trading as convex optimization; provides clean conditions for no-arbitrage and solvability.
  - Gives a principled route to extend beyond 2-asset pools.
- ZenoDex hooks:
  - Future: add an N-asset pool type with a Tau-verifiable certificate (KKT / dual) in bounded regimes.

---

## 2) Fees, curvature, oracles, and parameterization (what to compute + what to verify)

### An Analysis of Uniswap Markets
- Link: https://arxiv.org/abs/1911.03380
- Why it matters:
  - Empirical + microstructure analysis of Uniswap; links volume, fees, and liquidity behavior.
- ZenoDex hooks:
  - Use as a reality-check source when choosing default fee tiers and when designing user-facing “LP ROI” displays.

### When Does the Tail Wag the Dog? Curvature and Market Making
- Link: https://arxiv.org/abs/2012.08040
- Why it matters:
  - Connects curvature of CFMM invariants to market impact and behavior under arbitrage.
- ZenoDex hooks:
  - Treat curve selection (including ZenoDex’s cubic-sum family) as *risk-shaping*: curvature drives slippage/LVR tradeoffs.

### Improved Price Oracles: Constant Function Market Makers
- Link: https://arxiv.org/abs/2003.10001
- Why it matters:
  - Formalizes oracle constructions from CFMMs; clarifies TWAP/TWAMM-style measurement issues.
- ZenoDex hooks:
  - Add a deterministic “oracle module” that is explicitly *lagged* and uses bounded windows (Tau-checkable).

### A Note on Optimal Fees for Constant Function Market Makers
- Link: https://arxiv.org/abs/2105.13510
- Why it matters:
  - Analyzes fee choice under CFMM assumptions; clarifies the tradeoff between LP revenue and adverse selection.
- ZenoDex hooks:
  - Implement a fee-tier controller that is deterministic and policy-gated (Tau verifies tier changes are within bounds).

### Optimal Fees for Geometric Mean Market Makers
- Link: https://arxiv.org/abs/2104.00446
- Why it matters:
  - Studies fee optimality for G3M/Balancer-like invariants; useful if ZenoDex adds multi-asset pools.
- ZenoDex hooks:
  - Same as above, but for generalized invariants and possibly per-asset weights.

---

## 3) LP risk, impermanent loss, and LVR (what to show users)

### Automated Market Making and Loss-Versus-Rebalancing
- Link: https://arxiv.org/abs/2208.06046
- Why it matters:
  - Clear framing of LVR as a core cost paid by LPs to arbitrageurs; helps avoid “hand-wavy IL explanations”.
- ZenoDex hooks:
  - UX: show users *two* decompositions: (i) fee revenue, (ii) LVR estimate, under simple oracle assumptions.

### Liquidity Provider Returns in Geometric Mean Markets
- Link: https://arxiv.org/abs/2006.08806
- Why it matters:
  - LP returns and IL/LVR for geometric mean markets; ties to volatility and fee adequacy.
- ZenoDex hooks:
  - Use for educational tooling and for parameter stress tests (fee tiers vs volatility regimes).

### Risks and Returns of Uniswap V3 Liquidity Providers
- Link: https://arxiv.org/abs/2205.08904
- Why it matters:
  - Concentrated liquidity changes the risk/return profile; useful when considering any “range-liquidity” extension.
- ZenoDex hooks:
  - If ZenoDex adds any form of concentration, UX must show “out of range” behavior and rebalancing burden.

---

## 4) Routing, aggregation, and execution (math → UX)

### Optimal Routing for Constant Function Market Makers
- Link: https://arxiv.org/abs/2204.05238
- Why it matters:
  - Studies exact/approx algorithms for routing across CFMMs; supports deterministic bounded search.
- ZenoDex hooks:
  - Formalize a *bounded* router: exact for small candidate sets; approximate with certificates for large sets.

### Optimal Routing in DEX Aggregators (short note)
- Link: https://arxiv.org/abs/2104.00507
- Why it matters:
  - Presents algorithms for DEX aggregators and routing optimization.
- ZenoDex hooks:
  - UX: route explainability + deterministic tie-breaks; core: split-routing as a first-class primitive.

---

## 5) MEV, fairness, and batch auctions (designing “good execution”)

### Towards a Theory of Maximal Extractable Value I: Constant Function Market Makers
- Link: https://arxiv.org/abs/2207.11835
- Why it matters:
  - Formal models of MEV in CFMM environments; clarifies how ordering/extraction works mechanistically.
- ZenoDex hooks:
  - Use to motivate batch clearing + deterministic ordering; treat fairness as a spec-validated property.

### Credible Decentralized Exchange Design via Verifiable Sequencing Rules
- Link: https://arxiv.org/abs/2209.15569
- Why it matters:
  - Sequencing rules + credibility; bridges “we promise fair ordering” with verifiable mechanisms.
- ZenoDex hooks:
  - Encode sequencing rules as Tau-verifiable constraints; publish ordering proofs/certs in witnesses.

### Frequent Batch Auctions and Price Discovery in High-Frequency Trading
- Link: https://www.nber.org/papers/w18996
- Why it matters:
  - Seminal argument for batch auctions to reduce sniping; informs batch-based DEX fairness.
- ZenoDex hooks:
  - Batch duration design: balance fairness vs latency; use “small-batch” as a tunable, bounded parameter.

---

## 6) Broad surveys / SoKs (what to cross-check against)

### SoK: Decentralized Finance (DeFi)
- Link: https://arxiv.org/abs/2101.08778
- Why it matters:
  - Broad survey of DeFi primitives and risks; good map of attack surface and design patterns.
- ZenoDex hooks:
  - Use as a checklist for “DEX UX is security”: approvals, replay protection, slippage, sandwich awareness.

### SoK: Algorithms and Evaluation for DEXs
- Link: https://arxiv.org/abs/2406.01148
- Why it matters:
  - More recent SoK focused on algorithms and evaluation; good reference for routing/MEV mitigation taxonomy.
- ZenoDex hooks:
  - Use as a “coverage audit”: ensure our tests/metrics cover the standard failure modes.

---

## 7) “If we expand beyond CFMM-only” (order-flow + intents)

### CoW Protocol / intent-based execution (not a peer-reviewed paper, but highly relevant)
- Link: https://cow.fi/whitepaper
- Why it matters:
  - Practical, production-grade design for intents + solver-based batching + MEV mitigation.
- ZenoDex hooks:
  - Model “intent normal form” as consensus-critical; treat solver output as a certificate verified by Tau.

---

## Implementation-derived research questions for ZenoDex (seed list)

1) **Deterministic routing with split execution**:
   - Goal: given parallel pools, choose a split that maximizes output with a deterministic tie-break.
   - Certificate idea: bounded brute force for small amounts; local-search witness for large amounts (plus spot-checks).

2) **Quote explainability as a verifiable artifact**:
   - A quote should include: effective price, fee paid, price impact (vs mid), and “worst-case min-out” under slippage bps.
   - Make these computations deterministic and reusable by Tau specs.

3) **Batch fairness as a spec module**:
   - Encode sequencing/batch rules explicitly (e.g., within a pool: objective (A,B)+lex tie-break already exists in Python).
   - Add a witness format that proves the chosen ordering is canonical (min under a total key).