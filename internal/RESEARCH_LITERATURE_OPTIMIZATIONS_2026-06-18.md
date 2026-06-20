---
title: Research Literature — Optimizations, Assurance & Mechanism Design (2026-06-18)
type: note
permalink: autonomous-tau-dex-review/internal/research-literature-optimizations-2026-06-18
---

# Research Literature → Actionable Upgrades for ZenoDex

**Date:** 2026-06-18
**Scope (user-prioritized):** (1) algorithm/optimization upgrades, (2) formal verification & defensive coding, (3) mechanism design & DeFi economics. AMM curve math deprioritized.
**Method:** **three** `deep-research` workflow runs — **371 agents total, ~21M subagent tokens** (run 3 was max-effort/expanded: all stages `effort: max`, caps raised to 24 sources / 40 verified claims). Each run: 5 angles → sources → falsifiable claims → top-N adversarially verified (3 skeptics each; ≥2/3 refutes kills) → synthesized. Run 1 (angles 1–3) → **F1–F11** (11); run 2 (ZK + auctions + ADL) → **G1–G9** (9 numbered; run 2's 11 synthesized included 2 meta-entries folded into the shortlist/negative-results sections); run 3 (stablecoin/oracle/VRF + perps gaps) → **H1–H16** (16). **36 numbered findings total.** Every code surface cited below was mechanically confirmed against the **actual files** (not just agent summaries), and the report is Codex-reviewed.

**Location:** placed in `internal/` at the user's request (the approved plan had named `docs/`).
**Review:** Codex-reviewed across 7 rounds → **final grade A, sign-off ready, zero required fixes** (C+ → B → B+ → A− pre-run-3; run-3 H1–H16 integrated → B+ → B+ → **A** on citation hygiene). Every code-surface mapping independently confirmed by Codex against the live tree.

> **Read this first.** Findings are graded by the adversarial vote (e.g. `3-0` = all three verifiers failed to refute). Caveats attached to a finding are *load-bearing* — they mark exactly where a citation is an *applicable technique* rather than a *turnkey drop-in*. The credibility rule for this repo applies: a supported finding with an honest caveat beats an overclaim.

## Coverage status

| Angle | Area | Status |
|------|------|--------|
| 1 | Combinatorial optimization & exact matching (batch/CoW) | ✅ verified — 4 findings |
| 2 | Convex optimization & optimal routing (CFMMs) | ✅ verified — 5 findings |
| 3 | Nonlinear SMT & proof-assistant verification | ✅ verified — 2 findings |
| 4 | Verified ZK proof systems & proof-carrying settlement | ✅ verified — 4 findings (folding/lookups + Lean SNARK-soundness); Verkle/JMT still open |
| 5a | Mechanism design — multi-unit / batch auctions | ✅ verified — 4 findings (diagnose all 6 falsified sealed-bid claims; mechanism-level handling for the tie-break/reveal/decoy trio) |
| 5b | Mechanism design — perps funding / ADL / insurance | ◑ partial — ADL rule (G9) + over-liquidation defect (H16) found; **funding-rate mechanism, insurance ruin/VaR, keeper-MEV still open** (funding no-arb formulas refuted) |
| 5c | Mechanism design — stablecoin / oracle / VRF (zUSD) | ✅ verified — **15 findings (H1–H15)**: peg-game/de-peg theory, oracle cost-vs-depth, VRF + Aequitas tie-break |

Three deep-research runs were used. Run 1 (`wf_83852bc8-134`, 107 agents) covered angles 1–3; angles 4–5 came up empty there only because the verification budget was spent on angle 1–3 claims. Run 2 (`wf_f3f85031-9e7`, 109 agents) confirmed the ZK, auction, and ADL findings. Run 3 (`wf_898e6740-6a2`, 155 agents, **max-effort/expanded** — all stages at `effort: max`, caps raised to 24 sources / 40 verified claims) **closed the 5c stablecoin/oracle/VRF gap** (H1–H15) that run 2 had lost to transient rate-limiting, and added the perps over-liquidation finding (H16). The remaining open items are the **5b** perps funding-rate mechanism / insurance-fund sizing and the **Verkle/JMT** ADS question.

---

## Prioritized shortlist (impact ÷ effort)

| # | Upgrade | Surface | Impact | Effort | Findings |
|---|---------|---------|--------|--------|----------|
| 1 | **Sealed-bid / batch-auction mechanism framing** — current code *already* has pro-rata largest-remainder + non-reveal bonds, so the findings **confirm & frame** the design: mechanism-level handling for the tie-break/reveal/decoy trio (O-SB-03/05/06), the diagnosis that demand-reduction/shading (O-SB-01/02) are **inherent** to uniform pricing (not tunable away), and bond-adequacy (O-SB-04) left **unsourced**. NB `sealed_bid_auction.py` is an *experimental* primitive. | `sealed_bid_auction.py`, `sealed_bid_bonds.py` | High | **Low** (framing/confirmation) | G5, G6, G7, G8 |
| 2 | **Closed-form single-pool arb / trade-size + fee price-tracking bound** — for sizing a single-pool trade to a target price (e.g. zUSD buyback), *not* the swap math (`cpmm.py` swap is already closed-form O(1)) | new single-pool trade-size helper; adjacent: `homological_arbitrage.py`, `oi_liquidity_bound.py` | Medium | Low | F7 |
| 3 | **Risk-based water-filling ADL rule** — unique optimal deleveraging (minimize max leverage); distribution-free, wash-trade/Sybil-resistant, path-independent | experimental `_apply_liquidation_adl` in `experiments/perp_np_clearinghouse_v1/perp_np_core.py` | High | Medium | G9 |
| 4 | **Min-cost-flow / assignment CoW matcher** — replace exponential match/skip backtracking (cap ≤8) with a *strongly-polynomial exact* formulation **for the unconstrained singleton+swap core**; per-sender-constrained CoW remains open (may be NP-hard — must extend the flow network) | `batch_clearing_cow.py` (matcher), `settlement_cow_pairs.py` (validator) | High | Medium | F2, F3 |
| 5 | **Convex routing solver** — replace derivative-seed split heuristic + fixed 2-hop with one convex program, *provable global optimum*, heterogeneous pool curves | `split_routing.py`, `routing.py` | High | Medium | F5, F6 |
| 6 | **Add incremental-linearization solver to the ESSO gate** — decide the **compose/multi-step** nonlinear k-monotonicity invariant currently *omitted* for dual-solver inductiveness (single-swap k already proven in `cpmm_swap_v8`) + future richer NIA gates | ESSO gate, `cpmm_swap_compose_v2.yaml` | Med-High | Medium | F10 |
| 7 | **Lean 4 `x·y=k` formalization template** — mechanize the k-invariant as an *unbounded* Lean proof (complementary to ESSO's *bounded* SMT check) | `lean-mathlib/Proofs/AMM*` | Medium | Medium | F11 |
| 8 | **Machine-checked SNARK *soundness* (AGM/Lean) as the target assurance class** for the verifier path — formal soundness, not library trust | `proof_verifier.py` | Medium | Higher | G4 |
| 9 | **Convex-flow unification** — one model spanning CoW-netting (angle 1) *and* CFMM routing (angle 2), edge-parallel solver | routing/clearing architecture | High | Higher (research-grade) | F8 |
| 10 | **ZK folding/lookups** (HyperNova / ProtoStar / Lasso) — cheaper recursion + multi-transition aggregation — **but gated behind a RISC0/FRI → Plonkish/multilinear-PCS (Jolt-style) migration** | `zk/state_proof_risc0/` | High | **Highest** (architectural) | G1, G2, G3 |
| 11 | **VRF + Aequitas manipulation-resistant tie-break** — replace any hash/order priority with VRF cryptographic sortition gated by block-order-fairness (SCC-condensation batches); design against last-revealer grinding | `batch_clearing` / `sealed_bid_auction.py` tie-break | High | Med-High | H12, H14, H15 |
| 12 | **Architect the (design-stage) zUSD buyback oracle around pool depth, not window** — manipulation cost is window-*independent* under consecutive-block control; use closed-form cost-of-manipulation + 9.3×-depth bound + wide-range-mint lever + per-epoch truncation | design-stage gate in `experiments/zusd_hybrid_economics_v1` (not core `zusd.py`) | High | Medium | H7, H8, H10, H11 |
| 13 | **Formal zUSD peg-game model** — port the deleveraging-spiral submartingale + multi-equilibrium redemption coordination game; co-tune redemption fee/base-rate with run risk | `zusd.py` redemption/base-rate | Medium | Medium | H1, H3, H4 |
| 14 | **Tune `fraction_bps` + add liquidation-as-auction** — `perp_v2` already has `partial_liquidate`; the finding validates it and says don't over-seize (rescue often needs <50%); auction-for-price-discovery is the open part | `perp_v2` liquidation | Medium | Med-High | H16 |

> ⚠️ **Cross-cutting blocker for #2, #4, #5, #9 — the continuous↔integer gap.** Those four (closed-form single-pool arb #2, min-cost-flow CoW #4, convex routing #5, convex-flow unification #9) are proved over the reals (ℝ) or solved with floating-point interior-point methods. ZenoDex's consensus path is **integer-only and deterministic**. None of the cited sources closes the rounding-error bound that bridges the continuous optimum to consensus integer math. **That bound is an open obligation** (likely a novel one) and must be discharged — in Lean/ESSO, the project's usual way — before any of these ships to the authority path. Treat the literature as giving the *algorithm and its optimum*, not the *integer refinement*. (The sealed-bid mechanism fix #1 and the verification items #6–#8 are **not** convex/LP optima and are unaffected by this gap.)

---

## Angle 1 — Combinatorial optimization & exact matching (batch / CoW)

Current code: `optimal_ab_bounded` is **O(n!)** brute force (cap n≤12); the CoW matcher `_cow_pair_netting_exact_in_v1` (`batch_clearing_cow.py`) is **exponential match/skip backtracking, capped at total candidates ≤8**, with a greedy fallback that is **balance-aware but not globally AB-optimal**. (Both CoW paths gate each match on a per-sender debit-vs-balance check in `batch_clearing_cow.py` — the `deb0`/`deb1` guards in the brute-force and greedy selectors; it is the separate *batch-ordering* greedy/`mci_ab` heuristics that ignore sender balances. Line numbers are deliberately omitted — this file is under active refactor.)

### F2 — KEY: polynomial-time *exact* CoW clearing **and** pricing via min-cost flow `[3-0, high]`
- **Surface:** `src/core/batch_clearing_cow.py` (the CoW pair-netting **matcher**); `src/core/settlement_cow_pairs.py` is the replay-side **validator** that would need to accept the new matching (not itself the matcher).
- **Technique:** Model orders as arcs in a min-cost-flow network. Combinatorial markets restricted to **singleton orders + swap orders** (equal-quantity two-item exchanges = pair-netting) admit polynomial-time exact market-clearing *and* arbitrage-free price computation; the dual optimal solution gives the prices. Two hierarchical (lexicographic) objectives are collapsed into one weighted objective while preserving dual price info — **the scalarization technique that applies to ZenoDex's (A=volume, B=surplus) objective** (ZenoDex adds a *third* lexicographic level — a tie-break on intent IDs — which would need an extra tie-break stage on top of the two-objective weighting).
- **Source:** Müller, Martin, Pokutta, et al., *Math. Methods Oper. Res.* 85(2):155–177 (2017) — arXiv:[1404.6546](https://arxiv.org/abs/1404.6546), DOI [10.1007/s00186-016-0555-z](https://link.springer.com/article/10.1007/s00186-016-0555-z). Verbatim: *"We provide an algorithm that permits polynomial time market-clearing and -pricing"* via *"a minimum cost flow formulation … model orders as arcs in a network … two hierarchical objectives … combine these objectives into a single weighted objective while preserving the price information of dual optimal solutions."* Total unimodularity ⇒ integral extreme points ⇒ exact.
- **Expected gain:** exponential match/skip backtracking (cap ≤8) → **polynomial exact** clearing+pricing, removes the ≤8 cap.
- **Effort/risk:** Medium. **Caveat (load-bearing):** the paper's swaps are *equal-quantity* exchanges and it does **not** model the per-sender balance/budget constraints ZenoDex's CoW matcher *already* enforces — so this is an *applicable technique*, not a drop-in. The min-cost-flow network must be extended to carry per-sender balance arcs, and that extension may break the polynomial guarantee (see Open Questions).

### F3 — Foundational tractability + magnitude-independent worst-case bound: assignment = min-cost-flow, *strongly* polynomial `[3-0, high]`
- **Surface:** batch ordering + CoW matching
- **Technique:** Weighted bipartite matching = the assignment problem = a special case of min-cost flow; both have **strongly-polynomial** algorithms (operation count depends only on V, E — *not* on the bit-length of integer costs/amounts). The Hungarian/Kuhn-Munkres algorithm is O(n³).
- **Why it matters here:** a strongly-polynomial bound is **magnitude-independent** — runtime does not scale with token-amount bit-length. For a deterministic, replayable consensus path this is a stronger guarantee than a generic (weakly-polynomial) LP solver whose cost scales with amount magnitudes.
- **Sources:** Kuhn (1955) / Munkres (1957); Tardos (1985, strongly-poly min-cost flow); Orlin (INFORMS); Zwick, [min-cost-flow lecture notes](https://www.cs.tau.ac.il//~zwick/grad-algo-06/min-cost-flow.pdf); [Strongly-polynomial time](https://en.wikipedia.org/wiki/Strongly-polynomial_time), [Hungarian algorithm](https://en.wikipedia.org/wiki/Hungarian_algorithm).
- **Expected gain:** O(n!) brute ordering / exponential CoW backtracking → **O(n³) magnitude-independent exact assignment for the *unconstrained* core** (per-sender-constrained / sequencing variants can be NP-hard — see caveat).
- **Effort/risk:** Low-Medium. **Caveat:** per-sender balance/budget constraints and path-dependent *sequencing* are not pure assignment and can be NP-hard — this is a technique-direction for the structured core, not a polynomiality claim for the fully-constrained batch. (Minor: the Zwick host isn't whitelisted so the exact quote wasn't byte-verified, but the substance is textbook and corroborated.)

### F1 — Model framing: ZenoDex batch-clearing ≡ multi-asset auction with uniform clearing prices `[3-0, high]`
- **Surface:** `batch_clearing.py` / CoW (reference model)
- **Source:** Tom Walther (Gnosis/ZIB), *A Multi-Asset Exchange with Uniform Clearing Prices*, Operations Research Proceedings 2018 — DOI [10.1007/978-3-030-18500-8_29](https://link.springer.com/chapter/10.1007/978-3-030-18500-8_29). Abstract: *"an alternative exchange and price-finding mechanism that simultaneously considers multiple assets in a discrete-time setting."*
- **Expected gain:** a well-defined exact-clearing target replacing ad-hoc ordering. **Effort/risk:** Low (framing). See **Negative results** for the refuted MIP-hardness sibling claim.

### F4 — Motivation only: deterministic single-objective heuristics leave value on the table `[3-0, medium]`
- **Source:** Marfinetz, *NSGA-II for CoW batch auctions*, arXiv:[2510.21647](https://arxiv.org/abs/2510.21647) (Oct 2025). Abstract: *"Deterministic single-objective heuristics that optimize only expected output frequently fail to exploit split-flow opportunities…"*
- **Use:** motivational framing for replacing the greedy fallback. **Caveat:** single-author, non-peer-reviewed preprint; its split-flow is single-order AMM path-splitting (closer to angle 2) rather than order-netting — cite for the general suboptimality concern, **not** its self-reported 3–15% number.

---

## Angle 2 — Convex optimization & optimal routing (CFMMs)

Current code: `split_routing.py`'s **default** path is exact for `amount_in ≤ 4096`, else a derivative-seed window heuristic with no global-optimum guarantee — **but an opt-in exact 2-pool solver already exists** (`search_profile="staircase_exact"` → `split_routing_staircase.py:115`). `routing.py` is fixed 2-hop enumeration (O(P²)). So the convex-routing gains below target **multi-hop / >2-pool / global routing and replacing the default heuristic profile** — *not* the already-exact 2-pool opt-in path.

### F5 — KEY: optimal multi-CFMM routing is *convex* → provable global optimum `[3-0, high]`
- **Surface:** `src/core/split_routing.py`, `src/core/routing.py` (multi-hop)
- **Technique:** Optimal order execution across a network of multiple CFMMs over multiple assets is a **convex optimization problem** (when fixed per-order costs are ignored), generalizing beyond a fixed hop count to arbitrary multi-asset multi-CFMM networks. Choosing a multi-asset trade against a single CFMM is likewise convex. Convexity ⇒ any local optimum is global ⇒ solvable reliably to the global optimum instead of by heuristics.
- **Sources:** Angeris, Chitra, Evans, Boyd, *Optimal Routing for CFMMs*, ACM EC 2022 — arXiv:[2204.05238](https://arxiv.org/abs/2204.05238), DOI 10.1145/3490486.3538336. Angeris, Agrawal, Evans, Chitra, Boyd, *Constant Function Market Makers: Multi-Asset Trades via Convex Optimization* — arXiv:[2107.12484](https://arxiv.org/abs/2107.12484), Springer MARBLE 2022, DOI 10.1007/978-3-031-07535-3_13. Verbatim: *"this optimal routing problem can be cast as a convex optimization problem, which is computationally tractable"*; *"various problems of choosing a multi-asset trade can be formulated as convex optimization problems, and can therefore be reliably and efficiently solved."*
- **Expected gain:** heuristic / small-trade-only → **provable global optimum over arbitrary topology**.
- **Effort/risk:** Medium. **Caveat:** convexity is over continuous ℝ; *with* fixed (gas) costs it becomes mixed-integer convex (NP-hard); the integer-rounding bridge is the separate open obligation (see cross-cutting blocker). **Scope note:** a 2-pool exact solver already exists (`staircase_exact`), so the marginal gain is for **>2-pool / multi-hop / global** routing and for replacing the *default* heuristic profile — not the 2-pool opt-in path.

### F6 — Scalable decomposition solver, heterogeneous pools (incl. Uniswap v3) `[3-0, high]`
- **Surface:** `split_routing.py` + multi-hop enumeration
- **Technique:** A decomposition-based algorithm solves the routing problem and *makes it simple to incorporate complicated/aggregate CFMMs* (e.g. Uniswap v3) — one solver handles parallel (split) + serial (multi-hop) + heterogeneous pool curves rather than fixed enumeration. Empirically faster than commercial solvers.
- **Source:** Diamandis, Resnick, Chitra, Angeris, *An Efficient Algorithm for Optimal Routing Through Constant Function Market Makers*, Financial Cryptography 2023 — arXiv:[2302.04938](https://arxiv.org/abs/2302.04938), DOI 10.1007/978-3-031-47751-5_8. **Reference implementation:** `CFMMRouter.jl` (bcc-research) — directly usable as a prototype/oracle (ZenoDex already has Julia sims, e.g. `internal/julia_sims/cow_pair_validator_sim.jl`).
- **Expected gain:** one solver for split + multi-hop + heterogeneous curves. **Effort/risk:** Medium. **Caveat:** solves a concave-utility convex routing problem; does **not** directly encode ZenoDex's lexicographic (A,B) objective or integer-rounding bounds.

### F7 — Closed-form single-pool arbitrage + fee price-tracking bound `[3-0, high]`
- **Surface:** a (currently absent) helper for **single-pool optimal trade-sizing to a target price** — primary use would be zUSD buyback sizing / single-pool arb. Adjacent existing arb machinery, for context (these solve *different* problems, not drop-in targets): `src/core/homological_arbitrage.py` (cross-pool marginal *cycles*), `src/core/perp_v2/oi_liquidity_bound.py` (TWAP arb-bleed bound). **NB:** `cpmm.py`'s swap output is *already* closed-form O(1) — there is **no iterative *swap* solve** to replace; the gain is for the distinct *optimal-trade-size-to-a-target-price* computation.
- **Technique:** Optimal arbitrage against a single constant-product (Uniswap) pool *with* a fee is convex and has a **closed-form** solution for the two-asset optimal trade: `(R_α − √(k/(γ·m_p)))₊` with γ the fee factor. Under no-arbitrage the marginal price tracks the reference within the fee factor: `γ·m_p ≤ m_u ≤ γ⁻¹·m_p`, i.e. `≈ (1−τ)m_p ≤ m_u ≤ (1+τ)m_p` for small fee τ=1−γ. Generalizes to multi-asset constant-mean (weighted-geometric-mean) markets, which are log-log convex.
- **Source:** Angeris, Kao, Chiang, Noyes, Chitra, *An Analysis of Uniswap Markets* — arXiv:[1911.03380](https://arxiv.org/abs/1911.03380).
- **Expected gain:** closed-form optimal single-pool arb **trade-size** (no search loop) + a fee-parameterized analytic price-deviation bound. **Effort/risk:** Low (single-pool). **Caveats (precision, not refuting):** (a) closed form is *single-pool* — multi-pool split routing generally has **no** closed form; (b) `m_u` is the reserve-ratio price, not the per-trade marginal incl. fees; (c) Eq.(3) is an *equilibrium price-tracking* bound — **`[UNVERIFIED]` for repurposing as an implementation integer-rounding-error bound** (that was a requester extrapolation, not in the paper).

### F8 — Unifying framework: convex network flows (bridges angle 1 ↔ angle 2) `[3-0, high]`
- **Surface:** routing/clearing solver architecture
- **Technique:** The "convex flow problem" (maximize summed concave node/edge utilities subject to convex edge constraints over a hypergraph) generalizes max-flow, min-cost flow, and multi-commodity flow while allowing concave edge-gain functions — CFMM routing fits as edges with concave gain, and CoW-netting fits as network flow. Its **dual decomposes over the edges**, enabling per-pool parallel optimization of a global objective instead of a monolithic solve.
- **Sources:** Diamandis, Angeris, Edelman, *Convex Network Flows* — arXiv:[2404.00765](https://arxiv.org/abs/2404.00765); Diamandis MIT PhD thesis, [dspace 1721.1/158483](https://dspace.mit.edu/handle/1721.1/158483). Verbatim: dual *"decomposes over the edges of the hypergraph … a fast solution algorithm that parallelizes over the edges."*
- **Expected gain:** a single model spanning CoW-netting **and** CFMM routing; edge-parallel solver. **Effort/risk:** Medium-High (newer, research-grade). **Note:** this is the structural bridge between angle 1 and angle 2 — worth evaluating if you unify clearing + routing.

### F9 — Gas/fixed-cost-aware routing (closes the omitted-fixed-cost gap) `[3-0 claims, medium maturity]`
- **Surface:** routing cost model (gas not currently in objective), multi-hop pool activation
- **Technique:** Fixed on-chain gas costs modeled as a **mixed-integer** program inducing pool-activation thresholds, with necessary optimality as an explicit **KKT system** linking prices/fees/activation, and *sufficient* optimality via generalized convexity (pseudoconcavity, quasilinearity) — a verifiable optimality characterization **without** requiring globally convex trade functions.
- **Source:** Escudero, Lara, Sama, *Optimal Routing across CFMMs with Gas Fees*, arXiv:[2603.02844](https://arxiv.org/abs/2603.02844) (3 Mar 2026).
- **Expected gain:** gas-aware activation + verifiable optimality beyond convex-only curves. **Effort/risk:** Medium-High. **Caveat (time-sensitive):** single very recent preprint, not yet peer-reviewed; KKT derived for the *relaxed* formulation under a constraint qualification. MIP-for-gas itself is not net-new (2204.05238 already modeled fixed costs as mixed-integer convex); the KKT + generalized-convexity characterization is the new part.

---

## Angle 3 — Nonlinear SMT & proof-assistant verification

ESSO status (verified against the models): the **single-swap** k-non-decrease invariant is **already proven** — `cpmm_swap_v8.yaml` includes `k_after ≥ k_before` and its verification report shows Z3+CVC5 agreement (all invariants inductive). The omission is specifically the **composition / multi-step** model: `cpmm_swap_compose_v2.yaml` *intentionally omits* `k`-monotonicity because nonlinear multiplication across composed steps "prevents reliable dual-solver proofs in some bounded regimes" (it keeps `k_before/k_after` as effects but drops the invariant "to regain dual-solver inductiveness"). So the open nonlinear gate is **multi-step/compose k-monotonicity and richer nonlinear invariants**, not the single swap. Lean/Kani separately prove only arithmetic cores.

### F10 — KEY: decide the *compose-level* nonlinear k-invariant (+ richer NIA gates) with incremental linearization (MathSAT) `[3-0 technique; 2-1 benchmark magnitude]`
- **Surface:** the ESSO **compose/multi-step** k-monotonicity gate (`cpmm_swap_compose_v2.yaml`, intentionally omitted today) + any future richer nonlinear invariants; the multi-solver fail-closed gate. (The *single-swap* k-invariant is already proven in `cpmm_swap_v8.yaml` — F10 is **not** about that one.)
- **Technique:** Incremental linearization solves SMT over nonlinear integer arithmetic (NIA) via an abstraction-refinement loop: nonlinear multiplications are abstracted as uninterpreted functions over cheap UFLIA and incrementally axiomatized with linear lemmas on demand — avoiding expensive exact nonlinear solvers. It is **complementary** to z3/cvc5, so it can decide invariants they leave `UNKNOWN`.
- **Sources:** Cimatti, Griggio, Irfan, Roveri, Sebastiani, *Incremental Linearization for Satisfiability and Verification Modulo Nonlinear Arithmetic and Transcendental Functions* — SAT 2018 ([pdf](https://disi.unitn.it/rseba/papers/sat18.pdf)) + ACM TOCL 2018, DOI [10.1145/3230639](https://dl.acm.org/doi/10.1145/3230639). Tool: **MathSAT** / nuXmv. On the full QF_NIA SMT-LIB suite (23,876 instances): MathSAT 16,717 solved vs CVC4 11,638, Z3 9,831 (also > Yices 15,786, SMT-RAT 6,576) — most of any single tool; demonstrated complementarity (solves 2,436 instances Yices misses).
- **Expected gain:** decide the compose/multi-step nonlinear k-monotonicity invariant currently omitted for dual-solver inductiveness (and future richer NIA gates); add as a complementary solver in the fail-closed gate. **Effort/risk:** Medium (integration; NIA is undecidable so it may still return unknown — sound-but-incomplete, which fits fail-closed). **Caveats on the benchmark (2-1 vote):** numbers are 8 years old; ESSO runs *cvc5*, not the benchmarked *CVC4*, so the 2018 margin may have narrowed; it's the MathSAT authors' own paper (mitigated by the standard SMT-LIB suite + SMT-COMP). **Trust the technique and complementarity; discount the exact 2018 margins.**

### F11 — Lift `x·y=k` past tested-only in Lean 4 `[3-0, high]`
- **Surface:** `lean-mathlib/Proofs/AMM*` (CPMM invariant work)
- **Technique:** A Lean 4 formalization of constant-product (`x·y=k`) AMMs exists with mechanized proofs of economic properties and public code — a reusable template for machine-checking the nonlinear invariant class ZenoDex currently leaves tested-only in ESSO.
- **Source:** Pusceddu & Bartoletti, *Formalizing AMMs in the Lean 4 Theorem Prover*, FMBC 2024 (OASIcs/Dagstuhl) — arXiv:[2402.06064](https://arxiv.org/abs/2402.06064); code [github.com/danielepusceddu/lean4-amm](https://github.com/danielepusceddu/lean4-amm).
- **Expected gain:** reusable Lean formalization template for k-invariants — an *unbounded* mechanized proof complementary to ESSO's bounded SMT check (which already proves the single-swap case). **Effort/risk:** Medium. **Caveat:** their headline proofs target *economic* properties (e.g. arbitrage), not a dedicated k-non-decrease *swap* theorem — a foundation/template, not a turnkey ZenoDex invariant proof.

---

## Negative results & cross-cutting caveats

1. **Refuted (1-2): full multi-asset uniform-price clearing is *not* established as a tractable MIP.** The claim that the canonical full multi-asset uniform-price batch-clearing problem is "just a MIP" did **not** survive verification. So: do **not** assert general polynomiality *or* assert general NP-hardness. Provable polynomial exactness (F2/F3) holds **only** for the structured singleton+swap (pair-netting) sub-problem and pure assignment. Adding per-sender balance/budget constraints + path-dependent sequencing may push the general batch into NP-hardness — an open question.
2. **Continuous↔integer gap (the convex/LP/flow findings: F2/F3 CoW, F5/F6 routing, F7 closed-form, F8 convex-flow — shortlist #2/#4/#5/#9).** Every such optimum is over ℝ or via float interior-point. ZenoDex's authority path is integer-only and deterministic. The rounding-error bound from the continuous optimum to consensus integer math is **unclosed** and likely a novel obligation — discharge it (Lean/ESSO) before promotion. This is the single most important gate on shipping those; the sealed-bid (#1) and verification (#6–#8) items are unaffected.
3. **Fee price-tracking bound ≠ rounding-error bound.** F7's Eq.(3) is an equilibrium bound, `[UNVERIFIED]` for the implementation-rounding use it was hoped for.
4. **Source-quality discounts:** F4 is a single-author preprint (motivation only); F9 and **G9 (water-filling ADL) are single 2026 preprints, not peer-reviewed** (time-sensitive); F10's benchmark margins are dated (2-1 vote — trust the technique, not the exact numbers); F3's Zwick host wasn't byte-verifiable (substance is textbook).
5. **Refuted (0-3) in auctions: Ausubel clinching is NOT unconditionally strategyproof-efficient.** Sincere bidding is weakly dominant / efficient **only** under private values with diminishing marginal valuations — do not present G6 as an unconditional fix. **Also refuted (1-2):** the uniform-price "1−1/e price-of-anarchy welfare bound" — do not cite it as established.
6. **ZK architectural-migration caveat (G1–G3).** RISC0 is FRI/STARK-based; HyperNova/ProtoStar/Lasso target MSM/Plonkish/multilinear-PCS. The cited cost bounds apply only **after** migrating settlement to a Plonkish/multilinear-PCS IVC layer (Jolt-style). G4's AGM soundness likewise does not transfer to FRI — it is a methodological target. ZK is a roadmap, not a patch; cost-compare against RISC0-native recursion first.
7. **Repo-grounding note:** the second (gap-fill) run reported it did *not* re-verify file existence by filesystem inspection — but every cited surface (`sealed_bid_auction.py`, `batch_clearing.py`, `jmt.py`, `proof_verifier.py`, `zusd.py`, `perp_v2/funding_rule.py`, `batch_clearing_cow.py`, `settlement_cow_pairs.py`, `cpmm.py`) **was** mechanically confirmed present during report assembly.
8. **Run-3 refutations (do not cite as established):** the **linear TWAP-cost-vs-window** law (MDPI / euler-xyz, 0-3) — there is **no** clean linear cost-vs-window scaling; the surviving bound is in **pool depth** (H8/H10/H11). The **no-arbitrage perp-spot funding tethering** formulas `F=S(1+r/κ)` and the transaction-cost band (arXiv 2212.06888, 0-3 / 1-2) — funding mechanism design stays open. Several **VRF formalization** claims from IACR 2024/435 (MRV-insufficiency, unbiasability-sufficiency; 0-3 / 1-2) — ground the VRF primitive in Algorand sortition (H12) + Aequitas (H15), not 2024/435. The NBER **arbitrage-centralization** mechanism (1-2; only the general H3 tradeoff survives).
9. **Open gaps after run 3:** closed-form **insurance-fund adequacy** under correlated shocks (zero citations — ruin theory / VaR / EVT) and **Verkle / authenticated-data-structures for JMT** (zero) — the two highest-priority follow-up items.

## Open questions (carried forward)

- **Integer-rounding bridge:** does any source bound the continuous-optimum ↔ integer-consensus gap, or is it a novel obligation? (All cited optimality results live in ℝ.)
- **Per-sender balance-constrained CoW:** the current CoW matcher enforces per-sender balances imperatively, but the singleton+swap min-cost-flow result (F2) does **not** natively model them. Can F2 be extended to encode per-sender balance/budget constraints while preserving polynomial exactness *and* the lexicographic (A,B) objective — or does that push it into NP-hardness?
- **STARK-native vs migration:** is re-encoding RISC0/FRI settlement into a Plonkish/CCS or multilinear-PCS (Jolt) IVC justified versus STARK-native recursion (RISC0 continuations/aggregation)?
- **ADL scope:** does the single-asset isolated-margin water-filling ADL rule (G9) extend to the N-party clearinghouse perps and multi-asset/correlated portfolios, or does optimality break under cross-margin and price-mediated cascades?
- **Angle 5b residuals (still open after run 3):** optimal/strategyproof **funding-rate** mechanism + funding-timing game (the no-arb tethering formulas were refuted); **keeper / liquidation-as-auction** equilibrium; closed-form **insurance-fund adequacy** under correlated shocks (**zero** citations — ruin theory / VaR / EVT). Prior-run lead arXiv 2410.21446 still unresolved.
- **Angle 5c — CLOSED by run 3** (H1–H15). Residual quantitative question: re-derive the oracle manipulation-cost bound for zUSD's **specific 12-epoch** window (epoch ≠ 12s block) from the arXiv 2606.03548 dwell-time extension, parameterized in the actual `min_pool_depth` variable.
- **Angle 4 residual:** Verkle / authenticated data structures applicable to `jmt.py` — no surviving source this pass.

---

## Angle 4 — Verified ZK proof systems & proof-carrying settlement

Surfaces: `zk/state_proof_risc0/` (RISC0 guests), `src/state/jmt.py`, `src/integration/proof_verifier.py`.

> **Architectural caveat, load-bearing across G1–G3:** RISC0's zkVM is **FRI/STARK-based** (univariate, no group operations). HyperNova/ProtoStar fold **MSM/Plonkish** special-sound protocols and Lasso needs a **multilinear PCS**. So none of the cited cost bounds is a drop-in for the current RISC0 stack — realizing them implies migrating settlement to a Plonkish/multilinear-PCS IVC layer (e.g. a **Jolt**-style zkVM). Treat these as a *roadmap*, not a patch. ZenoDex's own STARK-native recursion (RISC0 continuations/aggregation) is the no-migration alternative and should be cost-compared first (open question).

### G1 — HyperNova: CCS folding / IVC for multi-transition aggregation `[3-0, high]`
- **Technique:** HyperNova is a recursive argument over **CCS** (generalizes Plonkish, R1CS, AIR with no overhead). Recursive prover cryptographic cost = **a single MSM** sized to the witness-variable count (degree-independent, no committed cross/error terms), and the folding scheme can **fold multiple instances at once → IVC/PCD** — i.e. batch many spot / perps-NP / zUSD settlement transitions into one recursive proof.
- **Sources:** Kothapalli & Setty, *HyperNova*, CRYPTO 2024 — IACR ePrint [2023/573](https://eprint.iacr.org/2023/573); CCS: Setty, Thaler, Wahby — IACR ePrint [2023/552](https://eprint.iacr.org/2023/552). Cross-term-free vs Nova corroborated by Mova (ePrint 2024/1220).
- **Expected gain:** cheaper per-step recursion + native multi-transition aggregation. **Effort/risk:** High (needs CCS/Plonkish-encoded settlement IVC).

### G2 — ProtoStar: generic accumulation for arbitrary settlement relations `[3-0, high]`
- **Technique:** A single generic accumulation (folding) scheme for **any (2k−1)-move special-sound protocol** whose verifier checks ℓ degree-d equations; accumulation verifier costs only k+2 EC mults + k+d+O(1) field/hash ops. As a non-uniform IVC for Plonk, the recursive in-circuit verifier is dominated by **just 3 group scalar mults + a hash of d\* field elements**, with **no trusted setup, no pairings, no prover FFTs**. Recursion cost scales with rounds/verifier-degree, **not** circuit size.
- **Source:** Bünz & Chen, *ProtoStar*, ASIACRYPT 2023 — IACR ePrint [2023/620](https://eprint.iacr.org/2023/620), Springer LNCS 14439, DOI 10.1007/978-981-99-8724-5_3.
- **Effort/risk:** High (settlement relations need a Plonkish/ProtoStar-compatible encoding).

### G3 — Lasso: cheap lookups for guest range-checks / big-int / instruction tables `[3-0 structured; 2-1 on m+n smallness; high]`
- **Technique:** For m lookups into a size-n table, Lasso's prover commits to only **m+n field elements, all small** (in {0,…,m}) regardless of field size; for **structured** tables **no party commits to the table at all**, enabling tables of size 2¹²⁸+ with the prover paying only for entries actually accessed.
- **Sources:** Setty, Thaler, Wahby, *Lasso*, EUROCRYPT 2024 — IACR ePrint [2023/1216](https://eprint.iacr.org/2023/1216), DOI 10.1007/978-3-031-58751-1_7; Jolt zkVM — IACR ePrint [2023/1217](https://eprint.iacr.org/2023/1217).
- **Expected gain:** lower commitment cost for guest range-checks / instruction lookups (a16z/Jolt comparison cited ~275 31-bit elts/step for RISC0 vs ~11 256-bit elts/step for Jolt). **Effort/risk:** Medium-High — gain comes via a **Lasso-based zkVM (Jolt)**, not by plugging Lasso into RISC0's univariate FRI stack.

### G4 — Target assurance class: machine-checked SNARK *soundness* under the AGM, in Lean `[3-0, high]`
- **Surface:** `src/integration/proof_verifier.py` (currently trusts the prover library; no soundness argument)
- **Technique:** Bailey & Miller formally verify SNARK **soundness** (not just functional correctness) under the **Algebraic Group Model**, machine-checked in **Lean**, across six linear-PCP-family constructions including **Groth16**. This is exactly the assurance class the verifier path lacks: a proven soundness argument rather than trust in a library.
- **Sources:** Bailey & Miller, *Formalizing Soundness Proofs of Linear PCP SNARKs*, USENIX Security 2024 — IACR ePrint [2023/656](https://eprint.iacr.org/2023/656), [USENIX page](https://www.usenix.org/conference/usenixsecurity24/presentation/bailey), code [github.com/BoltonBailey/formal-snarks-project](https://github.com/BoltonBailey/formal-snarks-project); Groth 2016 — ePrint 2016/260.
- **Expected gain:** a formal soundness target for the verifier. **Effort/risk:** High. **Caveat:** AGM is a pairing/linear-PCP idealized model and does **not** apply to RISC0's FRI/STARK soundness — this is a methodological **target**, not a transferable proof.
- **Residual gap:** no surviving source covered **Verkle trees / authenticated data structures** for `src/state/jmt.py` — JMT-specific ADS hardening remains open.

---

## Angle 5 — Verified mechanism design & DeFi economics

### Angle 5a — Multi-unit / batch auctions (diagnosis + mechanism-level fixes for the falsified sealed-bid claims) ✅

Surfaces: `src/core/sealed_bid_auction.py` (an **experimental** commit/reveal primitive — line 6: "deterministic and uniform-price for a fixed sell inventory"; one-sided, buyers bid for a fixed inventory), `sealed_bid_bonds.py`, `batch_clearing.py` tie-break.

**Mapping to the 6 falsified items:** O-SB-03 (biased tie-break), O-SB-05 (reveal free-option), O-SB-06 (decoy pinning) → addressed at the mechanism level by pro-rata rationing + non-display + bonds (G8; sealed/batch design G7), much already in code; O-SB-01 (demand reduction), O-SB-02 (shading to runner-up) → diagnosed **inherent** to uniform pricing (G5), mitigated only by switching pricing (G6 clinching — itself only *conditionally* strategyproof, see refutation); O-SB-04 (inadequate bonds, q≥2) → **not directly sourced** this run.

### G5 — ROOT CAUSE: uniform-price clearing is generically non-strategyproof & ex-post inefficient (demand reduction) `[3-0 ×5, high]`
- **Diagnosis:** A bid on a marginal unit affects payment on **inframarginal** units, so rational bidders shade more on later units **even with flat demand** → *demand reduction*. Every equilibrium yields inefficient outcomes with positive probability; an efficient equilibrium exists only under **knife-edge symmetry** (Theorem 1: equal capacities λᵢ=λ, 1/λ integer, equal marginal values). **A uniform-clearing batch/sealed-bid mechanism cannot be made strategyproof-efficient by parameter tuning alone** — this directly accounts for the demand-reduction and shading items (O-SB-01/02) and frames why the others are mechanism-design, not parameter-tuning, problems.
- **Sources:** Ausubel, Cramton, Pycia, Rostek, Weretka, *Demand Reduction and Inefficiency in Multi-Unit Auctions*, Rev. Econ. Studies 81(4):1366–1400 (2014) — [pdf](https://www.cramton.umd.edu/papers2010-2014/acprw-demand-reduction.pdf); Ausubel, AER 94(5) (2004) — [pdf](http://www.ausubel.com/auction-papers/efficient-ascending-auction-aer.pdf); Markakis & Telelis, *On the Inefficiency of the Uniform-Price Auction* — arXiv [1211.1860](https://arxiv.org/pdf/1211.1860).

### G6 — Pricing FIX: Ausubel clinching (Vickrey / opportunity-cost) prices `[pricing rule 3-0; high]`
- **Technique:** Charge **pay-as-clinched Vickrey prices** rather than (final quantity × final clearing price): at each price p, bidder i clinches and is awarded at p the units M − x₋ᵢ(p) by which aggregate rival demand falls below supply M. Concrete, portable rule for multi-unit settlement.
- **Source:** Ausubel, AER 94(5):1452–1475 (2004), DOI 10.1257/0002828043052330.
- ⚠️ **NEGATIVE RESULT (refuted 0-3):** the stronger claim that sincere bidding is **weakly dominant / unconditionally strategyproof-efficient** did **not** survive. VCG-equivalence holds **only** under private values with diminishing marginal valuations (substitutes). **Do not advertise unconditional strategyproofness.**

### G7 — Design template & MEV rationale: Budish–Cramton–Shim Frequent Batch Auctions `[core thesis unanimous; 2 of 4 merged sub-claims 2-1; high]`
- **Technique:** FBA = uniform-price sealed-bid double auctions at **discrete intervals**, orders processed **in a batch, not serially**. Continuous-time serial processing is *itself* the source of arbitrage rents (even symmetrically-observed public info creates mechanical arbitrage + a wasteful speed race); discrete batching **transforms competition on speed into competition on price**, neutralizing latency-arbitrage / sniping. Foundational rationale for `batch_clearing` over a serial book to blunt MEV.
- **Source:** Budish, Cramton, Shim, *The High-Frequency Trading Arms Race*, QJE 130(4):1547–1621 (2015) — [SSRN 2388265](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=2388265).
- **Caveat:** relocates (does not abolish) competition to solver/order-flow auctions; residual batch-boundary games; needs a rationing rule when demand ≠ supply at the clearing price (→ G8).

### G8 — Tie-break FIX: pro-rata within-batch rationing + non-display sealed bids `[3-0, high]`
- **Technique:** BCS prescribe within-batch rationing = **pro-rata, equal treatment of all orders in the same interval**, with time priority **only across (not within) intervals**, explicitly "without inducing a race to be first within a batch interval," and **orders not displayed during submission** ("why we describe the auction as sealed bid"). Together these **mitigate information leakage and within-batch priority races**.
- **Grounding note (corrects an earlier overclaim):** ZenoDex's sealed-bid path **already** implements pro-rata largest-remainder bucket allocation (`sealed_bid_auction.py:156`, `_pro_rata_marginal_bucket`) and handles the non-reveal free option via **bonds** (`sealed_bid_bonds.py:141`, `settle_sealed_bid_non_reveal_bonds`) — *not* via non-display alone. So BCS here largely **confirms and frames** the existing design. It does **not** "foreclose" every attack: residual *integer-remainder* ordering and non-reveal incentives still require the deterministic remainder rule + bond handling, and a fully neutral tie-break (if wanted) remains a **separate** mechanism choice — pro-rata is an alternative to a hash/VRF tie-break, not a wholesale elimination of deterministic remainder ordering.
- **Source:** Budish, Cramton, Shim, *Implementation Details for Frequent Batch Auctions*, AER P&P 104(5):418–424 (2014) — [pdf](https://ericbudish.org/wp-content/uploads/2022/03/implementation_details_frequent_batch_auctions.pdf).

### Angle 5b — Perps funding / ADL / insurance ◑ (partial)

Surfaces: `src/core/perp_v2/` (pure core) + `perp_engine.py` (shell). **The ADL algorithm itself lives in `experiments/perp_np_clearinghouse_v1/perp_np_core.py::_apply_liquidation_adl`** (insurance-first, then a *profit-priority* haircut on winners) — *not* in `src/core/perps.py`, which is state/validation wiring with no ADL path.

### G9 — Optimal ADL FIX: risk-based water-filling (leverage-draining) deleveraging `[3-0, high]`
- **Technique:** In a single-asset isolated-margin setting under a risk-neutral expected-loss objective, the **unique optimal ADL policy minimizes the maximum leverage** among participants: reduce the most highly-levered accounts first and progressively equalize leverage via a **water-filling** rule. Simultaneously **distribution-free, wash-trade resistant, Sybil resistant, and path-independent** — a canonical implementable benchmark that rationalizes queue-based ADL used in practice.
- **Source:** Campbell, Hey, Moallemi, Nutz, *Risk-Based Auto-Deleveraging*, arXiv [2603.15963](https://arxiv.org/abs/2603.15963) (Columbia, 2026; [mirror](https://www.math.columbia.edu/~mnutz/docs/Risk_Based_ADL.pdf)). ⚠️ **Single 2026 preprint, not yet peer-reviewed — time-sensitive, limited external replication.**
- **Surface / effort:** the candidate replacement target is the experimental profit-priority `_apply_liquidation_adl` in `perp_np_clearinghouse_v1/perp_np_core.py`; the water-filling rule would be evaluated *against* it. Medium effort. **Caveat:** scope is single-asset isolated-margin, risk-neutral; multi-asset / correlated-shock / N-party-clearinghouse extension is **open** — does optimality survive cross-margin and price-mediated cascades?
### H16 — Liquidation: fixed-spread liquidations over-liquidate (validates partial-liquidation; auction still open) `[3-0, high]`
- **Surface:** `perp_v2` liquidation (`apply_partial_liquidate` / `liquidation_penalty_bps` / `fraction_bps`) + the keeper path
- **Technique:** Existing fixed-spread DeFi liquidation mechanisms incentivize liquidators but **seize and sell excessive discounted collateral**, transferring value away from borrowers beyond what is needed to restore solvency (a position can often be rescued by selling **<50%** of its value). **ZenoDex's `perp_v2` already implements `partial_liquidate`** (guard/apply/effect wired) — so this finding **validates that design choice** and informs `fraction_bps` sizing (don't over-seize); the genuinely open part is **liquidation-as-auction** for price discovery.
- **Source:** Qin, Zhou, Gamito, Jovanović, Gervais, *An Empirical Study of DeFi Liquidations*, **ACM IMC 2021** — arXiv [2106.06389](https://arxiv.org/abs/2106.06389), DOI 10.1145/3487552.3487811 (Aave/Compound/Maker/dYdX, >85% of Ethereum lending). Corroborated by Miqado (FC 2023) and *Fixed-Spread Liquidation Lending* (FC 2024).
- **Expected gain:** a documented mechanism defect motivating partial-liquidation. **Effort/risk:** Medium-High (redesign).

- ⚠️ **Residual gaps (still open after run 3):** the optimal/strategyproof **funding-rate** mechanism + funding-timing game and the **keeper / liquidation-as-auction equilibrium** remain **unsourced** — the searched no-arbitrage perp-spot tethering formulas (arXiv 2212.06888) were **refuted** (votes 0-3 / 1-2). The closed-form **insurance-fund adequacy** bound under correlated shocks produced **zero** citations. These are the top items for a follow-up run.

### Angle 5c — Stablecoin / oracle / VRF (zUSD) ✅ (closed by run 3)

Surfaces: `src/core/zusd.py`, `experiments/zusd_hybrid_economics_v1/`. **15 findings (H1–H15)** from the max-effort run.

> **Cross-check with ZenoDex's own prior work:** H8/H10 (TWAP manipulation cost is **window-independent** under consecutive-block control; the real lever is **pool depth**) independently **corroborates** the project's earlier withdrawal of the "TWAP W² manipulation-cost" claim and its conclusion that pool depth + caps are load-bearing. External literature and the internal correction agree.

**Stablecoin peg-game & de-peg theory** (`zusd.py` redemption + base-rate + peg)

#### H1 — Deleveraging-spiral submartingale model `[3-0, high]`
Klages-Mundt & Minca, *While Stability Lasts* (Math. Finance 32(4):943–981, 2022; DOI [10.1111/mafi.12357](https://onlinelibrary.wiley.com/doi/abs/10.1111/mafi.12357); arXiv [2004.01304](https://arxiv.org/abs/2004.01304)) + *(In)Stability for the Blockchain* (arXiv [1906.02152](https://arxiv.org/abs/1906.02152)). Proves a deflationary **deleveraging spiral** (submartingale) that accelerates collateral drawdown and raises price variance (the Black Thursday dynamic), and **partitions the system into stable vs unstable regimes** with bounds on quadratic variation. **Over-collateralization alone does not prevent a de-peg.** → a formal stability-boundary + redemption/liquidation-cascade model for zUSD. **Caveat:** models the liquidation/demand spiral more than Liquity-style redemption arbitrage — the redemption-axis mapping is the looser one.

#### H2 — Liquidation-arbitrage / transaction-ordering attack model `[3-0, high]`
arXiv [1906.02152]. Novel attacks exploiting arbitrage around stablecoin **liquidations** are profitable and create perverse proposer incentives (Black Thursday: DAI auctions cleared near-zero, ~$8m loss). → an attack lens for zUSD redemption/liquidation **ordering** (bridges to the H12–H15 tie-break work).

#### H3 — Stability-vs-run-risk tradeoff `[3-0 on the general tradeoff, high]`
Ma, Zeng, Zhang, *Stablecoin Runs and the Centralization of Arbitrage*, NBER [w33882](https://www.nber.org/papers/w33882) (2025). Policies that **improve price stability can increase run risk** — cheaper/faster redemption tightens the peg but reduces sellers' price impact, amplifying runs. → peg-tightening (redemption fee / base rate) must be **co-optimized with run resilience.** **Caveat:** studies fiat-backed centralized stablecoins; the specific *arbitrage-centralization* mechanism was **refuted (1-2)** — only the general tradeoff survives.

#### H4 — Multi-equilibrium redemption coordination game `[3-0, high]`
Kwon et al., *What Drives the (In)stability of a Stablecoin?* (arXiv [2307.11754](https://arxiv.org/abs/2307.11754); **IEEE ICBC 2024**, DOI 10.1109/ICBC59979.2024.10634419; 22 stablecoins / 5 chains). A stablecoin has **multiple price equilibria** selected by a threshold θ\* and belief-driven coordination among redeemers — a de-peg is an equilibrium-**selection** outcome; over-collateralized designs have a smaller θ\*. → model zUSD's redemption game as a multi-equilibrium coordination problem with a computable de-peg threshold. **Tight match to the open question.**

#### H5 — Non-linear de-peg recovery threshold (mean-field game) `[3-0, high; preprint]`
Mohanty & Krishnamachari (USC), *Who Restores the Peg?* (arXiv [2601.18991](https://arxiv.org/abs/2601.18991), 2026). A calibrated mean-field game finds a **non-linear breakdown threshold** beyond which a de-peg is markedly slower to reverse (phase-transition-like). → a **stress-test methodology** to locate where zUSD's restoration infra fails. **Caveat:** ~5-month preprint; fiat-collateralized calibration.

#### H6 — SoK: emergent fragility + risk specialization `[3-0, high]`
Ling et al., *SoK: Stablecoin Designs, Risks, and the Stablecoin LEGO* (arXiv [2506.17622](https://arxiv.org/abs/2506.17622); 157 studies, 95 coins, 44 incidents). Peg stability is an **emergent, fragile** state (confidence × liquidity), and designs **relocate** risk rather than eliminate it (CDP shifts systemic equity risk onto over-collateralized vault owners as agent risk). → framing: choosing CDP+stability-pool *relocates* risk; a confidence+liquidity fragility checklist.

**Oracle / TWAP manipulation cost** — *applies to a design-stage feature:* the buyback/TWAP-gated eligibility currently lives in `experiments/zusd_hybrid_economics_v1/` (e.g. `twap_manipulation_cost_sim.jl`), **not yet in core `zusd.py`**; core oracle primitives are in `src/core/oracle.py` / `epoch_oracle_commitment.py`. (So H7–H11 inform the *design* of that gate.)

#### H7 — Closed-form cost-of-manipulation metric for CPMM oracles `[3-0, high; preprint]`
Mueller, Moumeni, Messaoudi, *Cost of Manipulation in AMM-Based Oracles* (arXiv [2606.03548](https://arxiv.org/abs/2606.03548), 2026). Defines cost = minimal mark-to-market loss to move the oracle by a multiplicative factor; **closed-form single-pool formulas**. → supplies the manipulation-cost bound (in pool depth) the buyback gate lacks. **Caveat:** single-pool/spot — the **12-epoch TWAP** window needs the paper's dwell-time/rate-limit extension; the cross-pool "total-quote-depth-only" claim was **refuted (1-2)**.

#### H8 — PoS multi-block TWAP cost + depth→cost + wide-mint defense `[3-0, high]`
Adams, Wan, Zinsmeister (Uniswap Labs), *Uniswap v3 TWAP Oracles in PoS* (SSRN [4384409](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=4384409), 2022). A validator with **two consecutive blocks** moves and reverts the TWAP with no arbitrage loss → cost collapses to **~2× the pool fee**. Cost scales with **depth**: a 20% two-block move on USDC/WETH 5bps needs ~$709B; a single **$1M wide-range LP mint raises attack cost by ~$360B.** → quantified depth→cost + a cheap defensive lever (seed wide-range protocol-owned liquidity). **Caveat:** constants are Uniswap-tick / 12s-block specific — re-derive for the 12-epoch window.

#### H9 — Per-update TWAP truncation cap `[2-1, medium]`
Same SSRN 4384409 (shipped as Uniswap **V4 truncated oracle**, `MAX_ABS_TICK_MOVE=9116`). Capping per-update change forces a ≥30-block manipulation to move a 30-min TWAP by 20%. → a transplantable **principle** (bound per-epoch TWAP delta). **Caveat (2-1):** literal constants don't transfer to a 12-epoch window, and truncating a *stablecoin* peg oracle risks **lagging a genuine de-peg** — the principle transfers, the constants are illustrative.

#### H10 — Window length is NOT a safety lever (MMEV window-independence) `[3-0, high]`
Mackinga, Nadahalli, Wattenhofer, *TWAP Oracle Attacks: Easier Done than Said?* (IACR [2022/445](https://eprint.iacr.org/2022/445); **IEEE ICBC 2022**). **Refutes** the assumption that multi-block TWAP cost scales **linearly with window length**; under consecutive-block MMEV the cost is **orders of magnitude cheaper and window-independent.** → kills "longer 12-epoch window = proportionally safer"; redirects defense to **pool depth + truncation + consecutive-slot risk.** (Independently corroborates ZenoDex's own withdrawn-W² conclusion.)

#### H11 — 9.3× pool-liquidity profitable-attack capital `[3-0, high]`
Aspembitova & Bentley (Euler Labs), *Oracles in DeFi*, **Entropy 25(1):60, 2023** ([MDPI](https://www.mdpi.com/1099-4300/25/1/60)). In a simulated CPMM-oracle attack, profitable manipulation needs **9.3× the pool's liquidity** in attacker capital (constant-product). → a concrete capital-vs-depth multiplier to parameterize the min-pool-depth threshold. **Caveat:** one calibrated example, not a universal law; the linear-cost-vs-window claim attributed to this paper was **refuted (0-3).**

**Manipulation-resistant tie-break** (`batch_clearing` / `sealed_bid_auction.py` — the O-SB-03 hash-tie-break concern)

#### H12 — VRF cryptographic sortition `[3-0, high]`
Gilad, Hemo, Micali, Vlachos, Zeldovich, *Algorand* (**SOSP 2017**; IACR [2017/454](https://eprint.iacr.org/2017/454)). VRF sortition gives, simultaneously: **unpredictability** (an adversary without `sk` can't anticipate selection), **Sybil-flatness** (selection count is binomial-additive, so splitting weight across accounts doesn't help), and **grinding-resistance** (`sk` committed before the seed). → a VRF-gated tie-break that is unpredictable-before-commit, Sybil-flat, grind-resistant. **Caveat:** properties hold for count-based weighted selection (not naive lowest-hash argmin); the specific Algorand max-over-sub-users transplant was **refuted (1-2)** — adopt the primitive, re-derive the rule.

#### H13 — DRB attack/countermeasure map `[3-0, high]`
Choi, Manoj, Bonneau, *SoK: Distributed Randomness Beacons* (IACR [2023/728](https://eprint.iacr.org/2023/728); **IEEE S&P 2023**). Catalogs predict/bias attack vectors incl. a named **biasing & grinding** attack + countermeasures (VDF unbiasability; commit-reveal-punish). → an off-the-shelf threat/countermeasure checklist. **Caveat:** the "exactly two properties" taxonomy claim was **refuted (1-2)** — use the attack map, not a clean 2-property reduction.

#### H14 — RANDAO last-revealer 2^h grinding `[3-0, high]`
Do Hai Son et al., *RANDAO-based RNG: Last Revealer Attacks* (arXiv [2403.09541](https://arxiv.org/abs/2403.09541), 2024). An adversary controlling **h tail-of-epoch proposer slots** gets **2^h** beacon outputs to choose from (reveal-or-withhold). → the precise design rule: **any tie-break seeded by a value the last actor can selectively reveal degrades by 2× per controlled final slot** — the canonical bias vector to eliminate. Corroborated by Alpturer-Weinberg, *Optimal RANDAO Manipulation* (AFT 2024).

#### H15 — Order-fairness impossibility + Aequitas SCC-condensation (THE template) `[3-0, high]`
Kelkar, Zhang, Goldfeder, Juels, *Order-Fairness for Byzantine Consensus* (**CRYPTO 2020** = Aequitas; IACR [2020/269](https://eprint.iacr.org/2020/269)). (1) Strict receive-order-fairness is **impossible** with consistency+liveness under asynchrony (Condorcet cycles). (2) Aequitas uses **block-order-fairness**: build a dependency graph, take its **condensation** (collapse each SCC → acyclic), totally order the SCCs, deliver each SCC's transactions in one batch. (3) Order-fairness is a **distinct third consensus property** — a malicious leader can otherwise choose the order. → the exact template: **fairness orders the batches; a canonical VRF-gated rule (H12) orders within an SCC/batch** — precisely the part Aequitas leaves free, which is the gap ZenoDex must fill.

> **Headline 5c recommendation:** compose **H15 (Aequitas batch-fairness) + H12 (VRF sortition)**, designed explicitly against **H14 (last-revealer grinding)**, as the manipulation-resistant tie-break; architect the **(design-stage) zUSD buyback oracle around pool depth (H8/H11), not window length (H10)**, with per-epoch truncation (H9); and port the **deleveraging-spiral (H1) + coordination-game (H4)** peg models, co-tuning redemption fee/base-rate with run risk (H3).

---

## Full source list (verified findings)

| Source | Angle | Quality | Used in |
|--------|-------|---------|---------|
| Müller/Pokutta et al. MMOR 2017 — arXiv 1404.6546 / DOI 10.1007/s00186-016-0555-z | 1 | primary | F2 |
| Walther, OR Proc. 2018 — DOI 10.1007/978-3-030-18500-8_29 | 1 | primary | F1 |
| Zwick notes; Hungarian; strongly-polynomial (Kuhn/Munkres/Tardos/Orlin) | 1 | primary | F3 |
| Marfinetz, arXiv 2510.21647 | 1 | preprint | F4 |
| Angeris et al. *Optimal Routing for CFMMs*, EC 2022 — arXiv 2204.05238 | 2 | primary | F5 |
| Angeris et al. *Multi-Asset Trades via Convex Opt.* — arXiv 2107.12484 | 2 | primary | F5 |
| Diamandis et al. FC 2023 — arXiv 2302.04938 (CFMMRouter.jl) | 2 | primary | F6 |
| Angeris et al. *Analysis of Uniswap Markets* — arXiv 1911.03380 | 2 | primary | F7 |
| Diamandis/Angeris/Edelman *Convex Network Flows* — arXiv 2404.00765 + MIT thesis | 2 | primary | F8 |
| Escudero/Lara/Sama — arXiv 2603.02844 (Mar 2026) | 2 | preprint | F9 |
| Cimatti/Griggio et al. SAT 2018 + TOCL 2018 (MathSAT) | 3 | primary | F10 |
| Pusceddu & Bartoletti FMBC 2024 — arXiv 2402.06064 (lean4-amm) | 3 | primary | F11 |
| Kothapalli & Setty *HyperNova* CRYPTO 2024 — IACR 2023/573; CCS IACR 2023/552 | 4 | primary | G1 |
| Bünz & Chen *ProtoStar* ASIACRYPT 2023 — IACR 2023/620 | 4 | primary | G2 |
| Setty/Thaler/Wahby *Lasso* EUROCRYPT 2024 — IACR 2023/1216; Jolt IACR 2023/1217 | 4 | primary | G3 |
| Bailey & Miller *Soundness of Linear-PCP SNARKs* USENIX Sec 2024 — IACR 2023/656 | 4 | primary | G4 |
| Ausubel/Cramton/Pycia/Rostek/Weretka RES 2014 (demand reduction) | 5a | primary | G5 |
| Ausubel AER 2004 (efficient ascending / clinching) | 5a | primary | G6 |
| Markakis & Telelis — arXiv 1211.1860 | 5a | primary | G5 |
| Budish/Cramton/Shim *HFT Arms Race* QJE 2015 — SSRN 2388265 | 5a | primary | G7 |
| Budish/Cramton/Shim *Implementation Details* AER P&P 2014 | 5a | primary | G8 |
| Campbell/Hey/Moallemi/Nutz *Risk-Based ADL* — arXiv 2603.15963 (2026) | 5b | preprint | G9 |
| Klages-Mundt & Minca *While Stability Lasts* — Math. Finance 32(4) 2022 / arXiv 2004.01304 (DOI 10.1111/mafi.12357) | 5c | primary | H1 |
| Klages-Mundt & Minca *(In)Stability for the Blockchain* — arXiv 1906.02152 | 5c | primary | H1, H2 |
| Ma/Zeng/Zhang *Stablecoin Runs* — NBER w33882 | 5c | primary | H3 |
| Kwon et al. *(In)stability of a Stablecoin* — arXiv 2307.11754 (IEEE ICBC 2024, DOI 10.1109/ICBC59979.2024.10634419) | 5c | primary | H4 |
| Mohanty & Krishnamachari *Who Restores the Peg?* — arXiv 2601.18991 (2026) | 5c | preprint | H5 |
| Ling et al. *SoK: Stablecoin Designs* — arXiv 2506.17622 | 5c | primary | H6 |
| Mueller et al. *Cost of Manipulation in AMM Oracles* — arXiv 2606.03548 (2026) | 5c | preprint | H7 |
| Adams/Wan/Zinsmeister *Uniswap v3 TWAP in PoS* — SSRN 4384409 | 5c | primary | H8, H9 |
| Mackinga/Nadahalli/Wattenhofer *TWAP Oracle Attacks* — IACR 2022/445 (ICBC 2022) | 5c | primary | H10 |
| Aspembitova & Bentley *Oracles in DeFi* — Entropy 25(1):60 (2023) | 5c | primary | H11 |
| Gilad et al. *Algorand* — SOSP 2017 / IACR 2017/454 | 5c | primary | H12 |
| Choi/Manoj/Bonneau *SoK: DRBs* — IACR 2023/728 (IEEE S&P 2023) | 5c | primary | H13 |
| Do Hai Son et al. *RANDAO Last Revealer* — arXiv 2403.09541 | 5c | primary | H14 |
| Kelkar et al. *Order-Fairness (Aequitas)* — IACR 2020/269 (CRYPTO 2020) | 5c | primary | H15 |
| Qin et al. *Empirical Study of DeFi Liquidations* — arXiv 2106.06389 (IMC 2021) | 5b | primary | H16 |

*Workflow stats — Run 1 `wf_83852bc8-134` (107 agents): 25 src · 109 claims · 24 confirmed · 11 synth → F1–F11. Run 2 `wf_f3f85031-9e7` (109 agents): 17 src · 79 claims · 23 confirmed · 11 synth → G1–G9 (+2 meta folded); 10 fetches rate-limited → 5c lost. Run 3 `wf_898e6740-6a2` (155 agents, max-effort/expanded): 28 src · 130 claims · 27 confirmed · 13 killed · 16 synth → H1–H16 (closes 5c). Combined: 3 runs · 371 agents · ~21M subagent tokens · 36 numbered findings.*
