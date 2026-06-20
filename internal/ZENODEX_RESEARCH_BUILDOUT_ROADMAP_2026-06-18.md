---
title: ZenoDex Research Build-Out Roadmap (2026-06-18)
type: note
permalink: autonomous-tau-dex-review/internal/zenodex-research-buildout-roadmap-2026-06-18
---

# ZenoDex Build-Out Roadmap — from the literature research

**Source:** `internal/RESEARCH_LITERATURE_OPTIMIZATIONS_2026-06-18.md` (3 deep-research runs · 371 agents · 36 verified findings F1–F11 / G1–G9 / H1–H16; Codex-reviewed A−, sign-off ready).
**Purpose:** turn the verified findings into a sequenced, codebase-grounded build plan — *what to build next*, in what order, with the blockers and verification each item needs. Every surface below was mechanically confirmed against the current tree.

## How to read this

Three rules govern the ordering:

1. **The integer-rounding bridge is the master gate.** Every convex/LP/flow optimum (F2/F3/F5/F6/F7/F8) is proved over the reals; ZenoDex's authority path is integer-only and deterministic. **No optimizer ships to authority until the continuous→integer rounding-error bound is discharged in Lean/ESSO.** That bound is Phase 0 and gates Phase 2.
2. **Build vs research-first.** Some items are ready to build; others (insurance-fund sizing, funding-rate mechanism, Verkle/JMT) returned **zero** citations and need a 4th research run *before* any code.
3. **CBC verification discipline applies.** Each consensus-critical promotion needs the full row: running impl → spec → Lean/ESSO/Kani proof → differential tests → runtime invariant → Codex review. This includes **Python↔Rust differential parity** for any surface that has — or will have — a Rust shadow (the runtime authority path): build both, lock them to a shared golden-vector/differential contract, and **never edit Python to mask a Rust parity bug** (canonical target = domain-bounded + stricter-fail-closed). "Definition of done" is stated per item.

Effort legend: **S** ≤ a few days · **M** ≈ 1–2 weeks · **L** ≈ multi-week / cross-cutting.

---

## Phase 0 — Prerequisite: the integer-rounding bridge `[L, gates Phase 2]`

- **Build:** a Lean/ESSO lemma family bounding the gap between a continuous convex/flow optimum and ZenoDex's deterministic integer-only computation — i.e. "the integer-rounded solution is within ε of the real optimum, and ε is bounded by X." This is the novel obligation the literature does **not** close (report §Negative results #2).
- **Why first:** without it, F2/F3 (CoW flow), F5/F6 (routing), F7 (closed-form), F8 (convex-flow) cannot move toward authority — only toward *off-chain advisory* quoting.
- **Done when:** a machine-checked bound exists for at least the CoW-matching and 2-pool-routing cases, with a witness that the bound is tight; differential test (integer impl vs rounded-real reference) stays within the bound across the full domain range.
- **Note:** until Phase 0 lands, Phase-2 work is still valuable as an **off-chain solver / oracle** (advisory quotes, cross-checks) — just not consensus authority.

---

## Phase 1 — Quick wins (independently shippable, no Phase-0 dependency)

### 1a. Neutral tie-break: VRF sortition + Aequitas block-order-fairness `[M]`
- **Draws on:** H12 (Algorand VRF sortition), H15 (Aequitas SCC-condensation), H14 (design against RANDAO last-revealer grinding); complements G8.
- **Surface:** the deterministic tie-break in `batch_clearing` / `sealed_bid_auction.py`.
- **What's actually new:** the code **already** has pro-rata largest-remainder + non-reveal bonds (G8). The genuinely missing primitive is a *manipulation-resistant* tie-break for the residual ordering: VRF-gated selection (unpredictable-before-commit, Sybil-flat, grind-resistant) used to order transactions *within* an Aequitas batch/SCC.
- **Gain:** closes the falsified-O-SB-03 biased-hash-tie-break concern with a cryptographic primitive (or formally retire the need for one if pro-rata suffices — decide explicitly).
- **Done when:** a VRF-sortition tie-break with a seed that the last actor cannot selectively reveal (H14), differential-tested for determinism + Sybil-flatness, **Python↔Rust parity** on the keying primitive, ESSO/Lean model of the selection rule, Codex review.
- **Progress (started):** `experiments/neutral_tiebreak_v1/` — the grinding-resistant keying primitive built as a **Python + Rust pair** (collision-free length-prefixed `sha256(framed(domain)‖framed(seed)‖framed(id))`), locked to a shared `parity_vectors.tsv` (11 Python + 3 Rust tests green). Isolated, not wired. Remaining: the unbiasable seed source (next increment), then the wire-in steps below.

### 1b. zUSD buyback-oracle design spec: pool-depth-gated, not window-gated `[S→M, design]`
- **Draws on:** H10 (window length is **not** a safety lever — cost is window-independent under consecutive-block MMEV), H8/H11 (cost scales with **pool depth**; 9.3× liquidity bound; wide-range-mint lever), H7 (closed-form cost-of-manipulation), H9 (per-epoch truncation principle).
- **Surface:** **design-stage** — the buyback/TWAP gate lives in `experiments/zusd_hybrid_economics_v1/` (`twap_manipulation_cost_sim.jl`), **not** core `zusd.py`. Core oracle primitives: `src/core/oracle.py`, `epoch_oracle_commitment.py`.
- **Gain:** parameterize the buyback `min_pool_depth` eligibility from the 9.3× bound; add a per-epoch TWAP-delta cap; **stop relying on the 12-epoch window length for safety** (it doesn't help). Independently corroborates the project's own withdrawn-"W²" conclusion.
- **Done when:** a design doc + a Julia/python parameterization deriving `min_pool_depth` for target attack-cost, re-deriving the truncation constants for the **12-epoch** window (epoch ≠ 12s block — H8/H9 caveat). Cross-check vs the existing `twap_manipulation_cost_sim.jl`.

### 1c. ESSO incremental-linearization solver for the compose-level k-invariant `[M, verification infra]`
- **Draws on:** F10 (MathSAT incremental linearization, complementary to z3/cvc5).
- **Surface:** the ESSO multi-solver fail-closed gate; the **compose/multi-step** model `cpmm_swap_compose_v2.yaml` that *intentionally omits* k-monotonicity. (Single-swap k is **already proven** in `cpmm_swap_v8.yaml` — not this.)
- **Gain:** decide the nonlinear k-monotonicity invariant the compose model drops; add a third complementary solver to the gate.
- **Done when:** MathSAT integrated as an optional solver; it decides at least one previously-`UNKNOWN` compose-model NIA query; gate stays fail-closed on disagreement.

### 1d. Lean mechanization of `x·y=k` (unbounded complement to the bounded SMT) `[M, proof]`
- **Draws on:** F11 (Pusceddu/Bartoletti lean4-amm template).
- **Surface:** `lean-mathlib/Proofs/AMM*`.
- **Gain:** an unbounded mechanized k-invariant proof, complementing ESSO's bounded SMT check.
- **Done when:** a Lean theorem for the swap k-non-decrease (not just economic properties), 0 `sorry`, non-vacuity witness, passing the project's Lean quality gates.

---

## Phase 2 — Integer-bridged optimization (after Phase 0; off-chain advisory before it)

### 2a. Min-cost-flow / assignment CoW matcher `[M]`
- **Draws on:** F2 (Müller/Pokutta singleton+swap polynomial clearing+pricing), F3 (assignment = strongly-polynomial min-cost flow).
- **Surface:** `batch_clearing_cow.py` (matcher; the `deb0`/`deb1` balance guards), `settlement_cow_pairs.py` (replay validator).
- **Gain:** replace the exponential match/skip backtracking (cap ≤8) with a **strongly-polynomial exact** matcher **for the unconstrained singleton+swap core**.
- **Blocker:** Phase 0 (continuous→integer); **plus** the per-sender balance constraint — F2 doesn't natively model it and adding it may push the structured sub-problem to NP-hard (open question). Start with the unconstrained core + a feasibility post-filter.
- **Done when:** characterization-corpus-first refactor (capture current (ok,err) over the domain → refactor → reproduce exactly), exactness differential vs the brute matcher on n≤8, polynomial scaling demonstrated above the old cap, Codex review.

### 2b. Convex routing prototype (multi-hop / global) `[M]`
- **Draws on:** F5 (Angeris optimal CFMM routing is convex), F6 (Diamandis decomposition + `CFMMRouter.jl`).
- **Surface:** `split_routing.py` (the *default heuristic* profile + the >2-pool case — note the opt-in exact `staircase_exact` 2-pool solver already exists), `routing.py` (fixed 2-hop).
- **Gain:** provable global-optimum routing over arbitrary topology / heterogeneous pools, replacing the derivative-seed heuristic for multi-hop.
- **Blocker:** Phase 0. Prototype first as an **off-chain oracle** (Julia `CFMMRouter.jl`) that differential-checks the production heuristic and quantifies the optimality gap — that alone is shippable value pre-bridge.
- **Done when:** off-chain solver reproduces/beats the heuristic on a corpus; optimality-gap report; (post-Phase-0) integer-bridged on-chain variant.

### 2c. Convex-flow unification (research-grade) `[L]`
- **Draws on:** F8 (Diamandis convex network flows — one model spanning CoW-netting *and* CFMM routing, edge-decomposable).
- **Surface:** routing/clearing architecture.
- **Gain:** a single solver for clearing + routing; only pursue if 2a/2b prove out and a unified surface is wanted.

---

## Phase 3 — Mechanism & economics

### 3a. Risk-based water-filling ADL + `fraction_bps` tuning `[M]`
- **Draws on:** G9 (unique optimal water-filling ADL: minimize max leverage; distribution-free / Sybil / path-independent), H16 (fixed-spread liquidations over-liquidate; rescue often needs <50%).
- **Surface:** the experimental profit-priority `_apply_liquidation_adl` in `experiments/perp_np_clearinghouse_v1/perp_np_core.py`; `perp_v2` `partial_liquidate` (already wired — `apply/guard/effect`) + `fraction_bps`.
- **Gain:** replace/evaluate the profit-priority ADL against the optimal water-filling rule; tune `fraction_bps` so liquidations don't over-seize.
- **Blocker / caveat:** G9 is a single 2026 preprint, and its optimality is single-asset isolated-margin — the **N-party clearinghouse / cross-margin** extension is open. Validate before promoting.
- **Done when:** water-filling ADL implemented behind the experimental clearinghouse, differential vs the profit-priority rule, the four robustness properties tested, scope caveat documented.

### 3b. Formal zUSD peg-game stress-test model `[M, modeling]`
- **Draws on:** H1 (deleveraging-spiral submartingale), H4 (multi-equilibrium redemption coordination game + computable de-peg threshold θ\*), H3 (stability-vs-run tradeoff), H5 (non-linear recovery threshold).
- **Surface:** `zusd.py` redemption + decaying base-rate (these **are** in core); the economics work in `experiments/zusd_hybrid_economics_v1/`.
- **Gain:** a redemption-pressure peg game with a computable de-peg boundary; a rule that **redemption-fee/base-rate tightening must be co-tuned with run resilience** (don't optimize the peg in isolation).
- **Done when:** a calibrated model (extending the existing Julia sims) that locates the regime where zUSD's redemption+base-rate+buyback becomes insufficient; design constraint added to the economics notes.

---

## Phase 4 — Strategic / research-gated

### 4a. ZK folding/lookup migration — **decision first, not code** `[L]`
- **Draws on:** G1 (HyperNova), G2 (ProtoStar), G3 (Lasso/Jolt), G4 (Bailey-Miller machine-checked SNARK soundness as the target assurance class for `proof_verifier.py`).
- **Surface:** `zk/state_proof_risc0/`, `src/integration/proof_verifier.py`.
- **Gate:** every Angle-4 gain is **behind a RISC0/FRI → Plonkish/multilinear-PCS (Jolt-style) migration.** First deliverable is a **cost-comparison memo**: STARK-native recursion (RISC0 continuations/aggregation) vs migrating to a Jolt-style IVC. Do **not** start the migration before that memo justifies it.

### 4b. 4th research run for the still-open gaps `[research, before any build]`
The report's zero-citation gaps — fund these before building:
- **Insurance-fund adequacy under correlated shocks** (ruin theory / Cramér-Lundberg, VaR / expected-shortfall CCP default-fund sizing, EVT correlated tail loss). Zero citations.
- **Funding-rate mechanism design** + funding-timing game, and the **keeper / liquidation-as-auction** equilibrium (the no-arb tethering formulas were *refuted*). Re-fetch the unresolved lead arXiv 2410.21446 first.
- **Verkle / authenticated data structures for `jmt.py`.** Zero citations.

---

## Do NOT build on (refuted / dead-ends — from the report's verification)

- **General multi-asset uniform-price clearing as a tractable MIP** — refuted; don't assume general polynomiality (only the singleton+swap core is polynomial).
- **Ausubel clinching as *unconditionally* strategyproof-efficient** — refuted; holds only under private values + diminishing marginal valuations.
- **Linear TWAP-cost-vs-window scaling** — refuted (0-3); there is no clean linear cost-vs-window law. Don't lengthen the window for "safety."
- **No-arbitrage perp-spot funding tethering formulas** (`F=S(1+r/κ)`) — refuted; funding mechanism design stays open.
- **IACR 2024/435 VRF "unbiasability-sufficiency" / MRV-insufficiency claims** — refuted; ground the VRF primitive in Algorand sortition + Aequitas, not 2024/435.
- **F7's fee price-tracking bound as an implementation rounding-error bound** — `[UNVERIFIED]` for that repurposing.

---

## Suggested first cut

If picking three to start: **1a (VRF+Aequitas tie-break)** and **1b (pool-depth oracle design)** are the highest value-to-effort and have no Phase-0 dependency; **Phase 0 (integer bridge)** should start in parallel because it unblocks everything in Phase 2. Everything in Phase 4b should be a research run, not engineering, until citations exist.
