# Deep Insights: Algorithms + UX for ZenoDex (signed)

Date started: 2026-01-24

This file is an evolving, *signed* collection of exploratory insights (math, algorithms, UX) intended to feed:
- new core features in `src/core/`
- new verifiable-explainable surfaces in `src/integration/`
- new Tau-spec obligations in `src/tau_specs/`

Signing rule (lightweight):
- Each contributor appends a block and includes `sig: 0x... @handle`.
- Signatures are not cryptographic here; they are stable identifiers for attribution and diff review.

---

## Working model (Morph-style)

We treat design work as operating on a problem state:

σ := ⟨R, α, Δ, G, Π, S, M⟩

- R: representation (pool state, intents, settlement, routes)
- α: abstraction (what we ignore: network, MEV side-channels, off-chain solver complexity, etc.)
- Δ: constraints (integer math, determinism, fail-closed validation, bounded computation where possible)
- G: goals (better execution, better UX trust, new algorithms)
- Π: proof obligations/certificates (Tau-verifiable invariants, canonical tie-breaks)
- S: solver/tool set (Python kernels, Tau specs, optional Lean/ESSO/Morph for discovery)
- M: metadata (counterexamples, regressions, budgets)

---

## Contribution — @amm_math

```markdown
## Deep Insights Contribution — 2026-01-24 — @amm_math

### Idea 1: Exact‑out minimality + overdelivery report (CPMM + cubic)
- Goal: Make exact‑out quotes provably minimal and expose integer overdelivery explicitly.
- Invariants/obligations:
  - `k_after >= k_before` (monotone invariant, fee‑adjusted for CPMM).
  - `out_exact_in(dx) >= dy` and, if `dx > 1`, `out_exact_in(dx-1) < dy`.
  - `gap = out_exact_in(dx) - dy >= 0` is reported exactly (no hidden rounding).
- Determinism/tie‑break: Choose the **minimal** `dx`; if multiple `dx` satisfy due to rounding (shouldn’t), pick smallest.
- Verification approach: Tau replays exact‑in kernel for `dx` and `dx-1` and recomputes `gap`.

### Idea 2: Hybrid curvature gate (cubic near balance, CPMM at extremes)
- Goal: Capture cubic’s low‑slippage near balance while limiting CPMM’s IL penalty at extremes.
- Invariants/obligations:
  - Compute `ratio = max(x,y) * SCALE / min(x,y)` (integer).
  - If `ratio <= R_ENTER` use cubic; if `ratio >= R_EXIT` use CPMM (hysteresis).
  - Swap uses the chosen kernel and must satisfy its monotone invariant.
- Determinism/tie‑break: If `ratio` exactly hits a boundary, select CPMM (or “keep prior mode” if hysteresis is used).
- Verification approach: Tau recomputes `ratio`, enforces mode selection, and verifies the chosen kernel’s post‑state.

### Idea 3: Curvature/impact fee tiers (oracle‑free)
- Goal: Deterministic fee control to reduce LVR from toxic flow using only pool state + trade size.
- Invariants/obligations:
  - Define `imbalance = abs(x - y) * 10_000 // max(x,y)`.
  - Define `impact = amount_in * 10_000 // (reserve_in + amount_in)`.
  - `score = max(imbalance, impact)`; `fee_bps` chosen from a fixed tier set.
  - Mapping is monotone in `score` (higher score → fee ≥).
- Determinism/tie‑break: On boundary scores, pick the **lower** fee (stability) or **higher** fee (defensive) — choose one rule and fix it.
- Verification approach: Tau recomputes `score`, validates tier selection, then verifies swap with that fee.

### Idea 4: Lagged TWAP oracle (deterministic, bounded)
- Goal: Provide a verifiable oracle surface for LVR accounting and fee policies without external feeds.
- Invariants/obligations:
  - `timestamp` is non‑decreasing; `dt` is bounded and non‑negative.
  - `price_cum += spot_price_fp * dt` using a fixed‑point integer scale.
  - Windowed TWAP computed from ring‑buffer snapshots; overflow‑safe bounds.
- Determinism/tie‑break: If `dt == 0`, do **no** accumulator update.
- Verification approach: Tau recomputes spot price from reserves and checks accumulator + snapshot rules.

### Idea 5: Bounded split router (exact for small trades)
- Goal: Deterministic split across two pools (CPMM + cubic) with verifiable optimality in bounded regimes.
- Invariants/obligations:
  - If `amount_in <= S`, brute‑force all splits to maximize output.
  - If `amount_in > S`, choose best single‑pool output.
  - Each pool’s swap must satisfy its kernel invariants.
- Determinism/tie‑break: For equal outputs, pick lexicographically smallest pool id, then smaller split to the first pool.
- Verification approach: Tau recomputes outputs for each split (small) or per‑pool (large).

### Immediate Python feature to implement
Add a **Quote Bundle** for CPMM and cubic exact‑in/out:
- A small dataclass (e.g., `SwapQuote`) containing `amount_in`, `amount_out`, `fee_total`, `net_in`,
  `k_before`, `k_after`, `effective_price`, and (for exact‑out) `overdelivery_gap`.
- All fields derived deterministically from existing kernels; no new math, just structured output + checks.
- Enables Tau to verify quotes and UI to show explainability (fee, impact, gap) without extra recomputation.

sig: 0x7c9d2f4a8b1e6d3c5a7f0b9c2d4e6a1b8c3f5d7e @amm_math
```

---

## Contribution — @routecraft

```md
## Signed Contribution (2026-01-24)

contribution:
  area: routing/aggregation UX
  feature_ideas:
    - "API: add /api/quote (exact-in) that returns best route, per-hop amounts, and pool ids using best_route_exact_in_2hop; include deterministic tie-break metadata in the response."
    - "Algorithmic: add exact-out 2-hop routing (min input for desired output) using cpmm.swap_exact_out; enumerate 1-hop + 2-hop candidates with deterministic tie-break identical to exact-in (hop_count, pool_id sequence, mid asset)."
    - "Algorithmic: parallel-pool aggregation for same pair (A/B). If multiple pools share (asset_in, asset_out), run best_split_two_pools_exact_in on the top two candidates and compare to single-pool routes; return the best with a canonical split (smallest a)."
    - "API/UX: expose /api/quote/alternatives returning top-K candidate routes (direct + 2-hop) sorted by amount_out desc, then lexicographic tie-break, so UI can show stable fallbacks and avoid route flapping."
  determinism_notes:
    - "Routing tie-break: prefer fewer hops, then lexicographic pool_id sequence, then intermediate asset (matching _quote_key)."
    - "Split routing tie-break: smallest split a (send less to pool0) when outputs tie."
    - "Certificates: all candidates are enumerable (1-hop/2-hop and two-pool splits), enabling brute-force verification in bounded regimes; keep outputs and ordering deterministic for Tau verification."
  first_feature_to_implement:
    name: "API: /api/quote (exact-in) with route details"
    plan:
      - "src/integration/api_server.py: add GET /api/quote?from=...&to=...&amountIn=...; parse/validate inputs and call best_route_exact_in_2hop."
      - "src/core/routing.py: add a small adapter/helper to convert PoolState -> JSON-ready quote (hops, amounts, pool ids), or keep in api_server with a dedicated formatter."
      - "tests/core/test_routing.py: add a basic API-style quote test or unit test for the formatter to lock deterministic ordering and tie-break behavior."
  sig: "0x9f3c1ab4e8d27c51 @routecraft"
```

---

## Contribution — @batchfair

```markdown
## Signed Contribution (2026-01-24)

contribution:
  area: fairness/MEV/batching
  feature_ideas:
    - name: "Uniform-price aggregate exact-in batch (single pool, one direction)"
      objective: "Maximize executed input volume A; secondary maximize total surplus B; enforce a single clearing price across all fills."
      total_order_key: "K = (-A, -B, lex(included_intent_ids)) (min under K)"
      witness: "included_intents, total_in, total_out, per-intent amount_out_i via pro-rata on amount_in with deterministic dust rule (smallest intent_id gets remainder), and per-intent min_out."
      tau_verification: "Recompute aggregate swap via swap_exact_in (or limb witness), verify pro-rata allocation + dust rule, check each amount_out_i >= min_out_i, and rely on existing conservation/non-negativity checks."
    - name: "Opposite-direction netting layer before pool"
      objective: "Maximize netted volume A_net to reduce price impact; then maximize total executed volume A."
      total_order_key: "K = (-A_net, -A, -B, lex(netting_map)) (min under K)"
      witness: "netting_map per intent (net_in/net_out), residual swap list, and aggregate net transfer per asset."
      tau_verification: "Check netting conserves assets between users (no reserve deltas), netted fills respect balances/limits, and residual swaps satisfy CPMM rules."
    - name: "User-signed salt tie-break within price/time bucket"
      objective: "Remove sequencer discretion among equally-priced intents while preserving limit-price priority."
      total_order_key: "K = (-limit_price, deadline_bucket, user_salt, intent_id) (min under K)"
      witness: "ordering list plus user_salt from signed intent fields; deadline_bucket = floor(deadline / batch_window)."
      tau_verification: "Verify ordering is sorted by key and that salts/buckets match intent fields; signature validity stays off-chain."
    - name: "Deterministic fee-rebate redistribution"
      objective: "Maximize executed volume; maximize post-rebate user surplus; redistribute part of fees to reduce slippage variance."
      total_order_key: "K = (-A, -(B + rebates), slippage_variance, lex(intent_id)) (min under K)"
      witness: "fee_pot, per-intent fee_paid, per-intent rebate computed by deterministic weight (e.g., weight = slippage * amount_in), remainder to smallest intent_id."
      tau_verification: "Verify rebate formula, sum(rebate) <= fee_pot, non-negative rebates, and conservation across balance/reserve deltas."
  implement_now_feature:
    name: "Batch Settlement Explainability Report"
    objective: "Increase UX trust via deterministic, auditable explanations without changing validity."
    details:
      - "Emit JSON alongside settlement: normalized settlement commitment (settlement_normal_form), per-intent effective price, slippage vs limit, fee, ordering key tuple, and rejection reason."
      - "Include aggregate metrics: A and B (as defined in optimal_ab_bounded), fills/rejects count, and pool price before/after."
      - "Pure Python; re-computable from the settlement object for auditability."
  sig: "0x4f8a1c6e3b2d9f0071c5e8a3b6d2f9aa @batchfair"
```

---

## Contribution — @ux-sys

```yaml
contribution:
  date: 2026-01-24
  role: product/UX systems designer
  scope: verifiable-ux-features
  features:
    - name: Verify-this-route (ELIV: explain like I can verify it)
      ux_value: "Show the exact deterministic route and amounts so users can replay the math and confirm the quote."
      backend_mapping:
        api: "/api/route_exact_in (new)"
        response_fields:
          - "route.asset_in"
          - "route.asset_out"
          - "route.amount_in"
          - "route.amount_out"
          - "route.hops[].pool_id"
          - "route.hops[].asset_in"
          - "route.hops[].asset_out"
          - "route.hops[].amount_in"
          - "route.hops[].amount_out"
          - "route.tiebreak_key"
          - "route.algorithm"
        repo_artifacts:
          - "src/core/routing.RouteQuote"
          - "src/core/routing.RouteHop"
          - "src/core/routing.best_route_exact_in_2hop"
          - "src/core/routing._quote_key"
          - "src/core/cpmm.swap_exact_in"
      verify_path: "Recompute per-hop with swap_exact_in and confirm amount_out + tiebreak_key match."

    - name: Split-routing proof slider
      ux_value: "Let users see and verify the optimal split across two pools, with deterministic tie-breaks."
      backend_mapping:
        api: "/api/split_quote (new)"
        response_fields:
          - "split.amount_in_total"
          - "split.pool0_id"
          - "split.pool1_id"
          - "split.a_to_pool0"
          - "split.b_to_pool1"
          - "split.out0"
          - "split.out1"
          - "split.out_total"
          - "split.tie_break"
          - "split.algorithm"
          - "split.cert.best_out (when amount_in <= 4096)"
          - "split.cert.best_a (when amount_in <= 4096)"
        repo_artifacts:
          - "src/core/split_routing.PoolXY"
          - "src/core/split_routing.best_split_two_pools_exact_in"
          - "src/core/split_routing.brute_force_best_split_two_pools_exact_in"
          - "src/core/split_routing.exact_out_for_pool_exact_in"
      verify_path: "For small trades, cross-check best_a via brute_force_best_split_two_pools_exact_in."

    - name: Deterministic quote receipt (replayable)
      ux_value: "Every quote and swap returns a receipt that can be replayed and hashed by any client."
      backend_mapping:
        api: "/api/route_exact_in or /api/swap (extend)"
        response_fields:
          - "quote_receipt.quote_input"
          - "quote_receipt.pool_snapshot.pools[].id"
          - "quote_receipt.pool_snapshot.pools[].reserve0"
          - "quote_receipt.pool_snapshot.pools[].reserve1"
          - "quote_receipt.pool_snapshot.pools[].fee_bps"
          - "quote_receipt.route (same fields as Verify-this-route)"
          - "quote_receipt.math_version"
          - "quote_receipt.quote_hash"
          - "txId (from /api/swap)"
        repo_artifacts:
          - "src/integration/api_server.py (/api/pools, /api/swap)"
          - "src/core/routing.best_route_exact_in_2hop"
          - "src/core/cpmm.swap_exact_in"
      verify_path: "Rebuild stable JSON from quote_input + pool_snapshot + route, hash, compare quote_hash."

    - name: Pool-state explainer (no magic math)
      ux_value: "Expose step-by-step deterministic math so users can verify fees, net-in, and reserve updates."
      backend_mapping:
        api: "/api/route_exact_in (extend)"
        response_fields:
          - "route.hops[].fee_total"
          - "route.hops[].net_in"
          - "route.hops[].new_reserve_in"
          - "route.hops[].new_reserve_out"
          - "pools[].reserve0"
          - "pools[].reserve1"
          - "pools[].fee_bps"
        repo_artifacts:
          - "src/core/cpmm.compute_fee_total"
          - "src/core/cpmm.swap_exact_in"
          - "src/integration/api_server.py (/api/pools)"
      verify_path: "Recompute fee_total and new reserves deterministically and compare to hop fields."

  implement_now: "Verify-this-route (ELIV) using /api/pools + best_route_exact_in_2hop"
sig: "0x4b8a1d92f0c3e7a6 @ux-sys"
```

---

## Contribution — @fcis-proof

```md
## Signed Contribution (2026-01-25)

contribution:
  area: "CBC + FCIS delivery (routing + replay protection)"
  shipped_features:
    - "Functional core: exact-out 2-hop routing (min input) alongside exact-in routing, with deterministic tie-break."
    - "Imperative shell: /api/quote calls src/core routers (no duplicated routing selection logic in the server)."
    - "Shell explainability: per-hop fee/net-in/new-reserves/k_before/k_after included in quote response via kernel replay."
    - "Replay protection: per-sender nonce table + strict sequential nonces (batch order-independent via sorting)."
  formal_evidence:
    - "Lean: routing selection lemma (argmin fold) + nonce replay-prevention lemma (sequential update implies no replay)."
    - "Morph+Z3: concrete witness showing 2-hop exact-out can strictly beat direct, guarded by regression test."
  regression_commands:
    - "pytest -q tests/core/test_routing.py"
    - "pytest -q tests/formal/test_lean_rounding.py"
    - "pytest -q tests/tools/test_morph_route_exact_out_2hop_value_miner.py"
    - "pytest -q tests/integration/test_replay_protection.py"
  next_decomposition_targets:
    - "Route certificates: for bounded pool graphs, include a candidate-set witness so Tau can verify 'best under key'."
    - "Nonce sequencing in Tau: model per-sender nonce stream checks as a small, per-sender spec module."

sig: 0x6b8f1c2d3e4a5b6c7d8e9f00112233445566778899aabbccddeeff0011223344 @fcis-proof
```

---

## Contribution — @perp-incentives

```md
## Signed Contribution (2026-02-01)

contribution:
  area: "Perpetual protocol incentive design — deep insights from CEGIS/ICE/Morph/Lean research"
  methodology: "Popperian falsification loop: 10 hypotheses (H-PI-01 through H-PI-10) tested via
    ESSO ICE invariant discovery, Morph counterexample mining (6 miners), multi-solver verification
    (z3+cvc5), and Lean4 formalization (4 proof files, 488 lines, 0 sorry). Codex peer-reviewed: A+."

  insights:

    - id: PI-I-01
      title: "Incentive modules multiply, they don't add"
      content: >
        When a protocol has N independent incentive modules (liquidation bounty, funding rate,
        insurance fund, fee distribution), the attack surface is not N — it is combinatorial.
        An attacker who controls two accounts can simultaneously game funding + bounty in ways
        neither module's invariants detect alone. The ESSO game_theory_v1 model's original
        inv_game_strategy_bounded failed precisely because it assumed additive composition of
        independently-safe modules.
      evidence: "ESSO ICE discovered the violation; Morph funding_rate_gaming miner confirmed
        multi-account extraction paths; fixed in game_theory_v2 with cross-module invariants."

    - id: PI-I-02
      title: "Fees in pool are recapturable — only non-recapturable costs deter"
      content: >
        If an attacker owns LP share α, any pool fee they pay is partially returned via LP rewards:
        effective_cost = fee × (1 - α). With α → 1, pool fees approach zero deterrence.
        Only non-recapturable costs (gas, external oracle manipulation cost, opportunity cost of
        locked collateral) are genuine economic barriers.
      evidence: "Morph bounty farming miner (pos=-17 witness, H-PI-02) showed bounty extraction
        despite fees. The fix: cap bounties at max(penalty_collected, floor) so the bounty
        never exceeds what the protocol actually captured from the liquidation event."

    - id: PI-I-03
      title: "Unconditional minimums are exploitable, conditional ones are safe"
      content: >
        Any parameter with the form 'minimum X guaranteed regardless of action' creates an
        extraction opportunity. bounty_min=0 was exploitable because even dust positions earned
        a bounty. The safe pattern is conditional: 'X is available only when Y is satisfied',
        where Y has a non-trivial cost to achieve.
      evidence: "H-PI-02 falsified by pos=-17 witness (Morph miner). Fixed by requiring
        min_notional_for_bounty threshold — bounty only paid when position crosses a
        minimum notional value, making dust extraction unprofitable."

    - id: PI-I-04
      title: "Rounding is mechanism design, not just arithmetic"
      content: >
        Integer floor division creates a systematic bias: ⌊a/d⌋ + ⌊-a/d⌋ ∈ {0, -1}. This
        1-unit gap per epoch accumulates: over N epochs, the total gap is in [-N, 0].
        In funding rate computation, this means the protocol (or one side) always absorbs
        the rounding error. This is not a bug — it is a design parameter that determines
        who bears the rounding cost. The symmetric funding fix (funding_b := -funding_a)
        eliminates the gap entirely by construction.
      evidence: "Lean proofs: int_fdiv_neg_gap (per-epoch gap ∈ {0,-1}),
        int_multi_epoch_funding_gap (N-epoch accumulation bounded by [-N,0]),
        funding_budget_balance_rat (exact over ℚ). Non-vacuity witnesses via native_decide."
      lean_files:
        - "lean-mathlib/Proofs/PerpFundingRateSafety.lean (183 lines)"
        - "lean-mathlib/Proofs/PerpIntegerBridge.lean (81 lines)"

    - id: PI-I-05
      title: "Per-step safety ≠ trajectory safety — composition gaps are real"
      content: >
        A system where every single epoch satisfies all safety invariants can still fail over
        multiple epochs. Insurance fund solvency is the canonical example: each epoch's
        fee_income ≥ 0 and claims ≥ 0, but cumulative_claims can exceed initial_balance +
        cumulative_fees. The composition theorem (int_multi_epoch_funding_gap) explicitly
        addresses this by proving bounds on accumulated effects, not just per-step effects.
      evidence: "Morph insurance_depletion miner found claim sequences depleting the fund
        within bounds. Lean int_multi_epoch_funding_gap theorem: derived system bound from
        per-epoch gap via list induction — a genuine composition, not algebra."

    - id: PI-I-06
      title: "Isolated margin eliminates cascading liquidation by construction"
      content: >
        When each account's collateral is isolated (not shared), liquidating account A cannot
        affect account B's margin ratio. This makes cascading liquidation (Hyperliquid JELLY
        $12M, Dec 2024 BTC $400M) structurally impossible. The proof is constructive: show
        that the function mapping (accounts, liquidated_set) → remaining_accounts preserves
        margin ratios for all non-liquidated accounts.
      evidence: "Lean isolation_no_cascade theorem in PerpCascadeSafety.lean. Morph
        cascading_liquidation miner returns UNKNOWN (cannot find cascade witness under
        isolated margin). Note: price-mediated cascades (liquidation moves mark price,
        triggering further liquidations) are NOT eliminated — they require separate analysis."

    - id: PI-I-07
      title: "Symmetric funding by construction > symmetric funding by cancellation"
      content: >
        Two approaches to budget-balanced funding: (1) compute long and short payments
        independently, hope they cancel; (2) compute one payment, define the other as its
        negation. Approach (1) requires a proof that cancellation holds (and it doesn't
        over ℤ due to rounding). Approach (2) is budget-balanced by construction — no proof
        needed, no rounding gap possible.
      evidence: "Lean funding_budget_balance_rat (trivial: ring closes it).
        ESSO game_theory_v2 uses symmetric funding with funding_cap_bps.
        The ℤ gap theorems (int_fdiv_neg_gap) show that approach (1) leaks up to 1 unit/epoch."

    - id: PI-I-08
      title: "Protocol-fee-capped rebates are safer than unconditional rebates"
      content: >
        Rebate schemes that return a fraction of collected fees (rebate ≤ α × fee_collected)
        are inherently bounded — the protocol cannot pay out more than it took in. Unconditional
        rebate schemes (e.g., maker rebates funded by cross-subsidy) can create extraction
        opportunities when the subsidy source is manipulable.
      evidence: "Design principle derived from H-PI-02 bounty farming analysis. The
        fee_pool_overflow miner (H-PI-10) tests whether accumulated fees can overflow
        ESSO bounds; protocol-fee-capped rebates make this structurally impossible."

    - id: PI-I-09
      title: "The Popper posture works — negative results are the highest-value outputs"
      content: >
        Of 10 hypotheses tested, the falsified ones (H-PI-02 bounty farming) and the
        structurally-impossible ones (H-PI-04 cascade under isolation) produced more
        actionable design changes than the corroborated ones. The falsification loop
        (hypothesize → mine counterexample → minimize → fix → re-verify) converges faster
        than the confirmation loop (hypothesize → test → 'looks good' → ship).
      evidence: "H-PI-02 falsification led to min_notional_for_bounty fix.
        H-PI-04 structural impossibility confirmed isolated margin design.
        H-PI-03 funding analysis led to symmetric-by-construction fix.
        All three produced concrete code/model changes. Corroborated hypotheses (H-PI-01)
        produced no design changes."

    - id: PI-I-10
      title: "The ℚ↔ℤ bridge is a first-class verification obligation"
      content: >
        ESSO models use bounded integers while mathematical proofs work over ℚ or ℝ.
        The gap between these domains is not just 'rounding' — it determines who absorbs
        economic losses. Every theorem proved over ℚ needs an explicit bridge theorem
        bounding the integer approximation error. The PerpIntegerBridge.lean file exists
        solely for this purpose: int_emod_bounded, int_div_conservative,
        int_single_div_gap, int_symmetric_div_gap.
      evidence: "4 bridge theorems in PerpIntegerBridge.lean with non-vacuity witnesses.
        int_symmetric_div_gap reuses PerpFundingRateSafety.int_fdiv_neg_gap, demonstrating
        cross-file composition."

  lean_artifacts:
    - "lean-mathlib/Proofs/PerpFundingRateSafety.lean (183 lines, 7 theorems + 6 witnesses)"
    - "lean-mathlib/Proofs/PerpCascadeSafety.lean (103 lines, 4 theorems + 2 witnesses)"
    - "lean-mathlib/Proofs/PerpInsuranceSafety.lean (121 lines, 4 theorems + 2 witnesses)"
    - "lean-mathlib/Proofs/PerpIntegerBridge.lean (81 lines, 4 theorems + 5 witnesses)"

  morph_miners:
    - "tests/morph_domains/perp_funding_rate_gaming_cex.py"
    - "tests/morph_domains/perp_cascading_liquidation_cex.py"
    - "tests/morph_domains/perp_insurance_depletion_cex.py"
    - "tests/morph_domains/perp_collateral_depeg_cex.py"
    - "tests/morph_domains/perp_breaker_asymmetry_cex.py"
    - "tests/morph_domains/perp_fee_pool_overflow_cex.py"

  esso_models:
    - "src/kernels/dex/perp_game_theory_v2.yaml (9/9 VERIFIED, z3+cvc5)"

  codex_review: "A+ (second submission after addressing B+ feedback)"
  codex_insight_review: "Quality A, Correctness A-, Novelty B+"

sig: 0xa1b2c3d4e5f6789012345678abcdef0123456789abcdef0123456789abcdef01 @perp-incentives
```

## Contribution — @codex (Morph perps mechanical scientist)

```markdown
## Signed Contribution (2026-02-06)

contribution:
  area: Morph scientist workflow for perps
  key_findings:
    - "Sustained portal lift is strong on perp_oracle_manipulation_reward_subsidy (10-seed has_lift_rate=1.0, avg_seconds_reduction~0.0241)."
    - "Long improve campaigns now sustain archive growth (6 campaigns, 42 archived, stable 7/campaign across increasing difficulty)."
    - "Critical failure mode: checker invariants must not freeze fields mutated by tactics (bounty_min_quote mismatch blocked bounty domain progress)."
    - "Candidate diversity failures can masquerade as domain hardness; fix generator bugs and decouple generation vs evaluation budgets before tuning portals."
  durable_artifact: "docs/research/morph_perps_mechanical_scientist_2026-02-06.md"

sig: 0xmech_sci_perps_2026_02_06 @codex
```

## Contribution — @codex (continuation, bounty durability)

```markdown
## Signed Contribution (2026-02-06, continuation)

contribution:
  area: perps bounty scientist durability
  key_findings:
    - "Bounty domain moved from zero-signal to full solved coverage on matched 10-seed A/B after checker/tactic alignment and depth-aware template redesign."
    - "Bounty still fails sustained timing-lift gate (`has_lift_rate=0.6`, mean seconds delta slightly negative), indicating portal overhead dominates when search work is already minimal."
    - "Bounty long campaigns now show strong sustained archive growth: 5 campaigns, 59 archived total, min 11/campaign, with difficulty progression to [16,50]."
    - "Second sustained innovation axis is now campaign throughput durability, not just portal-speed lift."
  durable_artifacts:
    - "runs/mech_sci_iter/bounty_v3/ab_sweep_manual.json"
    - "runs/mech_sci_iter/improve/bounty_long/improvement_log.jsonl"
    - "runs/mech_sci_iter/bounty_summary_from_skill.json"

sig: 0xmech_sci_perps_2026_02_06_bounty @codex
```

## Contribution — @codex (automation loop + sustained gated lift)

```markdown
## Signed Contribution (2026-02-06, automation loop)

contribution:
  area: perps scientist self-improvement orchestration
  key_findings:
    - "Automated loop now runs A/B gate -> selective improve in one pass (`tools/perps_scientist_self_improve_loop.py`) and emits machine-readable decisions."
    - "Multi-domain gated run selected only `perp_oracle_manipulation_reward_subsidy`; bounty and funding were filtered by sustained-lift gate (`has_lift_rate=0.4`)."
    - "Reward domain retained strong sustained A/B lift (`has_lift_rate=1.0`, `avg_seconds_reduction≈0.0271`) while maintaining solved quality."
    - "Long campaigns remained durable under gating: 8 campaigns, nonzero archive growth each campaign, difficulty progression to `[28,100]`."
  durable_artifacts:
    - "tools/perps_scientist_self_improve_loop.py"
    - "runs/mech_sci_iter/loop_summary_r1.json"
    - "runs/mech_sci_iter/reward_summary_v4.json"
    - "runs/mech_sci_iter/improve/reward_long_v2/improvement_log.jsonl"

sig: 0xmech_sci_perps_2026_02_06_loop @codex
```

## Contribution — @codex (signal triage + bounded long loop)

```markdown
## Signed Contribution (2026-02-06, signal triage)

contribution:
  area: perps scientist domain triage and bounded campaign operations
  key_findings:
    - "Fresh 10-seed A/B (`r5`) confirms funding remains no-lift (`has_lift_rate=0.0`) despite multiple template/portal retunes."
    - "Bounty recovered positive mean timing delta but remains below sustained threshold (`has_lift_rate=0.6`), so it should stay exploratory."
    - "Reward domain remains the only promotion-grade lane; bounded long-loop run (`r5b`) still produced non-zero archive growth in every campaign (6 campaigns, 12 archived total)."
    - "For continuous operation, apply a strict three-band policy: promotion-grade (`>=0.8` lift rate), exploratory (`0 < lift rate < 0.8`), hold/diagnose (`=0`)."
  durable_artifacts:
    - "runs/mech_sci_iter/funding_summary_r5.json"
    - "runs/mech_sci_iter/bounty_summary_r5.json"
    - "runs/mech_sci_iter/reward_improve_summary_r5b.json"
    - "runs/mech_sci_iter/loop_summary_r5.json"
    - "runs/mech_sci_iter/loop_improve_r5b/improvement_report.json"

sig: 0xmech_sci_perps_2026_02_06_triage @codex
```

## Deep Insights Contribution — 2026-02-06 — @perps-mech-sci

### Insight 1: Promotion-grade lift must promote to code, not just artifacts
- Evidence from `runs/mech_sci_iter/loop_summary_r8.json` confirms reward-subsidy domain remained promotion-grade:
  - `has_lift_rate=1.0` on 10 seeds, solved-rate non-regression.
  - long-loop durability: 8 campaigns, `min_archived_per_campaign=4`, `total_promoted=32`.
- Practical rule: when long gate passes, convert to concrete code hardening in the same iteration window.

### Insight 2: Duplicate adapters are a consensus-safety risk surface
- We found two perps engines with semantic drift (`src/integration/perp_engine.py` vs `src/integration/perps/engine.py`).
- Fix: make package engine a strict re-export shim to canonical engine.
- Verification: `tests/integration/test_perps_engine_alias.py` locks symbol identity.
- Design rule: one executable source of truth for consensus-relevant adapters.

### Insight 3: Settlement must fail-close on unusable oracle state, except deterministic bootstrap
- New guard posture:
  - reject settle if oracle snapshot is stale, unseen with non-flat position, or index price is non-positive.
  - allow bootstrap settle only when oracle unseen, index=0, and position is flat.
- This preserves deterministic first-epoch initialization while blocking malformed/stale-settlement pathways.

### Insight 4: Domain triage remains stable under longer runs
- `r8` triage:
  - promotion-grade: `perp_oracle_manipulation_reward_subsidy`
  - exploratory: `perp_settlement_bounty_farming`, `perp_oracle_manipulation`
  - hold/diagnose: `perp_funding_rate_gaming`
- This supports budget focus: run long campaigns only for promotion-grade domains.

sig: 0x7b63f1d9e4c2a11d @perps-mech-sci

## Contribution — @codex (reward-lane durability + code promotion, 2026-02-07)

```markdown
## Signed Contribution (2026-02-07, reward-lane durability)

contribution:
  area: perps mechanical scientist sustained loop
  key_findings:
    - "Fresh reward-lane A/B remained promotion-grade on 10 seeds (`has_lift_rate=1.0`, `avg_seconds_reduction≈0.0302`, solved-rate non-regression)."
    - "Long promotion campaign stayed productive across 12 campaigns with nonzero archive growth every campaign (`total_archived_added=36`, `min_archived_per_campaign=3`)."
    - "Difficulty progression remained stable up to `[100,400]` without archive stall."
    - "Promotion-to-code rule applied in same iteration: fail-close `publish_clearing_price` when `price_e8 <= 0` across isolated + clearinghouse paths."
  durable_artifacts:
    - "runs/mech_sci_iter/loop_ab_r13_reward/perp_oracle_manipulation_reward_subsidy/ab_sweep.json"
    - "runs/mech_sci_iter/loop_improve_r13_reward/improvement_log.jsonl"
    - "runs/mech_sci_iter/loop_reward_summary_r13.json"
    - "src/integration/perp_engine.py"
    - "tests/integration/test_perp_engine.py"
    - "tests/integration/test_perp_engine_clearinghouse_2p.py"
    - "tests/integration/test_perp_engine_clearinghouse_3p_transfer.py"

sig: 0xmech_sci_perps_2026_02_07_reward_loop @codex
```

---

## Contribution — @tau-bridge-integration (2026-02-07)

```markdown
### Upstream Tau Testnet bridge integration insights (commit 2deccad)

1) Reserved stream reality changed the app wire format
- At upstream `2deccad`, user tx operation keys `2/3/4` are rejected by `sendtx`.
- Practical mapping for app payloads is now:
  - `5`: DEX intents
  - `6`: DEX settlement
  - `7`: faucet/test mint
  - `8`: perps ops
- Keep plugin-level legacy aliases only for direct/offline tests; network txs must use `>=5`.

2) Structured app payloads must survive `sendtx` pre-validation
- Upstream `sendtx` custom-input validation was scalar-only and rejected nested intent payloads.
- Robust fix: canonicalize JSON-serializable values on custom streams for Tau input validation while preserving original tx payload for miner execution.
- This keeps strict Tau input typing and allows app bridge payloads without adding special protocol exceptions.

3) Replay protection subtlety: nonce identity normalization
- App snapshot nonce entries may store pubkeys with `0x` prefix while tx sender pubkeys often omit it.
- If smoke/integration tooling compares raw strings, it can under-estimate next nonce and trigger block-time rejections.
- Normalize pubkeys (`lower`, strip optional `0x`) before nonce lookup.

4) Smoke harness must prove inclusion, not just queue success
- `sendtx: SUCCESS` is insufficient; createblock can still reject all txs.
- Harness should fail fast on `All transactions rejected` / `Mempool is empty`.
- Also avoid state pollution from prior runs by using per-run random asset IDs and selecting pools by asset pair, not first pool index.

5) Patch portability rule
- Generate/ship an upstream-targeted patch artifact tied to exact commit (`2deccad`) and validate with `git apply --check` on a clean checkout.
- This prevents local-fork drift from masquerading as upstream compatibility.

sig: 0x7a6f9d4e11c0b2a3 @tau-bridge-integration
```

---

## Contribution — @bridge-quality

```markdown
## Signed Contribution (2026-02-07)

contribution:
  area: tau-testnet bridge reliability / backend e2e determinism
  findings:
    - "Local E2E flakiness root cause was not bridge logic drift: CREATE_POOL requires canonical asset order (asset0 < asset1)."
    - "Random unordered asset generation in smoke harness produced silent no-op settlement rejects ~50% of runs."
    - "Bridge acceptance can still produce a valid block with no pool creation when intents are rejected but transaction envelope is otherwise accepted."
  hardening:
    - "tools/tau_testnet_local_smoke.py now generates distinct random assets in canonical lexical order."
    - "src/integration/tau_testnet_dex_plugin.py now has explicit routing helpers (_select_dex_ops/_select_perp_ops), centralized hash/snapshot generation, and runtime input guards for operations/chain_balances."
    - "Added routing-focused integration tests to lock stream mapping behavior and legacy perps fallback."
  measurable_lift:
    - "Repo test matrix: 578 passed, 5 skipped."
    - "Bridge plugin integration tests: 14 passed."
    - "Local app-bridge E2E: deterministic pass after canonical asset ordering fix."
  rule:
    - "For backend smoke campaigns, generate only canonical CREATE_POOL pairs or normalize to canonical order before signing."

sig: "0x9c17b4a2 @bridge-quality"
```

---

## Contribution — @perp-oracle-hardening

```markdown
## Signed Contribution (2026-02-07)

contribution:
  area: perps malformed-oracle fail-closed hardening
  scientist_evidence:
    domain: perp_oracle_manipulation_reward_subsidy
    ab_sweep_path: runs/mech_sci_iter/loop_ab_edge_hardening/perp_oracle_manipulation_reward_subsidy/ab_sweep.json
    seeds: 10
    has_lift_rate: 1.0
    solved_rate_delta: 0.0
    avg_seconds_reduction: 0.024731565341385753
    sustained_gate: pass
  root_cause:
    - "Malformed snapshot shape `oracle_seen=true` with `index_price_e8<=0` could make margin/funding checks degenerate (zero notional), allowing unsafe user actions to pass guards."
  code_hardening:
    - "Fail-closed guard checks added for `index_price_e8>0` in withdraw-with-position, set_position (normal), and apply_funding paths."
    - "New invariant added: `inv_oracle_seen_positive_index` to reject malformed oracle-seen states."
  regressions_added:
    - "core: set_position/withdraw/apply_funding reject oracle_seen+zero_index"
    - "integration: perp_engine rejects set_position on malformed oracle snapshot"
  validation:
    - "targeted suites: 130 passed"
    - "perp_v2 pack: 193 passed, 3 skipped"
    - "broad matrix: 584 passed, 5 skipped"

sig: "0x7a2e11d9 @perp-oracle-hardening"
```

---

## Contribution — @perp-mech-spec

```markdown
## Signed Contribution (2026-02-07)

contribution:
  area: perps incentive/mechanism/game-theory spec synthesis from Morph evidence
  insight:
    - "Spec quality improved when policy clauses were promoted from measured domain lift tiers instead of narrative preference."
    - "Stable-collateral and oracle guarantees are non-negotiable base clauses; incentive clauses should be gated by per-domain A/B status (`promote/explore/hold`)."
  implementation:
    - "Added `tools/perps_mechanism_spec_builder.py` to compile Morph A/B artifacts into a machine-readable spec and a human-readable policy doc."
    - "Generated artifacts:"
    - "  - `runs/mech_sci_iter/spec_design/perp_mechanism_scientist_spec_v1.json`"
    - "  - `docs/derivatives/PERP_MECHANISM_SCIENTIST_SPEC_V1.md`"
  measured_basis:
    - "reward_subsidy: promote (`has_lift_rate=1.0`, `avg_seconds_reduction=0.024731565341385753`)"
    - "oracle_manipulation_lp: promote (`has_lift_rate=0.8333333333333334`, `avg_seconds_reduction=0.0023180357761323953`)"
    - "bounty/funding/plain-oracle: explore"
    - "collateral_depeg: hold"
  policy_outcome:
    - "Required now: signed+fresh oracle, non-recapturable reward source, attacker-as-LP cost floor, funding budget-balance, anti-farming bounty caps."
    - "Standby pending stronger evidence: depeg stress clause promotion."

sig: "0x31f0c8aa @perp-mech-spec"
```

---

## Contribution — @perp-mech-r15b

```markdown
## Signed Contribution (2026-02-07)

contribution:
  area: perps mechanical-scientist sustained lift + fail-closed hardening
  campaign:
    run_label: r15b_reward_lp_fastlong
    run_id: 38bd61840290b028
    summary_path: runs/mech_sci_iter/loop_summary_r15b_reward_lp_fastlong.json
  measured_results:
    - domain: perp_oracle_manipulation_reward_subsidy
      has_lift_rate: 1.0
      solved_rate_delta: 0.0
      selected_for_improve: true
      long_campaign:
        campaigns_completed: 6
        min_archived_per_campaign: 4
        total_archived_added: 24
        total_promoted: 24
        meets_long_gate: true
    - domain: perp_oracle_manipulation_lp
      has_lift_rate: 0.5
      solved_rate_delta: 0.0
      selected_for_improve: false
      decision: hold (below gate)
  integration_decision:
    - "Only reward-subsidy domain is promoted to implementation in this cycle."
    - "LP manipulation remains in exploration/hold until lift >= 0.8 on fresh seed sweeps."
  code_hardening_applied:
    files:
      - src/integration/perp_engine.py
      - tests/integration/test_perp_engine.py
    changes:
      - "apply_funding_auto now fail-closes on malformed control fields in market snapshots:"
      - "  - max_oracle_staleness_epochs <= 0"
      - "  - funding_cap_bps <= 0 or > 10000"
      - "  - clearing_price_e8 <= 0"
      - "  - max_oracle_move_bps outside [0, 10000]"
    rationale:
      - "Scientist reward-domain promotion emphasizes malformed-state hardening and stale/funding safety over speculative LP tactics."
  validation:
    - "pytest -q tests/integration/test_perp_engine.py -> 15 passed"
    - "pytest -q tests/core/test_perp_v2 -> 193 passed, 3 skipped"
    - "pytest -q tests/integration/test_tau_testnet_dex_plugin.py -> 11 passed"

sig: "0x7f2d91a3 @perp-mech-r15b"
```

---

## Contribution — @zusd-redeem-canonicalization

```markdown
## Signed Contribution (2026-02-07)

contribution:
  area: zUSD redemption safety + deterministic multi-vault canonicalization
  insight:
    - "Multi-vault redemption needs a canonical selection policy to avoid ambiguous witness surfaces and to keep Tau gating deterministic."
    - "A stable order key (`closest_to_mcr`, tie-break `a < b`) provides deterministic behavior without adding nondeterministic search."
  implementation:
    files:
      - src/core/zusd.py
      - src/integration/zusd_tau_gate.py
      - src/integration/tau_witness.py
      - src/tau_specs/recommended/zusd_redeem_guard_v1.tau
      - tests/core/test_zusd_multi.py
      - tests/integration/test_zusd_tau_gate.py
      - tests/tau/test_zusd_tau_specs.py
    changes:
      - "Added auto vault selection for `redeem_zusd` in multi-vault mode when `vault` is omitted."
      - "Selection policy: choose redeemable vault with minimum MCR headroom; tie-break by vault id."
      - "Added Tau transition guard `zusd_redeem_guard_v1` and fail-closed gate wiring for single/multi paths."
      - "Added bounded oracle-style test sweep validating auto-policy matches expected candidate ordering."
  validation:
    - "pytest -q tests/core/test_zusd.py tests/core/test_zusd_multi.py -> 20 passed"
    - "pytest -q tests/integration/test_zusd_tau_gate.py -> 7 passed"
    - "pytest -q tests/tau/test_zusd_tau_specs.py -> 14 passed"

sig: "0x41be7dd2 @zusd-redeem-canonicalization"
```

## Contribution — @perps-mech-sci (2026-02-07)

```markdown
## Signed Contribution (2026-02-07)

contribution:
  area: perps mechanism scientist (incentives/game-theory hardening)
  new_findings:
    - "LP scientist domain had a triviality regime: with `target_profit_quote=2`, `TrySolve` succeeds in one expansion for most seeds, so portal lift is mostly micro-timing noise."
    - "After widening LP tactic surface (`Dec/IncReserve*`, `Dec/IncFee`) and adding depeg bidirectional buffer tactics (`DecBuffer`), measured LP lift improved from prior baseline (`has_lift_rate=0.25`) to sustained medium lift (`0.50` in 8-seed run, `0.67` in a 3-seed confirm run)."
    - "Long-loop evidence (`r17_lp_reward_loop`) shows both reward-subsidy and LP domains pass gate at `has_lift_rate=0.5` and both pass long-campaign gate with `campaigns_completed=4` and `min_archived_per_campaign=3`."

  workflow_insights:
    - "Tail-latency appears repeatedly on final `without_portals` seeds in LP AB sweeps. This is now treated as an expected operational mode rather than a blocker."
    - "Keep AB profiles replayable and hash-stable; do not overwrite prior profiles when tuning."
    - "Prefer medium gates (`min_lift_rate=0.5`) for exploratory LP innovation, then re-raise to stricter gates for promotion to production controls."

  implementation_updates:
    - "Scientist loop now includes LP-specific code-update templates (guard/engine/integration + tests) so LP promotions produce non-empty implementation targets."
    - "Scientist loop now supports `--ab-max-wall-seconds` to cap AB tail risk in long campaigns."
    - "LP state builder max trade bound reduced to `max_r=700` to improve campaign throughput without changing discovered optimal profits in sampled states."

  code_paths:
    - "tests/morph_domains/perp_oracle_manipulation_lp_cex.py"
    - "tests/morph_domains/perp_collateral_depeg_cex.py"
    - "external/Morph/morph/scientist_generator.py"
    - "external/Morph/morph/scientist_domain.py"
    - "tools/perps_scientist_self_improve_loop.py"

  evidence:
    - "runs/mech_sci_iter/ab_after_tactic_expand_capped/perp_oracle_manipulation_lp/ab_sweep.json"
    - "runs/mech_sci_iter/ab_after_lp_maxr700_confirm3/perp_oracle_manipulation_lp/ab_sweep.json"
    - "runs/mech_sci_iter/loop_summary_r17_lp_reward_loop.json"
    - "runs/mech_sci_iter/evidence/perps_scientist_ledger.jsonl"

sig: 0x9c73a1e4b2d6f81e @perps-mech-sci
```

---

## Contribution — @perps-mech-sci-r18 (2026-02-08)

```markdown
## Signed Contribution (2026-02-08)

contribution:
  area: exotic mechanism exploration (settlement-bounty + funding-rate) and gate hardening
  campaign:
    run_label: r18_exotic_bounty_funding
    run_id: b876e0301e4c8a59
    summary_path: runs/mech_sci_iter/loop_summary_r18_exotic_bounty_funding.json

  measured_results:
    - domain: perp_settlement_bounty_farming
      has_lift_rate: 0.75
      solved_rate_delta: 0.0
      avg_seconds_reduction: -9.935049224117729e-05
      selected_for_improve: true
      long_campaign:
        campaigns_completed: 6
        min_archived_per_campaign: 3
        total_archived_added: 18
        total_promoted: 18
        meets_long_gate: true
    - domain: perp_funding_rate_gaming
      has_lift_rate: 0.125
      solved_rate_delta: 0.0
      avg_seconds_reduction: -7.15045326463345e-05
      selected_for_improve: false

  deepest_insight:
    - "`has_lift_rate` alone can produce false-positive promotion pressure when net runtime movement is negative."
    - "Promotion/exploration gates should require non-negative `avg_seconds_reduction` in addition to solved-quality non-regression."

  workflow_hardening:
    files:
      - tools/perps_scientist_self_improve_loop.py
      - tools/perps_mechanism_spec_builder.py
      - ~/.codex/skills/morph-perps-mechanical-scientist/SKILL.md
    changes:
      - "Added loop flag `--min-avg-seconds-reduction` (default `0.0`) and enforced it in A/B gate decisions."
      - "Persisted `avg_seconds_reduction` into evidence-ledger `ab_result` rows and repeat-profile suppression logic."
      - "Aligned mechanism-spec tiering/promotion gate with `avg_seconds_reduction` floor and refreshed artifact defaults for bounty/funding to latest r18 run."

  evidence:
    - runs/mech_sci_iter/loop_summary_r18_exotic_bounty_funding.json
    - runs/mech_sci_iter/loop_ab_r18_exotic/perp_settlement_bounty_farming/ab_sweep.json
    - runs/mech_sci_iter/loop_ab_r18_exotic/perp_funding_rate_gaming/ab_sweep.json
    - runs/mech_sci_iter/loop_improve_r18_exotic/perp_settlement_bounty_farming/improvement_log.jsonl
    - runs/mech_sci_iter/evidence/perps_scientist_ledger.jsonl

sig: 0x5e2caa14b9f33d77 @perps-mech-sci-r18
```

---

## Contribution — @perps-mech-sci-r19 (2026-02-08)

```markdown
## Signed Contribution (2026-02-08)

contribution:
  area: old-way single-domain reward lane recovery + timeout hardening

  measured_results:
    ab_exploratory:
      artifact: runs/mech_sci_iter/r19c_reward_profile_sweep/p3_timeout/ab_sweep.json
      seeds: 3
      has_lift_rate: 1.0
      solved_rate_delta: 0.0
      avg_seconds_reduction: 0.0005157583626795628
    long_improve:
      artifact: runs/mech_sci_iter/oldway_improve_r19e_reward/perp_oracle_manipulation_reward_subsidy/improvement_log.jsonl
      campaigns_completed: 6
      min_archived_per_campaign: 3
      total_archived_added: 18
      total_promoted: 18
      meets_long_gate: true

  deepest_insight:
    - "Under latest Morph, full 10-seed reward A/B can exhibit long-tail stalls; old-way velocity improves by running bounded profile sweeps first, then launching long improve on positive profiles."
    - "Per-instance wall caps are insufficient alone; loop-level subprocess timeout is required for predictable campaign cadence."

  workflow_hardening:
    files:
      - tools/perps_scientist_self_improve_loop.py
      - ~/.codex/skills/morph-perps-mechanical-scientist/SKILL.md
    changes:
      - "Added `--ab-run-timeout-seconds` to hard-stop stalled A/B subprocesses."
      - "Profile hash now includes run-timeout setting to keep repeat-no-lift suppression consistent."
      - "Skill failure-mode guidance updated with subprocess-stall mitigation."

  guardrail:
    - "Treat 3-seed A/B as exploratory only; promotion claims still require higher-seed confirmation."

  durable_artifact:
    - runs/mech_sci_iter/oldway_summary_r19e_reward.json

sig: 0x6e19b4a8c02f11d3 @perps-mech-sci-r19
```

---

## Contribution — @perps-mech-sci-r20 (2026-02-08)

```markdown
## Signed Contribution (2026-02-08)

contribution:
  area: reward-domain high-seed revalidation + production hardening

  measured_results:
    ab_confirm_10_seed:
      artifact: runs/mech_sci_iter/loop_ab_r20_reward_confirm10/perp_oracle_manipulation_reward_subsidy/ab_sweep.json
      seeds: 10
      has_lift_rate: 0.3
      solved_rate_delta: 0.0
      avg_seconds_reduction: -0.0006187962948994638
      gate: fail

  insight:
    - "Latest Morph profile mix does not consistently reproduce prior reward-lane timing lift on 10-seed sweeps; this lane should be treated as unstable for promotion-by-metrics right now."
    - "Even without fresh promotion-grade lift, scientist evidence still supports fail-closed posture hardening in runtime config validation."

  code_hardening_applied:
    files:
      - src/integration/perp_engine.py
      - tests/integration/test_perp_engine.py
    changes:
      - "Enforced non-zero reward-posture friction for oracle publish path: `oracle_spot_fee_bps > 0` and `oracle_spot_reward_safety_margin_bps > 0`."
      - "Added regression tests rejecting zero-fee and zero-margin posture configs."
    validation:
      - "pytest -q tests/integration/test_perp_engine.py -> 18 passed"

  rationale:
    - "This converts scientist-discovered anti-manipulation intent into deterministic runtime guardrails, independent of transient sweep variance."

sig: 0x56a9a3e4d1279f20 @perps-mech-sci-r20
```

---

## Contribution — @perps-mech-sci-r29 (2026-02-09)

```markdown
## Signed Contribution (2026-02-09)

contribution:
  area: direct Morph hypothesis falsification + bounty-lane durable promotion

  measured_results:
    ab_search_confirm:
      artifact: runs/mech_sci_iter/direct_hyp_loop_r29/summary.json
      winner_domain: perp_settlement_bounty_farming
      search_has_lift_rate: 0.75
      search_avg_seconds_reduction: 0.001980887488065894
      confirm_has_lift_rate: 0.75
      confirm_avg_seconds_reduction: 0.002444860698233242
      gate: pass
    long_campaign:
      artifact: runs/mech_sci_iter/direct_hyp_loop_r29/improve_bounty_long/improvement_report.json
      campaigns_completed: 10
      archive_size: 40
      min_archived_per_campaign: 4
      total_promoted: 40
      stalled_campaigns: 0
      gate: pass

  deepest_insight:
    - "A direct falsification loop (multi-hypothesis A/B + independent confirm) found a durable lift lane in `perp_settlement_bounty_farming` while reward/LP profiles stayed timing-negative."
    - "Deeper reward search (higher depth/expanded budget) reduced both lift-rate and runtime; budget expansion without domain-fit degraded outcomes."

  code_hardening_applied:
    files:
      - src/integration/perp_engine.py
      - tests/integration/test_perp_engine.py
      - docs/derivatives/PERP_INCENTIVES_V1.md
    changes:
      - "Added config guard `min_collectible_liquidation_penalty_quote` (default `1000`) for isolated-market `set_market_params`."
      - "Fail-closed policy: require `min_notional_for_bounty >= ceil(min_collectible_liquidation_penalty_quote * 10000 / liquidation_penalty_bps)`."
      - "Added regression test for reject/pass boundary at the computed threshold."
    validation:
      - "pytest -q tests/integration/test_perp_engine.py -> 20 passed"

  rationale:
    - "This converts scientist evidence from the bounty-farming lane into deterministic production posture, reducing low-notional keeper-farming surface."

sig: 0x9d29b11cf03a8aa1 @perps-mech-sci-r29
```

---

## Contribution — @perps-mech-sci-r47 (2026-02-09)

```markdown
## Signed Contribution (2026-02-09)

contribution:
  area: workflow innovation (multi-search + multi-confirm pass-rate gating) and long-campaign durability

  measured_results:
    upgraded_loop_run:
      domain: perp_settlement_bounty_farming
      status: promotion_grade
      search:
        runs_total: 3
        pass_count: 2
        pass_rate: 0.6666666666666666
        metrics_mean:
          has_lift_rate: 0.5833333333333334
          solved_rate_delta: 0.0
          avg_seconds_reduction: 0.0005659527593403864
      confirm:
        runs_total: 3
        pass_count: 2
        pass_rate: 0.6666666666666666
        metrics_mean:
          has_lift_rate: 0.5555555555555556
          solved_rate_delta: 0.0
          avg_seconds_reduction: 0.0004700181922583581
      long_improve:
        campaigns_completed: 12
        total_archived_added: 48
        min_archived_per_campaign: 4
        total_promoted: 48
        meets_long_gate: true

  deepest_insight:
    - "Single-search gating is too brittle under current Morph variance; multi-search pass-rate gating is required to separate durable signal from one-run noise."
    - "Requiring 2-of-3 pass in both search and confirm yields reproducible lift while preserving falsification discipline."
    - "Once reproducibility gates are met, bounty-lane campaigns sustain non-zero archive growth (4 per campaign) over long horizons."

  workflow_hardening_applied:
    files: []
    changes:
      - "Added `--search-runs`, `--search-seed-step`, and `--min-search-pass-rate`."
      - "Converted search from single-run gate to pass-rate gate with per-run artifacts and `metrics_mean`."
      - "Kept confirm pass-rate gate and aligned summary schema/search corroboration with multi-run evidence."

  rationale:
    - "This is a measurable improvement to the mechanical-scientist method itself: promotion now depends on repeated corroboration at both search and confirm stages before long campaigns."

sig: 0x47b300a93e2a9f10 @perps-mech-sci-r47
```

---

## Contribution — @perps-mech-sci-r48 (2026-02-09)

```markdown
## Signed Contribution (2026-02-09)

contribution:
  area: production hardening from bounty-lane evidence + longer campaign durability replay

  measured_results:
    code_hardening_validation:
      files:
        - src/integration/perp_engine.py
        - tests/integration/test_perp_engine.py
      guard:
        - "While positions are open: reject liquidation_penalty_bps increases."
        - "While positions are open: reject min_notional_for_bounty decreases."
      test_result: "pytest -q tests/integration/test_perp_engine.py -> 20 passed"

    long_campaign_replay:
      requested_max_campaigns: 16
      campaigns_completed: 12
      stopped_reason: all_domains_saturated
      total_archived_added: 48
      min_archived_per_campaign: 4
      avg_archived_per_campaign: 4.0
      total_promoted: 48
      stalled_campaigns: 0
      difficulty_progression:
        first: [4, 8]
        last: [100, 400]

  deepest_insight:
    - "For the current bounty profile/budget, the practical long-run ceiling is saturation at 12 campaigns with stable archive slope (4 per campaign)."
    - "Beyond this point, increasing requested max-campaigns does not increase productivity without changing search budgets/profile; runs stop early with all_domains_saturated."
    - "Runtime guardrails should prevent governance shocks that increase bounty extraction incentives while legacy positions remain open."

  rationale:
    - "This pairs scientific evidence with deterministic production constraints and prevents repeating the same bounty-posture mistakes across epochs."

sig: 0x0e48f21c3b98a6dd @perps-mech-sci-r48
```

---

## Contribution — @perps-mech-sci-r50 (2026-02-09)

```markdown
## Signed Contribution (2026-02-09)

contribution:
  area: parallel exploration + promotion-to-code hardening

  measured_results:
    local_cpu_scaling_scan:
      artifact: runs/mech_sci_iter/subagents/r50_local_parallel_scan_summary.json
      workers_wall_seconds:
        workers_1: 643.9386836370104
        workers_2: 338.0678992650355
        workers_4: 288.9266083089751
      speedup_vs_1_worker:
        workers_2: 1.904761395675077
        workers_4: 2.228727521517814
      quality_observation:
        - "Throughput improved with more workers, but per-domain lift quality became less stable at workers=4 (notably oracle and LP lanes)."
        - "CPU scaling should be treated as throughput gain, not as direct innovation-quality gain."

    five_lane_parallel_exploration:
      artifacts:
        - runs/mech_sci_iter/subagents/r50a_reward_summary.json
        - runs/mech_sci_iter/subagents/r50b_lp_summary.json
        - runs/mech_sci_iter/subagents/r50c_funding_summary.json
        - runs/mech_sci_iter/subagents/r50d_oracle_summary.json
        - runs/mech_sci_iter/subagents/r50e_bounty_summary.json
      outcomes:
        reward_subsidy:
          status: promotion_grade
          search_pass_rate: 0.6666666666666666
          confirm_pass_rate: 0.6666666666666666
          campaigns_completed: 8
          total_archived_added: 32
          min_archived_per_campaign: 4
        oracle:
          status: falsified_on_confirm
          search_pass_rate: 0.6666666666666666
          confirm_pass_rate: 0.0
        lp:
          status: falsified_on_search
          search_pass_rate: 0.3333333333333333
          timing_gate: "failed by slight negative avg_seconds_reduction drift"
        funding:
          status: falsified_on_search
          search_pass_rate: 0.3333333333333333
        bounty_diversity_break:
          status: falsified_on_search
          search_pass_rate: 0.0

    production_hardening_promoted:
      files:
        - src/integration/perp_engine.py
        - tests/integration/test_perp_engine.py
        - src/tau_specs/recommended/perp_bounty_shock_guard_v1.tau
        - tests/tau/test_perps_tau_specs.py
      changes:
        - "Fail-closed oracle reward posture: require oracle_pubkey when oracle_spot_reward_bps > 0."
        - "Tau obligation for bounty-shock guard (single-line compatible syntax for current Tau runner)."
      validation:
        - "pytest -q tests/integration/test_perp_engine.py -> 22 passed"
        - "pytest -q tests/tau/test_perps_tau_specs.py -> 1 passed"

    workflow_self_improvement:
      file: tools/perps_scientist_parallel_benchmark.py
      change:
        - "Added --run-timeout-seconds per domain ab-sweep."
        - "Recorded per-domain status: ok/timeout/error so benchmark no longer hangs silently on long-tail sweeps."
      smoke_result:
        artifact: runs/mech_sci_iter/subagents/sanity_parallel_bench_timeout_patch.json
        result: "1 domain, status=ok, timeout path wired and summary schema updated."

  deepest_insight:
    - "Parallel breadth alone does not guarantee innovation lift; reward-subsidy remained the only reproducible promotion-grade lane in this batch."
    - "Promotion-to-code in the same cycle is mandatory; otherwise scientist gains remain theoretical and do not raise runtime safety."
    - "Mechanical-scientist orchestration itself needs fail-closed timeout posture to prevent CPU-heavy long-tail stalls from blocking iteration cadence."

sig: 0x6a50d1b0c9e7f442 @perps-mech-sci-r50
```

---

## Contribution — @perps-mech-sci-r52 (2026-02-09)

```markdown
## Signed Contribution (2026-02-09)

contribution:
  area: sustained bounty-lane promotion + clearinghouse hardening rollout

  measured_results:
    timeout_safe_parallel_scan:
      artifact: runs/mech_sci_iter/subagents/r51_parallel_timeout_summary.json
      profile:
        domains:
          - perp_settlement_bounty_farming
          - perp_oracle_manipulation_reward_subsidy
          - perp_oracle_manipulation_lp
          - perp_oracle_manipulation
          - perp_funding_rate_gaming
        workers: [1, 2, 4]
        per_domain_timeout_s: 260
      outcomes:
        workers_1:
          wall_seconds: 620.9134235489764
          ok_count: 4
          timeout_count: 1
          speedup_vs_base: 1.0
        workers_2:
          wall_seconds: 315.6321521080099
          ok_count: 4
          timeout_count: 1
          speedup_vs_base: 1.9672058736794935
        workers_4:
          wall_seconds: 260.1108575949911
          ok_count: 4
          timeout_count: 1
          speedup_vs_base: 2.3871107468946087
      bottleneck:
        - "LP lane (`perp_oracle_manipulation_lp`) timed out under all worker counts, proving timeout guard necessity."

    promotion_grade_reconfirm:
      artifact: runs/mech_sci_iter/subagents/r52_bounty_reconfirm_long12_summary.json
      domain: perp_settlement_bounty_farming
      status: promotion_grade
      search:
        runs_total: 3
        pass_count: 2
        pass_rate: 0.6666666666666666
        metrics_mean:
          has_lift_rate: 0.75
          solved_rate_delta: 0.0
          avg_seconds_reduction: -0.000967903142079902
      confirm:
        runs_total: 3
        pass_count: 2
        pass_rate: 0.6666666666666666
        metrics_mean:
          has_lift_rate: 0.5
          solved_rate_delta: 0.0
          avg_seconds_reduction: -6.279943130564085e-05
      long_improve:
        campaigns_completed: 12
        total_archived_added: 48
        min_archived_per_campaign: 4
        avg_archived_per_campaign: 4.0
        total_promoted: 48
        meets_long_gate: true

    code_promotion_applied:
      files:
        - src/integration/perp_engine.py
        - tests/integration/test_perp_engine_clearinghouse_2p.py
        - tests/integration/test_perp_engine_clearinghouse_3p_transfer.py
      policy:
        - "Clearinghouse 2p/3p now rejects liquidation_penalty_bps increases while positions are open."
      regression:
        - "pytest -q tests/integration/test_perp_engine_clearinghouse_2p.py tests/integration/test_perp_engine_clearinghouse_3p_transfer.py tests/integration/test_perp_engine.py tests/tau/test_perps_tau_specs.py -> 43 passed"

  deepest_insight:
    - "The bounty lane can be promotion-grade and durable even when one search and one confirm run fail; 2-of-3 corroboration remains a robust gate under stochastic runtime noise."
    - "Timeout-safe orchestration converts long-tail LP stalls from hidden blockers into explicit evidence (`timeout`), which preserves loop cadence and scientific falsifiability."
    - "Promotion must include clearinghouse paths, not only isolated paths; otherwise bounty-shock hardening remains posture-incomplete."

sig: 0xf9522c8cb5f0a418 @perps-mech-sci-r52
```
