# Disaster State Minimization Analysis

Status: analysis + checked Lean strengthening (2026-06-11).

Companion to `docs/DISASTER_HARDNESS_ASSURANCE_METRIC.md` (DHAI),
`docs/DISASTER_STATE_COVERAGE.md` (125 named axes), and the disaster proof
cluster under `lean-mathlib/Proofs/`. Snapshot at time of writing: raw DHAI
80.8/100, level L3, 29 of 125 axes closed, production-blocker cap 84.

The question addressed: **where can the set of reachable disaster states be
made strictly smaller, and by what mechanism?** Four levers, ordered by
strength:

1. make the disaster state *unrepresentable* (parameter algebra / typestate),
2. make disaster dwell *time-bounded* (potential descent), not just non-worsening,
3. make the open frontier *smaller than it looks* (dominance closure dividend),
4. make the residual *explicitly priced* (insurance sized from the clamp model).

Lever 2 ships with a new checked theorem
(`DisasterPotentialSafety.strict_descent_reaches_threshold`). Lever 1's
flagship instance ships as
`PerpEpochSafety.liquidation_penalty_funded_after_bounded_move` (see the
mechanism analysis doc). Levers 3–4 are derivations over existing proofs.

---

## 1) Lever 1 — Unrepresentability: close the incentive-mediated bad-debt class

### 1.1 Why this axis first

`CBCDisasterStateRefactors.lean` already demonstrates the house style:
fee-bypass killed by `feeCeil`, JIT extraction killed by
`CooldownStabilityPool`, route cycles killed by the `AcyclicRoute` typestate.
Each converts a monitored bad state into a non-state. The largest remaining
*economic* disaster class with this shape is perp bad debt via underpaid
liquidation.

### 1.2 The precise mechanism of the disaster

The disaster trace is not arithmetic overflow; it is a rational-agent fixpoint:

```
account at maintenance  →  clamped move to band edge  →  equity ≈ 0
→  realized penalty = min(equity, raw) ≈ 0            (math.py:379)
→  keeper net = −gas < 0  →  keeper skips             (rational choice)
→  position survives epoch below maintenance
→  second clamped move  →  equity < 0                 (bad debt axis reached)
```

Every step is currently *allowed*: `inv_margin_params_ordered`
(`invariants.py:55`) only enforces `m ≤ maint_eff`, and
`inv_liquidation_penalty_lt_maint` (`invariants.py:96`) only enforces
`penalty < maint_eff`. Neither couples `penalty` to `m`.

### 1.3 The closing inequality

Proven (`liquidation_penalty_funded_after_bounded_move`): if

```
penalty·(10⁴ + m) ≤ 10⁴·(maint_eff − m)               (FUNDED-LIQ)
```

then after **any** single clamped oracle move, post-move equity covers the
full penalty at the post-move price, for every position size and price level.
The first arrow of the disaster trace breaks: the keeper's reward is funded by
the liquidated account itself, the `min` cap provably never binds, the skip
branch is never rational (given the gas floor, `liquidation_profitable_on_clamp_band`),
and the two-epoch continuation is never reached. The class becomes
unreachable through *every* trace whose per-epoch move respects the clamp —
which is exactly the guarantee class the epoch engine already targets.

Production parameters satisfy (FUNDED-LIQ) with ≈1.9× slack
(`witness_production_funded_liquidation`: `525,000 ≤ 1,000,000`), but no
invariant pins them there: `m` can drift from 500 to 547 bps silently, and at
548 the class reopens with no alarm. **Minimization action: add
`inv_funded_liquidation` to `src/core/perp_v2/invariants.py` and to the
parameter-update guard lane.** One inequality, one new unrepresentable class.

### 1.4 The same lever under oracle degradation

`CBCDisasterStateRefactors.dynamicMarginRatio` already raises margin with
oracle staleness: `min(maxMargin, base + penalty·staleness)`. Composition
note: since (FUNDED-LIQ) is monotone in `maint_eff` (slack increases as
`maint_eff` rises), a staleness-inflated margin *strengthens* the funded
property along the degradation path. The pair (dynamic margin, FUNDED-LIQ) is
therefore jointly sound without re-derivation: degraded oracles can only make
liquidation better-funded until the freeze point. Worth recording as a
one-line corollary when the dynamic-margin lane is instantiated.

---

## 2) Lever 2 — Bounded dwell: from "risk never worsens" to "risk drains"

### 2.1 The looseness in the current guard shape

`DisasterPotentialSafety.SafeTransition`:

```
postRisk ≤ preRisk  ∨  recoveryCertificate
```

This admits trajectories that sit at `postRisk = preRisk` **forever** at any
risk level, certificate-free. "No new disasters" is compatible with permanent
maximal danger. Every monitored axis whose guard has this shape inherits the
weakness: the system can plateau one step below the disaster predicate
indefinitely, where any unmodeled perturbation finishes the job.

### 2.2 The strengthening (now checked)

New in `DisasterPotentialSafety.lean`:

```
StrictDescentAbove θ trace :=
  at every adjacent pair, risk > θ → next risk < risk

strict_descent_step_is_safe :
  each strict step is in particular a SafeTransition (refines, not replaces)

strict_descent_reaches_threshold :
  StrictDescentAbove θ (a :: l) → a − θ ≤ length l →
  ∃ reading in the trace, reading ≤ θ
```

Interpretation: if the controller commits to strict descent while above a
danger threshold `θ` (each accepted step strictly reduces the ℕ-valued risk
potential whenever it exceeds `θ`), then dwell time above `θ` is **bounded by
the initial excess** `a − θ`. Disasters become transient with an explicit,
machine-checked recovery deadline, instead of merely non-compounding.

This is the discrete Lyapunov argument in its weakest useful form: no
continuity, no probabilistic drift, just well-foundedness of ℕ — which is
exactly what the receipt-based runtime can attest (each receipt carries
`preRisk`, `postRisk`, and the threshold; the checker verifies the strict
decrement pointwise, and the dwell bound follows globally with no further
trust).

### 2.3 Minimization actions

- Extend the disaster-potential receipt schema with `θ` and enforce the
  strict decrement on the risk-increase-free branch whenever `preRisk > θ`;
  keep the recovery-certificate branch as the only escape hatch above `θ`.
- Report, per axis, the implied worst-case dwell `currentRisk − θ` in the
  DHAI evidence. A bounded-dwell axis is strictly harder than a monitored
  axis and should score accordingly (today the metric cannot distinguish
  them).
- The plateau-at-θ behavior is intentional and honest: below the threshold
  the predicate imposes nothing (witnessed by `witness_strict_descent`, whose
  trace re-rises after touching θ). Choosing θ per axis is a policy decision,
  not a proof obligation.

---

## 3) Lever 3 — Dominance closure dividend: the open frontier is smaller than 96

### 3.1 What the antichain machinery already licenses

`DisasterAntichainBasis.basis_rejection_lifts_to_all_bad`: if rejection is
upward-closed along the severity/dominance order and a basis element is
rejected, **every axis it dominates is rejected for free**. The proof exists;
the bookkeeping does not. Axis accounting in
`docs/DISASTER_STATE_COVERAGE.md` counts 96 open axes as a flat set, which
overstates the true frontier if any open axis is dominated by another open
axis (close the dominator, get the dominated one at zero marginal guard
cost), and understates progress when a closed axis dominates open ones that
remain "open" only in the ledger.

### 3.2 Minimization actions

- Materialize the dominance relation over the 125 named axes (it is implicit
  in the taxonomy crosswalk, `docs/DISASTER_SHAPE_TAXONOMY_CROSSWALK.md`) and
  publish the **minimal open antichain** — the set of open axes not dominated
  by any other open-or-closed axis. That number, not 96, is the real guard
  workload. Mark dominated axes `closed-by-dominance(b)` with the basis
  element `b` and the lifting theorem as the citation.
- Guard placement is then a hitting-set problem over motifs, and
  `ForbiddenTraceMinor.guard_hitting_set_rejects_all_bad` is the soundness
  side of exactly that: a guard family that hits every minimal motif rejects
  all bad traces. Choosing the *minimum* hitting set is the optimization; the
  theorem guarantees any hitting set suffices, so the optimization is
  safe-by-default and can be greedy.
- Closure order should follow the partial order: closing a maximal
  (most-dominating) open basis element first maximizes the per-proof
  dividend. The current campaign order (chronological discovery order, per
  the runtime hardening docs) leaves this dividend on the table.

This lever changes no runtime code at all; it converts existing theorems into
accounting and prioritization, shrinking the *effective* disaster frontier
and concentrating proof effort where one artifact closes many axes.

---

## 4) Lever 4 — Price the residual: insurance sized from the clamp model

With (FUNDED-LIQ) enforced, single-epoch-move bad debt is unrepresentable, so
the insurance fund's actual job becomes precise: it covers exactly the
**liveness-failure tail** — `L ≥ 2` consecutive epochs in which a
below-maintenance position is not liquidated (censorship, keeper outage,
chain halt), plus any gap risk beyond the clamp model's scope.

Compounding the clamp: after `L` adversarial epochs the price factor is
`(1 + m/10⁴)^L`, so per unit notional the worst-case shortfall is

```
shortfall(L) = (1 + m/10⁴)^L − 1 − maint_eff/10⁴     (per unit notional, ≤ 0 means none)
```

With production `m = 500`, `maint_eff = 600`:

```
L = 1:  5.00% − 6% = −1.00%   → no shortfall (this is FUNDED-LIQ's regime)
L = 2: 10.25% − 6% = +4.25%   → 425 bps of notional at risk
L = 3: 15.76% − 6% = +9.76%
```

So the entire insurance requirement is generated at `L ≥ 2`, and it is linear
in the open interest that can plausibly be stranded for `L` epochs.
Minimization actions:

- Declare a target liveness budget `L*` (the number of consecutive
  no-liquidation epochs the system is engineered to survive) and size the
  fund as `insurance ≥ OI_cap · shortfall(L*)`. This replaces an unanchored
  balance with a derived one, and turns "insurance adequacy" into a checkable
  inequality between three declared parameters — same shape as
  (FUNDED-LIQ), provable with the same toolkit as
  `PerpLiquidationInsuranceBound`.
- The two knobs that shrink `shortfall(L)` are visible in the formula:
  lower `m` (tighter clamp ⇒ slower worst-case drift, at the cost of slower
  price discovery after gaps) and per-epoch forced partial deleveraging of
  below-maintenance positions (caps the exposure factor between epochs, the
  ADL lane already has the machinery). Both are parameter/policy changes
  inside already-modeled lanes, not new mechanisms.
- A two-epoch Lean lemma (`|P₂ − P₀| ≤ (2m + m²/10⁴)·P₀/10⁴` by two
  applications of the clamp bound and one triangle inequality) is the natural
  next proof artifact; the `L`-epoch version is an induction over the same
  step. This would move `shortfall(L)` from doc arithmetic to checked
  arithmetic.

---

## 5) What this does *not* claim

- No claim that the 125-axis registry is complete (the metric doc itself caps
  the score for this reason); levers 2–3 reduce and re-price the *known*
  frontier.
- The funded-liquidation result covers the clamped single-epoch move class;
  beyond-clamp gaps and multi-epoch liveness failures are deliberately routed
  to Lever 4 (priced residual), not claimed impossible.
- `strict_descent_reaches_threshold` binds only axes whose risk is scored in
  ℕ by a receipt the runtime actually verifies; it is a guard-shape upgrade,
  not a statement that all axes have such scores today.

## 6) Summary

| Lever | Action | Disaster-state effect | Cost |
|---|---|---|---|
| 1 | `inv_funded_liquidation` (R1 of mechanism doc) | single-epoch bad-debt class unrepresentable | one runtime inequality |
| 2 | strict-descent receipts above per-axis θ | unbounded dwell → dwell ≤ initial excess (checked) | receipt field + checker rule |
| 3 | dominance accounting + minimal antichain + hitting-set order | effective open frontier < 96; per-proof closure dividend | bookkeeping only |
| 4 | `insurance ≥ OI_cap·shortfall(L*)` | residual tail explicitly priced; adequacy checkable | parameter declaration + one lemma |
