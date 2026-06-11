# Mechanism Design Improvement Analysis

Status: analysis + checked Lean strengthenings (2026-06-11).

This document records concrete, mathematically precise improvement points in
ZenoDEX's incentive structures and mechanism design. Each section states:

1. the mechanism as currently specified (with file references),
2. the precise gap or looseness,
3. the improvement, with derivation,
4. what is now machine-checked in Lean versus what remains a recommendation.

Companion Lean strengthenings shipped with this analysis:

- `lean-mathlib/Proofs/PerpEpochSafety.lean`:
  `collateral_headroom_after_bounded_move`,
  `liquidation_penalty_funded_after_bounded_move`,
  `witness_production_funded_liquidation`
- `lean-mathlib/Proofs/PerpGameTheory.lean`:
  `liquidation_reward_floor`, `liquidation_profitable_on_clamp_band`,
  `liquidation_game_strict_dominant`, `liquidation_game_unique_nash`
- `lean-mathlib/Proofs/PerpMechanismDesign.lean`:
  `StrictlyDominantStrategy`, `strict_dominant_unique_nash`,
  `nash_iff_eq_of_strict_dominant`
- `lean-mathlib/Proofs/FundingImbalanceEV.lean`:
  `dualEV_eq_imbalance_form`, `two_mul_imbalance_sq_le_dualEV`,
  `dualEV_scale_invariant`, `dualEV_strict_mono_in_imbalance`
- `lean-mathlib/Proofs/MEVResistanceBound.lean`:
  `batch_dilution_compose`, `k_fold_batch_dilution`,
  `k_fold_batch_dilution_sharp`

Honest boundary: everything below is model-level mechanism analysis over the
declared parameter algebra. It does not claim production-network evidence, and
it inherits every boundary already declared by the cited proof files.

---

## 1) The liquidation incentive chain: from "solvent" to "funded"

### 1.1 Current state

Three previously disconnected results:

- Solvency after a bounded move
  (`PerpEpochSafety.collateral_nonneg_after_bounded_move`): if the per-epoch
  oracle move is clamped to `m` bps (`max_oracle_move_bps`,
  `src/core/perp_v2/math.py:206`-style clamp), maintenance margin is `maint ≥ m`
  (enforced by `inv_margin_params_ordered`,
  `src/core/perp_v2/invariants.py:55-57`), and the account met maintenance at
  the old price, then post-move equity satisfies `0 ≤ C + pos·(P' − P)`.
- Liquidator reward formula
  (`PerpGameTheory.liquidation_reward = |pos|·P·penalty/10000`).
- Liquidation dominance (`PerpGameTheory.liquidation_game_dominant`), which
  **assumes** non-negative net keeper profit as a hypothesis.

The runtime additionally caps the realized penalty at remaining collateral:
`liq_penalty_capped = min(collateral_after_pnl, raw_penalty)`
(`src/core/perp_v2/math.py:379`).

### 1.2 The gap

`equity ≥ 0` does not fund a positive penalty. The cap
`min(collateral_after_pnl, raw_penalty)` binds exactly when positions are
deepest underwater — meaning the keeper's reward is silently reduced precisely
in the states where liquidation matters most. The existing invariant

```
inv_liquidation_penalty_lt_maint:  penalty < maint_eff        (invariants.py:96)
```

does **not** close this gap, because it ignores the oracle move `m`.
Counterexample (passes both current invariants, fails funding): take
`m = maint_eff = 600`, `penalty = 50`. Then `m ≤ maint_eff` holds and
`penalty < maint_eff` holds, but a maintenance-exact account after a full
downward clamp move has equity exactly `0`, so the realized penalty is `0`,
keeper profit is `−gas`, and the rational keeper skips. The position then
enters the next epoch unliquidated with zero buffer: the next clamped move can
produce bad debt. The disaster path is *incentive-mediated*, not arithmetic.

### 1.3 The funded-liquidation inequality

Work over ℚ with bps scale `10⁴`. Let `m` = per-epoch clamp, `maint` =
effective maintenance (maintenance + depeg buffer), `penalty` = liquidation
penalty, all in bps. Post-move price satisfies `|P' − P| ≤ m·P/10⁴`.

Step 1 (quantitative headroom; now `collateral_headroom_after_bounded_move`):

```
C + pos·(P' − P)  ≥  |pos|·P·(maint − m)/10⁴
```

This strengthens the old non-negativity lemma (and needs strictly fewer
hypotheses: neither `0 ≤ P` nor `m ≤ maint` is required). It is sharp: with
`maint = m` and a clamp-edge downward move on a maintenance-exact account, the
bound is attained with equality (`witness_headroom_tight`).

Step 2 (penalty at the post-move price): `P' ≤ P·(10⁴ + m)/10⁴`, so the raw
penalty obeys

```
|pos|·P'·penalty/10⁴  ≤  |pos|·P·penalty·(10⁴ + m)/10⁸.
```

Step 3 (parameter condition). The penalty is covered by post-move equity for
**every** admissible price and **every** position size iff the per-unit rates
satisfy

```
penalty·(10⁴ + m)  ≤  10⁴·(maint − m).            (FUNDED-LIQ)
```

This is `liquidation_penalty_funded_after_bounded_move`. Consequences when
(FUNDED-LIQ) holds:

- the `liq_penalty_capped` cap never binds after a single clamped move;
- the keeper receives the full advertised penalty, paid entirely out of the
  liquidated account: **zero insurance-fund draw, zero bad debt** for the
  single-epoch move class;
- the hypothesis of `liquidation_game_dominant` is discharged by construction
  (given the gas bound of §1.4), instead of assumed.

Solving (FUNDED-LIQ) for each parameter:

```
m       ≤  10⁴·(maint − penalty) / (10⁴ + penalty)
penalty ≤  10⁴·(maint − m) / (10⁴ + m)
maint   ≥  m + penalty·(10⁴ + m)/10⁴
```

Production defaults (`src/core/perp_v2/types.py:83-87`): `maint = 600`
(500 + 100 depeg buffer), `m = 500`, `penalty = 50`:

```
50·10500 = 525,000  ≤  10⁴·100 = 1,000,000   ✓  (slack ≈ 1.9×)
```

checked as `witness_production_funded_liquidation`. The margin is real but not
enforced: governance can move `m` up to `547` bps (`10⁴·550/10050 ≈ 547.26`)
before funding breaks, yet no current invariant trips until `m > 600`.

**Recommendation R1.** Add to `src/core/perp_v2/invariants.py`:

```python
def inv_funded_liquidation(s: PerpState) -> bool:
    eff_maint = s.maintenance_margin_bps + s.depeg_buffer_bps
    return (s.liquidation_penalty_bps * (BPS_SCALE + s.max_oracle_move_bps)
            <= BPS_SCALE * (eff_maint - s.max_oracle_move_bps))
```

and gate parameter updates on it (same lane as the existing bounty-farming
guards in `src/integration/perp_engine.py`). This converts the bad-debt-via-
underpaid-keeper path from "currently false" to "unrepresentable", which is
the repository's stated correct-by-construction principle.

### 1.4 Keeper gas floor and the dust-position hole

Dominance needs `gas ≤ reward`. The new uniform floor
(`liquidation_reward_floor`) bounds the reward over the whole admissible band,
computable at the *pre-move* price:

```
reward(P')  ≥  |pos|·P·(10⁴ − m)·penalty / 10⁸      for all admissible P'.
```

`liquidation_profitable_on_clamp_band` then gives: if

```
gas  ≤  |pos|·P·(10⁴ − m)·penalty / 10⁸             (KEEPER-GAS)
```

then liquidation has non-negative net profit at every admissible post-move
price — dominance is robust to the oracle move, not contingent on one realized
price.

Inverting (KEEPER-GAS) for the minimum profitable notional `N = |pos|·P`:

```
N  ≥  gas·10⁸ / (penalty·(10⁴ − m)).
```

With `penalty = 50`, `m = 500`: `N ≥ gas·10⁸/475,000 ≈ 210.5·gas`. The
anti-bounty-farming gate `min_notional_for_bounty = 1e8` (≈ $1,
`src/core/perp_v2/types.py:107`) zeroes the penalty *below* $1 notional, so for
positions just above the gate the keeper bounty is ≈ $0.00475. Any gas above
half a cent makes the entire band of small positions rationally
un-liquidatable; they then sit as un-cleared margin risk (each one is below
maintenance, and §1.3's funding analysis does not apply to a position no one
will liquidate).

**Recommendation R2.** Either
(a) tie the gate to gas: `min_notional_for_bounty ≥ gas_budget·10⁸/(penalty·(10⁴ − m))`
with an explicit declared `gas_budget`, or
(b) add a fixed gas compensation to perp liquidations, as zUSD already has
(`liquidation_gas_comp_fixed_collateral_e8`, `src/core/zusd.py:164`), funded
from the position with the same (FUNDED-LIQ)-style headroom accounting:
replace `penalty·(10⁴+m)` in (FUNDED-LIQ) by `penalty·(10⁴+m) + 10⁸·comp/N_min`
where `N_min` is the smallest admissible notional. (a) is parameter-only; (b)
changes settlement arithmetic and needs its own conservation lemma.

### 1.5 From "an equilibrium" to "the equilibrium"

`liquidation_game_dominant` certifies weak dominance, which certifies that
liquidating *is a* Nash equilibrium — it does not exclude other equilibria.
With strictly positive net profit the prediction can be pinned:

- `PerpMechanismDesign.strict_dominant_unique_nash`: a strictly-dominant
  profile is the **unique** Nash equilibrium of the game (new, generic).
- `PerpGameTheory.liquidation_game_strict_dominant` +
  `liquidation_game_unique_nash`: with `0 < net profit`, "liquidate" is the
  unique equilibrium of the liquidation game.

Why it matters: a mechanism whose desired outcome is merely *supported* leaves
coordination risk (in richer models: equilibrium selection, keeper apathy). A
unique strict equilibrium is the strongest prediction this solution concept
offers. The chain is now:

```
(FUNDED-LIQ) + (KEEPER-GAS strict)  ⇒  0 < net profit at every admissible P'
                                    ⇒  liquidate strictly dominant
                                    ⇒  unique Nash equilibrium.
```

### 1.6 Honest model boundary: the keeper race

The liquidation game is 1-player. Real keeper competition is a race: the first
valid liquidation claims the full penalty, so in an open mempool the penalty
is dissipated into latency/priority competition (the classic rent-dissipation
result — total expenditure approaches the prize). ZenoDEX's batch philosophy
suggests the consistent fix: clear liquidations inside the same uniform-batch
mechanism as orders (per-batch liquidation set, deterministic split or
lowest-claimed-penalty auction among valid claimants). Formalizable as an
n-player extension of `liquidationGame`; the 1-player payoff results above are
the per-claimant building block. Not shipped in Lean here; flagged as the next
formalization target.

---

## 2) Funding-rate mechanism: the imbalance term is scale-free and divergent

### 2.1 Current state

`src/core/perp_v2/funding_rule.py:8-38`:

```
basis_bps := floor(|mark − index| / index · 10⁴)
rate_bps  := sign(mark − index) · min(basis_bps, funding_cap_bps)
```

with `funding_cap_bps = 100` (±1%/epoch). Funding is a pure **premium**
signal; open-interest imbalance is not an input. Budget balance and the
integer floor gap (≤ 1 base unit per epoch, `PerpFundingRateSafety`) are
already proven.

### 2.2 What the new identity says

`FundingImbalanceEV.dualEV L S = (L − S)²/(2·L·S)` is the wave-analysis EV
term for long/short stakes `L, S > 0`. The file previously proved only
non-negativity and the zero/positivity criteria. The new structural results:

```
ρ := (L − S)/(L + S)          (normalized imbalance, ρ ∈ (−1, 1))

dualEV L S = 2ρ² / (1 − ρ²)                    (exact; dualEV_eq_imbalance_form)
dualEV L S ≥ 2ρ²                               (two_mul_imbalance_sq_le_dualEV)
dualEV (cL) (cS) = dualEV L S  (c ≠ 0)         (dualEV_scale_invariant)
ρ²-monotone across any two markets             (dualEV_strict_mono_in_imbalance)
```

All three earlier lemmas become corollaries of the identity. Three mechanism
consequences:

1. **Scale-freeness.** The imbalance EV depends only on the *shape* of the
   market (ρ), not its size. A funding controller keyed on `dualEV` needs no
   size normalization, and any size-dependent tuning of it is provably
   redundant.
2. **Divergence at one-sidedness.** `2ρ²/(1 − ρ²) → ∞` as `ρ → ±1`. The
   economic pressure to restore balance grows without bound as the market
   becomes one-sided — but the current funding rate is capped at
   `funding_cap_bps` and reads only the premium. In a one-sided market with a
   well-arbitraged mark (small premium), funding pressure is ≈ 0 while the
   stranded-side risk term diverges. The mechanism is blind exactly where the
   EV term says risk concentrates.
3. **Quadratic floor.** Any imbalance-responsive term inherits the scale-free
   floor `2ρ²`: a controller that prices balance restoration below `2ρ²`
   (in EV units) under-prices it at every market size.

### 2.3 Improvement

**Recommendation R3.** Add a bounded imbalance component to funding:

```
rate_bps = clamp( basis_bps_signed + κ·sign(L − S)·floor(10⁴·ρ²·imb_gain_bps/10⁴),
                  ±funding_cap_bps_total )
```

with `funding_cap_bps_total = funding_cap_bps + imb_cap_bps` and the new
component independently capped by `imb_cap_bps`. Safety composition is free:
`PerpFundingRateSafety.funding_extraction_bounded` is already parametric in
the cap, so the existing extraction bound holds verbatim with
`cap := funding_cap_bps + imb_cap_bps`; symmetry/budget-balance lemmas apply
unchanged because the component is a pure rate adjustment. The ρ² form (not
|ρ|) is justified by the quadratic floor above; gain `κ` calibrates EV-units
to bps. Keep `imb_cap_bps` small (e.g. 25–50) so the worst-case per-epoch
extraction bound moves by the same audited amount.

What this buys: funding begins to act on the divergent term *before* the
one-sided market reaches the ADL/insurance lanes, instead of relying on
premium alone. The cost is one more parameter pair and one more clamp, both
inside already-proven envelopes.

---

## 3) Batch MEV dilution: exact scaling law and its honest limits

### 3.1 What was strengthened

`MEVResistanceBound` had `2·profit(2n) ≤ profit(n)` (doubling only). Now:

```
profit(k·n) = profit(n) / k          exactly (floor)   batch_dilution_compose
k·profit(k·n) ≤ profit(n)                              k_fold_batch_dilution
profit(n) − k·profit(k·n) < k                          k_fold_batch_dilution_sharp
```

The dilution family composes *exactly* (not just monotonically), and rounding
loses strictly less than one unit of modeled profit per dilution factor:
`k·profit(kn)` is pinned in `(profit(n) − k, profit(n)]`. The doubling lemma
is the `k = 2` slice. No positivity hypotheses are needed for the first two.

### 3.2 The honest limit (and what to do about it)

The `1/n` family models *equal* intents. With heterogeneous sizes the
sandwichable surface is proportional to the victim's share `wᵢ = sᵢ/Σs`, so
one whale in a batch of 100 retains ≈ its full exposure. The file's own header
already scopes it as an "arithmetic sidecar".

**Recommendation R4.** State the protocol-level claim in weighted form and
keep the toy family as its equal-weight corollary: per-intent modeled exposure
`profitᵢ = base·wᵢ`, total `Σᵢ base·wᵢ = base` (conservation), equal-weight
specialization `wᵢ = 1/n` recovers the current family. This is a small Lean
file (sum over a list of weights), and it prevents the `1/n` figure from being
quoted as a protocol guarantee for whale-bearing batches. UPBA's real defense
for the whale case is uniform clearing itself (no intra-batch reordering), and
that is already the certified surface — the dilution numbers should not be
asked to carry that weight.

---

## 4) Solver bounty: the missing detection-probability margin

README claims (scoped honestly): bounty > compute cost, slash > 0, and
**verifier always catches invalid submissions** ⇒ honest solving dominates.
The third hypothesis is doing all the work. With catch probability `q < 1`
(bug, sandbox escape, spec gap — the repo's own threat docs treat these as
live), a cheating solver's expected value is

```
EV_cheat = (1 − q)·gain − q·slash
```

so deterrence needs

```
slash ≥ gain·(1 − q)/q + ε,        bond ≥ slash.       (DETERRENCE)
```

At `q = 1` this degenerates to `slash > 0` — the README's condition. The
oracle lane already encodes exactly this shape with a margin:
`docs/ZENO_ORACLE_ECONOMIC_SECURITY_V1.md` requires
`slash_amount ≥ ceil(expected_cheat_gain·(10⁴ + deterrence_margin_bps)/10⁴)`,
i.e. (DETERRENCE) with `q` folded into a 20% margin. The solver lane has no
such inequality, and `ZenoLedgerBondedSlashingSafety` (correctly) proves only
conservation and bond-coverage of an *admitted* slash, not deterrence sizing.

**Recommendation R5.** Lift the oracle deterrence law into a shared Lean
lemma parameterized by `(gain, slash, q, margin)`:

```
q·slash ≥ (1 − q)·gain·(1 + margin)  →  EV_cheat ≤ −margin·(1 − q)·gain
```

and instantiate it for (a) oracle reporters (recovering the doc law), and
(b) UPBA solvers (new). This unifies two currently-parallel mechanisms under
one checked inequality and makes the `q = 1` assumption visible as a
parameter instead of implicit.

---

## 5) Smaller precise points

- **Funding floor-gap routing.** The per-epoch integer funding gap is proven
  to sit in `{0, −1}` (`PerpFundingRateSafety.int_fdiv_neg_gap`) and to
  accumulate in `[−N, 0]` over `N` epochs. Recommendation: route the gap unit
  explicitly to the insurance bucket in the settlement code path and assert
  the conservation identity `longs + shorts + insurance_dust = 0` per epoch,
  upgrading a bounded leak into an exact conservation law
  (`PerpFundingSinkConservation` is the natural home).
- **Oracle reporter laws are doc-only.** The three inequalities in
  `ZENO_ORACLE_ECONOMIC_SECURITY_V1.md` (attack-cost floor, honest-reward
  floor, slash deterrence) are enforced by a Python checker but have no Lean
  artifact. Each is one `linarith` lemma; formalizing them removes a
  doc/check divergence class. (R5 covers the deterrence one.)
- **Emission vs. verified value.** `TokenomicsMechanismSafety` proves
  `reward spend ≤ verified value gained + treasury drawdown` for any
  controller satisfying `StepRewardFunded`. The active-participant emission
  lane (1%/epoch of remaining pool, 25% burn,
  `src/integration/zeno_ledger_tokenomics.py:36-39`) is not yet expressed as
  such a controller. Wiring it in costs one instantiation and buys the
  no-unfunded-reward theorem (`excess_reward_implies_not_stepwise_funded`)
  for the live emission path.

---

## 6) Summary table

| # | Mechanism | Gap | Improvement | Status |
|---|-----------|-----|-------------|--------|
| 1 | Liquidation | equity ≥ 0 proven, penalty funding unproven; cap binds under stress | (FUNDED-LIQ): `penalty·(10⁴+m) ≤ 10⁴·(maint−m)` | **Proven in Lean**; runtime invariant recommended (R1) |
| 2 | Liquidation | keeper profitability assumed | (KEEPER-GAS) uniform floor over clamp band | **Proven in Lean**; gate sizing recommended (R2) |
| 3 | Liquidation | weak dominance only | strict dominance ⇒ unique Nash | **Proven in Lean** |
| 4 | Funding | premium-only signal; imbalance EV diverges unobserved | exact `2ρ²/(1−ρ²)` identity; bounded ρ² funding term | **Identity proven in Lean**; controller change recommended (R3) |
| 5 | Batch MEV | doubling-only bound; equal-size model quotable as guarantee | exact k-fold composition + sharpness; weighted restatement | **Proven in Lean**; weighted file recommended (R4) |
| 6 | Solver bounty | `q = 1` catch assumption implicit | (DETERRENCE) with explicit `q`, shared with oracle lane | Recommended (R5) |
| 7 | Funding dust | bounded leak, destination unspecified | exact conservation with insurance sink | Recommended |
| 8 | Tokenomics | emission lane outside proven guard | instantiate `RewardControllerGuard` | Recommended |
