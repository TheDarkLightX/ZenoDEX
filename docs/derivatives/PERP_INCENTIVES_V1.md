# Perp DEX v1: Incentive Design + Game Theory (Draft)

The perp safety kernels (`perp_epoch_isolated_v1*.yaml`) enforce *mechanized* invariants
like non-negative collateral and bounded oracle moves. That is necessary, but not sufficient:
**real systems need incentives** so that rational agents cause the actions and value flows that
keep the invariants *operationally true* (oracle updates happen, settlement happens, depth exists,
manipulation is unprofitable, etc.).

This document treats incentive design as a *scientific layer*:
- every economic claim is a **falsifiable hypothesis**,
- we build **refuters** (counterexample miners) with Morph,
- we log hypotheses + evidence in PopperPad,
- we only “promote” designs that survive refutation under explicit bounds.

## 1) Problem state (Morph-style)

We model the incentive layer as:

```
σ := ⟨R, α, Δ, G, Π, S, M⟩
```

- `R` (representation): on-chain/per-kernel state + parameters (fees, max position, oracle rule, reward pools).
- `α` (abstraction): bounded economic games (oracle manipulation, keeper liveness, LP depth, liquidation).
- `Δ` (constraints): safety invariants (ESSO/Tau), conservation/accounting invariants (fee splits), bounds (caps).
- `G` (goal): no profitable manipulations; liveness is rational; depth is rewarded; protocol is solvent.
- `Π` (obligations/certs): counterexample bundles, audit logs, solver/Lean proofs for margin lemmas.
- `S` (tools/portals): ESSO kernels, Tau traces, Morph refuters/miners, (optional) Lean math.
- `M` (metadata): fixed seeds, scenario packs, attack budgets, and the “best known” witnesses.

## 2) Roles and “critical actions”

These are the actions that *must* happen for the protocol to function:

- **Oracle / clearing-price publication**
  - produces the per-epoch settlement price.
  - safety dependency: correctness + boundedness + timeliness.
- **Settlement / liquidation execution**
  - advances epoch and runs the risk engine (mark-to-market + liquidation).
  - safety dependency: liveness (no stale oracle / stuck market).
- **Liquidity provision (depth)**
  - provides spot depth if the perp oracle is derived from spot/TWAP.
  - safety dependency: depth makes oracle manipulation expensive.

If these actions require off-chain work, they must have on-chain incentives:
fees → rewards, plus slashing/penalties for economically dangerous behavior.

## 3) Economic threat model (minimum set)

### T1: Oracle manipulation for perp profit
If the perp settlement price is derived from a spot CPMM observation (or a weak TWAP),
an attacker can:
1) take a perp position,
2) trade spot to move the oracle in their favor,
3) settle, then unwind spot.

This is the central game-theory constraint: **spot depth + fees must make this unprofitable**,
or the system becomes a value pump.

### T2: Keeper liveness failure / censorship
If publishing/settlement is permissioned or unrewarded, it can stall:
trading stops (oracle staleness), breaker persists, liquidations delayed.

### T3: Reward farming / wash loops
If we pay “keepers” or “LPs” naïvely, rational agents will farm rewards via self-trades,
self-liquidations, or creating artificial volume. Rewards must be tied to *scarce, verifiable work*.

## 4) Core mechanism design principles (v1 posture)

1) **Minimize discretion; maximize determinism**
   - Prefer a deterministic clearing/oracle rule (batch auction with canonical tie-break) over “trusted publisher”.

2) **Pay for liveness**
   - A bounded keeper bounty per epoch (or per settlement) ensures someone runs the required transitions.
   - Funding source: a bounded share of protocol fees.

3) **Pay for depth**
   - If perps use spot/TWAP, depth is a safety primitive.
   - Incentives (fee share, staking rewards) should flow to the liquidity that defends the oracle.

4) **Cap incentives and make them auditable**
   - Rewards, rebates, and penalties should be explicit integer math modules, validated by Tau/ESSO.

## 5) Key incentive design results (sanitized)

We keep a Popperian posture (hypotheses must be falsifiable), but we **do not commit internal refuter/miner code**
or large evidence bundles. The items below summarize the current best-known *results* and the corresponding design takeaways.

### R1: Raw volume rewards are farmable

Result:
- Bounded counterexample search finds wash-trade loops where `reward > roundtrip_cost`.

Takeaway:
- Do not pay on raw volume. Pay for scarce, verifiable work (e.g., time-weighted liquidity / stake),
  and cap any incentives by **non-recapturable protocol revenue**.

### R2: Fixed/min keeper bounties are farmable in rounding-to-zero regimes

Result:
- If a keeper bounty has a minimum payout but the collectible penalty can round to 0,
  rational agents can farm the minimum.

Takeaway:
- Enforce `bounty ≤ penalty_collected` and add minimum-notional / minimum-penalty rules to avoid the “penalty=0” regime.

### R3: Spot-derived perps must assume attacker-as-LP

Result:
- If the attacker also owns LP share, “LP fees” are partially recaptured, collapsing the effective manipulation cost.
- If protocol fee extraction is `protocol_fee = floor(fee_total * pfs / 10_000)`, then for trades where `fee_total = 1`,
  the extracted protocol fee can be 0 for any `pfs < 10_000`. Rational attackers can pick trade sizes that exploit this.

Takeaway:
- Only **non-recapturable** fees deter attacker-as-LP. Ensure extracted fees are non-zero whenever `fee_total > 0`
  (or change rounding), and combine with position caps and bounded oracle move rules.

### R4: “Fee-rebates” are safer when capped by extracted protocol fees

Result:
- Rebates funded by a share of already-extracted protocol fees are significantly harder to farm than fresh “volume rewards”
  (bounded evidence).

Takeaway:
- If incentives must exist, fund them out of extracted revenue (not out of in-pool LP fees) and treat “attacker is also LP/staker”
  as the default adversary.

## 6) Design knobs (what incentives must control)

These are the minimum knobs that an incentive layer must be able to tune (and cap):

- `fee_bps` (spot + perp): increases manipulation cost, but taxes honest users.
- `max_position_abs`: caps how much perp PnL can be extracted per epoch via oracle moves.
- `max_oracle_move_bps`: limits per-epoch PnL extraction; breaker posture in v1.1 contains tail events.
- `depth targets` (LP incentives): deeper pools increase the cost to shift price.
- `keeper bounty` (liveness): ensures settlement is rational even in low-fee epochs.

The *game theory layer* is what ties these knobs to value flow:
fees → (keepers, LPs, insurance, buyback/burn) with explicit caps and auditable accounting.

## 7) Deep Incentive Design Research (CEGIS/ICE/Morph/Lean)

Systematic discovery, testing, and formalization of perpetual protocol incentive
vulnerabilities using Popperian falsification. Results from the multi-phase CEGIS loop:

### Key Discovery: Integer Floor-Division Breaks Funding Budget Balance

**ESSO verify-multi** found that a naive funding computation violates the funding
budget-balance invariant (`funding_paid_a + funding_paid_b = 0`) due to integer floor
division. Counterexample: `pos=1, price=1, rate=1` → `floor(1/10000)=0`,
`floor(-1/10000)=-1`, sum=-1≠0. Both z3 and cvc5 confirm.

**Fix (v2):** Symmetric funding formula: `funding_b := -funding_a` (not computed
independently). The v2 model (`perp_game_theory_v2.yaml`) passes all 9/9 inductive
queries (init + 8 actions) with both z3 and cvc5.

### Lean4 Formal Proofs

Lean proof artifacts (game theory + accounting):

| File | Key Theorems | Lines |
|------|-------------|-------|
| `PerpMechanismDesign.lean` | `dominant_implies_nash`, `ic_iff_dominant`, `witness_two_player_game` | 145 |
| `PerpGameTheory.lean` | liquidation / self-liquidation / funding games + `native_decide` witnesses | 286 |
| `PerpProtocolSafety.lean` | `unified_perp_safety`, `no_value_creation` | 155 |
| `PerpFundingRateSafety.lean` | `funding_budget_balance_rat`, `funding_extraction_bounded`, `int_fdiv_neg_gap`, `int_multi_epoch_funding_gap` (composition) | 183 |
| `PerpCascadeSafety.lean` | `isolated_margin_independence`, `cascade_impossible_isolated`, `total_conservation_two` | 103 |
| `PerpInsuranceSafety.lean` | `insurance_multi_epoch_solvent`, `insurance_survives_epochs`, `insurance_depletion_bounded` | 121 |
| `PerpIntegerBridge.lean` | `int_div_conservative`, `int_single_div_gap`, `int_symmetric_div_gap` | 81 |

All 4 files compile with 0 errors, 0 sorry. Each theorem has a dedicated non-vacuity
witness (primarily `native_decide` for ℤ; `norm_num` and small `simp`/`ring` steps for ℚ).
Pre-existing
warnings in other files (e.g., `ImpossibilityTheorem.lean` unused simp args) are unrelated.
Full build: `cd lean-mathlib && lake build` (3081 jobs, all pass).

### PopperPad Hypothesis Status

| ID | Hypothesis | Status | Evidence |
|----|-----------|--------|----------|
| H-PI-01 | Oracle manipulation unprofitable | UNTESTED | Bounded by clamp+cap (no miner run) |
| H-PI-02 | Bounty farming unprofitable | UNTESTED | pos=-17, bounty_min=3 (prior session) |
| H-PI-03 | Funding budget-balanced | **FALSIFIED** | Integer floor-division CE (z3+cvc5) |
| H-PI-04 | Cascade impossible (isolated) | survived 1 test | Lean proof + Morph miner UNKNOWN |
| H-PI-05 | Insurance solvent (fees≥claims) | survived 1 test | Lean proof + ESSO v2 VERIFIED |
| H-PI-06 | Depeg buffer prevents insolvency | UNTESTED | Miner created, not yet run |
| H-PI-07 | Keeper liveness | survived 1 test | ESSO penalty guard |
| H-PI-08 | Breaker asymmetry bounded | survived 1 test | Lean clamp_move bound |
| H-PI-09 | Integer gap ≤ 1 | survived 1 test | Lean `int_symmetric_div_gap` |
| H-PI-10 | Fee pool no overflow | survived 1 test | ESSO type bounds + guard |

*Note: "survived N tests" = Popper-style corroboration (not proof). See PopperPad CLI: `python3 tools/popper_pad.py briefing --domain perp-incentives`.*

### v2 Model Changes

```diff
- funding_b = floor(pos_b * price * rate / denom)   # Independent computation
+ funding_b = -funding_a                              # Symmetric by construction
+ guard: insurance_balance + penalty <= max            # Overflow prevention
+ guard: collateral_b + funding_a >= 0                 # Bounds check
+ guard: collateral_b + funding_a <= max               # Overflow check
```

### Verification Commands

```bash
# Validate v2 model
python3 -m ESSO validate src/kernels/dex/perp_game_theory_v2.yaml

# Multi-solver verification (MUST pass for production)
python3 -m ESSO verify-multi src/kernels/dex/perp_game_theory_v2.yaml --solvers z3,cvc5

# Lean proofs
cd lean-mathlib && lake build
```
