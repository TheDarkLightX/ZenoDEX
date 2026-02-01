# Perp DEX v1: Incentive Design + Game Theory (Draft)

Safety logic can enforce invariants (e.g., non-negative collateral, bounded oracle moves). That is necessary, but not sufficient: **real systems need incentives** so rational agents reliably perform the actions that keep the system healthy (oracle updates, settlement, liquidations, depth, etc.).

This document treats incentive design as hypothesis-driven engineering:
- Every economic claim is a **testable hypothesis**.
- We actively look for **counterexamples** (adversarial strategies) under explicit bounds.
- We only ship mechanisms that remain safe under those bounds.

## 1) System framing

We model the incentive layer as:

```
σ := ⟨R, α, Δ, G, V⟩
```

- `R` (representation): on-chain state + parameters (fees, caps, oracle rules, reward pools).
- `α` (abstraction): the games we care about (oracle manipulation, keeper liveness, LP depth, liquidation behavior).
- `Δ` (constraints): protocol invariants + accounting conservation + explicit bounds/caps.
- `G` (goals): manipulation is unprofitable; liveness is rational; depth is rewarded; protocol is solvent.
- `V` (validation): adversarial simulation, property-based tests, and (where feasible) formal checks of invariants.

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
   - Rewards, rebates, and penalties should be explicit integer math, fully auditable from on-chain data.

## 5) Known pitfalls (and design takeaways)

The items below are common failure modes we explicitly design against.

### R1: Raw volume rewards are farmable

What goes wrong:
- Any reward proportional to “reported volume” can be farmed by self-trading loops whenever `reward > roundtrip_cost`.

Takeaway:
- Do not pay on raw volume. Pay for scarce, verifiable work (e.g., time-weighted liquidity, bounded keeper work),
  and cap incentives by **non-recapturable protocol revenue**.

### R2: Fixed/min keeper bounties are farmable in rounding-to-zero regimes

What goes wrong:
- If a keeper bounty has a minimum payout but the collectible penalty can round to 0, rational agents can farm the minimum.

Takeaway:
- Enforce `bounty ≤ penalty_collected` and add minimum-notional / minimum-penalty rules to avoid the “penalty=0” regime.

### R3: Spot-derived perps must assume attacker-as-LP

What goes wrong:
- If the attacker also owns LP share, “LP fees” are partially recaptured, collapsing the effective manipulation cost.
- If protocol fee extraction can round to zero on small trades, attackers can choose trade sizes that minimize non-recapturable cost.

Takeaway:
- Only **non-recapturable** fees deter attacker-as-LP. Ensure extracted fees don’t silently round to zero when nonzero fees were paid,
  and combine with position caps and bounded oracle move rules.

### R4: “Fee-rebates” are safer when capped by extracted protocol fees

What goes wrong:
- Rebates funded by newly minted rewards behave like volume rewards and are usually farmable.

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

## 7) Deployment checklist (what “good” looks like)

Before treating v1 incentives as “deployable”, we want all of the following to hold under explicit bounds:

- **Budget soundness:** rewards/rebates are ≤ extracted protocol revenue (per-epoch caps, no “infinite subsidy”).
- **Farm resistance:** no obvious self-trade / self-liquidation / loop strategy where `payout > costs`.
- **Attacker-as-LP assumed:** every manipulation cost model assumes the attacker can recapture LP fees.
- **Liveness:** at least one actor is economically motivated to advance epochs and execute liquidations.
- **Determinism:** payouts depend only on on-chain data and deterministic integer math (no discretion, no “oracle committee” payouts).
- **User safety:** UI/UX surfaces the incentive knobs (fees, caps, bounty rules) so governance changes are reviewable.

## 8) Common pitfall: asymmetric rounding breaks “budget balance”

Any time you compute equal-and-opposite transfers independently using integer division, you risk breaking conservation due to rounding on negatives.

Example pattern (bad):
```
a = floor(x / denom)
b = floor(-x / denom)
```
With floor division, `b` is not guaranteed to equal `-a`.

Safer pattern (good):
```
a = floor(x / denom)
b = -a
```
If you need “closer to zero” behavior, do it explicitly (e.g., by using a symmetric rounding rule), but keep the accounting identity true by construction.
