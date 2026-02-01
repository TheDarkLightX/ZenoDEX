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

## 5) Scientific posture (Popper): hypotheses + refuters

### H1 (refuter-first): “Oracle manipulation is not profitable under bounds”

We treat the statement “oracle manipulation is unprofitable” as something to **refute** by mining
concrete profitable attacks under explicit bounds.

Refuter (Morph domain):
- `tests/morph_domains/perp_oracle_manipulation_cex.py`

Repro command (bounded, deterministic):

```bash
PYTHONPATH=external/Morph \
  python3 -m morph run kernel \
  --out runs/morph_perp_oracle_manipulation/out \
  --sigma0-json runs/morph_perp_oracle_manipulation/sigma0.json \
  --domain-import tests.morph_domains.perp_oracle_manipulation_cex:PerpOracleManipulationDomain \
  --runtime-import tests.morph_domains.perp_oracle_manipulation_cex:build_runtime_factory \
  --tactics-json runs/morph_perp_oracle_manipulation/tactics.json \
  --strategy-file runs/morph_perp_oracle_manipulation/strategy.txt \
  --seed 0 \
  --max-depth 30 \
  --max-expanded 5000 \
  --mdl-portal \
  --strict

PYTHONPATH=external/Morph python3 -m morph doctor --strict runs/morph_perp_oracle_manipulation/out
```

Interpretation:
- If a witness is found, **the mechanism is attackable** under those bounds.
- We then adjust design knobs (fees, max position, oracle window, depth incentives) and rerun until
  the refuter fails to find profit under the chosen bounds.

### PopperPad logging (optional but recommended)

Store the hypothesis, its refuter recipe, and the best-known witness bundle:

```bash
PYTHONPATH="$PWD/external/PopperPad/src${PYTHONPATH:+:$PYTHONPATH}" \
  python3 -m popperpad --pad internal/popperpad/zenodex add --json <hypothesis>.json
```

## 6) Design knobs (what incentives must control)

These are the minimum knobs that an incentive layer must be able to tune (and cap):

- `fee_bps` (spot + perp): increases manipulation cost, but taxes honest users.
- `max_position_abs`: caps how much perp PnL can be extracted per epoch via oracle moves.
- `max_oracle_move_bps`: limits per-epoch PnL extraction; breaker posture in v1.1 contains tail events.
- `depth targets` (LP incentives): deeper pools increase the cost to shift price.
- `keeper bounty` (liveness): ensures settlement is rational even in low-fee epochs.

The *game theory layer* is what ties these knobs to value flow:
fees → (keepers, LPs, insurance, buyback/burn) with explicit caps and auditable accounting.

