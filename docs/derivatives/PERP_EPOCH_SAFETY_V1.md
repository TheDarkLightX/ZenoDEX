# Perp DEX v1: Safety-First “European-Style” (Epoch) Perpetuals

This document is a **safety-first** design spec for a minimal perpetuals venue built in the
ZenoDEX style: deterministic state machines with explicit, verifiable invariants.

We call it “European-style” because all economically relevant transitions are **epoch-based**
(batch/epoch boundaries): oracle update, mark-to-market, margin check, and (if needed) liquidation.

## 1. Scope (MVP)

**Market model**
- **Linear** perp: position is in base units; collateral and PnL are in quote units.
- **Cash-settled** in a single quote collateral asset.
  - **Tau Net v1 recommendation:** use **AGRS** (native) or a wrapped form (e.g., `wAGRS`) as the quote collateral asset.
  - Later upgrade: list a stable collateral asset via the token registry once that listing path is proven safe.
- **Isolated margin** (no cross-margin in v1).
- **One market** per kernel instance.

**Execution model**
- Deterministic, epoch-based processing:
  1) epoch advances
  2) a single **clearing price** is published for the epoch (from the batch-auction execution posture)
  3) epoch settlement: mark-to-market at the clearing price, then margin check; if below maintenance ⇒ liquidation (deterministic)

**Non-goals (v1)**
- Multi-collateral, portfolio margin, cross-market netting.
- External liquidity assumptions (“sell on DEX at market”) inside safety proofs.
- High-leverage parameters.

## 2. Threat Model (what we explicitly defend against)

### T1: Oracle manipulation / staleness
**Risk:** wrong/stale index → incorrect margin/liquidations.
**Mitigations:**
- Freshness gate: `now_epoch - oracle_last_update_epoch <= max_oracle_staleness_epochs`.
- **Bounded move** gate per update: new price must be within `max_oracle_move_bps` of last price.
- If bounded-move fails, the safe default is **fail-closed** (no state transition).

### T2: Liquidation liquidity failure (dYdX-style insurance drain)
**Risk:** liquidations can’t execute fast enough; bad debt socialized to insurance.
**Mitigation (v1 posture):**
- Liquidation is modeled as a **deterministic state transition** (not “sell into a book”).
- Safety proofs do **not** assume external liquidity exists.
- Parameters are chosen so that under the oracle’s bounded-move assumption, **equity cannot go negative between oracle updates**.

### T3: MEV / execution discretion
**Risk:** execution ordering or discretionary matching causes unfair fills.
**Mitigation (MVP posture):**
- This v1 kernel models the **risk engine** (margin/solvency) rather than the full matching engine.
- When we add matching, we use **batch auction / canonical tie-breaking** (see existing `batch_auction_settler_v1.yaml`).

### T4: Arithmetic/overflow
**Risk:** integer overflow breaks invariants.
**Mitigation:**
- Fixed-point integer math with explicit scales (`price_e8`, `bps`).
- Bounded domains in the ESSO kernel (and later, overflow-aware implementation constraints).

## 3. Core Safety Claims (mathematical invariants)

This section states the **precise invariants** we intend the protocol to enforce.
They are “claims” only in the sense that they are *statements to be mechanically checked*.

### 3.1 Units and notation

All quantities are integer/fixed-point in the executable kernel.
For readability, we write the math below in real-number form, with the understanding that the
kernel computes the same expressions with explicit scaling and rounding.

Let:
- `pos ∈ ℤ` be the signed base position (long positive, short negative).
- `P_e8 ∈ ℕ` be the index price in **quote-per-base**, scaled by `1e8` (`index_price_e8`).
- `C ∈ ℕ` be the quote collateral (`collateral_quote`).
- `m_bps ∈ ℕ` be `max_oracle_move_bps` (basis points).
- `maint_bps ∈ ℕ` be `maintenance_margin_bps` (basis points).

Define (conceptually):
- `P := P_e8 / 1e8` (quote per base).
- Notional at price `P`: `N(P) := |pos| · P` (quote units).
- Maintenance requirement at price `P`: `M(P) := N(P) · maint_bps / 10_000`.
- Mark-to-market collateral delta from price `P` to `P'`: `ΔC := pos · (P' - P)`.
  - For a long (`pos > 0`): price up ⇒ `ΔC > 0`; price down ⇒ `ΔC < 0`.
  - For a short (`pos < 0`): price up ⇒ `ΔC < 0`; price down ⇒ `ΔC > 0`.

In the kernel, `ΔC` is computed with fixed-point arithmetic as:
`floor(pos * (P'_e8 - P_e8) / 1e8)`, with explicit bounded domains to avoid overflow.

### 3.2 Execution interface (epoch posture)

The v1 risk engine is intentionally minimal. Its intended “epoch” interface is:
1) `advance_epoch`: increment time.
2) `publish_clearing_price`: publish exactly one candidate clearing price for the current epoch.
3) `settle_epoch`: mark-to-market at that clearing price and enforce maintenance/liquidation.

Trading (`set_position`) is allowed only when the oracle is fresh.

**I1. Oracle freshness.**
- A position update is only permitted when `now_epoch - oracle_last_update_epoch <= max_oracle_staleness_epochs`.
- (Intuition) The system refuses to trade on a stale price.

**I2. Maintenance safety.**
- If `pos != 0`, then `C >= M(P)` at the current index price `P` (post-settlement).

**I3. Entry/mark-to-market discipline.**
- If `pos != 0`, then `entry_price_e8 = index_price_e8` (PnL is realized at every oracle update).

**I4. No negative balances (solvency).**
- `C >= 0` always.

**Key parameter relationship (safety knob):**
- `maint_bps >= m_bps`.

### 3.3 One-step solvency under bounded move

Assume the bounded-move oracle gate enforces:
\[
  |P' - P| \le \frac{m_{\mathrm{bps}}}{10{,}000} \, P
\]
and the safety knob holds (`maint_bps >= m_bps`).
If the account is maintenance-safe at the old price,
\[
  C \ge M(P),
\]
then a single epoch’s mark-to-market cannot drive collateral negative:
\[
  0 \le C + \Delta C = C + pos\cdot(P' - P).
\]

This inequality is mechanized as `Proofs.PerpEpochSafety.collateral_nonneg_after_bounded_move`
and is reflected operationally by fail-closed guards in the epoch settlement transition.

### 3.4 What this does *not* claim yet

- It does not claim anything about how the clearing price is produced (that is the matching module).
- It does not model funding (v1 can run without funding; later versions can add epoch funding as an explicit transition).
- It does not assume “liquidate on an external book”; liquidation is a deterministic state transition.

## 4. Artifacts

- ESSO kernel (MVP): `src/kernels/dex/perp_epoch_isolated_v1.yaml`
  - This is the executable spec we gate with `python3 -m ESSO verify-multi ...`.
  - Oracle posture: publish an epoch clearing price (`publish_clearing_price`), then settle the epoch at that price (`settle_epoch`).

## 5. Next steps (after the MVP kernel verifies)

1) Add an explicit **matching module**:
   - batch auction per epoch (canonical, deterministic).
2) Replace “bounded move” with a **circuit breaker**:
   - when violated: halt opens; only reduce-only; deterministic resolution path.
3) Upgrade oracle to 2-of-2 composition:
   - on-chain TWAP + signed quorum feed, with deviation checks.
4) Add “bad debt” module only if needed:
   - and cap it; prefer ADL over insurance drains.
