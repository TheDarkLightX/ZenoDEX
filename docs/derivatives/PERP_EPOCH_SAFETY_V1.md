# Perp DEX v1: Safety-First European-Style (Epoch) Perpetuals

This document is a **safety-first** design spec for a minimal perpetuals venue built in the
ZenoDEX style: deterministic state machines with explicit, verifiable invariants.

We call it European-style because all economically relevant transitions are **epoch-based**
(batch/epoch boundaries): oracle update, mark-to-market, margin check, and (if needed) liquidation.

For the complementary **game theory / incentive layer**, see `docs/derivatives/PERP_INCENTIVES_V1.md`.

**Recommendation (single-account risk kernel):** use the **v2 isolated kernel** (`perp_epoch_isolated_v2.yaml`)
when you want a compact, per-account risk engine with clamp+breaker safety posture and hardened accounting knobs
(depeg buffer, explicit fee/insurance tracking, anti-bounty-farming threshold).

For the production peer-to-peer posture (net-zero clearinghouse kernels), see `docs/derivatives/PERP_SOTA_ROADMAP.md`.

Reproducible verification snapshot (2026-02-03):
- `perp_epoch_isolated_v2.yaml` is **VERIFIED** under strict `verify-multi` cross-check (`--solvers z3,cvc5`).
- `perp_epoch_isolated_v1_1.yaml` is **REVIEW_NEEDED** under strict cross-check: `inductive_settle_epoch` is UNSAT
  in CVC5 but returns UNKNOWN in Z3 at a 60s per-query timeout.

## 1. Scope (MVP)

**Market model**
- **Linear** perp: position is in base units; collateral and PnL are in quote units.
- **Cash-settled** in a single quote collateral asset.
  - **Tau Net v1 recommendation:** use the chain’s **native asset** (the always-available quote unit) as collateral.
  - Later upgrade: list a stable collateral asset via the token registry once that listing path is proven safe.
- **Isolated margin** (no cross-margin in v1).
- **One market** per kernel instance.
- Liquidation penalties flow into an explicit **fee pool** (`fee_pool_quote`) rather than an implicit insurance/backstop layer.

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
- If bounded-move fails:
  - v1: **fail-closed** (no state transition).
  - v1.1: **clamp + breaker**: settle at the clamped boundary price and enter a reduce-only posture until cleared.

### T2: Liquidation liquidity failure (dYdX-style insurance drain)
**Risk:** liquidations can’t execute fast enough; bad debt socialized to insurance.
**Mitigation (v1 posture):**
- Liquidation is modeled as a **deterministic state transition** (not “sell into a book”).
- Safety proofs do **not** assume external liquidity exists.
- Parameters are chosen so that under the oracle’s bounded-move assumption, **equity cannot go negative between oracle updates**.

### T3: “Market-maker of last resort” backstops (HLP/insurance/ADL)
**Risk:** if liquidations depend on external liquidity, protocols often add layered backstops:
forced protocol counterparties, insurance fund drains, and finally profit-haircut mechanisms
(ADL / socialized loss) that punish winners to keep the system solvent.

**Mitigation (v1 posture):**
- We do **not** rely on “someone must buy the liquidation” as a safety assumption.
- We aim to make **insolvency structurally impossible** under explicit model assumptions:
  bounded per-epoch price movement and conservative margin parameters.
- In v1.1, if the raw oracle move violates the configured bound, we **clamp** the effective settlement
  move and enter **reduce-only** mode until the market is closed and the breaker is cleared.
- Any liquidation penalty is an explicit transfer from the liquidated account into `fee_pool_quote` (no hidden “insurance fund” accounting).

### T4: MEV / execution discretion
**Risk:** execution ordering or discretionary matching causes unfair fills.
**Mitigation (MVP posture):**
- This v1 kernel models the **risk engine** (margin/solvency) rather than the full matching engine.
- When we add matching, we use **batch auction / canonical tie-breaking** (see existing `batch_auction_settler_v1.yaml`).

### T5: Arithmetic/overflow
**Risk:** integer overflow breaks invariants.
**Mitigation:**
- Fixed-point integer math with explicit scales (`price_e8`, `bps`).
- Bounded domains in the executable kernel spec (and later, overflow-aware implementation constraints).

## 3. Core Safety Properties (mechanized invariants)

This section states the **precise properties** the protocol is intended to enforce.
They are mechanized: written as statements to be checked by tools (Lean for math lemmas, and SMT cross-checks
for the executable kernel invariants).

### 3.1 Units and notation

All quantities are integer/fixed-point in the executable kernel.
For readability, we write the math below in real-number form; the mechanized statements are in integer /
fixed-point arithmetic (with explicit floor division) matching the kernel.

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
`floor(pos * (P'_e8 - P_e8) / 1e8)`, with explicit bounded domains to avoid overflow. The Lean artifact
`Proofs.PerpEpochSafety` is stated in the same integer form (not just the real-number restatement).

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

**Accounting note (scope).**
- The isolated-margin kernel is a *per-account* risk engine: it does not explicitly model counterparties.
  Mark-to-market PnL changes an account’s collateral, but the offsetting PnL lives “elsewhere” (in other accounts)
  and is not tracked in this single-account abstraction.
- For closed-system conservation (no mint/burn across the whole venue), use a clearinghouse posture with explicit
  counterparties and a deterministic remainder/dust policy.

### 3.3 One-step solvency under bounded move (v1)

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

### 3.4 Clamping makes the bounded-move guarantee enforceable (v1.1)

In v1.1 we do not assume the raw clearing price update satisfies the bounded-move inequality.
Instead we define an **effective settlement price** \(\widehat{P}'\) by clamping the raw update \(P'\)
into the allowed band around \(P\):
\[
  \widehat{P}' \;:=\; \mathrm{clamp}\!\left(P',\; P\!\left(1-\frac{m_{\mathrm{bps}}}{10{,}000}\right),\;
  P\!\left(1+\frac{m_{\mathrm{bps}}}{10{,}000}\right)\right).
\]
Then, by construction,
\[
  \bigl|\widehat{P}' - P\bigr| \le \frac{m_{\mathrm{bps}}}{10{,}000}\,P,
\]
so the v1 solvency lemma applies verbatim with \(P'\) replaced by \(\widehat{P}'\).
Operationally, v1.1 marks-to-market using \(\widehat{P}'\) and sets a breaker flag if clamping occurred.
This reduction is mechanized in Lean as `Proofs.PerpEpochSafety.abs_clamp_move_sub_le` and
`Proofs.PerpEpochSafety.collateral_nonneg_after_clamped_move`.

### 3.5 What this does *not* claim yet

- It does not claim anything about how the clearing price is produced (that is the matching module).
- It does not model funding (v1 can run without funding; later versions can add epoch funding as an explicit transition).
- It does not assume “liquidate on an external book”; liquidation is a deterministic state transition.

## 4. Artifacts

- Kernel specs (MVP):
  - v1: `src/kernels/dex/perp_epoch_isolated_v1.yaml` (strict bounded-move; fail-closed on violation)
  - v1.1: `src/kernels/dex/perp_epoch_isolated_v1_1.yaml` (clamp + breaker; reduce-only while breaker is active)
  - v2: `src/kernels/dex/perp_epoch_isolated_v2.yaml` (v1.1 + depeg buffer, insurance accounting, anti-bounty-farming)
  - These specs are gated by the repo’s evidence runner (`tools/run_perps_evidence.sh`).
  - Oracle posture: publish an epoch clearing price (`publish_clearing_price`), then settle the epoch at that price (`settle_epoch`).
  - v1.1 additionally maintains a `fee_pool_quote` and fail-closes if a liquidation would overflow the finite-domain fee pool.

## 5. Next steps (after the MVP kernel verifies)

1) Add an explicit **matching module**:
   - batch auction per epoch (canonical, deterministic).
2) Upgrade oracle to 2-of-2 composition:
   - on-chain TWAP + signed quorum feed, with deviation checks.
3) Extend the v1.1 breaker into a complete **resolution protocol**:
   - deterministic “walk” the index price toward the raw oracle price in bounded steps,
     while permitting only reduce-only account actions.
4) Add “bad debt” layers only if required by a future, strictly wider model:
   - treat any such mechanism as a separate module with explicit caps and explicit victim sets;
     do not silently socialize losses.
