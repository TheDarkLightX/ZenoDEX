# Perpetuals (Perps): Design + Math + Evidence (Public Overview)

This document explains the perpetuals features in this repository and the design choices behind them.
It is written for public consumption and is intentionally implementation-aware: every claim and rule is
grounded in concrete artifacts in this repo.

## Goals and constraints

ZenoDEX perps are designed to be:

- Deterministic and fail-closed (no “best effort” execution for consensus-critical transitions).
- Integer-first with explicit units and bounds.
- Evidence-backed with replayable checks (pytest, kernel-level SMT checks, and optional proof builds).
- Compatible with peer-to-peer operation (participants can authorize matched position updates directly).

## What exists today (map to code)

**Execution adapter (tx → deterministic state transition)**
- `src/integration/perp_engine.py`: parses perps ops (group `"5"`) and applies them deterministically to `DexState` with explicit authorization:
  - isolated markets: operator-only admin actions + user-only account actions
  - clearinghouse markets: participant-authorized market init + matched position updates, and oracle-authorized clearing-price publication (when an oracle signer is configured)

**Production perps posture: clearinghouse markets (net-zero exposure, closed-system accounting)**
- 2-party kernel spec: `src/kernels/dex/perp_epoch_clearinghouse_2p_v0_1.yaml`
  - Adapter: `src/kernels/python/perp_epoch_clearinghouse_2p_v0_1_adapter.py`
  - Committed reference model (dependency-free): `generated/perp_python/perp_epoch_clearinghouse_2p_v0_1_ref.py`
- 3-party transfer kernel spec: `src/kernels/dex/perp_epoch_clearinghouse_3p_transfer_v0_1.yaml`
  - Committed reference model: `generated/perp_python/perp_epoch_clearinghouse_3p_transfer_v0_1_ref.py`

**Isolated-margin risk kernel (single-account abstraction; useful for development + per-account checks)**
- Kernel spec: `src/kernels/dex/perp_epoch_isolated_v2.yaml`
- Native implementation (pure Python): `src/core/perp_v2/`
- Wrapper that selects the backend and exposes a stable API: `src/core/perp_epoch.py`

## Two coherent perps models (pick one family; don’t mix halfway)

Perpetual markets force you to decide who is the “counterparty of last resort”. This repo supports two
coherent design families.

### Option A: peer-to-peer clearinghouse with **net-zero** exposure

**Goal:** avoid protocol “market maker of last resort” behavior (insurance / ADL) by construction.

**Production choice (v1.0 posture):** Option A.

Core accounting constraint:
- If the protocol does not carry an explicit balance sheet, it must enforce net exposure `Σpos = 0`.

How the clearinghouse family does this:
- Positions are updated as a matched vector across participants (pairwise or with an explicit idle account).
- Settlement and liquidation preserve a closed-system invariant exactly (see “Rounding and conservation”).

Practical scaling note:
- The 2-party kernel uses deterministic “pair close-out” liquidation (both sides flat) to remain fully closed-system without assuming external liquidity.
- The 3-party kernel adds a deterministic **position transfer** path (distressed side moves into an idle account that satisfies initial margin), which is the minimal building block for scalable liquidation without forcing healthy counterparties flat.

### Option B: protocol counterparty with explicit insurance / ADL rules

**Goal:** allow open interest without enforcing net-zero matching by giving the protocol an explicit balance sheet.

Minimum requirements (otherwise it is fail-open economics):
- an explicit protocol inventory / equity state variable,
- explicit loss allocation rules (insurance → haircut / ADL),
- verifiable accounting over multi-epoch trajectories (not just one-step safety).

In this repository, the isolated-margin kernel family is the right starting point for Option B, but
Option B is not “free”: if you want protocol-counterparty behavior, model it explicitly end-to-end.

## Rounding and conservation (consensus-critical)

A common pitfall:
- Even when `Σpos = 0`, per-account PnL updates that use Euclidean division can leak value
  (`Σpnl` need not be `0` when `pnl_i := (pos_i·ΔP_e8) div 1e8`).

Two robust solutions exist:

### Fix 1 (preferred): store collateral in **quote-e8** for exact PnL

If `price_e8` is quote-per-base scaled by `1e8`, then `pos * Δprice_e8` is already in quote-e8 units.
By storing collateral internally in quote-e8, settlement becomes exact integer arithmetic with no division.

This is the approach used by the clearinghouse kernels (`collateral_e8_*`), and it enables an exact
closed-system invariant:
- `net_deposited = Σ collateral_e8 + fee_pool_e8`

### Fix 2: deterministic dust allocator under net-zero

If you must divide (e.g., external quote units), use a deterministic “largest remainder” allocator that:
- restores `Σpnl = 0` under net-zero exposure,
- differs from the floor by at most `+1` per account,
- has a total order tie-break (e.g., by account key).

## Clamp + breaker: safety and quantization

The isolated-margin kernel uses bounded-move oracle enforcement via **clamp + breaker**. This provides a
simple, auditable safety posture.

Quantization note: prices are discrete in 1e-8 ticks. To avoid a zero-width clamp band when
`P * m_bps / 10000` is smaller than one tick, the implementation uses a quantization-safe bound:
- `δ := ceil(P * m_bps / 10000)` (so `δ` is non-zero whenever the intended percent move is non-zero).

This removes the “stall” hazard at tiny prices while staying within one tick of the intended percent bound.

## Authorization model (peer-to-peer by construction)

Clearinghouse operations are explicitly authorized:
- Market initialization and matched position updates require signatures from all affected participants.
- Clearing-price publication can be gated by an oracle signer when configured.
- Per-operation signatures are domain-separated by `chain_id`, include a deadline, and consume per-signer nonces.

See:
- Engine: `src/integration/perp_engine.py`
- Signing helper (Tau client): `src/integration/tau_net_client.py`

## Evidence: what to run

Single entrypoint:
- `bash tools/run_perps_evidence.sh`
- `bash tools/run_mechanical_scientist_evidence.sh` (mechanical-scientist campaign smoke + strict replay)

This runs unit/integration tests and kernel-level checks. Some checks require optional local toolchains; the script fails closed when prerequisites are missing so “production posture” is always explicit.

Mechanical-scientist iteration notes and measured throughput improvements are tracked in:
- `docs/derivatives/MECHANICAL_SCIENTIST_LIFTOFF_20260206.md`

## Roadmap to v1.0 (pragmatic)

The repo currently ships both isolated-margin and clearinghouse perps. A practical v1.0 target is:

- Use clearinghouse kernels as the production posture for peer-to-peer perps, with participant/oracle authorization and exact quote-e8 accounting.
- Keep isolated-margin v2 (`src/core/perp_v2/`) as a useful single-account risk abstraction and as a fast development target, gated by parity tests against committed reference models.
- Expand evidence coverage on edge cases that matter for production:
  - replay protection (nonce reuse, wrong `chain_id`),
  - deadline enforcement,
  - mixed batches (atomicity expectations for nonce consumption),
  - breaker quantization edge case mitigation (whichever policy is chosen).
