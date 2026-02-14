# ZenoDEX Algorithm Promotions (2026 Q1)

This document explains promoted mechanism/algorithm upgrades that were moved from research into production code.

## Why these were promoted

Each change had to satisfy all three criteria:

1. **Safety-preserving**: no weakening of settlement invariants or replay protections.
2. **Deterministic**: same inputs always produce same outputs (including tie-breaks).
3. **Measurable utility**: lower routing scan cost, lower settlement payload size, or fewer false-negative settlement mismatches.

## 1) Array-indexed routing backend (`data_structure_array`)

### What changed

Routing in `best_route_exact_in_2hop` now uses a deterministic indexed representation:

- Pools are sorted once by `pool_id`.
- An adjacency index is built: `asset -> tuple(pool_indices)`.
- Candidate scans iterate only pools adjacent to the relevant asset.

### Why this is better

Previous scans repeatedly iterated the full pool list for direct hops and second-hop candidates. The indexed representation narrows scans to relevant pools while keeping deterministic ordering.

### Determinism and correctness

- Pool ordering is canonical (`pool_id` sorted).
- Adjacency tuples are canonical (`pool_id` sorted).
- Existing route tie-break key (`_quote_key`) is unchanged.
- Inactive/non-connecting pools are still rejected via quote guards.

## 2) Chunked invariant-preserving delta aggregation (`invariant_chunking`)

### What changed

Before creating a `Settlement`, balance/reserve/LP deltas are now aggregated with chunked reducers:

- `_aggregate_balance_deltas_chunked`
- `_aggregate_reserve_deltas_chunked`
- `_aggregate_lp_deltas_chunked`

The reducers:

1. Aggregate within bounded chunks.
2. Merge chunk totals into a global accumulator.
3. Emit canonical key-sorted outputs.
4. Drop exact zero rows.

### Why this is better

- Reduces duplicate delta rows in large batches.
- Shrinks settlement payloads.
- Keeps transition semantics identical (sum-preserving per key and side).

### Determinism and correctness

- Aggregation uses integer addition only.
- Keys are emitted in sorted canonical order.
- `delta_add` and `delta_sub` are preserved independently (no accidental sign-netting).

## 3) Rewrite-normal-form settlement matching (`algebraic_rewrite`)

### What changed

When `require_settlement_match=True`, matching now compares **normalized semantic forms** for both computed and provided settlements.

Normalization includes:

- Drop non-transition metadata (`batch_ref`, `events`, fill `reason`).
- Normalize omitted vs `null` optional fields.
- Sort `included_intents`, `fills`, and deltas deterministically.
- Aggregate duplicate deltas.

### Why this is better

Equivalent settlements from different encoders (different list order, split-vs-aggregated deltas) now match correctly. This removes false mismatches without accepting non-equivalent transitions.

### Determinism and correctness

- Comparison is done in a canonical quotient form.
- If forms match, engine still executes the locally recomputed settlement.
- Malicious non-equivalent settlements still fail with `settlement mismatch`.

## 4) IL Futures Margin-Capped Settlement (`il_margin_cap`)

### What changed

IL-futures settlement payout is now capped by short margin only:

- old: `available = premium_pool + margin_pool`
- new: `available = margin_pool`

### Why this is better

This removes cross-subsidy from premium funds into leveraged settlement payouts. Long-side settlement remains bounded by posted short-side margin.

### Determinism and correctness

- Integer arithmetic and invariant checks are unchanged.
- Settlement remains fail-closed.
- New regression test locks “premium pool not consumed at settlement” behavior.

## 5) FRM Exposure Imbalance Cap (`frm_imbalance_cap`)

### What changed

FRM open-long/open-short actions now support an optional deterministic imbalance cap:

- `max_imbalance_ratio_bps`
- `imbalance_cap_min_total`

If enabled, post-trade skew `|L-S|/(L+S)` must stay within the configured bound once total exposure reaches the activation threshold.

### Why this is better

It constrains highly one-sided books that amplify manipulation risk and dual-position gaming EV under extreme imbalance.

### Determinism and correctness

- Guard-only change (no stochastic behavior).
- Default posture is backward-compatible when cap is unset (`<= 0`).
- New tests cover reject/allow boundaries.

## 6) zUSD↔Perp Oracle Synchronization Gate (`oracle_sync_gate`)

### What changed

zUSD API oracle-activating commands (`bootstrap_oracle`, `oracle_commit`) now support an optional cross-module sync gate against perps oracle state:

- `ZUSD_PERP_ORACLE_SYNC_ENABLED`
- `ZUSD_PERP_ORACLE_SYNC_MARKET_ID`
- `ZUSD_PERP_ORACLE_SYNC_MAX_DIVERGENCE_BPS`
- `ZUSD_PERP_ORACLE_SYNC_MAX_EPOCH_LAG`

### Why this is better

It directly mitigates cross-module oracle divergence risk by fail-closing zUSD oracle activation when divergence or epoch lag exceeds configured limits.

### Determinism and correctness

- Checks are integer-only and deterministic.
- Gate is opt-in and fail-closed.
- New integration tests cover aligned acceptance, divergence rejection, and epoch-lag rejection.

## Default posture updates

Core and engine defaults now use:

- `swap_ordering = "greedy_ab_refined"`

This favors high-quality deterministic batch ordering while staying computationally practical for production.

## Evidence gates run

The following gates were run after promotion:

1. `pytest tests/` -> **751 passed, 6 skipped**
2. `bash tests/tau/test_specs_syntax.sh` -> **58 passed, 0 failed**
3. `lake build` in `lean-mathlib/` -> **build succeeded**

Additional regression tests were added to lock behavior:

- Chunked aggregation semantic/order preservation.
- Semantic-equivalence acceptance for settlement match under canonical normalization.

## Files changed

- `src/core/routing.py`
- `src/core/batch_clearing.py`
- `src/core/dex.py`
- `src/integration/dex_engine.py`
- `src/core/il_futures.py`
- `src/core/funding_rate_market.py`
- `src/integration/perps_api.py`
- `src/integration/zusd_api.py`
- `tests/core/test_batch_clearing.py`
- `tests/core/test_il_futures.py`
- `tests/core/test_funding_rate_market.py`
- `tests/integration/test_dex_engine.py`
- `tests/integration/test_zusd_api.py`
- `docs/ALGORITHM_PROMOTIONS_2026Q1.md`
