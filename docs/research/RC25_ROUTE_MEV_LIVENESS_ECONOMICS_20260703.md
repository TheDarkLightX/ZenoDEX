# RC25 Route MEV/Liveness Economics under Stale-Quote Rejection

**Date**: 2026-07-03
**Scope**: Analysis of route MEV (sandwich/back-running) payoff boundaries under the `quote_receipt_hash` stale-quote defense, the `stable_route_lift` and `component_repair` tx-ordering schedulers, and the liveness cost of stale-quote rejection vs executing at bad prices.
**Evidence**: Python analysis script (`/tmp/route_mev_liveness_analysis.py`), Rust kernel source (`zk/state_proof_risc0/shared/src/lib.rs`), 97 shared Rust tests + 22 CLI tests, 128 Python parity tests.
**Non-claims**: This is a research analysis, not a production security claim. The sandwich payoff model uses standard CPMM math with 30 bps fee; real-world attacker strategies may differ. Cross-block MEV is out of scope.

## 1. Defense Architecture

Three defense layers protect route intents from MEV extraction:

### Layer 1: `quote_receipt_hash` (Stale-Quote Rejection)

**Mechanism**: The route intent binds a SHA-256 hash of the pool snapshots (reserves, fee_bps, asset ids) for every pool in the route. The hash is computed by `route_quote_receipt_hash_with_frontier_binding_v1` at intent construction time. At execution time, the ZK proof kernel recomputes the hash from the current pool state and rejects the route if the hashes mismatch.

**Source**: `zk/state_proof_risc0/shared/src/lib.rs:4248` (`route_quote_receipt_hash_with_frontier_binding_v1`), `zk/state_proof_risc0/shared/src/lib.rs:2101` (mismatch check).

**Effect**: If any pool in the route is touched by a prior tx in the same block, the pool's reserves change, the recomputed hash mismatches, and the route is rejected. This makes intra-block sandwich attacks impossible: the attacker's front-run tx touches the pool, staling the victim's quote.

**Binding domain**: The hash binds:
- Route kind (`ROUTE_EXACT_IN` / `ROUTE_EXACT_OUT`)
- `asset_in`, `asset_out`
- `total_amount_in`, `total_min_amount_out`, `total_amount_out`, `total_max_amount_in`
- `protocol_fee_share_bps`, `protocol_fee_recipient`
- `leg_indices` (length + values)
- Per-leg pool snapshot (pool_id, asset0, asset1, reserve0, reserve1, fee_bps, lp_supply, status, created_at)
- Optional frontier signature certificate root (v2 binding)

### Layer 2: `stable_route_lift` (Tx-Ordering Scheduler)

**Mechanism**: The scheduler lifts route txs before different-sender pool writer txs when possible. Routes that read pools not yet touched by any accepted writer are prioritized (priority 0). Stale routes (whose pools have been touched) are deferred (priority 1). Non-route txs are scheduled last (priority 2).

**Source**: `zk/state_proof_risc0/shared/src/lib.rs:3383` (`stable_route_lift_prestate_tx_order_v1`).

**Effect**: Minimizes false-positive stale-quote rejections by executing routes before writers when the conflict graph allows it. The same-sender barrier prevents lifting when a route and a writer share the same sender (to prevent self-front-running).

### Layer 3: `component_repair` (FPT Scheduler)

**Mechanism**: For large tx batches that exceed the bruteforce oracle cap (`MAX_PRESTATE_TX_ORDER_ORACLE_TXS`), the component repair scheduler decomposes the conflict graph into connected components and repairs each component independently using FPT (fixed-parameter tractable) search.

**Source**: `zk/state_proof_risc0/shared/src/lib.rs:3443` (`component_repair_prestate_tx_order_v1`).

**Effect**: Scales the scheduling problem past the bruteforce cap while preserving the stale-quote defense. Accepted routes are still validated against the `quote_receipt_hash` at execution time.

## 2. Sandwich Payoff Boundaries

### Q1: Sandwich payoff without stale-quote defense

A classic sandwich attack on a `swap_exact_in` victim:
1. Attacker front-runs: swaps `attacker_capital` asset_in -> asset_out
2. Victim swaps: `victim_amount_in` asset_in -> asset_out (at inflated price)
3. Attacker back-runs: swaps received asset_out -> asset_in

**Result** (30 bps fee, R_in = R_out = 1,000,000):

| Victim amount_in | Attacker capital | Attacker profit | Victim loss |
|-----------------|-----------------|----------------|-------------|
| 10,000 | 50,000 | **-5,617** | 912 |
| 10,000 | 100,000 | **-19,606** | 1,704 |
| 10,000 | 500,000 | **-312,120** | 5,465 |
| 100,000 | 500,000 | **-335,252** | 49,070 |
| 100,000 | 1,000,000 (10M pool) | **-196,077** | 17,037 |

**Finding**: Sandwich attacks are **unprofitable** for the attacker at 30 bps fee. The attacker pays fees on both legs (front-run + back-run = 60 bps round-trip), plus price impact on both swaps. The victim loss is bounded and small relative to the attacker's loss.

**Implication**: The stale-quote defense is **defense-in-depth**, not the primary MEV barrier. The primary barrier is the CPMM fee structure itself. However, the defense is still valuable because:
- It eliminates the victim loss entirely (route is rejected, not executed at bad price)
- It prevents MEV extraction at lower fee tiers (e.g., 1 bps pools)
- It prevents MEV extraction via correlated non-route pools

### Q2: Sandwich payoff WITH stale-quote defense

Under stale-quote rejection, the attacker's front-run touches the pool, making the victim's `quote_receipt_hash` stale. The victim's route is **rejected** before execution.

- Attacker profit = 0 (no victim to back-run into)
- Attacker is left with a single swap (no sandwich), paying fees
- Victim loss = 0 (route rejected, no execution at bad price)
- **Maximum extractable intra-block MEV = 0**

### Q3: Liveness cost of stale-quote rejection

A route is rejected if any of its pools is touched by a prior writer tx in the same block AND the route cannot be lifted before the writer (same-sender barrier). The collision probability is approximated by the birthday bound:

```
P(collision) ≈ 1 - exp(-n_routes * pools_per_route * n_writers / n_pools)
```

The rejection rate is the collision rate times the same-sender fraction (the fraction of routes that share a sender with a writer and thus cannot be lifted):

| Routes | Writers | Pools | Pools/route | Collision % | Rejection % |
|--------|---------|-------|-------------|-------------|-------------|
| 1 | 1 | 10 | 1 | 9.52% | 9.52% |
| 5 | 5 | 50 | 2 | 63.21% | 12.64% |
| 10 | 10 | 100 | 2 | 86.47% | 8.65% |
| 20 | 20 | 200 | 3 | 99.75% | 4.99% |
| 50 | 50 | 500 | 3 | 100.00% | 2.00% |
| 100 | 100 | 1000 | 4 | 100.00% | 1.00% |

**Finding**: Collision rate grows with block density, but rejection rate stays low because `stable_route_lift` lifts routes before different-sender writers. Only same-sender barrier cases (self-inflicted) are actually rejected. At realistic block density (100 routes, 100 writers, 1000 pools), the rejection rate is ~1%.

**Liveness vs bad-price tradeoff**: A rejected route costs the user one block of latency (must resubmit with a fresh quote). An executed route at a stale price costs the user the price impact of the prior writer. For a 30 bps fee pool with a 10% price impact writer, the bad-price cost is ~10% of the swap value, while the liveness cost is one block of latency. **Stale-quote rejection is strictly better** when the price impact exceeds the user's time preference.

## 3. Exact-Out Overdelivery and Sandwich Payoff

Exact-out routes have a `target_out` and may overdeliver (`amount_out >= target_out`). The overdelivery stays in the pool (not credited to the recipient).

Under stale-quote defense, the victim's route is rejected before execution, so overdelivery is irrelevant to MEV. If the defense were absent, overdelivery would **increase** the attacker's back-run profit (more asset_out to swap back). The stale-quote defense eliminates this overdelivery MEV amplification.

## 4. Residual MEV Surface

After all three defense layers, the residual MEV surfaces are:

| Surface | Extractable? | Mitigation |
|---------|-------------|------------|
| Cross-block sandwich via correlated non-route pools | Yes | Out of scope for `quote_receipt_hash` (only binds route pools) |
| Same-sender self-sandwich | No (self-inflicted) | Same-sender barrier prevents lifting |
| Quote freshness window | No | User must refresh quote each block |

**Primary residual risk**: Cross-block sandwich via correlated non-route pools. An attacker can manipulate a pool NOT in the route but correlated (e.g., pool A->D where D affects A's price in a route A->B). The `quote_receipt_hash` does not bind D, so the route's hash is still valid. This is a fundamental limitation of route-scoped binding vs global state binding.

**Mitigation options** (future work):
- Extend `quote_receipt_hash` to bind a broader state frontier (all pools touching the route's assets)
- Use frontier signature certificates (v2 binding already supports this)
- Add a slippage tolerance check that rejects routes with excessive price impact vs a reference price

## 5. Conclusion

The stale-quote defense reduces intra-block sandwich MEV to zero. The liveness cost is bounded by the birthday collision rate times the same-sender fraction, which is ~1% at realistic block density. The primary residual MEV surface is cross-block sandwich via correlated non-route pools.

**Defense layer summary**:
- Layer 1 (`quote_receipt_hash`): intra-block sandwich -> 0 MEV
- Layer 2 (`stable_route_lift`): minimizes false-positive rejections
- Layer 3 (`component_repair`): scales scheduling past bruteforce cap

**Key finding**: Sandwich attacks are already unprofitable at 30 bps fee due to round-trip fee costs. The stale-quote defense is defense-in-depth that eliminates the victim loss entirely and extends protection to lower fee tiers.

## Repro Commands

```bash
# Run the MEV/liveness analysis
python3 /tmp/route_mev_liveness_analysis.py

# Rust tests (includes stale-quote defense tests)
cd zk/state_proof_risc0 && cargo test --all

# Python parity tests
python3 -m pytest tests/core/test_route_protocol_fee_parity.py -v
```

## Next Frontier

1. **Cross-block MEV via correlated non-route pools**: Quantify the extractable MEV from manipulating pools outside the route's `quote_receipt_hash` binding but correlated to the route's assets.
2. **Frontier signature certificates (v2 binding)**: Extend the `quote_receipt_hash` to bind a broader state frontier, closing the correlated-pool MEV gap.
3. **Slippage tolerance check**: Add a reference-price-based slippage check that rejects routes with excessive price impact, independent of the `quote_receipt_hash` binding.
