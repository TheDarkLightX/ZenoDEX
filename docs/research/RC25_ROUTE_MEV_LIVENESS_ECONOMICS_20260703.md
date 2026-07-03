# RC25 Route MEV/Liveness Economics under Stale-Quote Rejection

**Date**: 2026-07-03
**Scope**: Analysis of route MEV (sandwich/back-running) payoff boundaries under the `quote_receipt_hash` stale-quote defense, the `stable_route_lift` and `component_repair` tx-ordering schedulers, and the liveness cost of stale-quote rejection vs executing at bad prices.
**Evidence**: Python analysis script (`tools/route_mev_liveness_analysis.py`), Rust kernel source (`zk/state_proof_risc0/shared/src/lib.rs`), Rust test suite (`cargo test --all`).
**Non-claims**: This is a research analysis, not a production security claim. The sandwich payoff model uses standard CPMM math with integer arithmetic; real-world attacker strategies may differ. Cross-block and cross-venue MEV are out of scope. The liveness collision probabilities are Poisson approximations of pool overlap events; the distribution-free rejection ceiling is the union bound `min(1, P(rw) + P(rr))`, while the "Combined %" column is an independence-based point estimate, not a bound.

## 1. Defense Architecture

Three defense layers protect route intents from MEV extraction:

### Layer 1: `quote_receipt_hash` (Stale-Quote Rejection)

**Mechanism**: The route intent binds a SHA-256 hash of the pool snapshots (reserves, fee_bps, asset ids) for every pool in the route. The hash is computed by `route_quote_receipt_hash_with_frontier_binding_v1` at intent construction time. At execution time, the ZK proof kernel recomputes the hash from the current pool state and rejects the route if the hashes mismatch.

**Source**: `zk/state_proof_risc0/shared/src/lib.rs:4248` (`route_quote_receipt_hash_with_frontier_binding_v1`), `zk/state_proof_risc0/shared/src/lib.rs:2111-2112` (mismatch check).

**Effect**: If any pool **in the route** is touched by a prior tx in the same block, the pool's reserves change, the recomputed hash mismatches, and the route is rejected. This blocks same-route-pool front-run sandwiches: the attacker's front-run tx touches a route pool, staling the victim's quote.

**Narrowed claim**: This only blocks sandwiches where the front-run touches a pool **in the route**. It does NOT block:
- Post-route back-running (attacker swaps after victim, no front-run needed)
- Cross-venue arbitrage (external pools not in the route)
- Correlated non-route pool manipulation (pool not in route but correlated to route assets)

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

**Effect**: Minimizes false-positive stale-quote rejections by executing routes before writers when the conflict graph allows it. The same-sender barrier (`same_sender_precedence_ready`) prevents lifting when a route and a writer share the same sender, to prevent self-front-running.

**Important**: This is a **certificate/order-selection protection**, not an unconditional execution behavior. The kernel uses a supplied verified `tx_execution_order` (via `resolve_tx_execution_order_v1` at `lib.rs:4077`); if no certified order is supplied, the kernel falls back to default order, which may not lift routes before writers. Layer 2/3 only apply when a certified order is provided.

### Layer 3: `component_repair` (FPT Scheduler)

**Mechanism**: For large tx batches that exceed the bruteforce oracle cap (`MAX_PRESTATE_TX_ORDER_ORACLE_TXS`), the component repair scheduler decomposes the conflict graph into connected components and repairs each component independently using FPT (fixed-parameter tractable) search.

**Source**: `zk/state_proof_risc0/shared/src/lib.rs:3443` (`component_repair_prestate_tx_order_v1`).

**Effect**: Scales the scheduling problem past the bruteforce cap while preserving the stale-quote defense. Accepted routes are still validated against the `quote_receipt_hash` at execution time.

**Important**: Same as Layer 2 — this is a **certificate/order-selection protection**. It only applies when a certified order is supplied to the kernel. If no order is supplied, the default order is used and no component repair occurs.

## 2. Sandwich Payoff Boundaries

### Q1: Sandwich payoff without stale-quote defense

A classic sandwich attack on a `swap_exact_in` victim:
1. Attacker front-runs: swaps `attacker_capital` asset_in -> asset_out
2. Victim swaps: `victim_amount_in` asset_in -> asset_out (at inflated price)
3. Attacker back-runs: swaps received asset_out -> asset_in (reverse direction)

**Result** (30 bps fee, R_in = R_out = 1,000,000):

| Victim amount_in | Attacker capital | Attacker profit | Victim loss |
|-----------------|-----------------|----------------|-------------|
| 10,000 | 50,000 | **+640** | 912 |
| 10,000 | 100,000 | **+1,185** | 1,704 |
| 10,000 | 500,000 | **+3,538** | 5,465 |
| 100,000 | 500,000 | **+54,273** | 49,070 |
| 100,000 | 1,000,000 (10M pool) | **+11,857** | 17,037 |

**Finding**: Sandwiches ARE profitable at 30 bps fee. The attacker's back-run benefits from the victim's price impact moving the pool in the attacker's favor. Fee drag (60 bps round-trip) does NOT dominate at standard fee tiers.

### Q2: Fee tier sensitivity

| Fee (bps) | Attacker profit | Victim loss |
|-----------|----------------|-------------|
| 1 | +1,721 | 1,711 |
| 3 | +1,685 | 1,711 |
| 10 | +1,556 | 1,709 |
| 30 | +1,185 | 1,704 |
| 100 | **-110** | 1,686 |
| 300 | **-3,775** | 1,638 |

**Finding**: Sandwiches become unprofitable at ~100 bps fee for this parameter set. At 30 bps (standard), the attacker profits ~1,185 on a 10,000 swap (11.85% of victim amount). The stale-quote defense is the **PRIMARY MEV barrier**, not defense-in-depth.

### Q3: Same-route-pool sandwich under stale-quote defense

Under stale-quote rejection, the attacker's front-run touches a pool in the route, making the victim's `quote_receipt_hash` stale. The victim's route is **rejected** before execution.

- Attacker profit = 0 (no victim to back-run into)
- Attacker is left with a single swap (no sandwich), paying fees
- Victim loss = 0 (route rejected, no execution at bad price)
- **Same-route-pool front-run sandwich MEV = 0** (under `quote_receipt_hash`)

**Narrowed claim**: This only applies to sandwiches where the front-run touches a pool **in the route**. Post-route back-running, cross-venue arbitrage, and correlated non-route pool manipulation are NOT blocked.

## 3. Liveness Cost of Stale-Quote Rejection

A route is rejected if its `quote_receipt_hash` mismatches at execution time. Two distinct staleness sources cause mismatch:

1. **Route-writer staleness**: a prior writer tx touches a pool in the route, changing its reserves. The route cannot be lifted before the writer if they share a sender (same-sender barrier in `stable_route_lift`).

2. **Route-route staleness**: two routes sharing the same pool — the first route's execution changes the pool's reserves, staling the second route's quote. This happens even with zero writers. Covered by Rust test `same_pool_prestate_route_hashes_second_rejects_without_mutation` (`lib.rs:5349`).

The total per-route rejection probability is the **union** of these two sources:

```
P(reject) = P(route-writer staleness) ∪ P(route-route staleness)
```

### Route-writer collision probability

**Per-route** (a single route's pools overlap with any prior writer):
```
P(rw_collision) ≈ 1 - exp(-pools_per_route * n_writers / n_pools)
```

**Batch-level** (at least one route in the batch collides with a writer):
```
P(batch_rw_collision) ≈ 1 - exp(-n_routes * pools_per_route * n_writers / n_pools)
```

### Route-route collision probability

**Per-route** (a single route's k pools overlap with any prior route's k pools). Two k-pool routes share at least one pool with probability ~k²/n_pools, so for (n_routes-1) prior routes:
```
P(rr_collision) ≈ 1 - exp(-(k²) * (n_routes - 1) / n_pools)
```
where k = pools_per_route.

### Combined per-route independence estimate

Under independence assumption (RW and RR collisions are independent):
```
P(RW ∪ RR) ≈ 1 - (1 - P(rw)) * (1 - P(rr))
```
This is a point estimate, not a bound. The distribution-free upper bound is the union bound `min(1, P(rw) + P(rr))`.

### Combined table

| Routes | Writers | Pools | PPR | RW per-route % | RR per-route % | Combined % | Batch RW % |
|--------|---------|-------|-----|----------------|----------------|------------|------------|
| 1 | 1 | 10 | 1 | 9.52% | 0.00% | 9.52% | 9.52% |
| 5 | 5 | 50 | 2 | 18.13% | 27.39% | 40.55% | 63.21% |
| 10 | 10 | 100 | 2 | 18.13% | 30.23% | 42.88% | 86.47% |
| 20 | 20 | 200 | 3 | 25.92% | 57.47% | 68.49% | 99.75% |
| 50 | 50 | 500 | 3 | 25.92% | 58.60% | 69.33% | 100.00% |
| 100 | 100 | 1000 | 4 | 32.97% | 79.48% | 86.25% | 100.00% |

**Note**: These are collision probabilities, not rejection probabilities. A collision only causes rejection if the scheduler cannot lift the route before the conflicting tx. The "Combined %" column is an **independence-based estimate** (`1-(1-rw)(1-rr)`), NOT a distribution-free ceiling. Under positive correlation between RW and RR collisions, the true P(RW ∪ RR) may be lower; under negative correlation, it may be higher. A distribution-free upper bound is the **union bound**: `min(1, rw + rr)`. The actual rejection rate depends on same-sender prefix ordering, route-route pool sharing, and scheduler behavior.

**Bounds on per-route rejection rate**:
- **Distribution-free upper bound**: `min(1, P(rw) + P(rr))` (union bound). With no prior writers, this reduces to `P(rr_collision)`. With no competing prior routes (P(rr)=0), this reduces to `P(rw_collision)`.
- **Independence-based estimate**: `1 - (1-P(rw))*(1-P(rr))` (the "Combined %" column). This is a point estimate, not a bound — it is exact only if RW and RR are independent.
- **Distribution-free lower bound**: Zero. A route with no conflicting prior txs is never rejected. However, for a concrete conflicting batch with route-route same-pool overlap, the realized rejection rate is positive (route-route staleness rejects the second route sharing a pool, even with zero writers and zero same-sender overlap).

A precise estimate requires simulation of the scheduler over realistic tx mixes.

**Liveness vs bad-price tradeoff**: A rejected route costs the user one block of latency (must resubmit with a fresh quote). An executed route at a stale price costs the user the price impact of the prior pool-mutating tx. For a 30 bps fee pool with a 10% price impact writer, the bad-price cost is ~10% of the swap value, while the liveness cost is one block of latency. Stale-quote rejection is generally preferable when the price impact exceeds the user's latency cost, though a formal comparison requires an explicit latency utility model (out of scope here).

## 4. Exact-Out Overdelivery and Sandwich Payoff

Exact-out routes have a `target_out` and may overdeliver (`amount_out >= target_out`). The overdelivery surplus stays in the pool by construction — the Rust kernel credits only `target_out` to the recipient and subtracts only `target_out` from the pool's output reserve.

**Source**: `zk/state_proof_risc0/shared/src/lib.rs:2329` (`target_out` from `target_outs[leg_index]`), `zk/state_proof_risc0/shared/src/lib.rs:2386` and `zk/state_proof_risc0/shared/src/lib.rs:2395` (reserve subtraction uses `target_out`), `zk/state_proof_risc0/shared/src/lib.rs:2405` (audit records `target_out` as `reserve_out_delta`), `zk/state_proof_risc0/shared/src/lib.rs:2409` (chain passes `target_out`), `zk/state_proof_risc0/shared/src/lib.rs:2414` (recipient credited `target_out`).

**Finding**: The overdelivery bound is a **construction property**, not a stale-quote defense property. The surplus stays in the pool regardless of whether the stale-quote defense is active. The stale-quote defense eliminates the scenario where a sandwiched route executes at a bad price with overdelivery, but the construction itself is the primary bound on overdelivery.

## 5. Residual MEV Surface

After all three defense layers, the residual MEV surfaces are:

| Surface | Blocked? | Mechanism |
|---------|----------|-----------|
| Same-route-pool front-run sandwich | **Yes** | `quote_receipt_hash` rejects stale quotes |
| Post-route back-running | **No** | Attacker swaps after victim; no front-run needed, no stale quote |
| Cross-venue arbitrage | **No** | External pools not in route; outside `quote_receipt_hash` scope |
| Correlated non-route pool manipulation | **No** | Pool not in route but correlated to route assets; not bound by hash |
| Same-sender self-sandwich | **No** (self-inflicted) | Same-sender barrier prevents lifting; self-inflicted, not extractable by third parties |
| Inclusion/censorship liveness griefing | **No** | Attacker censor's victim's tx; outside defense scope |
| Reference-price staleness | **No** | External price feed staleness; outside defense scope |
| No certified improved order supplied | **No** | If no scheduler runs, default order may be exploitable |

**Primary residual risk**: Post-route back-running and correlated non-route pool manipulation. These are outside the `quote_receipt_hash` binding scope.

**Mitigation options** (future work):
- Extend `quote_receipt_hash` to bind a broader state frontier (all pools touching the route's assets)
- Use frontier signature certificates (v2 binding already supports this)
- Add a slippage tolerance check that rejects routes with excessive price impact vs a reference price
- Add a post-route back-run detection mechanism (monitor for swaps in the opposite direction immediately after a route)

## 6. Conclusion

The stale-quote defense (`quote_receipt_hash`) is the **PRIMARY MEV barrier** for same-route-pool front-run sandwiches, reducing them to zero. Sandwiches are profitable at 30 bps fee (attacker profit ~12% of victim amount), so the defense is necessary, not merely defense-in-depth.

The liveness collision probabilities are Poisson approximations of pool overlap events. The distribution-free rejection ceiling is the union bound `min(1, P(rw) + P(rr))`; the "Combined %" column is an independence-based point estimate. The actual rejection rate depends on same-sender prefix ordering in `stable_route_lift`. A precise estimate requires scheduler simulation.

**Defense layer summary**:
- Layer 1 (`quote_receipt_hash`): same-route-pool front-run sandwich -> 0 MEV
- Layer 2 (`stable_route_lift`): minimizes false-positive rejections by lifting routes before writers
- Layer 3 (`component_repair`): scales scheduling past bruteforce cap

**Residual MEV surfaces NOT blocked**:
- Post-route back-running
- Cross-venue arbitrage
- Correlated non-route pool manipulation
- Inclusion/censorship liveness griefing
- Reference-price staleness

**Exact-out overdelivery**: Bounded by construction (surplus stays in pool), independent of the stale-quote defense.

## Repro Commands

```bash
# Run the MEV/liveness analysis
python3 tools/route_mev_liveness_analysis.py

# Rust tests (includes stale-quote defense tests)
cd zk/state_proof_risc0 && cargo test --all

# Python parity tests
python3 -m pytest tests/core/test_route_protocol_fee_parity.py -v
```

## Next Frontier

1. **Post-route back-running**: Quantify the extractable MEV from back-running a route without front-running. The attacker swaps in the opposite direction after the victim's route executes.
2. **Frontier signature certificates (v2 binding)**: Extend the `quote_receipt_hash` to bind a broader state frontier, closing the correlated-pool MEV gap.
3. **Slippage tolerance check**: Add a reference-price-based slippage check that rejects routes with excessive price impact, independent of the `quote_receipt_hash` binding.
4. **Scheduler simulation**: Build a simulation of `stable_route_lift` over realistic tx mixes to estimate the actual rejection rate, replacing the Poisson approximation and union bound.
