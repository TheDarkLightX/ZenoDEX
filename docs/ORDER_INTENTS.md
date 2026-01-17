# Limit Orders + Stop Orders (Stop-Loss) on a DEX

Centralized exchanges can “auto trade” because they have a trusted always-on matching engine.
On a DEX, contracts don’t wake up on their own; **an on-chain action only happens when someone submits a transaction**.

So the DEX-native equivalent is:
1) Users publish a *standing* intent/order with strict bounds.
2) Keepers/bots submit the transaction when conditions are met.
3) The protocol **fails closed** unless the conditions hold.

This repo models that as a small deterministic kernel.

## The Order/Intent kernel

Kernel:
- `src/kernels/dex/order_intent_v1.yaml`

High-level behavior:
- `place_order`: registers a limit/stop trigger + a time window + a slippage bound (`min_amount_out`).
- `execute_order`: permissionless execution when the trigger is satisfied (and oracle data is fresh).
  It emits an “intent” describing the swap that a settlement/execution layer applies.

Important:
- `execute_order` is designed to be called as part of the DEX execution path (batch/transaction). If downstream
  settlement fails (min-out not met, pool frozen, etc.), the system must reject the overall step (fail-closed).

## Mapping: Limit vs Stop (stop-loss)

The kernel defines:
- `oracle_price_y_per_x`: integer “quote per base” price (scaled)
- `swap_dir`:
  - `XForY`: sell base `X` for quote `Y`
  - `YForX`: buy base `X` with quote `Y`
- `order_kind`: `Limit` or `Stop`
- `trigger_price`: the threshold price

### Limit orders

Limit means “execute when the price is *favorable enough*”:
- Sell limit (`XForY`): execute when `price >= trigger_price`
- Buy limit (`YForX`): execute when `price <= trigger_price`

### Stop orders (stop-loss / stop-buy)

Stop means “execute when the price has moved *through* a boundary”:
- Stop-loss sell (`XForY`): execute when `price <= trigger_price`
- Stop-buy (`YForX`): execute when `price >= trigger_price`

In both cases, the user should set `min_amount_out` to cap slippage.

## Automation (keepers)

To make “scheduled trades” work, you need at least one of:
- the user running a bot,
- a public keeper network,
- solvers that continuously search for executable orders.

A keeper can be incentivized by:
- a dedicated `keeper_fee` field (modeled in `order_intent_v1`), paid by the settlement layer.

## Oracle freshness and manipulation

Stop/limit triggers are MEV targets if the trigger price is based on a manipulable spot price.
`order_intent_v1` includes:
- `oracle_seen` + `oracle_last_update_epoch` + `max_oracle_staleness_epochs`
- execution requires oracle freshness: `now_epoch - oracle_last_update_epoch <= max_oracle_staleness_epochs`

To harden further, compose with:
- a median/TWAP oracle kernel, and/or
- settlement-time checks that the pool’s implied execution price is within tolerance of the oracle price.
