# ShapeForge Promising Gates, 2026-05-10

This note records two small ShapeForge promotions from the temporal-desync review.
Both are public runtime contracts with regression tests. They are not production
claims until a deployment profile requires them and the surrounding receipts bind
the same fields.

## Endogenous Payout Reference Gate

```text
Phi := <M, S, A, T, V, O, G, Obs, K, E, Gap, N, Delta>
M     = zenodex_shape_reference
S     = il_futures_endogenous_reference
A     = guard/source_kind
T     = reject instantaneous AMM spot for endogenous payout settlement
V     = source_kind, twap_window_blocks, reference_elapsed_blocks
O     = snapshot_epoch_start, settle_il_epoch
G     = source_kind = twap_accumulator
        and twap_window_blocks >= min_twap_window_blocks
        and reference_elapsed_blocks >= min_reference_elapsed_blocks
Obs   = accepted/rejected IL futures snapshot and settlement
K     = none
E     = contract: src/core/endogenous_reference_gate.py
        implemented: src/core/il_futures.py
        tested_discovery: tests/core/test_endogenous_reference_gate.py,
          tests/core/test_il_futures.py
Gap   = TWAP computation and external data provenance remain outside this gate
N     = same-block spot reads are blocked only when require_twap_reference is enabled
Delta = IL futures can opt into a fail-closed TWAP reference contract
```

The hardened IL futures mode rejects `spot` references and rejects same-block
TWAP references. This targets flash-loan-style endogenous payout manipulation by
making the dangerous reference source inadmissible at the state-machine guard.

## Governance Timelock Snapshot Gate

```text
Phi := <M, S, A, T, V, O, G, Obs, K, E, Gap, N, Delta>
M     = zenodex_shape_reference
S     = governance_timelock_snapshot
A     = guard/delay_source
T     = execute proposals against snapshotted delay, with an absolute floor
V     = proposal_id, proposed_at_seconds, snapshotted_min_delay_seconds,
        absolute_floor_seconds, current_time_seconds
O     = create_timelock_proposal_snapshot, evaluate_timelock_execution,
        evaluate_timelock_delay_update
G     = snapshotted_min_delay_seconds >= absolute_floor_seconds
        and current_time_seconds >= proposed_at_seconds
        and elapsed_seconds >= snapshotted_min_delay_seconds
Obs   = accepted/rejected governance execution and delay update
K     = none
E     = contract: src/core/governance_timelock.py
        tested_discovery: tests/core/test_governance_timelock.py
Gap   = receipt/schema integration and production governance wiring remain open
N     = mutable current min-delay is not trusted at execution time
Delta = proposals carry their own delay snapshot, and delay updates below floor fail
```

This blocks the rogue-admin shape where a later `setMinDelay(0)` attempts to
make an already-created proposal immediately executable. Existing proposals are
judged against the delay recorded at proposal creation.

## Deferred Shape

Asynchronous N+1 intent settlement remains a hypothesis. It needs a stronger
economic model before promotion because a next-block price rule changes latency,
inclusion, cancellation, and adverse-selection behavior. The next useful artifact
is a bounded model with explicit attacker timing, cancellation, and oracle-update
rules, followed by runtime contract targets only for the parts that survive.
