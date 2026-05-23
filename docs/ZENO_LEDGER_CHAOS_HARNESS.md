# ZenoLedger Chaos Harness

`tools/zeno_ledger_chaos_harness.py` is a deterministic adversarial model for
network and admission failures. It is intentionally cheap and replayable, so it
can run in operator gates before live multi-node drills.

Covered scenarios:

- peer churn and incompatible peer admission
- gossip duplicate and oversized envelope rejection
- same-height equivocation with slashing evidence
- fork-choice extension and stale fork rejection
- transport/auth failure
- validator proposer schedule rejection
- checkpoint quorum failures and acceptance
- degraded network catch-up shape

The core invariant is:

```text
InvalidBlockOrPeer(trace) -> RejectedWithStableReason(trace)
```

Each scenario emits a JSON report with rejection reasons, accepted block counts,
equivocation events, slashing receipts, and per-node state.

Run:

```bash
python3 tools/zeno_ledger_chaos_harness.py --json
```

This harness is not a substitute for the live public-testnet candidate gate. It
is the fast adversarial layer that should run before live tests.
