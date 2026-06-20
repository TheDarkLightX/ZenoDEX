# DST slice 2: operation-history checker (resilience gap #3)

The second named piece of gap #3 (an **Elle/Knossos-style history-checker**), after
DST slice 1 (snapshot crash-consistency). gitignored prototype, 6 tests.

## Why
Today's chaos tests assert *per-scenario expected values* ("after this batch, balance
should be X"). A **history-checker** instead records the **operation history** of a
settlement trajectory and checks the *whole history* for consistency **anomalies** —
catching violations a scripted assert never anticipated.

## What it records + checks
`run_history(initial, batches)` settles a sequence of batches through the **real**
engine (`compute_settlement` + `apply_settlement_pure`), recording per step: the
pre/post **state-root** and the per-asset **total supply** (every balance + every pool
reserve). `check_history` then flags:

1. **Chaining** — each step must start exactly where the previous ended
   (`post_root[i] == pre_root[i+1]`, and carried per-asset supplies). Catches a
   spliced/forked/tampered history.
2. **Conservation** — a swap *moves* value, never creates/destroys it: per-asset total
   supply is invariant across each step. Catches **phantom value** (mint/burn) that an
   individually-plausible settlement might hide.
3. **Replay-determinism** (`replay_matches`) — re-running the batches from the genuine
   initial state must reproduce **every** recorded post-root. Catches a
   non-replayable / tampered history.

## Verified
- A **genuine** 3-batch history has **zero** anomalies and is non-vacuous (roots
  evolve, assets present).
- The checker **detects** each injected anomaly: a broken state-root chain, a
  conservation violation (1,000,000 phantom units), and a non-replayable post-root.
- Replay is deterministic.

## Honest scope
This checks the **settlement** operation history (the consistency of a recorded
sequence of batch settlements). It is **not**:
- a full **linearizability** oracle over a concurrent multi-client operation log (Elle
  in its strongest form) — ZenoLedger settles batches sequentially, so the relevant
  history is the batch trajectory;
- **IO virtualization** (that is DST slice 1's fault domain + the remaining
  clock/network/disk piece).

Together with slice 1 (crash-consistency), gap #3 now has both its named pieces in
prototype: torn-write/corruption fault injection on the commit path, and an
operation-history anomaly checker. The remaining piece is a VOPR-style clock/network/disk
deterministic hypervisor.
