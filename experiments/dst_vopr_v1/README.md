# DST slice 3: VOPR-style deterministic simulation core (resilience gap #3)

The third and final named piece of gap #3, after slice 1 (snapshot crash-consistency)
and slice 2 (operation-history checker). gitignored prototype, 3 tests (~6.5s).

## What it is
A **seed-reproducible deterministic simulation** that composes slices 1+2 into one
loop and virtualizes the IO ZenoLedger **owns**:
- **logical clock** = step index,
- **disk** = snapshot persist / recover (the slice-1 commitment integrity),
- **crash timing** = seed-driven,

and injects **crashes + disk corruption** between settlements. Network / consensus is
Tau's, so it is deliberately **not** virtualized.

`simulate(seed)` is a pure function of the seed (the FoundationDB / TigerBeetle-VOPR
property), so any failure reproduces exactly.

## Invariants asserted across the seeded sweep
- **Fail-closed recovery** — a crash that reads a torn/corrupted *newest* on-disk
  snapshot never adopts it; it falls back to the previous durable checkpoint. The
  recovered state-root is always a previously-**committed** root, never a corrupt one.
  Verified: **0 anomalies over 120 seeds** (987 injected crashes / 438 fail-closed
  fallbacks — exact, since the sweep is deterministic).
- **Determinism** — `simulate(seed)` yields an identical op-log + final root + crash
  counts every time.

## Live-checker proof (not vacuous)
A **planted bug** (`verify_commitment=False`, trusting the disk blindly) adopts a
corrupt state under corruption. The *same* invariant **catches** it, the **seed
reproduces** it exactly, and the real (verify-on) system is **clean for that very
seed** — demonstrating the harness finds-and-reproduces a real bug, VOPR-style.

## Honest scope
This virtualizes **clock + disk + crash-timing** (ZenoLedger-owned) and uses the REAL
engine + snapshot (`compute_settlement` / `apply_settlement_pure` / `dex_snapshot`).
It does **not** virtualize the **network** (Tau's consensus domain), and it **models**
the on-disk bytes rather than intercepting a real filesystem — a production DST would
add a real IO-intercept layer. Together with slices 1 & 2, gap #3's three named pieces
(crash-consistency · history-checker · deterministic VOPR loop) now exist in prototype;
the remaining work is a production-grade IO-virtualization layer.
