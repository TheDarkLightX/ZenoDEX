# RISC0 Prove-Time Benchmark (F5)

Measured steady-state prove cost per surface, so the WS3 proof-market pricing floor
(`R·(1−α_max) ≥ measured_prove_cost(surface)`) and the SLA-deadline floor
(`d ≥ measured_prove_time + race_rescue_margin`) can be parameterized. WS3 finding **F5**
("perps-NP/zUSD prove-times unmeasured") is now closed for spot/perps/zUSD.

## Methodology (`tools/bench_prove_times.py`)

Build the CLI + guest ELF **once** (recorded separately as `build_cost`), then time
**only** the steady-state `prove()` invocations against the cached binary — never
build/compile time. Per-surface deterministic requests; 1 warm-up (discarded) + N timed
reps; min/median/mean/p99/stdev. **`RISC0_DEV_MODE` guard** (refuses to run under dev
mode, which fakes proofs); **fail-closed** (build/toolchain/prove/verify failure →
`unmeasured` + reason, never a fabricated number; a surface with *any* failed rep is
`unmeasured`, not a partial measurement). Dual-reviewed (workflow A−/B+/A−; Codex C+ →
the fail-closed HIGH + OSError findings fixed).

## Results — 2026-06-08

Environment: `dev_mode=False` (real STARKs), RISC0 2.3.2, `default_prover` (CPU),
build_cost ≈ **115 s** (one-time, excluded from prove times). Run: 1 warm-up + 3 timed reps.

| Surface | Status | median (s) | min (s) | mean (s) | p99 (s) | stdev | verify (ms) |
|---|---|---:|---:|---:|---:|---:|---:|
| spot | measured | **10.37** | 10.19 | 10.40 | 10.62 | 0.2 | 33 |
| zusd | measured | **24.48** | 23.68 | 24.27 | 24.64 | 0.5 | 30 |
| perps_np | measured | **45.50** | 44.79 | 45.82 | 47.17 | 1.2 | 28 |
| clob | **unmeasured** | — | — | — | — | — | — |

**clob** is honestly `unmeasured`: the harness's CLOB *verify*-request builder omits
`context.app_hash_pre`, so the representative verify is rejected and — per the fail-closed
verify gate — the whole surface is downgraded rather than reporting a prove number it
can't confirm verifies. The prove itself succeeded; the gap is the verify-request builder
(a small harness follow-up), not the prover. Tracked.

## Key findings

- **Verify is ~1000× cheaper than prove** (≈28–33 ms vs 10–46 s) — the prove/verify
  asymmetry that is the proof-market's reason to exist (WS3).
- **The old "~31s CLOB / 46–96s spot" anecdote was build+compile time, not prove time.**
  Measured steady-state spot prove is ~10.4 s. This validates the methodology's
  build-vs-prove separation.
- Prove cost scales with circuit complexity: spot (10 s) < zUSD (24 s) < perps-NP (46 s).

## WS3 pricing implication

The pricing floor `R·(1−α_max) ≥ measured_prove_cost` can now use real numbers for
spot/zUSD/perps. SLA deadlines must satisfy `d ≥ ~p99_prove + race_rescue_margin`
(e.g. perps-NP ≥ ~47 s + margin). These are CPU `default_prover` numbers; GPU/Bonsai
would change the absolutes (re-measure per deployment target). Raw data:
`runs/bench_prove_times_real_v1.json`.
