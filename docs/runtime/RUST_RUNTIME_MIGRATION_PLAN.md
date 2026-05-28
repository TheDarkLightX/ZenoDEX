# Rust Deterministic Runtime — Migration Plan

## Goal

Build a **Rust deterministic runtime core** for ZenoDEX while keeping **Python**
as the current reference/orchestration runtime, with optional **SPARK/Ada** used
only for tiny high-assurance accounting kernels. Purpose: higher assurance,
deterministic replay, performance, and a smaller trusted runtime surface.

We do **not** rewrite the system at once. We build a small canonical kernel,
conformance-test it against existing Python behavior, then widen only after
trace equality is stable.

## Architecture target

* **Production candidate:** Rust deterministic runtime core (`rust-runtime/`).
* **Reference (authoritative today):** the Python runtime (`src/**`).
* **Formal/spec layer (unchanged):** Tau specs, ESSO kernels, Lean proofs.
* **Optional high-assurance sidecar:** SPARK/Ada for small accounting kernels
  (e.g. fee-split conservation) — advisory only unless explicitly integrated.

Python and Rust are **not** both independently authoritative on network state.
The first milestone is **shadow execution and exact state-root agreement**.

## Hard rules (and how they are honored)

1. **Respect `AGENTS.md`.** No `AGENTS.md`/`CLAUDE.md` is present in the repo;
   conventions were inferred from existing code (`src/state/canonical.py` style,
   `from ..state.canonical import …`, MIT license, `resolver = "2"`).
2. **No unrelated worktree reverts.** This work is purely additive.
3. **External Tau Lang untouched.**
4. **No weakening of Tau/ESSO/Lean.** The new 4-way `fee_router` is a distinct
   surface from the legacy 3-way `src/core/fees.py`; that module and its Tau
   (`tokenomics_fee_split_32_v1.tau`) / ESSO (`fee_split_dust_carry_*`) specs are
   left intact.
5. **One authoritative transition semantics.** Python is authoritative; Rust is
   a shadow until promotion (Phase 9).
6. **Multiple runtimes only as shadow/reference/checker** until conformance is
   mature.
7. **No floating point** in runtime-critical logic (integer-only, LEB128).
8. **No wall-clock / randomness / network / filesystem / env reads** inside
   transitions (the core crate forbids them by construction).
9. **`#![forbid(unsafe_code)]`** on every Rust consensus crate.
10. **Every transition returns `Result<Accepted, RejectedReason>`** — never a
    silent fallback.

## Status by phase

| Phase | Title | Status |
|-------|-------|--------|
| 0 | Runtime boundary audit | ✅ `RUNTIME_TRUSTED_CORE_BOUNDARY.md` |
| 1 | Golden trace corpus | ✅ format + exporter/replayer + `smoke.json` |
| 2 | Rust workspace scaffold | ✅ `rust-runtime/` core + cli, checked arithmetic |
| 3 | Minimal Rust transition kernel (fee router) | ✅ `route_fee` + Python/Rust conformance |
| 4 | State root & canonical serialization | ◑ canonical primitives + fee receipt/accumulator roots done; full network state-encoder parity pending |
| 5 | Shadow runtime mode | ✅ `tools/runtime/rust_shadow_replay.py` |
| 6 | Expand Rust surface | ☐ replay guards → balances → zUSD → buyback burn → batch clearing |
| 7 | SPARK/Ada sidecar | ☐ spec drafted; toolchain (`gnatprove`) not available in this env |
| 8 | CI integration | ✅ `.github/workflows/runtime-shadow.yml` (+ existing Tau/ESSO/Lean jobs) |
| 9 | Promotion criteria | ☐ documented; not yet met for any surface |

## Phase 3 — fee router (delivered)

`route_fee(source, asset, amount, split_table, accumulator) -> receipt,
new_accumulator` routes a per-domain protocol fee into four buckets — `buyburn`,
`stakers`, `reserve`, `hosts` — with **dust carry**.

Conservation invariant (identical in form to the ESSO `fee_split_dust_carry`
kernel, generalized from 3 to 4 buckets):

```
amount + dust_in == buyburn + stakers + reserve + hosts + dust_out
```

Safety floors enforced as explicit rejections (Hard Rule #10):

* `redemption.buyburn = 0`, `redemption.hosts = 0`, `redemption.reserve >= 2000` bps
* `dex/perps.buyburn >= 5000` bps
* `borrow.stakers >= 5000` bps
* all outputs `>= 0`

### Canonical MVP split (bps)

| domain | buyburn | stakers | reserve | hosts |
|--------|---------|---------|---------|-------|
| DEX/perps | 6000 | 0 | 2000 | 2000 |
| Borrow | 0 | 6000 | 2000 | 2000 |
| Redemption | 0 | 6000 | 4000 | 0 |

(i.e. `60/0/20/20`, `0/60/20/20`, `0/60/40/0` across buyburn/stakers/reserve/hosts).

## Important current economics context

* Use the corrected MVP split above. The floors are *invariants* (looser than
  the concrete table); `canonical_split_table()` returns the concrete table.
* **Host compensation is internal protocol-fee routing** (the `hosts` bucket).
  It is **not** modeled as hidden add-on debt, and **no unfunded zDEX is minted**
  for hosts — `route_fee` only ever partitions an existing `amount`.
* **SP-ZDEX rewards are locked-vault transfers with remainder carry**, *not* new
  supply minting. The `fee_router` accrues to buckets only; it never mints.
* **Buyback accrual is accrual only.** `cum_buyburn` accumulates; this plan does
  **not** implement buyback execution. Buyback TWAP security is *not* solved by
  window length alone — pool depth, budget caps, slippage caps, and wash-trade
  gates are required controls and are prerequisites before any execution path is
  built (tracked for Phase 6 "buyback").

## Rust core design

* Crate `zenodex-runtime-core` (`#![forbid(unsafe_code)]`): `arith` (checked
  `u128`), `canonical` (LEB128 / domain-sep / SHA-256, mirrors Python),
  `error` (`thiserror` `RejectedReason` with stable `code()`/`reason_str()`),
  `fee_router`.
* Crate `zenodex-runtime-cli` (bin `zenodex-runtime`): the cross-language bridge
  — `replay-fee-trace` reads a golden trace and emits computed per-step results.
  Used by both conformance tests and the shadow driver. FFI is intentionally
  deferred (a CLI bridge avoids `unsafe`/ABI surface for the MVP).
* Avoided: floats, global mutable state, system time, randomness, panics in
  public transition functions, unordered-map iteration in canonical output.

## Forward path (Phases 6–9)

For each new surface: add the Rust implementation, add golden traces (happy +
disaster), add Python/Rust differential + property + rejection tests, run fuzz,
and update the boundary table. Recommended order: replay/idempotency guards →
balance accounting → zUSD mint/redeem → buyback accumulator/burn floor → batch
clearing admission → batch clearing settlement. **Do not move crypto first** —
wrap established libraries behind a deterministic verification interface.

### Phase 9 promotion criteria

A surface becomes Rust-authoritative only when **all** hold: (1) Python/Rust
golden-trace equality, (2) property tests pass, (3) fuzzing has run for the
module, (4) no `unsafe`, (5) no float use, (6) no nondeterministic iteration in
canonical output, (7) the module's Tau/ESSO/Lean obligations still pass, and
(8) the Python path remains available as a shadow checker.

## How to run

```bash
# Python reference + golden traces + (if Rust present) conformance
pytest tests/runtime -q
python3 tools/runtime/export_golden_trace.py --out tests/runtime/golden_traces/smoke.json
python3 tools/runtime/replay_golden_trace.py tests/runtime/golden_traces/smoke.json

# Rust core
cd rust-runtime && cargo test && cargo clippy --all-targets -- -D warnings && cargo fmt --check

# Shadow differential (Rust vs Python)
python3 tools/runtime/rust_shadow_replay.py tests/runtime/golden_traces/smoke.json
```

See also: `RUNTIME_TRUSTED_CORE_BOUNDARY.md`, `GOLDEN_TRACE_FORMAT.md`,
`../../rust-runtime/README.md`, `../../spark-kernels/fee_router/README.md`.
