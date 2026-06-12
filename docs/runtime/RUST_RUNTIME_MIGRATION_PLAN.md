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
| 6 | Expand Rust surface | ✅ replay/idempotency guards, balance accounting, zUSD mint/redeem, buyback burn rails, batch-clearing settlement primitive (ordering/liquidity orchestration staged) |
| 7 | SPARK/Ada sidecar | ☐ spec drafted; toolchain (`gnatprove`) not available in this env |
| 8 | CI integration | ✅ `.github/workflows/runtime-shadow.yml` (+ existing Tau/ESSO/Lean jobs) |
| 9 | Promotion criteria | ☐ documented; not yet met for any surface |

## Phase 3 — fee router (delivered)

`route_fee(source, asset, amount, split_table, accumulator) -> receipt,
new_accumulator` routes a per-domain protocol fee into four buckets — `buyburn`,
`stakers`, `reserve`, `hosts` — with **source/asset-scoped dust carry**.

Conservation invariant (identical in form to the ESSO `fee_split_dust_carry`
kernel, generalized from 3 to 4 buckets):

```
amount + dust_in == buyburn + stakers + reserve + hosts + dust_out
```

`dust_in` and `dust_out` are keyed by `(source, asset)`. Cumulative bucket
balances are keyed by `asset`, so zUSD, AGRS, quote assets, and future bridge
assets cannot be added into one untyped integer.

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

## Phase 6 — replay / idempotency guard (delivered)

First widening surface. `admit(state, sender, nonce) -> receipt, new_state`
enforces the per-sender **strict-sequential** nonce policy of
`src/state/nonces.py` as a single transition: a sender's nonces must be
`1, 2, 3, …` with no gaps; `nonce == last` is a duplicate, `< last` a stale
replay, `> last + 1` a gap. State is keyed per sender.

* Python authority: `src/core/replay_guard.py`
* Rust shadow: `rust-runtime/crates/zenodex-runtime-core/src/replay_guard.rs`
* Golden trace: `tests/runtime/golden_traces/replay_guard_smoke.json`
  (`replay-guard-trace` CLI subcommand; kernel-dispatched shadow + replay tools).
* Conformance + invariants: `tests/runtime/test_replay_guard_conformance.py`
  (static + 400-case differential) and
  `tests/runtime/test_replay_guard_semantic_invariants.py` (per-sender
  isolation, monotonic acceptance, anti-replay, no-op-on-reject).

## Phase 6 — balance accounting (delivered)

Second widening surface. The transition form of `src/state/balances.py`:
`credit(state, recipient, asset, amount)` funds an account; `transfer(state,
sender, recipient, asset, amount)` is a supply-conserving move that rejects
insufficient balance. Balances are keyed per `(pubkey, asset)` and stored
sparsely (zero entries dropped).

* Python authority: `src/core/balance_kernel.py`
* Rust shadow: `rust-runtime/crates/zenodex-runtime-core/src/balance_kernel.rs`
* Golden trace: `tests/runtime/golden_traces/balance_smoke.json`
  (`replay-balance-trace` subcommand).
* Conformance + invariants: `test_balance_kernel_conformance.py` (static +
  400-case) and `test_balance_kernel_semantic_invariants.py` (supply
  conservation, only-named-keys-change, non-negativity/sparsity, no-op-on-reject).

## Phase 6 — zUSD mint/redeem accounting (delivered)

Third widening surface, and the first with a pre-existing authoritative module:
`src/core/zusd.py`'s single-vault `step` (oracle flow, recovery-mode gating, MCR,
base-rate fees, mint/redeem/liquidate). The harness **drives that authority
directly** (no second semantics); the Rust shadow `zenodex-runtime-core::zusd`
mirrors it.

Key fidelity point: zUSD's CDP ratio checks (`collateral * price * bps` vs
`debt * mcr * 1e8`) reach ~`2^213` at the `1e30` amount bound — beyond `u128`.
A `u128`-only port would silently diverge on large values (the drift trap), so
the shadow computes those products with `num_bigint` and parses amounts as
bignums (`_require_pos_int` is unbounded in the authority; huge values are
rejected by *command-specific* logic, not a uniform bound). The 500-case
differential deliberately includes amounts above `u128` to exercise this.

* Authority: `src/core/zusd.py`; harness `tools/runtime/zusd_kernel_lib.py`.
* Rust shadow: `rust-runtime/crates/zenodex-runtime-core/src/zusd.rs`.
* Golden trace: `tests/runtime/golden_traces/zusd_smoke.json`
  (`replay-zusd-trace` subcommand).
* Conformance + invariants: `test_zusd_conformance.py` (static + 500-case
  differential with bignum edges) and `test_zusd_semantic_invariants.py`
  (supply conservation, mint/repay/redeem balance-sheet deltas, no bad debt,
  no-op-on-reject).

## Phase 6 — buyback / burn accounting rails (delivered)

Fourth widening surface. Authority `src/core/burn_receipts.py` decomposes a
burn receipt into four integer **rails**: replay (host gating), amount/budget
(the burn **floor** / budget: `burn_budget >= burn_amount`), supply (conserves
supply: `supply_after == supply_before - burn_amount`), and batch-sum (the
public burn **accumulator**: `after == before + burn_amount`). The Rust shadow
`zenodex-runtime-core::burn_receipts` mirrors these rails; the harness drives the
authority's rail functions directly. The verifier is stateless (each `tx` is a
self-contained rail tuple), so `post_state_root == initial_state_root`.

* Authority rails: `src/core/burn_receipts.py`; harness
  `tools/runtime/burn_receipts_lib.py`.
* Rust shadow: `rust-runtime/crates/zenodex-runtime-core/src/burn_receipts.rs`.
* Golden trace: `tests/runtime/golden_traces/burn_smoke.json`
  (`verify-burn-trace` subcommand).
* Conformance + invariants: `test_burn_receipts_conformance.py` (static +
  600-case differential) and `test_burn_receipts_semantic_invariants.py`
  (budget floor, supply conservation, accumulator growth, replay gating,
  no-burn inertness).

**Scope:** the integer rails are shadowed. The receipt structural envelope
(canonical-JSON `receipt_hash` and `verify_burn_receipt`'s lenient `int()`
coercion) stays Python-only pending bit-exact canonical-JSON/coercion parity in
Rust. Buyback **execution** (TWAP, pool depth, budget/slippage caps, wash-trade
gates) is not implemented — accrual + rails are accounting only.

## Phase 6 — batch-clearing settlement primitive (delivered)

Fifth widening surface. `batch_clearing.py` is large (~2130 lines: seven swap-
ordering strategies, CoW netting, liquidity, multi-pool aggregation). Its
consensus-critical **arithmetic** core — shared by every ordering strategy — is
the per-pool CPMM swap quote (`quote_cpmm_swap_exact_in/out` in
`settlement_swap_runtime_v1.py`, backed by the v8 kernel). That primitive is the
delivered surface; the Rust shadow `zenodex-runtime-core::cpmm_swap` threads a
single pool's reserves across a batch order, mirroring the deterministic
rounding (fee = ceil, exact-in out = floor, exact-out in = ceil) and domain
bounds.

* Authority: `settlement_swap_runtime_v1.py`; harness
  `tools/runtime/cpmm_settlement_lib.py`.
* Rust shadow: `rust-runtime/crates/zenodex-runtime-core/src/cpmm_swap.rs`.
* Golden trace: `tests/runtime/golden_traces/cpmm_smoke.json`
  (`settle-swap-trace` subcommand).
* Conformance + invariants: `test_cpmm_settlement_conformance.py` (static +
  500-case differential) and `test_cpmm_settlement_semantic_invariants.py`
  (constant-product k non-decreasing, exact reserve conservation, slippage
  admission, no-op-on-reject).

**Staged (orchestration, not consensus arithmetic):** the swap-ordering
heuristics (`optimal_ab_bounded`, `greedy_ab[_refined/_global]`,
`mci_ab_global`, `cow_pair_netting`), multi-pool aggregation, and liquidity
(create/add/remove) intents. The MEV-resistance of batch ordering is a property
of those layers; the per-swap math shadowed here is what they all apply.

## Avoiding semantic drift (lesson learned)

The fee router initially shipped a global accumulator that let dust cross token
units and fee streams; Python and Rust agreed, so the differential stayed green.
**Cross-language equality proves agreement, not correctness.** Every surface now
ships independent *semantic invariants* (run on each runtime separately) in
addition to the differential, and golden traces include a cross-key regression
case. See `SEMANTIC_DRIFT_CONTROLS.md` for the full discipline and the
per-surface checklist.

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

Status against these criteria (all six kernels): (1) ✅ differential, (2) ✅
proptest + semantic invariants, (4) ✅ `#![forbid(unsafe_code)]`, (5) ✅
integer-only, (6) ✅ explicit ordered byte encodings, (8) ✅ Python is authority.
For (3) fuzzing: the always-on **robustness harness**
(`crates/zenodex-runtime-core/tests/robustness.rs`, ~4000 adversarial cases per
kernel on the stable toolchain) runs in CI and asserts the no-panic / typed-
`Result` / invariant property a fuzzer targets; the matching `cargo-fuzz`
targets live in `fuzz/` and need a **bounded libFuzzer campaign on nightly**
(unavailable in the authoring environment) to fully discharge (3). (7) is
per-surface and tracked in the boundary table.

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
