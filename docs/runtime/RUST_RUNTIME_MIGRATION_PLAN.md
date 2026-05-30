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
| 4 | State root & canonical serialization | ✅ canonical primitives and state root v5 promoted to public-testnet `rust_authority_with_python_shadow` |
| 5 | Shadow runtime mode | ✅ `tools/runtime/rust_shadow_replay.py` |
| 6 | Expand Rust surface | ◑ replay/idempotency guards ✅, balance accounting ✅, **zUSD full single-vault** (mint/repay/deposit-sp/withdraw-sp/redeem/liquidate + oracle/recovery gating) ✅, buyback burn rails ✅, **batch-clearing CPMM settlement** (per-pool primitive) ✅; next: state-root, perps math, tx/receipt hashes |
| 7 | SPARK/Ada sidecar | ☐ fee-router + burn-rail kernels drafted; toolchain (`gnatprove`) not available in this env → **advisory / vector-checked only** |
| 8 | CI integration | ✅ `.github/workflows/runtime-shadow.yml` (Python + Rust + shadow + OCaml jobs; existing Tau/ESSO/Lean jobs untouched) |
| 9 | Promotion criteria | ◑ canonical primitives, state root v5, replay/idempotency guard, and balance accounting promoted on public-testnet; remaining surfaces stay in evidence-gathering |
| I | OCaml executable spec oracle | ◑ `ocaml-runtime/` — third independent impl of fee-router split + replay-guard nonce policy, driven by Python-derived TSV vectors; `dune build && dune test` green. Pure spec oracle, never a production path. More surfaces TBD |

> The Phase 0–9 numbering above is the original internal milestone scheme. The
> "remaining-phases" task (`internal/prompts/claude_complete_runtime_port_remaining_phases_2026_05_29.md`)
> uses a parallel A–K lettering; the gap map below reconciles the two against
> the actual tree state on `main` and is the authoritative status for that work.

## Remaining-phases gap map (as of 2026-05-29, `main` @ `7b587cf2`)

Each row is a runtime surface. `Rust` = shadow status; `GT` = golden trace;
`Diff` = randomized Python/Rust differential; `Inv` = independent semantic
invariants. SPARK/OCaml columns mark assurance-sidecar coverage.

| Surface | Python authority | Rust | GT | Diff | Inv | SPARK | OCaml | Next action |
|---------|------------------|------|----|----|-----|-------|-------|-------------|
| Fee router (4-way + dust) | `src/core/fee_router.py` | ✅ | ✅ | ✅ 400 | ✅ | advisory ✅ | ✅ oracle | fuzz (promotion) |
| Replay/idempotency guard | `src/core/replay_guard.py` | ✅ | ✅ | ✅ 400 | ✅ | — | ✅ oracle | public-testnet promoted |
| Balance accounting | `src/core/balance_kernel.py` | ✅ | ✅ | ✅ 400 | ✅ | — | — | public-testnet promoted |
| zUSD single-vault (full) | `src/core/zusd.py` `step` | ✅ mint/repay/deposit-sp/withdraw-sp/redeem/liquidate + oracle/recovery | ✅ | ✅ 500 (>u128) | ✅ + `_reference` (13) | — | — | promotion gate (fuzz) |
| Buyback burn rails | `src/core/burn_receipts.py` | ✅ rails | ✅ | ✅ 600 | ✅ | advisory ✅ | — | receipt-body JSON hash (Phase F) |
| Canonical primitives | `src/state/canonical.py` | ✅ uvarint/bytes/domain-sep/sha256 + `hex_to_bytes_fixed` + `canonical_json_bytes` | n/a | ✅ vectors | n/a | — | planned | — |
| CPMM settlement (per-pool) | `src/kernels/python/settlement_swap_runtime_v1.py` | ✅ | ✅ `cpmm_smoke` | ✅ shadow | ✅ | — | — | orchestration (multi-pool/CoW/ordering) deferred |
| State root (network) | `src/state/state_root.py` | ✅ v5 | ✅ vectors | ✅ shadow | ✅ | — | — | promotion gate (fuzz) |
| Perps math (stateless) | `src/core/perp_v2/math.py` | ✅ E1 (9 fns) | n/a | ✅ shadow | ✅ sign-sym | — | — | stateful engine/lifecycle = E2 (deferred) |
| Tx auth / receipt hash | `src/core/dex_intent_auth_message.py`, `src/core/burn_receipts.py` body | ✅ `domain_json_hash` op | n/a | ✅ vectors | ✅ sensitivity | — | — | shape-gate + BLS verify still out of scope |
| Batch-clearing orchestration | `src/core/batch_clearing.py` (2129 ln) | ❌ | — | — | — | — | — | **OUT OF SCOPE** (multi-pool/CoW/ordering deferred) |
| Revenue router (fine-source) | *(not on `main`)* | n/a | — | — | — | — | — | hybrid-economics branch only — separate prompt |

### Reconciliation notes (corrections to the remaining-phases prompt's assumed map)

* **zUSD is already a full single-vault shadow.** `zusd.rs` shadows `DepositSp`,
  `WithdrawSp`, `RedeemZusd`, `Liquidate` and recovery-mode gating (`tcr_ok`,
  `in_recovery_mode`, `risky_ops_allowed`). The remaining-phases "zUSD" work is a
  **test-audit** (add the missing `_reference` + overflow tests), not new handlers.
* **`revenue_router.py` does not exist on `main`.** Fee routing has a single
  authority (`fee_router.py`); the fine-source revenue router lives only on the
  hybrid-economics branch and is out of scope here. No router reconciliation code
  is needed (Phase G is a one-paragraph decision in the boundary doc).
* **Canonical-primitive prerequisite.** State-root parity (Phase C) needs
  `hex_to_bytes_fixed`; tx/receipt hashing (Phase F) needs `canonical_json_bytes`.
  Both are added first (Phase A.5) before the surfaces that consume them.
* **Tooling on this host:** `cargo` 1.87.0 ✅; `gnatprove` ❌ (SPARK advisory only,
  never claimed "proven"); `opam exec -- dune` ✅ (OCaml spec-oracle build/test
  passes here).

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

### Phase 9 / K promotion criteria

**Canonical primitives and state root v5 are the first shadow-checked
Rust-authority lanes on `public-testnet`.** Python remains the default
authority, `production-strict` remains all-Python, and no surface runs pure
`rust_authority`. Further promotions require explicit profile entries,
replayable evidence, and human review.

A surface is *eligible* for Rust authority only when **all** hold:

```text
1.  Python/Rust golden-trace equality
2.  randomized differential tests pass
3.  independent semantic invariants pass (per runtime, not a cross-impl diff)
4.  state-root and receipt-hash parity
5.  malformed-input rejection tests pass
6.  no unsafe (#![forbid(unsafe_code)])
7.  no floats / no nondeterministic iteration in canonical output
8.  deterministic canonical encoding (explicit ordered byte encodings)
9.  fuzz / stateful weird-machine test evidence
10. Tau/ESSO/Lean obligations still green where applicable
11. Python remains available as a shadow checker
12. human review + explicit promotion decision
```

Per-surface status (criteria 1–8, 10–11 are what this work can establish; **9
fuzz** and **12 human promotion** are outstanding for *every* surface):

| Surface | 1 trace | 2 diff | 3 inv | 4 root/receipt | 5 reject | 6–8 hygiene | 9 fuzz | 12 promoted |
|---------|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
| fee_router | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ☐ | ☐ |
| replay_guard | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| balance_kernel | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| zusd (single-vault) | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ☐ | ☐ |
| burn_receipts rails | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ☐ | ☐ |
| cpmm_settlement | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ☐ | ☐ |
| state_root | ✅ vectors | ✅ | ✅ | ✅ | ✅ | ✅ | ☐ | ☐ |
| tx/receipt hash | ✅ vectors | ✅ | ✅ | n/a | ✅ | ✅ | ☐ | ☐ |
| perp_math (E1) | ✅ vectors | ✅ | ✅ | n/a | ✅ | ✅ | ☐ | ☐ |

The remaining authoritative surfaces with no Rust shadow yet (full batch-clearing
orchestration, the stateful perps engine, multi-vault zUSD, the intent
shape-gate, BLS verification) are tracked in the gap map above and are **not**
eligible until shadowed.

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
`../../rust-runtime/README.md`, `../../spark-kernels/fee_router/README.md`,
`../../spark-kernels/burn_rails/README.md`.
