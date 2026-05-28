# Runtime Trusted-Core Boundary

This document draws the line between **consensus/runtime-critical** logic (a
candidate for the Rust deterministic core) and **non-critical** logic (which
stays Python). It is the Phase 0 boundary audit.

Authoritative-semantics rule: there is exactly **one** authoritative transition
semantics per surface. Today that authority is the **Python runtime**. The Rust
core (`rust-runtime/`) is a **shadow / reference / checker** until conformance
for a surface is mature and it is explicitly promoted (see
`RUST_RUNTIME_MIGRATION_PLAN.md`, Phase 9). Python and Rust are **not** both
independently authoritative on network state.

## What Rust owns first

**Fee routing + accounting conservation.** It is small, high-value, and
load-bearing for zUSD compensation, host compensation, the reserve, and
buy-burn. It is implemented and conformance-tested today:

* Authoritative Python reference: `src/core/fee_router.py`
* Rust shadow: `rust-runtime/crates/zenodex-runtime-core/src/fee_router.rs`
* Conformance: `tests/runtime/test_fee_router_conformance.py` (static +
  400-case randomized differential), `tools/runtime/rust_shadow_replay.py`.

Rust is **not** production-authoritative for fee routing yet — Python remains
the authority and Rust is the shadow checker.

The fee-router accumulator is asset-aware. Dust is keyed by `(source, asset)`;
bucket totals are keyed by `asset`. This is part of the trusted-core boundary
because fee units from different tokens must never be merged into one scalar.

## Trusted-core boundary table

`RC?` = runtime-critical. *Evidence required* lists what must be green before a
surface can be promoted to Rust authority.

| Module | Current language | RC? | Target | Evidence required |
|--------|------------------|-----|--------|-------------------|
| Protocol fee routing — `src/core/fee_router.py` | Python (+ Rust shadow) | yes | **Rust (owns first)** | ✅ golden traces, ✅ Python/Rust differential, ✅ property tests, fuzz (Phase 9) |
| Canonical serialization — `src/state/canonical.py` | Python (+ Rust `canonical`) | yes | Rust | cross-language primitive vectors (✅ uvarint/bytes/domain-sep/sha256), full state-encoder parity (Phase 4/6) |
| State-root generation — `src/state/state_root.py` | Python | yes | Rust | same-root / different-root fixtures; cross-version + cross-language equality |
| Replay / idempotency guards — `src/core/replay_guard.py` (+ Rust shadow), policy from `src/state/nonces.py` | Python (+ Rust shadow) | yes | **Rust (Phase 6, done)** | ✅ golden traces incl. duplicate/stale/gap rejection + cross-sender case, ✅ Python/Rust differential, ✅ semantic invariants (per-sender isolation), fuzz (Phase 9) |
| Balance accounting — `src/core/balance_kernel.py` (+ Rust shadow), table from `src/state/balances.py` | Python (+ Rust shadow) | yes | **Rust (Phase 6, done)** | ✅ golden traces incl. insufficient/self/overflow + cross-account/asset case, ✅ Python/Rust differential, ✅ semantic invariants (supply conservation, only-named-keys-change, non-negativity), fuzz (Phase 9) |
| zUSD mint/redeem accounting — `src/core/zusd.py` (authority) + Rust shadow `zenodex-runtime-core::zusd` | Python (+ Rust shadow) | yes | **Rust (Phase 6, done)** | ✅ golden trace (mint/redeem/oracle/recovery gates), ✅ Python/Rust differential incl. >u128 amounts (bignum CDP-ratio math), ✅ semantic invariants (supply conservation, balance-sheet deltas, no bad debt), fuzz (Phase 9) |
| Buyback accrual + burn floor — accrual in `fee_router` (`cum_buyburn`) ✅; burn **accounting rails** `src/core/burn_receipts.py` + Rust shadow `zenodex-runtime-core::burn_receipts` | Python (+ Rust shadow) | yes | **Rust rails (Phase 6, done)**; burn *execution* later | ✅ accrual conservation, ✅ burn rails (budget/floor, supply conservation, batch accumulator) shadowed + differential + semantic invariants. Receipt envelope (canonical-JSON hash + lenient `int()` coercion) stays Python-only pending bit-exact parity. Burn **execution** still gated on TWAP / pool-depth / budget+slippage caps / wash-trade controls before any execution path |
| Batch clearing — `src/core/batch_clearing.py`, `settlement*.py` | Python | yes | Rust (Phase 6, last) | admission + settlement golden traces; differential; property; existing Tau/Lean batch obligations stay green |
| Receipt generation — fee receipt (✅), `src/core/quote_receipts.py`, `src/core/burn_receipts.py` | Python (+ Rust fee-receipt) | yes | Rust per-surface | canonical receipt-hash parity (✅ for fee receipts); per-surface vectors |
| Legacy swap-fee split (3-way) — `src/core/fees.py` | Python | yes | stays Python (Tau/ESSO-covered) | already covered by `tokenomics_fee_split_32_v1.tau` + `fee_split_dust_carry_*` ESSO kernels; **unchanged** by this work |
| Transaction validation — `src/integration/validation.py`, `tau_gate.py`, `zusd_tau_gate.py` | Python | yes | Rust verification interface (Phase 6+) | golden traces incl. invalid-signature/insufficient-balance rejection; Tau-gate parity; differential |
| Crypto (BLS12-381 verify) — `py-ecc` via integration | Python | yes | **wrapped, not rewritten** | established library behind a deterministic verification interface; *do not migrate crypto first* |

## Non-critical modules (stay Python)

These never decide network state and are not in the trusted core:

| Concern | Location(s) | Notes |
|---------|-------------|-------|
| Orchestration | `src/integration/dex_engine.py` (wiring), `src/agents/**` | sequences calls into the trusted core; carries no authoritative transition math |
| CLI tools | `tools/**` (incl. `tools/runtime/*.py`) | exporters, replayers, shadow drivers, operator tooling |
| Dashboards / UI | `tools/dex-ui/**` | presentation only |
| Experiments | `experiments/**` | research; excluded from `pytest`/lint by config |
| Local testnet harness | `docker-compose.local-testnet.yml`, related `tools/**`, `bin/**` | dev/operability |
| Docs generation | `docs/**`, generators under `tools/**` | documentation |

## Formal layer (unchanged)

Tau specs (`src/tau_specs/**`, `formal/tau/**`), ESSO kernels
(`src/kernels/**`, `formal/esso/**`), and Lean proofs (`lean-mathlib/**`,
`formal/**`) are the spec/proof layer. This migration **does not modify or
weaken** any of them. In particular, the new 4-way protocol `fee_router` is a
**distinct surface** from the legacy 3-way swap-fee split in `src/core/fees.py`;
the latter's Tau spec (`tokenomics_fee_split_32_v1.tau`) and ESSO kernels
(`fee_split_dust_carry_*`) are left intact. Each Rust-owned surface must keep
its corresponding Tau/ESSO/Lean obligations green as a promotion gate (Phase 9).
