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

### Router ownership (Phase G decision)

There is **one** router authority on `main`: `src/core/fee_router.py` (coarse
four-destination domains: buyburn / stakers / reserve / hosts). The fine-source
hybrid-economics router (`src/core/revenue_router.py`) **does not exist on
`main`** — it lives only on the hybrid-economics branch and is governed by a
separate prompt. There is therefore **no two-router divergence to reconcile
here, and no adapter is needed**. If/when `revenue_router.py` lands on `main`,
the required reconciliation (a documented collapse of fine sources into the
coarse domains with identical semantics, or an explicit supersedes-decision with
the legacy router retained for old traces) must happen *before* any Rust shadow
of the fine-source router is added.

## Trusted-core boundary table

`RC?` = runtime-critical. *Evidence required* lists what must be green before a
surface can be promoted to Rust authority.

| Module | Current language | RC? | Target | Evidence required |
|--------|------------------|-----|--------|-------------------|
| Protocol fee routing — `src/core/fee_router.py` | Python (+ Rust shadow) | yes | **Rust (owns first)** | ✅ golden traces, ✅ Python/Rust differential, ✅ property tests, fuzz (Phase 9) |
| Canonical serialization — `src/state/canonical.py` | Python (+ Rust `canonical`) | yes | Rust | cross-language primitive vectors (✅ uvarint/bytes/domain-sep/sha256), full state-encoder parity (Phase 4/6) |
| State-root generation — `src/state/state_root.py` (+ Rust `state_root`) | Python (+ Rust shadow) | yes | **Rust (Phase C, done)** | ✅ v5 shadow (`zenodex-runtime-core::state_root`) over six sections incl. LP duration-risk and fee-accumulator dust; ✅ same-root/different-root/order-independence fixtures; ✅ Python/Rust differential (static + 4×250 randomized) feeding the *normalized* built state; ✅ malformed-encoding + duplicate-key + fee-bps rejection. Amounts use `u128` (covers the live domain; ≥2^128 rejected at the bridge). fuzz (Phase 9) |
| Replay / idempotency guards — `src/core/replay_guard.py` (+ Rust shadow), policy from `src/state/nonces.py` | Python (+ Rust shadow) | yes | **Rust (Phase 6, done)** | ✅ golden traces incl. duplicate/stale/gap rejection + cross-sender case, ✅ Python/Rust differential, ✅ semantic invariants (per-sender isolation), fuzz (Phase 9) |
| Balance accounting — `src/core/balance_kernel.py` (+ Rust shadow), table from `src/state/balances.py` | Python (+ Rust shadow) | yes | **Rust (Phase 6, done)** | ✅ golden traces incl. insufficient/self/overflow + cross-account/asset case, ✅ Python/Rust differential, ✅ semantic invariants (supply conservation, only-named-keys-change, non-negativity), fuzz (Phase 9) |
| zUSD full single-vault — `src/core/zusd.py` (authority) + Rust shadow `zenodex-runtime-core::zusd` | Python (+ Rust shadow) | yes | **Rust (Phase 6, done)** | ✅ shadows the full single-vault `step`: mint/repay/deposit-sp/withdraw-sp/redeem/liquidate + oracle bootstrap/report/commit and recovery-mode gating (`tcr_ok`/`in_recovery_mode`/`risky_ops_allowed`). ✅ golden trace, ✅ Python/Rust differential incl. >u128 amounts (bignum CDP-ratio math), ✅ semantic invariants (supply conservation, balance-sheet deltas, no bad debt). ✅ `_reference` unit suite (mint/repay/sp/redeem/liquidate balance-sheet deltas, supply conservation, no-op-on-reject, arbitrary-precision CDP path). Remaining: fuzz (Phase 9). The multi-vault `step` (`zusd.py` L850+) stays Python-only |
| Buyback accrual + burn floor — accrual in `fee_router` (`cum_buyburn`) ✅; burn **accounting rails** `src/core/burn_receipts.py` + Rust shadow `zenodex-runtime-core::burn_receipts` | Python (+ Rust shadow) | yes | **Rust rails (Phase 6, done)**; burn *execution* later | ✅ accrual conservation, ✅ burn rails (budget/floor, supply conservation, batch accumulator) shadowed + differential + semantic invariants. Receipt envelope (canonical-JSON hash + lenient `int()` coercion) stays Python-only pending bit-exact parity. Burn **execution** still gated on TWAP / pool-depth / budget+slippage caps / wash-trade controls before any execution path |
| Batch clearing — `src/core/batch_clearing.py`, `settlement*.py` | Python | yes | Rust (Phase 6, last) | ✅ per-pool CPMM settlement primitive shadowed (`cpmm_swap`); orchestration (multi-pool/CoW/ordering/liquidity) still Python-only; existing Tau/Lean batch obligations stay green |
| Perps risk math — `src/core/perp_v2/math.py` (+ Rust `perp_math`) | Python (+ Rust shadow) | yes | **Rust math (E1, done)** | ✅ stateless slice shadowed (oracle freshness/move/clamp, margin, signed PnL, liquidation eligibility, funding) with signed `i128` + sign-symmetry invariants + static/4×500 differential + domain rejection. The stateful epoch lifecycle / clearinghouse settlement / insurance (`engine.py`, `updates.py`) is a later slice (E2) |
| Perps stateful — `advance_epoch` + `apply_funding_auto` settlement (`src/integration/perp_engine.py::_apply_isolated_advance_epoch`, `_apply_isolated_apply_funding_auto`) (+ Rust `perp_advance_epoch`, `perp_funding_auto`) | Python (+ Rust shadow) | yes | **Rust shadow (E2 partial)** | ✅ FIRST stateful-perps slices shadowed. `advance_epoch` models the settled-epoch integration gate (`oracle_last_update_epoch == now_epoch`), delta/domain guard, and exact global update (`now_epoch += delta`, `epoch_phase = Open`) with Python/Rust differential + golden trace (`advance_epoch_smoke.json`). `apply_funding_auto` shadows the bounded-sink funding settlement: per-account `collateral_quote`, `funding_paid_cumulative`, `funding_last_applied_epoch` (same-epoch replay/double-apply rejects), global `funding_rate_bps`, and `fee_pool/fee_income/insurance += projected_net` (fail-closed sink bounds; no counterparty residual; no `Σ position_base == 0` requirement). Funding transition arithmetic is **checked** (`checked_add/_sub`, fail-closed `funding_arithmetic_overflow`). Evidence: Rust unit tests + `proptest` properties + Python/Rust differentials that drive the real authority via `apply_perp_ops` and compare reject reasons; funding gate `tools/run_perp_funding_auto_sink_assurance_gate.sh` + Lean `Proofs.PerpFundingSinkConservation` wired into `run_perps_evidence.sh`. **Shadow only — NOT Rust authority.** Remaining E2: `publish_clearing_price`, `settle_epoch`, liquidation, insurance accounting |
| Receipt generation — fee receipt (✅), `src/core/quote_receipts.py`, `src/core/burn_receipts.py` | Python (+ Rust fee-receipt) | yes | Rust per-surface | canonical receipt-hash parity (✅ for fee receipts); per-surface vectors |
| Legacy swap-fee split (3-way) — `src/core/fees.py` | Python | yes | stays Python (Tau/ESSO-covered) | already covered by `tokenomics_fee_split_32_v1.tau` + `fee_split_dust_carry_*` ESSO kernels; **unchanged** by this work |
| Transaction validation — `src/integration/validation.py`, `tau_gate.py`, `zusd_tau_gate.py` | Python | yes | Rust verification interface (Phase 6+) | golden traces incl. invalid-signature/insufficient-balance rejection; Tau-gate parity; differential. **Hashing slice done**: DEX intent auth message hash (`dex_intent_auth_message.py`) + burn-receipt body hash (`burn_receipts.py`) shadowed via the `domain_json_hash` op (`sha256(domain_sep(label,version)+canonical_json_bytes)`); cross-language vectors (static + 3×300 randomized) + chain-id/field sensitivity. The intent **shape-gate** and **BLS signature verification** remain Python-only (crypto is wrapped, never reimplemented) |
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
