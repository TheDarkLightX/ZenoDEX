# Runtime Trusted-Core Boundary

This document draws the line between **consensus/runtime-critical** logic (a
candidate for the Rust deterministic core) and **non-critical** logic (which
stays Python). It is the Phase 0 boundary audit.

Authoritative-semantics rule: there is exactly **one** authoritative transition
semantics per surface. The default authority is the **Python runtime**. A small
set of public-testnet surfaces now use Rust authority with Python shadow after
explicit promotion (see `RUST_RUNTIME_MIGRATION_PLAN.md`, Phase 9). Python and
Rust are **not** both independently authoritative on network state.

## What Rust owns first

**Fee routing + accounting conservation.** It is small, high-value, and
load-bearing for zUSD compensation, host compensation, the reserve, and
buy-burn. It is implemented and conformance-tested today:

* Python reference: `src/core/fee_router.py`
* Rust authority candidate: `rust-runtime/crates/zenodex-runtime-core/src/fee_router.rs`
* Conformance: `tests/runtime/test_fee_router_conformance.py` (static +
  400-case randomized differential), `tools/runtime/rust_shadow_replay.py`.
* Live authority wiring: `tests/runtime/test_fee_router_live_path.py`.
* Disaster-state evidence:
  `tests/runtime/test_fee_router_disaster_state.py`.

Fee routing now runs as `rust_authority_with_python_shadow` in the
`public-testnet` profile. The default and `production-strict` profiles remain
Python-authoritative.

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
| Protocol fee routing — `src/core/fee_router.py` | Rust+Python shadow on public-testnet | yes | **Rust (public-testnet promoted)** | ✅ golden traces, ✅ Python/Rust differential, ✅ property tests, ✅ live authority wiring, ✅ disaster-state rows and deterministic fuzz, ✅ Kani on the running split core for totality/dust exactness/non-vacuity, ✅ ESSO finite model + Rust codegen receipt for exact 4-way dust-core conservation. Production remains Python authority |
| Canonical serialization — `src/state/canonical.py` | Rust+Python shadow on public-testnet | yes | **Rust (public-testnet promoted)** | ✅ cross-language primitive vectors (uvarint/bytes/domain-sep/sha256), ✅ canonical authority live-path tests, ✅ disaster/fuzz evidence, ✅ Kani on heap-free helper predicates for domain-label bytes, ASCII hex digits, and selected LEB128 length boundaries. Full `Vec`/`String` encoders, SHA-256, and canonical JSON remain vector/fuzz/differential backed |
| State-root generation — `src/state/state_root.py` (+ Rust `state_root`) | Rust+Python shadow on public-testnet | yes | **Rust (public-testnet promoted)** | ✅ v5 shadow (`zenodex-runtime-core::state_root`) over six sections incl. LP duration-risk and fee-accumulator dust; ✅ same-root/different-root/order-independence fixtures; ✅ Python/Rust differential (static + 4×250 randomized) feeding the *normalized* built state; ✅ malformed-encoding + duplicate-key + fee-bps rejection; ✅ fuzz; ✅ Kani on scalar root-admission guards for fee bps, nonce bounds, LP duration metadata presence, and pool-status code distinctness. Amounts use `u128` (covers the live domain; ≥2^128 rejected at the bridge). Full section encoding, duplicate detection, BigUint curve-param parsing, and SHA-256 remain vector/fuzz/differential backed |
| Replay / idempotency guards — `src/core/replay_guard.py` (+ Rust shadow), policy from `src/state/nonces.py` | Rust+Python shadow on public-testnet | yes | **Rust (public-testnet promoted)** | ✅ golden traces incl. duplicate/stale/gap rejection + cross-sender case, ✅ Python/Rust differential, ✅ semantic invariants (per-sender isolation), ✅ live authority wiring, ✅ disaster-state rows and deterministic fuzz. Production remains Python authority |
| Balance accounting — `src/core/balance_kernel.py` (+ Rust shadow), table from `src/state/balances.py` | Rust+Python shadow on public-testnet | yes | **Rust (public-testnet promoted)** | ✅ golden traces incl. insufficient/self/overflow + cross-account/asset case, ✅ Python/Rust differential, ✅ semantic invariants (supply conservation, only-named-keys-change, non-negativity), ✅ live authority wiring, ✅ disaster-state rows and deterministic fuzz. Production remains Python authority |
| zUSD full single-vault — `src/core/zusd.py` (authority) + Rust shadow `zenodex-runtime-core::zusd` | Rust+Python shadow on public-testnet | yes | **Rust (public-testnet promoted)** | ✅ full single-vault `step` live-wired through `zusd-op`: mint/repay/deposit-sp/withdraw-sp/redeem/liquidate + oracle bootstrap/report/commit, epoch advance, and recovery-mode gating (`tcr_ok`/`in_recovery_mode`/`risky_ops_allowed`). ✅ golden trace, ✅ Python/Rust differential incl. >u128 amounts (bignum CDP-ratio math), ✅ semantic invariants, ✅ `_reference` unit suite, ✅ active-policy live-path tests, ✅ disaster-state rows and deterministic fuzz, ✅ Kani on BigInt-free scalar risk helpers for oracle freshness, base-rate decay, fee cap, and debt-floor guard. Event/effect payloads remain Python-derived after Rust/Python state-root and receipt agreement. Production remains Python authority. The multi-vault `step` (`zusd.py` L850+) stays Python-only. Full BigInt CDP ratio arithmetic and full single-vault `step` remain differential/property backed |
| Buyback accrual + burn floor — accrual in `fee_router` (`cum_buyburn`) ✅; burn **accounting rails** `src/core/burn_receipts.py` + Rust shadow `zenodex-runtime-core::burn_receipts` | Rust+Python shadow on public-testnet | yes | **Rust rails (public-testnet promoted)**; burn *execution* later | ✅ accrual conservation, ✅ burn rails (budget/floor, supply conservation, batch accumulator) shadowed + differential + semantic invariants, ✅ live authority wiring, ✅ disaster-state rows and deterministic fuzz, ✅ Kani on the running rail core for totality, accepted supply/budget/batch conservation, and non-vacuity. Receipt envelope (schema, canonical-JSON hash, lenient `int()` coercion) stays Python-owned before the authority-gated rail tuple. Burn **execution** still gated on TWAP / pool-depth / budget+slippage caps / wash-trade controls before any execution path |
| Batch clearing — `src/core/batch_clearing.py`, `settlement*.py` | Python orchestration; Rust+Python shadow for per-pool CPMM quotes on public-testnet | yes | Rust per-surface | ✅ per-pool CPMM settlement primitive live-wired and promoted on public-testnet (`quote_cpmm_swap_exact_in/out` → `cpmm-op`), including exact-out overdelivery-gap parity. ✅ golden traces, ✅ Python/Rust differential, ✅ semantic invariants, ✅ disaster-state rows and deterministic fuzz, ✅ Kani on the tractable initialization/fail-closed slice plus checked helper boundaries for invalid fees, zero denominators, small-domain fee-ceil boundedness, and small-domain exact-in reserve shape. Full live-domain symbolic exact-in/out `u128` swap arithmetic remains outside Kani; existing Tau/Lean/ESSO + property/differential evidence remain the current arithmetic assurance. Orchestration (multi-pool/CoW/ordering/liquidity) still Python-only; existing Tau/Lean batch obligations stay green |
| Perps risk math — `src/core/perp_v2/math.py` (+ Rust `perp_math`) | Rust+Python shadow on public-testnet | yes | **Rust math (public-testnet promoted)** | ✅ stateless slice live-wired for oracle freshness/move/clamp, margin, signed PnL, liquidation eligibility, and funding. ✅ signed `i128` + sign-symmetry invariants, static/4×500 differential, active-policy live-path tests, disaster-state rows, deterministic fuzz, malformed-output fail-closed checks, explicit signed safe-domain rejection (`abs(value) <= 1e18`, `abs(bps) <= 1e7`), and Kani on checked materializer-effect helper totality, bridge-domain classifiers, `abs_val` safety, oracle helper totality, sign classifiers, flat-position liquidation rejection, and non-vacuity. Full symbolic live-domain multiplication/division remains property/differential backed. Production remains Python authority. The stateful epoch lifecycle / clearinghouse settlement / insurance (`engine.py`, `updates.py`) is a separate E2 surface |
| Perps stateful — `advance_epoch` + `publish_clearing_price` + `settle_epoch` + `partial_liquidate` + `apply_funding_auto` settlement (`src/integration/perp_engine.py::_apply_isolated_advance_epoch`, `_apply_isolated_publish_clearing_price`, `_apply_isolated_settle_epoch`, `_apply_isolated_partial_liquidate`, `_apply_isolated_apply_funding_auto`) + account ops `deposit_collateral`/`withdraw_collateral`/`set_position`/`clear_breaker`) + `set_market_params` (+ Rust `perp_advance_epoch`, `perp_publish_clearing_price`, `perp_settle_epoch`, `perp_partial_liquidate`, `perp_funding_auto`, `perp_account_ops`, `perp_set_market_params`) | Rust+Python shadow on public-testnet | yes | **Rust (public-testnet promoted); all 10 isolated ops materialized** | ✅ Every `_ISOLATED_ACTION_HANDLERS` op has full Rust state/effect materialization, real-authority differentials, golden traces, Rust unit/proptests, fuzz/input-disaster coverage, live accepted-path tests, and funding-sink Lean/ESSO evidence. `public-testnet` now configures `perp_stateful: rust_authority_with_python_shadow`; Rust decides and commits isolated-op post-state/effects, with Python shadow disagreement fail-closed. The request carries pre-state integration facts for operator/sender/oracle/balance checks, including a `balance_available` deposit guard so Rust cannot accept deposits the Python shell would reject for insufficient wallet balance. Deposit/withdraw also debit/credit the Python wallet after Rust accepts. Production remains Python authority, and pure `rust_authority` remains blocked pending soak evidence and a future schema/sign-off. Kani now covers `advance_epoch` and `publish_clearing_price` totality, phase classifiers, accept shapes, and reachability; account-op domain/deposit/clear-breaker tractable slice; settle-epoch phase/account/flat-fast-path/global-guard helper classifiers; partial-liquidate parameter-boundary, non-open guard, concrete full-close shape, and reachability; set-market-params no-account overlay/clamp slice; and funding-auto bounded-sink arithmetic on the heap-free helpers used by the running Rust transition. Withdraw, set-position, settle per-account PnL/liquidation accumulation, partial-liquidate auto-fraction/liquidation arithmetic, and set-market account-safety paths stay differential/live-shadow covered. |
| Receipt generation — fee receipt (✅), `src/core/quote_receipts.py`, `src/core/burn_receipts.py` | Python (+ Rust fee-receipt) | yes | Rust per-surface | canonical receipt-hash parity (✅ for fee receipts); per-surface vectors |
| Legacy swap-fee split (3-way) — `src/core/fees.py` | Python | yes | stays Python (Tau/ESSO-covered) | already covered by `tokenomics_fee_split_32_v1.tau` + `fee_split_dust_carry_*` ESSO kernels; **unchanged** by this work |
| Transaction validation — `src/integration/validation.py`, `tau_gate.py`, `zusd_tau_gate.py` | Python | yes | Rust verification interface (Phase 6+) | golden traces incl. invalid-signature/insufficient-balance rejection; Tau-gate parity; differential. **Hashing slice done**: DEX intent auth message hash (`dex_intent_auth_message.py`) + burn-receipt body hash (`burn_receipts.py`) shadowed via the `domain_json_hash` op (`sha256(domain_sep(label,version)+canonical_json_bytes)`); cross-language vectors (static + 3×300 randomized) + chain-id/field sensitivity. The intent **shape-gate** and **BLS signature verification** remain Python-only (crypto is wrapped, never reimplemented) |
| Crypto (BLS12-381 verify) — `py-ecc` via integration | Python | yes | **wrapped, not rewritten** | established library behind a deterministic verification interface; *do not migrate crypto first* |

## Strict Deployment Oracle Posture

The `public-testnet` and `production-strict` deploy profiles now include an
explicit `oracle_policy`. Startup refuses to bind unless the corresponding
routing, zUSD, isolated-perps, and clearinghouse-perps Oracle adapter /
authorization environment flags are enabled. This is a deployment gate around
the trusted core: local-dev can keep replay/debug liveness, while strict
profiles fail closed before serving if critical Oracle evidence paths are not
active.

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

The 4-way protocol-fee split core now has its own finite ESSO model:
`src/kernels/dex/protocol_fee_router_4way_dust_core_v1.yaml`. It models
`buyburn/stakers/reserve/hosts` per-bucket remainders and folded dust, proves
the cumulative conservation invariant inductive with Z3+CVC5, and records
reproducible Rust codegen receipts under
`docs/runtime/receipts/protocol_fee_router_4way_dust_core_v1/`. The generated
crate is reproducible output under the ignored `generated/` tree; the live
runtime still calls the hand-written `fee_router.rs` and checks it with
Kani/proptest/Python-Rust differential evidence.
