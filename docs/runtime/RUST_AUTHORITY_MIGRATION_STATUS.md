# Rust Authority Migration — Status

> **Superseded authority decision (2026-07-22):** Historical live-wiring claims
> below no longer authorize partial-CBC Rust surfaces. Public testnet Rust
> authority with Python shadow is limited to replay guard, balances, fee router,
> and burn receipts. Canonical, CPMM, perps, state root, and zUSD are Python
> authority until full public-transition evidence is complete. Production-
> strict remains all Python authority. Exact facts are recorded in
> `RUST_FCIS_BASELINE_20260722.json`.

Living status for the Python→Rust authority promotion. Pairs with
`RUST_AUTHORITY_PROMOTION_GATE.md` (the gate) and
`RUST_RUNTIME_MIGRATION_PLAN.md` (the phase plan). The proof-grade view is
tracked separately in `RUNTIME_CBC_CORE_STATUS.md`.

**As of this writing: canonical primitives, state root v5, replay/idempotency
guard, balance accounting, the fee router, zUSD single-vault, burn rails, CPMM
per-pool settlement, perp stateless math, and the stateful isolated-perps engine
are promoted only in the `public-testnet` profile to
`rust_authority_with_python_shadow`.** The
default mode remains `python_authority`, `production-strict` remains all-Python,
and no surface runs pure `rust_authority`.

## Authority mode glossary

The mode names are directional:

- `rust_authority_with_python_shadow`: Rust computes the canonical decision and
  result. Python reruns as the shadow checker, and disagreement fails closed.
- `rust_shadow`: Python computes and commits the canonical result. Rust reruns
  as the checker after Python materializes the transition; available Rust
  disagreement fails closed, but unavailable Rust is skipped for deployability.
- `rust_authority`: Rust computes and commits without a Python shadow. No
  deployment profile currently uses this mode; the current strict-profile
  schema rejects it until a future schema/validator update records soak evidence
  and sign-off.
- `python_authority`: Python computes and commits without a Rust requirement.

Accordingly, "Rust authority with Python shadow" and "Rust shadow" are opposite
authority directions.

## Phase 0 inventory — promotion map

`Authority` = who computes the canonical result today. Promoted public-testnet
surfaces run Rust authority with Python shadow; all other surfaces remain Python
authority with a Rust shadow. `1–8/10–11` = the migration plan's met criteria;
`DS` = disaster-state suite; `Fuzz` = fuzz/weird-machine evidence; `Promoted` =
human decision + profile entry.

| Surface | Authority | Rust shadow | 1–8,10–11 | DS (4) | Fuzz (9) | Promoted (12) |
|---|---|---|---|---|---|---|
| Canonical primitives | Rust authority + Python shadow on public-testnet | `canonical.rs` | ✅ | ✅¹ | ✅ | ✅¹ |
| State root v5 | Rust authority + Python shadow on public-testnet | `state_root.rs` | ✅ | ✅² | ✅ | ✅² |
| Replay / idempotency guard | Rust authority + Python shadow on public-testnet | `replay_guard.rs` | ✅ | ✅⁴ | ✅ | ✅⁴ |
| Balance accounting | Rust authority + Python shadow on public-testnet | `balance_kernel.rs` | ✅ | ✅⁵ | ✅ | ✅⁵ |
| Fee router (4-way + dust) | Rust authority + Python shadow on public-testnet | `fee_router.rs` | ✅ | ✅⁶ | ✅ | ✅⁶ |
| Burn rails | Rust authority + Python shadow on public-testnet | `burn_receipts.rs` | ✅ | ✅⁷ | ✅ | ✅⁷ |
| CPMM per-pool settlement | Rust authority + Python shadow on public-testnet | `cpmm_swap.rs` | ✅ | ✅⁸ | ✅ | ✅⁸ |
| zUSD single-vault | Rust authority + Python shadow on public-testnet | `zusd.rs` | ✅ | ✅¹⁰ | ✅ | ✅¹⁰ |
| Perp stateless math (E1) | Rust authority + Python shadow on public-testnet | `perp_math.rs` | ✅ | ✅⁹ | ✅ | ✅⁹ |
| Perp stateful (E2, all 10 ops) | Rust authority + Python shadow on public-testnet | `perp_*` (7 modules) | ✅ | ✅³ | ✅ | ✅³ |

¹ Canonical primitives (stateless) have the applicable disaster-state rows
(malformed bytes, overflow/underflow, determinism, purity) covered by
`tests/runtime/test_canonical_primitives_disaster_state.py`, plus the
cross-language disaster differential and the first end-to-end authority-selector
exercise over a real surface. `tests/runtime/test_canonical_primitives_fuzz_gate.py`
adds the deterministic fuzz gate for JSON, domain-separated hashes, and fixed
hex. `config/deploy/public-testnet.yaml` now lists `canonical` in
`promoted_surfaces` and sets it to `rust_authority_with_python_shadow`; rollback
to Python is root-preserving by differential test. The first live call site is
`src/core/burn_receipts.py::burn_receipt_hash`, which routes its
domain-separated body hash through the active authority policy. Production
remains `python_authority`. Kani now covers heap-free helper predicates for
domain-label bytes, ASCII hex digits, and selected LEB128 length boundaries.
Full `Vec`/`String` encoders, SHA-256, and canonical JSON remain
vector/fuzz/differential backed.

² State root v5 has a disaster-state suite
(`tests/runtime/test_state_root_disaster_state.py`) that documents the bridge
boundaries and the selector wiring. It surfaced SR-DRIFT-001, which has now been
fixed in Rust and locked by regression tests. `tests/runtime/test_state_root_fuzz_gate.py`
adds deterministic valid-state and invalid-state fuzz. `compute_state_root`
itself now routes through the active authority policy, using a private Python
implementation for shadow comparison so the Python shadow cannot recurse through
the selector. `config/deploy/public-testnet.yaml` lists `state_root` in
`promoted_surfaces`; production remains `python_authority`. Kani now covers the
scalar root-admission guards for fee bps, nonce bounds, LP duration metadata
presence, and pool-status code distinctness. Full section encoding, duplicate
detection, BigUint curve-param parsing, and SHA-256 remain
vector/fuzz/differential backed.

⁴ Replay/idempotency guard is now live-wired through
`src/core/replay_guard.py::admit`. The Rust bridge evaluates one transition from
explicit current state entries, so it does not replay history to reconstruct the
state. `tests/runtime/test_replay_guard_disaster_state.py` covers copied-tx
replay, stale snapshot replay, duplicate decoded state IDs, malformed sender
bytes, nonce over/underflow, unauthorized cross-sender mutation, no-op-on-reject,
deterministic fuzz, and selector fail-closed rows. `test_replay_guard_live_path.py`
checks active-policy wiring for `rust_authority_with_python_shadow`,
`rust_shadow`, unavailable Rust, and injected disagreement. `public-testnet`
lists `replay_guard` in `promoted_surfaces`; production remains
`python_authority`.

⁵ Balance accounting is now live-wired through `src/core/balance_kernel.py`
for both `credit` and `transfer`. The Rust bridge evaluates one transition from
explicit sparse `(pubkey, asset, amount)` entries. `tests/runtime/test_balance_kernel_disaster_state.py`
covers stale-snapshot determinism, duplicate decoded state IDs, malformed
pubkeys/assets, amount over/underflow, no-op-on-reject, cross-asset isolation,
deterministic fuzz, and selector fail-closed rows. Copied transaction replay is
owned by the now-promoted `replay_guard`; the balance test exercises that
composed boundary rather than pretending balances alone carry nonce semantics.
`test_balance_kernel_live_path.py` checks active-policy wiring for
`rust_authority_with_python_shadow`, `rust_shadow`, unavailable Rust, and
injected disagreement. `public-testnet` lists `balances` in
`promoted_surfaces`; production remains `python_authority`.

⁶ Fee router is now live-wired through `src/core/fee_router.py::route_fee`.
The Rust bridge evaluates one route from an explicit current accumulator
(`dust_by_stream`, `cum_buyburn`, `cum_stakers`, `cum_reserve`, `cum_hosts`),
so it does not replay prior fee history to reconstruct state.
`tests/runtime/test_fee_router_disaster_state.py` covers stale-snapshot
determinism, duplicate decoded accumulator keys, malformed bridge inputs,
amount/split/domain over/underflow, no-op-on-reject, cross-stream dust and
asset isolation, deterministic fuzz, and selector fail-closed rows. Copied
transaction replay is owned by the promoted `replay_guard`; the fee-router test
exercises that composed boundary. `test_fee_router_live_path.py` checks
active-policy wiring for `rust_authority_with_python_shadow`, `rust_shadow`,
unavailable Rust, and injected disagreement. `public-testnet` lists
`fee_router` in `promoted_surfaces`; production remains `python_authority`.
CBC evidence now includes Kani on the running split arithmetic for totality,
typed overflow rejection, dust exactness, and non-vacuity, plus a deterministic
one-quantum conservation test over all canonical domains and carried-dust
patterns. Full-range conservation remains covered by proptest and Python/Rust
parity. The exact 4-way dust-core model is now also captured in
`src/kernels/dex/protocol_fee_router_4way_dust_core_v1.yaml`: Z3+CVC5
`verify-multi` proves the cumulative conservation invariant inductive, and
ESSO `codegen-rust-kernel` emits a Rust kernel crate that passes its generated
Cargo tests. The generated crate itself remains reproducible output under the
ignored `generated/` tree; the tracked evidence is the model plus receipts under
`docs/runtime/receipts/protocol_fee_router_4way_dust_core_v1/`.
The broader runtime-core CBC Kani receipt is tracked at
`docs/runtime/receipts/cbc_runtime_core_kani_v1/`: 78 harnesses on the actual
runtime crate passed (arith, canonical helper predicates, state-root scalar
guards, zUSD scalar risk helpers, balance, replay, fee-router, burn rails, the
tractable CPMM initialization/fail-closed/helper slice, stateless perps
checked-effect helpers plus bridge-domain scalar guards, stateful perps
`advance_epoch`/`publish_clearing_price` contracts, account-op deposit and
clear-breaker contracts, settle-epoch helper classifiers, partial-liquidate
boundary/full-close contracts, set-market-params scalar/no-account contracts,
and funding-auto arithmetic).

⁷ Burn rails are now live-wired through
`src/core/burn_receipts.py::verify_burn_receipt` after the Python receipt
envelope and hash checks. The Rust bridge verifies the eleven integer rail
fields as a stateless tuple, while Python still owns schema validation,
canonical-JSON receipt hashing, and the existing lenient `int()` coercion.
`tests/runtime/test_burn_receipts_disaster_state.py` covers replay/nullifier
flag failure, stateless deterministic replay, malformed rail tuples,
amount/supply/batch over/underflow, hash mismatch before rails, deterministic
fuzz, and selector fail-closed rows. `test_burn_receipts_live_path.py` checks
active-policy wiring for `rust_authority_with_python_shadow`, `rust_shadow`,
unavailable Rust, and injected disagreement. `public-testnet` lists
`burn_receipts` in `promoted_surfaces`; production remains `python_authority`.
Kani now covers the running Rust rail core for totality, accepted
supply/budget/batch conservation, and non-vacuity.

⁸ CPMM per-pool settlement is now live-wired through
`src/kernels/python/settlement_swap_runtime_v1.py` for exact-in and exact-out
quotes. The Rust bridge evaluates a single initialized pool transition via
`cpmm-op`; trace replay still uses `settle-swap-trace`. The promotion fixed a
real semantic drift: Rust exact-out previously accepted overdelivery-gap cases
that Python rejects by policy. `zenodex-runtime-core::cpmm_swap` now enforces
the same default `200` bps overdelivery cap and reports the quote gap fields for
shadow comparison. `tests/runtime/test_cpmm_settlement_disaster_state.py` covers
stale deterministic quotes, malformed bridge output, no-op-on-reject,
overdelivery policy, slippage, amount/reserve boundaries, and deterministic
fuzz. `test_cpmm_settlement_live_path.py` checks active-policy wiring for
`rust_authority_with_python_shadow`, `rust_shadow`, unavailable Rust, injected
disagreement, and the allowed-overdelivery witness. `public-testnet` lists
`cpmm_settlement` in `promoted_surfaces`; production remains
`python_authority`. Kani now covers pool initialization, uninitialized-swap
fail-closed behavior, invalid-fee and zero-denominator helper behavior,
small-domain fee-ceil boundedness, small-domain exact-in reserve shape, and
non-vacuity on the running Rust module. Full live-domain symbolic exact-in/out
`u128` swap arithmetic remains outside the current Kani receipt; it remains
covered by Tau/ESSO/Lean plus property and Python/Rust differential evidence.
Batch-clearing orchestration remains Python-owned.

¹⁰ zUSD single-vault is now live-wired through `src/core/zusd.py::step` using
the `zusd-op` Rust bridge from an explicit 32-field state object. The promoted
surface is the single-vault transition only: oracle bootstrap/report/commit,
collateral deposit/withdraw, mint/repay, stability-pool deposit/withdraw,
redeem, liquidate, and epoch advance. The Python reference remains `_step_python`
for differential evidence, and the runtime returns the Python event/effects only
after Rust/Python state-root and receipt agreement. `tests/runtime/test_zusd_disaster_state.py`
covers half-configured profile rejection, deterministic replay from a stale
state, no-op-on-reject, malformed state documents, huge command rejection,
malformed Rust output, malformed rejected-output payloads, and deterministic
fuzz. `tests/runtime/test_zusd_live_path.py` checks active-policy wiring for
`rust_authority_with_python_shadow`, `rust_shadow`, unavailable Rust, and
injected disagreement. `public-testnet` lists `zusd` in `promoted_surfaces`;
production remains `python_authority`. Kani now covers BigInt-free scalar risk
helpers for oracle freshness, base-rate decay, fee capping, and debt-floor
admission. Full BigInt CDP ratio arithmetic and full single-vault `step` remain
property/differential backed. Multi-vault zUSD remains Python-owned.

⁹ Perp stateless math is now live-wired through `src/core/perp_v2/math.py` for
the nine pure E1 operations: oracle freshness, oracle move, settle-price clamp,
notional, maintenance margin, initial margin, signed PnL, liquidation
eligibility, and funding payment. The Rust bridge is `perp-math`; accepted
outputs are typed as decimal-string `value` or boolean `flag`, and malformed
Rust output fails closed under the selector. The promoted live domain is the
signed safe integer bridge (`abs(value) <= 1e18`, `abs(bps) <= 1e7`); Python is
unbounded, so over-domain values intentionally become Rust/Python disagreement
and fail closed in `rust_authority_with_python_shadow`.
`tests/runtime/test_perp_math_disaster_state.py` covers malformed bridge output,
out-of-domain values, stale deterministic stateless replay, deterministic fuzz,
and selector fail-closed rows. `tests/runtime/test_perp_math_live_path.py`
checks active-policy wiring for `rust_authority_with_python_shadow`,
`rust_shadow`, unavailable Rust, and injected disagreement. Existing
`test_perp_math_vectors.py` remains the cross-language vector suite. Kani now
covers checked-effect helper totality, bridge-domain classifier exactness,
`abs_val` safety, oracle helper totality, sign classifier exactness, and
flat-position liquidation rejection.
`public-testnet` lists `perp_math` in `promoted_surfaces`; production remains
`python_authority`. The stateful perps engine is tracked as the separate E2
surface below.

³ Perp stateful (E2): all 10 isolated handlers (`advance_epoch`,
`publish_clearing_price`, `settle_epoch`, `apply_funding_auto`,
`partial_liquidate`, `deposit_collateral`, `withdraw_collateral`, `set_position`,
`clear_breaker`, `set_market_params`) are shadowed across `perp_advance_epoch`,
`perp_publish_clearing_price`, `perp_settle_epoch`, `perp_funding_auto`,
`perp_partial_liquidate`, `perp_account_ops`, `perp_set_market_params`, each with
golden traces, a real-authority differential (driving `apply_perp_ops`), and Rust
unit/proptests. `tests/runtime/test_perp_disaster_state.py` adds the **fuzz**
evidence (≈1.7k randomized cases/run) and the **input-disaster** rows
(malformed/out-of-domain, overflow/underflow at every parameter bound,
reject-path parity). The live integration path now enables `perp_stateful:
rust_authority_with_python_shadow` in `public-testnet`: Rust decides
accept/reject from the pre-state, the Python shell commits the parsed Rust
post-market and effect, and the Python handler reruns as the shadow check.
Any Python/Rust disagreement fails closed before the copied transaction state is
committed. Unavailable Rust is fatal under this promoted public-testnet lane.
Kani now covers the global-only `advance_epoch` and `publish_clearing_price`
transition cores for totality, phase classifier exactness, accept shapes, and
reject/accept reachability. It also covers the account-op domain predicate,
deposit accept shape, clear-breaker accept shape, and account-op reachability
for the tractable deposit/clear slice. Set-market-params has Kani coverage for
empty no-op overlays, funding-rate cap clamp shape, and scalar reachability.

**Shadow materialization.** The materializer
`zenodex-runtime perp-isolated-op` emits the **full post-market
state** (`quote_asset` + every global key + every account) **plus the exact kernel
effect payload**, consuming explicit integration facts (`operator_ok`,
`sender_bound_ok`, `oracle_adapter_ok`, `oracle_authorization_ok`,
`all_positions_flat`, `balance_available`) without re-deriving crypto; a reject
never carries a post-state. The request boundary is authority-grade: it requires
the exact `schema` (`zenodex/perp_isolated_op/v1`) and `version` (1), requires the
`facts` object with every required key (a missing fact rejects as
`perp_isolated_op_missing_facts`, *not* as a semantic operator failure), and
rejects unknown op fields. All ten isolated ops are materialized: the
global ops **`advance_epoch`**, **`publish_clearing_price`**, and **`settle_epoch`**
(the first account-mutating op — per-account realized P&L / liquidation + global
fee/insurance accumulation); the four `account_op`-family ops
**`deposit_collateral`**, **`withdraw_collateral`**, **`set_position`**, and
**`clear_breaker`**; and **`partial_liquidate`** (penalty accumulation into
fee_pool/fee_income/insurance, `liquidated_this_step=true`); plus
**`apply_funding_auto`** (bounded-sink funding settlement, preserving untouched
account fields and emitting the normalized funding-summary effect); and
**`set_market_params`** (operator-only control-param overlay, funding-rate cap
clamp, account-safety checks, and params effect). Each emits its full
post-state and exact kernel effect (`EpochAdvanced` / `ClearingPricePublished` /
`EpochSettled` / `CollateralDeposited` / `CollateralWithdrawn` / `PositionSet` /
`BreakerCleared` / `PartialLiquidationApplied` / funding-summary effect).
`settle_epoch` and
`partial_liquidate` additionally fail closed on the oracle-adapter / authorization
facts, matching their Python handlers.

The Python bridge now snapshots those integration facts from the **pre-state**
shell before running the Python handler. Deposit requests carry the actual wallet
balance as `balance_available`, and the Rust materializer rejects
`deposit_collateral` with `insufficient balance for deposit` when that fact is
below the requested amount. Over-`i128` Python wallet balances are treated as
sufficient for any in-domain deposit amount, so this guard does not introduce a
new fail-closed drift on arbitrary-precision wallet balances. This closes a
promotion blocker where a future Rust authority path could otherwise accept a
deposit the Python shell would reject.

A strict Python-side parser now converts an accepted Rust `post` object back
into `PerpMarketState` and rejects malformed commit shapes (including duplicate
accounts). A live-shadow regression round-trips the actual Rust post-state for a
deposit and compares it with the Python-committed market. This parser is the
commit boundary used by the manual authority slices.

The authority-inversion slices are live for all ten isolated ops. The
public-testnet profile now uses the shadow-checked Rust-authority lane:
`rust_authority_with_python_shadow` fails closed on Python/Rust post-state
disagreement. The deposit/withdraw slices also commit the Python wallet-balance
debit/credit after Rust accepts.

Under `rust_shadow`, this is consumed as a check only: the bridge
(`rust_invoker.perp_isolated_op`) and `perp_engine` compare the **full** Rust
post-market **and the effect payload** vs Python (`_full_post_markets_agree` +
`_effects_agree`), failing closed on any state OR effect divergence. Manual
`rust_authority*` policies use the same materializer as the decision source.
Accordingly **`perp_stateful` is promoted to
`rust_authority_with_python_shadow` in `public-testnet` only**. Production-strict
remains all-Python, and pure `rust_authority` remains blocked by the strict
profile schema until soak evidence and a future sign-off update.
Kani 0.60.0 is available.
The bounded-sink
funding arithmetic now has exact Kani receipts on heap-free
helpers called by the running `perp_funding_auto` transition: sink mirror deltas,
per-account collateral/payment delta, two-account conservation, replay-predicate
parity, and non-vacuity. The Vec/String sorting wrapper remains covered by
differential/live-shadow tests rather than Kani. The same runtime-core Kani
receipt also covers balance and replay arithmetic contracts. No profile flips in
this change.

## Findings / blockers

### SR-DRIFT-001 — Rust state-root shadow did not enforce the u32 nonce bound `[FIXED]`

**What.** Python's `NonceTable` rejects `last_nonce >= 2^32` (a u32 bound). The
Rust `state_root` shadow accepted and encoded such a nonce. So on the adversarial
input `nonce = 2^32`, Python rejected and Rust accepted — a Python/Rust
divergence.

**Why it was missed.** The existing randomized differential
(`state_root_lib.random_states`) draws nonces from `randint(1, 0xFFFFFFFF)`, so
it never reaches `2^32`. The static corpus uses `0xFFFFFFFF` (max u32) but not
the overflow. Cross-language equality stayed green because the drift point is
outside the generated domain — the classic semantic-drift trap from
`SEMANTIC_DRIFT_CONTROLS.md`.

**Fix.** `zenodex-runtime-core::state_root` now rejects nonce entries above
`0xFFFFFFFF` with stable code `nonce_too_large`, matching Python's `NonceTable`
domain.

**Regression guard.** `test_nonce_u32_overflow_rejected_by_both` verifies Python
and Rust both reject `last_nonce = 2^32`, and
`test_selector_rust_authority_with_shadow_rejects_nonce_overflow_in_agreement`
verifies the selector receives an agreed rejection rather than a drift.

### Classification (Phase 0 step 3)

- **Promoted to public-testnet shadow-checked Rust authority**: canonical
  primitives, state root v5, replay/idempotency guard, balance accounting, fee
  router, zUSD single-vault, burn rails, CPMM per-pool settlement, perp
  stateless math, and the stateful isolated-perps engine (all 10 ops).
- **Intentionally Python-only**: batch-clearing orchestration, multi-vault zUSD,
  intent shape-gate, BLS verification (crypto is wrapped, never reimplemented).

### The one universal blocker

Evidence categories 1–3, 5–6 (golden traces, differential, property tests, CI,
formal) are **green for all 10 surfaces**. The outstanding gate for most
remaining surfaces is **disaster-state (4) + fuzz (9)** plus the human promotion
decision (12). Canonical primitives, state root v5, replay/idempotency guard,
balance accounting, the fee router, zUSD single-vault, burn rails, CPMM
per-pool settlement, and perp stateless math have passed those rows for the
public-testnet shadow-checked Rust lane.

## This PR (Phase 1 + 2)

Delivered:

- **Authority selector** — `src/runtime/authority.py`:
  - `AuthorityMode` = `python_authority | rust_shadow |
    rust_authority_with_python_shadow | rust_authority`, default
    `python_authority`.
  - `decide(...)` dispatches per mode and **fails closed** on disagreement,
    Rust error/timeout, malformed Rust output, or a missing authority engine.
  - Every decision carries audit metadata (`mode`, `decided_by`,
    `shadow_checked`, `shadow_agreed`) for receipts/logs.
- **Deployment-facts wiring** — `runtime_authority_policy` section added to
  `config/deploy/{local-dev,public-testnet,production-strict}.yaml`. Public
  testnet now promotes `canonical`, `state_root`, `replay_guard`, `balances`,
  `fee_router`, `zusd`, `burn_receipts`, `cpmm_settlement`, `perp_math`, and
  `perp_stateful`; production remains all-Python.
  `validate_authority_policy` rejects non-trusted-core authority surfaces,
  missing or downgraded public-testnet trusted-core surfaces, half-configured
  Rust authority, pure `rust_authority` under the current strict schema, and a
  blanket Rust default under `public-testnet` and `production-strict`;
  `tools/check_deployment_profiles.py` enforces it in CI.
- **Tests** — `tests/runtime/test_authority_selector.py`: unsupported
  mode rejects; default is Python; each mode's semantics; disagreement fails
  closed; Rust-unavailable skipped in shadow but fatal under authority;
  state-root unchanged across `python_authority` and
  `rust_authority_with_python_shadow`; strict-profile half-configured rejection;
  real deploy profiles load + validate.
- **Gate** — `RUST_AUTHORITY_PROMOTION_GATE.md`.

Not in this PR (require explicit go-ahead — they change another surface's authority):

- The disaster-state test catalog rows (criterion 4) and fuzz harness
  (criterion 9) for non-canonical surfaces.
- Wiring `decide(...)` into the live transaction path of any non-canonical surface.

## Preconditions / environment notes

- This work landed on branch `codex/rust-authority-promotion`, cut from a
  checkpoint of the in-progress runtime-hardening tree (the prompt assumed a
  clean `main`; the tree was a dirty feature branch, so it was checkpointed
  first).
- The checkout shows **concurrent activity from another session** (API-surface
  -profile enforcement, recompute-witness work). This PR's commit was made with
  **explicit file paths only** — it does not include or disturb the concurrent
  session's uncommitted changes.
- Pre-existing test failures unrelated to this work (present at the checkpoint):
  3 in `tests/integration/test_deployment_profiles.py` (DexEngineConfig
  UPBA/oracle/proof-verifier posture). Not introduced here.

## Pointers

- Gate: `RUST_AUTHORITY_PROMOTION_GATE.md`
- Plan: `RUST_RUNTIME_MIGRATION_PLAN.md`
- Boundary: `RUNTIME_TRUSTED_CORE_BOUNDARY.md`
- Drift discipline: `SEMANTIC_DRIFT_CONTROLS.md`
- Selector: `src/runtime/authority.py`
- Selector tests: `tests/runtime/test_authority_selector.py`
