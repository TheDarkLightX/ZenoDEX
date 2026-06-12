# Rust Authority Promotion Gate

This is the **operational gate** a runtime surface must pass before its
canonical authority moves from Python to Rust. It refines the abstract
12-point promotion criteria in `RUST_RUNTIME_MIGRATION_PLAN.md` (Phase 9/K)
into concrete, checkable evidence and wires them to the authority selector
(`src/runtime/authority.py`).

**No promotion by assertion.** A surface flips authority only when the
evidence below exists, CI enforces it, and a human records the decision in a
deployment profile's `promoted_surfaces` list. Building the selector and this
gate does *not* promote anything — the default everywhere remains
`python_authority`.

## Authority lifecycle

A surface advances through four modes (see `AuthorityMode`). Each arrow is
gated by accumulated evidence; each is reversible (see Rollback).

```
python_authority ──▶ rust_shadow ──▶ rust_authority_with_python_shadow ──▶ rust_authority
   (Python only)     (Py auth,        (Rust auth, Python re-checks         (Rust only;
                      Rust checks)      every call; disagreement            Python retired
                                        fails closed)                        for the surface)
```

| Transition | Gate |
|---|---|
| → `rust_shadow` | Evidence 1–5 below green; surface shadowed in `rust-runtime`; CI runs the differential. |
| → `rust_authority_with_python_shadow` | All evidence 1–7 green **including disaster-state (E4) and fuzz**; surface listed in profile `promoted_surfaces`; rollback rehearsed. |
| → `rust_authority` | Sustained green `rust_authority_with_python_shadow` across ≥1 release lane with zero disagreements; explicit human sign-off; future profile schema/validator update that explicitly admits pure Rust authority; docs updated to stop calling Rust a shadow for the surface. |

`rust_authority_with_python_shadow` is the **load-bearing** production mode for
a first promotion: Rust decides, Python verifies every transition, and any
divergence **fails closed** (the transition is rejected, not silently retried).

## Per-surface evidence requirements

A surface is *eligible* only when **all** of these exist and are green:

### 1. Golden traces (`tests/runtime/golden_traces/<surface>_*.json`)
- accepted cases
- rejected cases (one per stable reject code)
- malformed / out-of-domain inputs
- replay / idempotency cases
- boundary values (zero, max-domain, off-by-one at every threshold)

### 2. Differential tests (Python authority vs Rust shadow)
- static vectors + randomized **valid** inputs (≥400 cases)
- randomized **invalid** inputs (reject-code equality, not just accept/reject)
- stable reject codes (the code string, not only the boolean)

### 3. Property tests (run on **each** runtime independently)
- conservation (value in = value out + dust, per the surface's invariant)
- determinism (same input → same output, byte-for-byte canonical encoding)
- no mutation on reject (rejected tx leaves state and roots unchanged)
- idempotency / replay rejection
- state-root agreement (post-root and receipt hash match Python)

Independent invariants are mandatory because **cross-language equality proves
agreement, not correctness** (see `SEMANTIC_DRIFT_CONTROLS.md`).

### 4. Disaster-state tests (the criterion-9 gap; **blocking for authority**)
- copied-tx replay
- stale-snapshot replay
- duplicated settlement / proof IDs
- malformed canonical bytes
- overflow / underflow at the `u128` (and bignum, where applicable) boundary
- unauthorized state mutation
- Rust-timeout and malformed-Rust-output paths **fail closed** in the selector

### 5. CI gates (must be green on the PR that promotes)
- `cargo fmt --check`
- `cargo test`
- `cargo clippy -- -D warnings`
- focused `pytest` for the surface (conformance + invariants + disaster-state)
- golden-trace replay (`tools/runtime/rust_shadow_replay.py`)
- `python3 tools/check_deployment_profiles.py` (authority-policy facts valid)
- `python3 -m pytest tests/runtime/test_authority_selector.py`

### 6. Formal / semi-formal evidence (where available)
- Tau / ESSO / Lean obligations for the surface stay green
- SPARK/Ada is **advisory** unless `gnatprove` actually passes in CI
- the surface's hybrid-economics math invariants (where one exists) are
  referenced, not re-derived (e.g. fee-router dust conservation =
  `FeeDustCarryConservation`)

### 7. Rollback plan (rehearsed, not just documented)
- a deployment-profile edit reverts the surface to `python_authority` for one
  release window
- rollback **must not change state roots silently**: because promotion
  requires Python/Rust agreement, the canonical result (and its state-root
  contribution) is identical in `python_authority` and
  `rust_authority_with_python_shadow`; reverting is therefore root-preserving
  by construction (test: `test_state_root_unchanged_across_python_and_shadow…`)

## Disaster-state test catalog (per surface)

Until each shadowed surface has the applicable rows below, it is **not**
authority-eligible:

| Disaster | fee_router | replay_guard | balance | zusd | burn | cpmm | state_root | perp_math |
|---|---|---|---|---|---|---|---|---|
| copied-tx replay | upstream ✅ | ✅ | upstream ✅ | upstream ✅ | replay flag ✅ | n/a | n/a | n/a |
| stale snapshot | ✅ | ✅ | ✅ | ✅ | stateless ✅ | ✅ | ✅ | stateless ✅ |
| duplicate IDs | ✅ | ✅ | ✅ | n/a | n/a | n/a | ✅ | n/a |
| malformed bytes | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| overflow/underflow | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ⚠️ | ✅ |
| unauthorized mutation | ✅ | ✅ | ✅ | auth gates ✅ | n/a | n/a | n/a | n/a |
| no-op on reject | ✅ | ✅ | ✅ | ✅ | stateless ✅ | ✅ | n/a | stateless ✅ |

state_root rows are covered by `tests/runtime/test_state_root_disaster_state.py`.
⚠️ overflow/underflow: both bridge boundaries are tested, but the u32-nonce case
revealed SR-DRIFT-001, a nonce-bound semantic drift now fixed and locked by
regression tests. The state_root row remains eligible for the next promotion
gate only while those regressions stay green.

(Evidence 1–3 and 5–6 are already green for all 10 surfaces. See
`RUST_RUNTIME_MIGRATION_PLAN.md` Phase 9 table. Disaster-state (4) + fuzz are
what this gate adds.)

**Canonical primitives (stateless).** Not in the table above because the
stateful rows (copied-tx replay, stale snapshot, duplicate IDs, unauthorized
mutation, no-op-on-reject) do not apply to pure encoders. Its applicable rows —
malformed bytes, overflow/underflow, determinism/normalization, and purity —
are **✅ covered** by `tests/runtime/test_canonical_primitives_disaster_state.py`,
which also runs the cross-language disaster differential and the first
end-to-end authority-selector exercise (`rust_authority_with_python_shadow`:
agreement, root-stability, fail-closed on disagreement and on unavailable Rust).
`tests/runtime/test_canonical_primitives_fuzz_gate.py` adds the deterministic
fuzz gate. `config/deploy/public-testnet.yaml` is the first promoted lane:
`canonical` runs as `rust_authority_with_python_shadow` and is listed in
`promoted_surfaces`. The live path currently covers the burn-receipt
domain-separated canonical hash. `production-strict` remains `python_authority`;
pure `rust_authority` still requires a sustained shadow-checked release lane.

**State root v5.** `tests/runtime/test_state_root_disaster_state.py` covers
u128/u32 bridge boundaries, malformed bytes, duplicate decoded keys,
determinism, root sensitivity, and selector fail-closed rows. SR-DRIFT-001
(Rust accepted `last_nonce = 2^32` while Python rejected) is fixed and locked by
regression. `tests/runtime/test_state_root_fuzz_gate.py` adds deterministic
valid-state and invalid-state fuzz. `compute_state_root` is now live-wired to
the authority selector, with Rust deciding and Python shadow-checking under
`public-testnet`; rollback to Python is root-preserving by differential test.
`production-strict` remains `python_authority`.

**Replay / idempotency guard.** `tests/runtime/test_replay_guard_disaster_state.py`
covers copied transaction replay, stale replay from the same snapshot, duplicate
decoded state IDs at the Rust bridge, malformed sender bytes, nonce
over/underflow, unauthorized cross-sender mutation, no-op-on-reject, deterministic
fuzz, and selector fail-closed rows. `tests/runtime/test_replay_guard_live_path.py`
proves the real `admit` call uses the active authority policy and remains
root-preserving across `python_authority`, `rust_shadow`, and
`rust_authority_with_python_shadow`. `public-testnet` now runs `replay_guard` as
`rust_authority_with_python_shadow`; production remains `python_authority`.

**Balance accounting.** `tests/runtime/test_balance_kernel_disaster_state.py`
covers stale-snapshot determinism, duplicate decoded state IDs at the Rust
bridge, malformed pubkeys/assets, amount over/underflow, unauthorized
cross-asset mutation, no-op-on-reject, deterministic fuzz, and selector
fail-closed rows. Balance transitions intentionally do not carry nonce
semantics; copied transaction replay is blocked by the promoted `replay_guard`
upstream, and the balance disaster suite exercises that composed boundary.
`tests/runtime/test_balance_kernel_live_path.py` proves the real `credit` and
`transfer` calls use the active authority policy and remain root-preserving
across `python_authority`, `rust_shadow`, and
`rust_authority_with_python_shadow`. `public-testnet` now runs `balances` as
`rust_authority_with_python_shadow`; production remains `python_authority`.

**Fee router.** `tests/runtime/test_fee_router_disaster_state.py` covers
stale-snapshot determinism, duplicate decoded accumulator keys at the Rust
bridge, malformed bridge inputs, amount/split/domain over/underflow,
unauthorized cross-stream mutation, no-op-on-reject, deterministic fuzz, and
selector fail-closed rows. Fee-router transitions intentionally do not carry
nonce semantics; copied transaction replay is blocked by the promoted
`replay_guard` upstream, and the fee-router disaster suite exercises that
composed boundary. `tests/runtime/test_fee_router_live_path.py` proves the real
`route_fee` call uses the active authority policy and remains root-preserving
across `python_authority`, `rust_shadow`, and
`rust_authority_with_python_shadow`. `public-testnet` now runs `fee_router` as
`rust_authority_with_python_shadow`; production remains `python_authority`.

**Burn rails.** `tests/runtime/test_burn_receipts_disaster_state.py` covers
the replay/nullifier host flag, stateless deterministic replay, malformed rail
tuples, amount/supply/batch over/underflow, hash mismatch before rails,
deterministic fuzz, and selector fail-closed rows. The live verifier keeps the
receipt envelope, canonical-JSON hash, and legacy `int()` coercion in Python,
then routes the eleven integer rails through Rust under the active authority
policy. `tests/runtime/test_burn_receipts_live_path.py` proves
`verify_burn_receipt` uses the active authority policy and remains
root-preserving across `python_authority`, `rust_shadow`, and
`rust_authority_with_python_shadow`. `public-testnet` now runs `burn_receipts`
as `rust_authority_with_python_shadow`; production remains `python_authority`.

**CPMM per-pool settlement.** `tests/runtime/test_cpmm_settlement_disaster_state.py`
covers stale deterministic quote replay, malformed Rust output, boundary
rejections, no-op-on-reject, overdelivery-gap policy, deterministic fuzz, and
selector fail-closed rows. The promotion fixed a Rust semantic drift in exact-out:
the Rust path now enforces Python's default `200` bps overdelivery cap and emits
`amount_out_quote`, `overdelivery_gap`, and `gap_bps` for exact shadow comparison.
`tests/runtime/test_cpmm_settlement_live_path.py` proves
`quote_cpmm_swap_exact_in/out` use the active authority policy and remain
root-preserving across `python_authority`, `rust_shadow`, and
`rust_authority_with_python_shadow`. `public-testnet` now runs
`cpmm_settlement` as `rust_authority_with_python_shadow`; production remains
`python_authority`. Multi-pool ordering, CoW netting, and liquidity operations
remain Python-owned batch-clearing orchestration.

**zUSD single-vault.** `tests/runtime/test_zusd_disaster_state.py` covers
half-configured profile rejection, deterministic stale-state replay,
no-op-on-reject, malformed state documents, huge command rejection,
malformed Rust output, malformed rejected-output payloads, deterministic fuzz,
and selector fail-closed rows. The live path is `src/core/zusd.py::step`, which
routes the single-vault transition through `zusd-op` when the active surface
policy selects Rust authority. The bridge takes the full 32-field state object,
returns the post-state object plus receipt hash, and compares the Python
reference `_step_python` by state root, receipt hash, reject code, and post-state
fields. Event/effect payloads remain Python-derived after agreement, so API
callers keep the existing effect shape while the state transition is
shadow-checked Rust authority. `tests/runtime/test_zusd_live_path.py` proves
active-policy wiring for `rust_authority_with_python_shadow`, `rust_shadow`,
unavailable Rust, and injected disagreement. `public-testnet` now runs `zusd` as
`rust_authority_with_python_shadow`; production remains `python_authority`.
Multi-vault zUSD remains Python-owned.

**Perp stateless math (E1).** `tests/runtime/test_perp_math_disaster_state.py`
covers stale deterministic replay of pure math cases, malformed Rust output,
unknown or malformed operations, out-of-domain integer and bps inputs,
deterministic fuzz, and selector fail-closed rows. The live path is
`src/core/perp_v2/math.py`, which routes the nine pure E1 operations through
`perp-math` when the active surface policy selects Rust authority. Accepted Rust
outputs must carry exactly one of decimal-string `value` or boolean `flag`; any
shape drift rejects before the value is trusted. The promoted public-testnet
domain is intentionally signed and bounded (`abs(value) <= 1e18`,
`abs(bps) <= 1e7`). Python can evaluate larger integers, so those over-domain
cases become Rust/Python disagreement and fail closed under
`rust_authority_with_python_shadow`. `tests/runtime/test_perp_math_live_path.py`
proves active-policy wiring for `rust_authority_with_python_shadow`,
`rust_shadow`, unavailable Rust, and injected disagreement. `public-testnet` now
runs `perp_math` as `rust_authority_with_python_shadow`; production remains
`python_authority`. Stateful perps is the separate E2 surface below.

**Stateful isolated perps (E2).** All 10 isolated handlers are shadowed with
real-authority differentials. `tests/runtime/test_perp_disaster_state.py` adds the
**input-disaster + fuzz** evidence: a high-volume randomized differential per op
(≈1.7k cases) whose distributions straddle every bound (zero, max-domain,
off-by-one, over-domain), exercising malformed/out-of-domain, overflow/underflow,
and reject-path parity (rejected cases yield no Rust post-state and stable reject
codes). The same test also exercises the generic authority selector over the perps
shadow surface in `rust_authority_with_python_shadow` mode, including fail-closed
rows for injected disagreement, malformed Rust output, and unavailable Rust.
`public-testnet` now configures
`perp_stateful: rust_authority_with_python_shadow`: Rust decides accept/reject
and emits the full post-market state/effect document, while Python reruns as the
shadow checker. Any disagreement fails closed before copied transaction state is
committed. Pure `rust_authority` remains blocked by the strict-profile schema
until soak evidence and a future sign-off update.

## Promotion order (lowest risk first)

Per the migration plan and the math-side `RUNTIME_READINESS.md`:

1. canonical primitives — public-testnet shadow-authority lane active
2. state root v5 — public-testnet shadow-authority lane active
3. replay / idempotency guard — public-testnet shadow-authority lane active
4. balance accounting — public-testnet shadow-authority lane active
5. fee router — public-testnet shadow-authority lane active
6. zUSD single-vault — public-testnet shadow-authority lane active
7. burn rails — public-testnet shadow-authority lane active
8. CPMM per-pool primitive — public-testnet shadow-authority lane active
9. perp stateless math — public-testnet shadow-authority lane active

Next candidates: classify batch-clearing orchestration and multi-vault zUSD for
the trusted-core list before adding Rust authority work. Defer non-consensus
API/tooling surfaces.

**Update (E2 promoted).** The **stateful isolated-perps engine is now promoted
to public-testnet shadow-checked Rust authority**:
all 10 `_ISOLATED_ACTION_HANDLERS` ops (`advance_epoch`, `publish_clearing_price`,
`settle_epoch`, `apply_funding_auto`, `partial_liquidate`, `deposit_collateral`,
`withdraw_collateral`, `set_position`, `clear_breaker`, `set_market_params`) have
Rust shadows with real-authority differentials, golden traces, property/proptests,
and now the high-volume fuzz + input-disaster-state gate
(`tests/runtime/test_perp_disaster_state.py`). It now also has live
`rust_authority_with_python_shadow` wiring in `src/integration/perp_engine.py`
and `tests/runtime/test_perp_stateful_live_shadow.py`, plus the public-testnet
profile entry in `promoted_surfaces`. The promoted lane is still shadow-checked:
production remains Python authority, and pure Rust authority needs soak evidence
plus a future schema/sign-off update.

## How a promotion PR looks

1. Add the disaster-state tests (catalog above) for the surface.
2. Add fuzz evidence.
3. Set the surface to `rust_authority_with_python_shadow` in the target
   deployment profile **and** add it to that profile's `promoted_surfaces`.
   `check_deployment_profiles.py` rejects the half-configured case (rust
   authority without the `promoted_surfaces` entry) under `public-testnet` and
   `production-strict`. The current strict-profile schema admits
   `rust_authority_with_python_shadow` only; pure `rust_authority` needs a
   later schema/validator change after soak evidence and sign-off.
   `public-testnet` also rejects missing or downgraded trusted-core surfaces,
   so the current TCB set cannot regress back to `rust_shadow` silently.
4. Prove no state-root drift (the selector + agreement guarantee it; assert it).
5. Document residual risk in `RUST_AUTHORITY_MIGRATION_STATUS.md`.
6. Get explicit human sign-off (criterion 12).

## What this gate does NOT permit

- Promoting a surface with no disaster-state evidence.
- A blanket `default: rust_authority*` in a strict profile (rejected by
  `validate_authority_policy`).
- Promotion of a surface not present in `rust-runtime` (batch-clearing
  orchestration, multi-vault zUSD, intent shape-gate, BLS).
- Silent fallback: any Rust error/timeout/disagreement is a hard reject.
