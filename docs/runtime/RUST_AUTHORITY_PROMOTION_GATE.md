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
| → `rust_authority` | Sustained green `rust_authority_with_python_shadow` across ≥1 release lane with zero disagreements; explicit human sign-off; docs updated to stop calling Rust a shadow for the surface. |

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

Until each shadowed surface has the rows below, it is **not** authority-eligible
(this is the single outstanding gate for all 9 surfaces today — criterion 9):

| Disaster | fee_router | replay_guard | balance | zusd | burn | cpmm | state_root | perp_math |
|---|---|---|---|---|---|---|---|---|
| copied-tx replay | ☐ | ✅ | upstream ✅ | ☐ | ☐ | n/a | n/a | n/a |
| stale snapshot | ☐ | ✅ | ✅ | ☐ | ☐ | ☐ | ✅ | n/a |
| duplicate IDs | ☐ | ✅ | ✅ | ☐ | ☐ | ☐ | ✅ | n/a |
| malformed bytes | ☐ | ✅ | ✅ | ☐ | ☐ | ☐ | ✅ | ☐ |
| overflow/underflow | ☐ | ✅ | ✅ | ☐ | ☐ | ☐ | ⚠️ | ☐ |
| unauthorized mutation | ☐ | ✅ | ✅ | ☐ | ☐ | ☐ | n/a | n/a |
| no-op on reject | ☐ | ✅ | ✅ | ☐ | ☐ | ☐ | n/a | n/a |

state_root rows are covered by `tests/runtime/test_state_root_disaster_state.py`.
⚠️ overflow/underflow: both bridge boundaries are tested, but the u32-nonce case
revealed SR-DRIFT-001, a nonce-bound semantic drift now fixed and locked by
regression tests. The state_root row remains eligible for the next promotion
gate only while those regressions stay green.

(Evidence 1–3 and 5–6 are already green for all 9 surfaces — see
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

**Stateful isolated perps (E2).** All 10 isolated handlers are shadowed with
real-authority differentials. `tests/runtime/test_perp_disaster_state.py` adds the
**input-disaster + fuzz** evidence: a high-volume randomized differential per op
(≈1.7k cases) whose distributions straddle every bound (zero, max-domain,
off-by-one, over-domain), exercising malformed/out-of-domain, overflow/underflow,
and reject-path parity (rejected cases yield no Rust post-state and stable reject
codes). The same test also exercises the generic authority selector over the perps
shadow surface in `rust_authority_with_python_shadow` mode, including fail-closed
rows for injected disagreement, malformed Rust output, and unavailable Rust. This
is a test-only selector exercise. It does not wire perps into the live transaction
path and does not flip any deployment profile, so perps stays `python_authority`.

## Promotion order (lowest risk first)

Per the migration plan and the math-side `RUNTIME_READINESS.md`:

1. canonical primitives — public-testnet shadow-authority lane active
2. state root v5 — public-testnet shadow-authority lane active
3. replay / idempotency guard — public-testnet shadow-authority lane active
4. balance accounting — public-testnet shadow-authority lane active
5. fee router

Then, only after the above are promoted and stable: burn rails, CPMM per-pool
primitive, zUSD single-vault, perp stateless math. **Defer** batch-clearing
orchestration and multi-vault zUSD (not shadowed).

**Update (E2 done).** The **stateful isolated-perps engine is now fully shadowed**:
all 10 `_ISOLATED_ACTION_HANDLERS` ops (`advance_epoch`, `publish_clearing_price`,
`settle_epoch`, `apply_funding_auto`, `partial_liquidate`, `deposit_collateral`,
`withdraw_collateral`, `set_position`, `clear_breaker`, `set_market_params`) have
Rust shadows with real-authority differentials, golden traces, property/proptests,
and now the high-volume fuzz + input-disaster-state gate
(`tests/runtime/test_perp_disaster_state.py`). It joins the eligibility queue
behind the lower-risk surfaces above; what remains before it can flip to
`rust_authority_with_python_shadow` is live-path wiring, target-profile policy
updates, the CI gate, and human sign-off. The current selector coverage is
deliberately test-only and does not promote the surface.

## How a promotion PR looks

1. Add the disaster-state tests (catalog above) for the surface.
2. Add fuzz evidence.
3. Set the surface to `rust_authority_with_python_shadow` in the target
   deployment profile **and** add it to that profile's `promoted_surfaces`.
   `check_deployment_profiles.py` rejects the half-configured case (rust
   authority without the `promoted_surfaces` entry) under `public-testnet` and
   `production-strict`.
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
