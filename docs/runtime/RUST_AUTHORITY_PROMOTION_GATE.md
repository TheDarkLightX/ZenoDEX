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
| copied-tx replay | ☐ | ☐ | ☐ | ☐ | ☐ | n/a | n/a | n/a |
| stale snapshot | ☐ | ☐ | ☐ | ☐ | ☐ | ☐ | ✅ | n/a |
| duplicate IDs | ☐ | ☐ | ☐ | ☐ | ☐ | ☐ | ✅ | n/a |
| malformed bytes | ☐ | ☐ | ☐ | ☐ | ☐ | ☐ | ✅ | ☐ |
| overflow/underflow | ☐ | ☐ | ☐ | ☐ | ☐ | ☐ | ⚠️ | ☐ |
| unauthorized mutation | ☐ | ☐ | ☐ | ☐ | ☐ | ☐ | n/a | n/a |
| no-op on reject | ☐ | ☐ | ☐ | ☐ | ☐ | ☐ | n/a | n/a |

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
Canonical primitives are therefore the first surface with complete criterion-4
evidence; fuzz (criterion 9) and the human decision (criterion 12) remain.

## Promotion order (lowest risk first)

Per the migration plan and the math-side `RUNTIME_READINESS.md`:

1. canonical primitives
2. state root v5
3. replay / idempotency guard
4. balance accounting
5. fee router

Then, only after the above are promoted and stable: burn rails, CPMM per-pool
primitive, zUSD single-vault, perp stateless math. **Defer** batch-clearing
orchestration, the stateful perps engine, and multi-vault zUSD (not shadowed).

## How a promotion PR looks

1. Add the disaster-state tests (catalog above) for the surface.
2. Add fuzz evidence.
3. Set the surface to `rust_authority_with_python_shadow` in the target
   deployment profile **and** add it to that profile's `promoted_surfaces`.
   `check_deployment_profiles.py` rejects the half-configured case (rust
   authority without the `promoted_surfaces` entry) under `production-strict`.
4. Prove no state-root drift (the selector + agreement guarantee it; assert it).
5. Document residual risk in `RUST_AUTHORITY_MIGRATION_STATUS.md`.
6. Get explicit human sign-off (criterion 12).

## What this gate does NOT permit

- Promoting a surface with no disaster-state evidence.
- A blanket `default: rust_authority*` in a strict profile (rejected by
  `validate_authority_policy`).
- Promotion of a surface not present in `rust-runtime` (batch-clearing
  orchestration, stateful perps, multi-vault zUSD, intent shape-gate, BLS).
- Silent fallback: any Rust error/timeout/disagreement is a hard reject.
