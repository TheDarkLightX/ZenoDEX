# Prompt For Claude 4.8: Rust Authority Promotion

Use effort max.

You are working on ZenoDEX in the `Autonomous Tau DEX` repository. Start from the latest `origin/main` after the runtime v5 state-root hardening branch has landed. Work in a clean branch. Do not use `/tmp` workspaces for final edits.

## Objective

Create the concrete migration path from the current Python-authority / Rust-shadow runtime to Rust-authority runtime, then implement the next safe slice.

## Current Baseline

- Python is still authority.
- Rust shadows several surfaces: fee router, replay guard, balances, zUSD single-vault, burn rails, CPMM primitive, state root v5, and perps stateless math.
- State root is v5 and includes `fee_accumulator.dust` via the `FEE` section.
- Rust must remain bit-exact with Python until a surface passes the promotion gate.
- No unsafe Rust.
- No authority promotion by assertion. Promotion requires evidence.

## Definition Of Rust Authority

For a promoted surface, Rust computes the canonical accept/reject result, state transition, receipt hash, and state-root contribution. Python becomes a compatibility shadow/test oracle for that surface until removed. A runtime flag must make the authority choice explicit and auditable.

## Phase 0: Inventory And Promotion Map

1. Read:
   - `docs/runtime/RUST_RUNTIME_MIGRATION_PLAN.md`
   - `docs/runtime/RUNTIME_TRUSTED_CORE_BOUNDARY.md`
   - `docs/runtime/GOLDEN_TRACE_FORMAT.md`
   - `src/state/state_root.py`
   - `rust-runtime/`
2. Produce a table:
   - surface
   - current authority
   - Rust coverage
   - missing parity tests
   - missing rejection tests
   - missing property tests
   - state-root/receipt impact
   - promotion risk
3. Split surfaces into:
   - promotable now after evidence refresh
   - promotable after small missing tests
   - not promotable yet
   - intentionally Python-only for now

## Phase 1: Promotion Gate Design

Create `docs/runtime/RUST_AUTHORITY_PROMOTION_GATE.md`.

For each surface, promotion requires:

1. Golden traces:
   - accepted cases
   - rejected cases
   - malformed inputs
   - replay/idempotency cases
   - boundary values
2. Differential tests:
   - Python authority vs Rust shadow
   - randomized valid inputs
   - randomized invalid inputs
   - stable reject codes
3. Property tests:
   - conservation
   - determinism
   - no mutation on reject
   - idempotency / replay rejection
   - state-root agreement
4. Disaster-state tests:
   - copied tx replay
   - stale snapshot replay
   - duplicated settlement/proof IDs
   - malformed canonical bytes
   - overflow / underflow
   - unauthorized state mutation
5. CI gates:
   - `cargo fmt`
   - `cargo test`
   - `cargo clippy -D warnings`
   - focused `pytest`
   - golden trace replay
6. Formal/semi-formal evidence where available:
   - Lean/Tau/ESSO stays green
   - SPARK/Ada is advisory unless `gnatprove` actually passes
7. Rollback plan:
   - a runtime config can revert authority to Python for one release window
   - rollback must not change state roots silently

## Phase 2: Authority Boundary Implementation

Implement an explicit authority selector.

Create or update a runtime boundary module with a shape like:

```text
AuthorityMode :=
  python_authority
  rust_shadow
  rust_authority_with_python_shadow
  rust_authority
```

Rules:

- Default remains `python_authority` unless this PR explicitly promotes a surface.
- `rust_authority_with_python_shadow` runs Rust first, then checks Python agrees.
- Any disagreement must fail closed.
- All authority decisions must be visible in receipts/logs.
- Authority mode must be part of deployment facts.

Add tests proving:

- unsupported authority mode rejects;
- production profile cannot enable half-configured Rust authority;
- disagreement between Rust and Python fails closed;
- state roots are unchanged across `python_authority` and `rust_authority_with_python_shadow` for promoted surfaces.

## Phase 3: Promote The Lowest-Risk Surfaces First

Start with these, in order:

1. canonical primitives
2. state root v5
3. replay/idempotency guard
4. balance accounting
5. fee router

For each surface:

1. Refresh golden traces.
2. Run Python/Rust differential tests.
3. Add missing disaster-state tests.
4. Add authority-mode wiring.
5. Enable `rust_authority_with_python_shadow` only for that surface.
6. Prove no state-root drift.
7. Document residual risk.

Do not promote zUSD, perps lifecycle, batch clearing orchestration, or full DEX apply path until the smaller surfaces are promoted and stable.

## Phase 4: State-Root v5 Authority

For state root specifically:

1. Confirm Python and Rust encode exactly:
   - `BAL`
   - `POL`
   - `LPB`
   - `LPA`
   - `NNC`
   - `FEE`
2. Add vectors where only `fee_accumulator.dust` changes.
3. Add vectors with max `u128` in Rust domain and Python rejection/out-of-domain behavior at the bridge.
4. Ensure docs say v5 everywhere.
5. Run:

```bash
python3 tools/runtime/state_root_injectivity.py --json
python3 -m pytest -q tests/state/test_state_root_determinism.py \
  tests/runtime/test_state_root_vectors.py \
  tests/runtime/test_state_root_injectivity_proof.py
cd rust-runtime && cargo test -q state_root && cargo clippy -q -- -D warnings
```

Promotion output:

- Rust may become authority for state-root computation only after these pass.

## Phase 5: Runtime Authority Wiring

After Phases 3 and 4:

1. Create a Rust runtime service/CLI boundary that accepts canonical JSON or binary canonical payloads.
2. Avoid unsafe FFI for the first authority release unless there is a measured reason.
3. Python calls Rust for promoted surfaces.
4. Python verifies Rust in shadow mode for at least one release lane.
5. Every Rust authority call returns:
   - accept/reject
   - stable reject code
   - receipt hash
   - post-state root or contribution
   - authority metadata
6. Add timeout behavior:
   - Rust timeout fails closed
   - malformed Rust output fails closed
   - Python/Rust disagreement fails closed in shadow mode

## Phase 6: CI And Release Gating

Add CI jobs:

1. Rust full:
   - `cargo fmt --check`
   - `cargo test`
   - `cargo clippy -- -D warnings`
2. Python/Rust parity:
   - all runtime differential tests
   - golden trace replay
3. Authority-mode tests:
   - `python_authority`
   - `rust_shadow`
   - `rust_authority_with_python_shadow`
4. Disaster-state suite:
   - replay
   - stale proof
   - malformed witness
   - duplicate IDs
   - overflow
   - no mutation on reject

Do not merge if any promoted surface lacks CI coverage.

## Phase 7: Next Surfaces After First Promotion

Only after small surfaces are green:

1. Promote burn accounting rails.
2. Promote CPMM per-pool settlement primitive.
3. Promote zUSD single-vault step.
4. Promote perps stateless math.
5. Defer full batch-clearing orchestration until:
   - multi-pool traces exist
   - ordering/CoW behavior is fully modeled
   - replay/disaster tests exist
   - state-root impact is proven stable

## Phase 8: Final Rust-Authority Criteria

The phrase "Rust is authority" is only allowed when:

1. All consensus-critical surfaces in the selected release profile run through Rust authority.
2. Python shadow agrees across a replay corpus.
3. Disaster-state tests pass.
4. Docker live-testnet smoke passes.
5. State roots match historical promoted vectors.
6. Deployment profile records Rust authority explicitly.
7. Rollback behavior is documented.
8. Docs no longer describe Rust as shadow for promoted surfaces.

## Required Deliverables

- `docs/runtime/RUST_AUTHORITY_PROMOTION_GATE.md`
- `docs/runtime/RUST_AUTHORITY_MIGRATION_STATUS.md`
- code for authority selector
- tests for authority selector
- first promoted surface implementation
- updated CI
- updated trusted boundary docs
- exact command log in PR summary

## Required Commands

```bash
python3 -m pytest -q tests/state/test_state_root_determinism.py \
  tests/runtime/test_state_root_vectors.py \
  tests/runtime/test_state_root_injectivity_proof.py \
  tests/core/test_proof_mining_manager.py \
  tests/integration/test_recompute_batch_proof_verifier.py

python3 tools/runtime/state_root_injectivity.py --json

cd rust-runtime && cargo fmt --check && cargo test -q && cargo clippy -q -- -D warnings
```

## PR Summary Shape

```text
Summary
- ...

Promoted Surfaces
- surface, old authority, new authority, evidence.

Evidence
- command and result.

Disaster States Covered
- ...

Residual Risk
- ...
```

## Stop Conditions

- If Python/Rust disagree, stop and report the minimal counterexample.
- If a state root changes unexpectedly, stop.
- If a surface lacks deterministic replay evidence, do not promote it.
- If authority mode is ambiguous, do not promote it.
