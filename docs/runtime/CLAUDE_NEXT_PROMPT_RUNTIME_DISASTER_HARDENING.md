# Prompt For Claude 4.8: Runtime Disaster-State Hardening

Use effort max.

You are working on ZenoDEX in the `Autonomous Tau DEX` repository. Start from the latest `origin/main` after the runtime v5 state-root hardening branch has landed. Work in a clean branch. Do not use `/tmp` workspaces for final edits. Do not touch the GUI unless a runtime/API bug directly requires a narrow UI fixture update.

## Objective

Maximally reduce disaster states in the runtime codebase. Search for real bugs, fix them, and add replayable tests. Treat this as production hardening, not demo polishing.

The current trusted baseline includes:

- Python remains the authoritative runtime.
- Rust, OCaml, and SPARK are assurance sidecars unless a separate promotion gate explicitly passes.
- State root is v5 and must bind `fee_accumulator.dust` through the `FEE` section.
- Rust `state_root` must remain bit-exact with Python v5.
- `recompute_batch_v1/v2` full-state proofs must include `fee_accumulator`.
- `recompute_batch_v3/v4` support-root proofs must reject projected witnesses carrying unbound `fee_accumulator`, `vault`, or `oracle` state.
- Proof-mining submit flags must match the flags committed in the claim artifact.

Do not weaken any of those.

## Critical Surfaces To Audit

Audit and harden these surfaces in this order:

1. `src/integration/tau_testnet_dex_plugin.py`
   - stream selection ambiguity;
   - replay/idempotency across all operation streams;
   - no duplicate settlement IDs where a stream has a settlement identifier;
   - no faucet or fixture path that can affect protocol token balances outside explicit local fixture mode;
   - no legacy stream alias that changes semantics silently.

2. `src/integration/dex_engine.py` and proof verifier paths
   - pre/post-state commitment consistency;
   - settlement proof scheme dispatch;
   - proof witness decompression and reject-order behavior;
   - no unbound state inside projected proofs;
   - no acceptance of a settlement whose normalized commitment differs from the recomputed settlement.

3. `src/core/zusd.py`, `src/integration/zusd_monetary_bridge.py`, `src/integration/zusd_tau_wallet_api.py`
   - base-rate coupling and fee routing;
   - redemption and liquidation edge cases;
   - staking reward accounting and activation delay;
   - conservation of zUSD, AGRS collateral, protocol fees, and accumulator dust;
   - migration of legacy snapshots.

4. `src/integration/perp_engine.py`, `src/core/perp_v2/*`, and oracle adapter bridge paths
   - stale oracle acceptance;
   - split-brain oracle packets;
   - liquidation and insurance accounting;
   - epoch settlement idempotency;
   - cross-language Rust parity for stateless perps math must remain green.

5. Wallet/API/runtime boundaries
   - no private key, signed Tau payload, seed, backup share, or raw authority material in default API responses;
   - production deploy profiles must reject local fixture settlement, raw signer payload return, unsigned-sender bypass, demo APIs, and browser key generation unless explicitly in local-only test mode;
   - loopback-only assumptions must be documented and enforced at runtime where security depends on them.

6. Rust/OCaml/SPARK sidecars
   - keep Rust shadows synced with Python authority for every surface already ported;
   - add differential tests before adding new Rust code;
   - no `unsafe`;
   - do not promote Rust to authority in this PR;
   - SPARK/Ada artifacts may be advisory if `gnatprove` is unavailable, but say so honestly.

## Method

Use a disaster-state table before editing. For each audited surface define:

```text
DisasterClass := name, state variables, action sequence, expected reject, invariant, existing test coverage, gap.
```

Prioritize sequence-sensitive bugs:

- submit the same transaction twice;
- submit a copied proof against a later state;
- mutate a compressed witness;
- replay a settlement with a fresh nonce but same semantic ID;
- mix legacy and upstream stream keys;
- flip one authorization flag after claim generation;
- include valid-looking but unbound state in projected proofs;
- force stale oracle data through a batch;
- cross one module's balance accounting into another module's root.

Use deterministic tests first. Add property tests, stateful fuzz, or boundary atlas cases only when they target a named disaster class.

If you find a bug:

1. Write or extend a regression test that fails on current `main`.
2. Fix the smallest runtime surface that owns the bug.
3. Add defense-in-depth validation at the boundary closest to untrusted input.
4. Re-run focused tests.
5. Update the hardening report with the bug, impact, fix, and residual risk.

If you do not find a bug on a surface, leave a bounded negative receipt: what was tested, what was not tested, and what would falsify the claim.

## Required Deliverables

1. Code fixes for every confirmed bug.
2. Regression tests for every confirmed bug.
3. A refreshed `docs/runtime/FULL_RUNTIME_CRITICAL_SURFACE_HARDENING_REPORT.md`.
4. Updates to `docs/runtime/RUST_RUNTIME_MIGRATION_PLAN.md` and `docs/runtime/RUNTIME_TRUSTED_CORE_BOUNDARY.md` only if facts changed.
5. A short `docs/runtime/NEXT_RUNTIME_HARDENING_QUEUE.md` listing remaining surfaces in priority order.

## Required Verification

Run at minimum:

```bash
python3 -m pytest -q tests/state/test_state_root_determinism.py \
  tests/runtime/test_state_root_vectors.py \
  tests/runtime/test_state_root_injectivity_proof.py \
  tests/core/test_proof_mining_manager.py \
  tests/integration/test_recompute_batch_proof_verifier.py

python3 tools/runtime/state_root_injectivity.py --json

cd rust-runtime && cargo fmt --check && cargo test -q && cargo clippy -q -- -D warnings
```

Then run any focused tests for surfaces you changed. Do not claim full assurance from bounded tests. State exact coverage and exact remaining risk.

## Hard Rules

- Do not delete audit scaffolds just because they use internal state setup.
- Do not introduce mocks, simulations, demo APIs, or local fixture paths into production defaults.
- Do not weaken Tau, Lean, ESSO, Rust, OCaml, or SPARK artifacts to make tests pass.
- Do not alter GUI layout or styling in this branch.
- Do not rewrite broad runtime architecture unless a small fix cannot close a confirmed bug.
- Do not make claims like "zero days impossible" or "bug free." Use bounded evidence language.

## PR Summary Shape

Use this exact structure:

```text
Summary
- ...

Bugs Found
- ID, surface, impact, fix, regression test.

Evidence
- commands run and result.

Residual Risk
- ...
```
