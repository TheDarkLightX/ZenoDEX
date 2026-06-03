# Rust Runtime Parity — Audit Status (2026-06-03)

Point-in-time **verification** of the Python↔Rust runtime parity for the
consensus-critical surfaces (swap, zUSD, perps, replay guard, state root,
authority, golden traces). This is an audit artifact, not a promotion decision.

**`production_security_claim = false`.** No deployment profile was changed; the
default authority remains `python_authority`, `production-strict` remains
all-Python, and pure `rust_authority` remains blocked by the strict-profile
schema. Pairs with `RUST_AUTHORITY_MIGRATION_STATUS.md` (the living promotion
map) and `RUST_AUTHORITY_PROMOTION_GATE.md` (the gate).

## Scope and base

- Base commit: `91b64fd6` ("Wire live swap and NP perps proof surfaces"), branch
  cut as `claude/dex-audit-rust` off `main`.
- Toolchain present: `cargo 1.87.0`, `python3 3.12.3`. The Rust binary was built
  in release and the Python parity tests were pointed at it via
  `ZENODEX_RUNTIME_BIN`, so the parity-bearing tests **ran Rust** (no skips) —
  see "How this was run".

## Verification commands and results

```bash
# 1. Rust workspace (all 3 crates: core / cli / launcher)
export PATH="$HOME/.cargo/bin:$PATH"
export CARGO_TARGET_DIR=/tmp/cargo-target-rust-unit   # kept OUT of the worktree
cargo build --release --manifest-path rust-runtime/Cargo.toml
cargo test  --release --manifest-path rust-runtime/Cargo.toml
#   launcher: 7 passed | cli: 88 passed | core: 176 passed | doc-tests: 0
#   => 271 Rust tests, 0 failed
#   (cli was 84 before this audit; +4 new mark_price_source_kind tests)

# 2. Python runtime parity / golden-trace / replay-guard / state-root / authority
export ZENODEX_RUNTIME_BIN=/tmp/cargo-target-rust-unit/release/zenodex-runtime
export PYTHONPATH="$PWD:$PWD/tools/runtime"
python3 -m pytest -q tests/runtime/
#   => 803 passed, 0 failed (187s)

# 3. Named-path conformance/live-path/golden-trace ran Rust (0 skipped)
python3 -m pytest -q -rs \
  tests/runtime/test_cpmm_settlement_{conformance,live_path}.py \
  tests/runtime/test_zusd_live_path.py \
  tests/runtime/test_perp_math_live_path.py \
  tests/runtime/test_perp_stateful_live_shadow.py \
  tests/runtime/test_replay_guard_live_path.py \
  tests/runtime/test_state_root_disaster_state.py \
  tests/runtime/test_authority_selector.py \
  tests/runtime/test_balance_kernel_conformance.py \
  tests/runtime/test_fee_router_conformance.py \
  tests/runtime/test_burn_receipts_live_path.py
#   => 149 passed, 0 skipped
python3 -m pytest -q -k golden_trace tests/runtime/   # => 43 passed, 0 skipped
```

### Initial run found a real divergence (now fixed)

The first full `tests/runtime/` run was **769 passed / 34 failed**, with all 34
failures isolated to `tests/runtime/test_perp_stateful_live_shadow.py`
("python/rust disagreement"). Root cause and fix below. After the fix the suite
is **803 passed / 0 failed**.

## Per-surface parity verdict

`VERIFIED` = the Python↔Rust differential/live-shadow/golden-trace tests ran the
Rust binary and agreed bit-for-bit. Authority column is unchanged by this audit.

| Critical path | Rust kernel | Parity verdict | Evidence (tests/runtime) |
|---|---|---|---|
| CPMM swap settlement | `cpmm_swap.rs` | VERIFIED | `test_cpmm_settlement_{conformance,live_path,golden_trace,disaster_state,semantic_invariants}.py` |
| zUSD single-vault | `zusd.rs` | VERIFIED | `test_zusd_{vectors,live_path,disaster_state}.py` |
| Perp stateless math (E1) | `perp_math.rs` | VERIFIED | `test_perp_math_{vectors,live_path,disaster_state}.py` |
| Perp stateful (E2, 10 ops) | `perp_*` (7 modules) + `perp_isolated_op.rs` | VERIFIED **(after fix)** | `test_perp_stateful_live_shadow.py` (49), `test_perp_disaster_state.py`, golden traces |
| Replay / idempotency guard | `replay_guard.rs` | VERIFIED | `test_replay_guard_{conformance,live_path,disaster_state,golden_trace}.py` |
| State root v5 | `state_root.rs` | VERIFIED | `test_state_root_{vectors,disaster_state,fuzz_gate}.py` |
| Balance accounting | `balance_kernel.rs` | VERIFIED | `test_balance_kernel_{conformance,live_path,golden_trace,disaster_state}.py` |
| Fee router (4-way + dust) | `fee_router.rs` | VERIFIED | `test_fee_router_{conformance,live_path,disaster_state}.py` |
| Burn rails | `burn_receipts.rs` | VERIFIED | `test_burn_receipts_{conformance,live_path,golden_trace,disaster_state}.py` |
| Canonical primitives | `canonical.rs` | VERIFIED | `test_canonical_{primitives_vectors,live_path,disaster_state,fuzz_gate}.py` |
| Authority selector | `src/runtime/authority.py` + `rust_invoker.py` | VERIFIED | `test_authority_selector.py` |

All eleven rows ran with the Rust binary present; none skipped.

## Finding: SR-DRIFT-002 — perp materializer rejected `mark_price_source_kind` `[FIXED]`

**What.** Every stateful-perps materialized op (all 10) failed the
`rust_shadow` / `rust_authority_with_python_shadow` parity check with the Rust
materializer returning `perp_isolated_op_bad_request`.

**Why.** The Python perp authority schema `PERP_ISOLATED_GLOBAL_KEYS`
(`src/core/perps.py`) added the global field `mark_price_source_kind` (commit
`a0438a57`, "Add perps NP RISC0 proof surfaces"). It controls the mark-price
source and must be **derivatives-safe** (`== 1`, external median) whenever
`clearing_price_seen`. The Rust materializer
(`rust-runtime/crates/zenodex-runtime-cli/src/perp_isolated_op.rs`) was never
taught about the field: its `GLOBAL_KEYS` list had 25 entries and used an
**exact-key** request contract, so every request carrying the 26th key was
rejected as malformed. The randomized/golden corpora never exercised the live
materializer request shape against the current Python global schema, so the
drift stayed green until the live-shadow suite exercised it — the classic
semantic-drift trap from `SEMANTIC_DRIFT_CONTROLS.md` (the drift point was
outside the generated domain). This is the Rust analogue of SR-DRIFT-001
(state-root nonce bound). It was **pre-existing on `main`**, not introduced by
this audit.

**Fix.** Taught `perp_isolated_op.rs` the field, mirroring the Python authority:

- Added `mark_price_source_kind` to `GLOBAL_KEYS` (request parse + post emit). It
  is a shell-preserved global key, so the existing "clone global map, overwrite
  only changed keys" design preserves it verbatim for all 9 non-publish ops with
  no per-op code.
- `apply_funding_auto`: added the derivatives-safe gate at the exact Python gate
  position (right after `clearing_price_seen`), failing closed with the exact
  Python string `"cannot apply funding: mark_price_source_kind is not
  derivatives-safe"`.
- `publish_clearing_price`: sets the post `mark_price_source_kind` to external
  median (`1`), mirroring Python's `_split_kernel_state` force + op default (the
  materialized request never forwards a non-default source for publish).

**Regression guard.** 4 new Rust unit tests
(`global_state_without_mark_price_source_kind_rejects`,
`mark_price_source_kind_passes_through_advance_epoch`,
`publish_clearing_price_post_is_external_median_source`,
`apply_funding_auto_rejects_non_derivatives_safe_mark_price_source`) plus the now
fully-green `test_perp_stateful_live_shadow.py` (49 tests, all 10 ops). The fix
was cross-checked against the Python authority for the default-1, pass-through-0
(advance), funding-gate-0, and publish-force-1-from-0 branches; all agree.

The fix changes only the Rust shadow to match the Python authority — Python
behavior is unchanged, and no profile was flipped.

## GUI / backend critical paths still on Python (Rust equivalent exists)

These run **Python authority** in the default and `production-strict` profiles
even though a verified Rust kernel exists. Documented for visibility only — **no
flip is wired here.** The promotion lever is the per-surface authority mode in
the deploy profiles + the human gate, not this audit.

- Live call sites that route through the authority selector but default to
  `python_authority`: `src/core/{fee_router,balance_kernel,replay_guard,zusd,
  burn_receipts}.py`, `src/state/state_root.py`,
  `src/kernels/python/settlement_swap_runtime_v1.py`, `src/core/perp_v2/math.py`,
  `src/integration/perp_engine.py` (stateful perps), and the REST surface
  `src/integration/api_server.py`. In the default/production profiles every one
  of these computes and commits in Python; Rust is, at most, a `rust_shadow`
  checker — and in the default profile is not invoked at all.
- The **only** profile that flips these to `rust_authority_with_python_shadow`
  is `config/deploy/public-testnet.yaml` (the 10 promoted surfaces). The GUI
  (`tools/dex-ui/`) talks to `api_server.py`; its trades therefore execute on the
  Python authority in every non-public-testnet deployment.

## Intentionally Python-only (no Rust authority candidate)

Per `RUST_AUTHORITY_MIGRATION_STATUS.md`, these are out of scope for a Rust flip
and are correctly Python-only — not parity gaps:

- Batch-clearing orchestration (the per-pool CPMM math is the Rust surface; the
  auction orchestration is Python).
- Multi-vault zUSD (only the single-vault transition is shadowed).
- Intent shape-gate.
- BLS verification (crypto is wrapped, never reimplemented in Rust).

## How this was run

- `CARGO_TARGET_DIR` was set to `/tmp/cargo-target-rust-unit`, **outside** the
  worktree, so no `target/` dir or binary is ever staged or committed.
- Both the live invoker (`src/runtime/rust_invoker.py`) and the test shadow
  harness (`tools/runtime/rust_shadow_replay.py`) honor `ZENODEX_RUNTIME_BIN`
  first; pointing it at the prebuilt release binary made the parity tests use
  Rust without an in-worktree debug rebuild.

## Net

- Rust workspace: **271 tests, 0 failed**.
- Python runtime parity suite: **803 tests, 0 failed** (after the SR-DRIFT-002
  fix; 34 were failing before).
- All 11 critical paths: **parity VERIFIED** against the Rust binary.
- `production_security_claim = false`; no authority profile changed.
