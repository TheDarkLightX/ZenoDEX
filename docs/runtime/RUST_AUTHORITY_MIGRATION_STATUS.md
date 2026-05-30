# Rust Authority Migration — Status

Living status for the Python→Rust authority promotion. Pairs with
`RUST_AUTHORITY_PROMOTION_GATE.md` (the gate) and
`RUST_RUNTIME_MIGRATION_PLAN.md` (the phase plan).

**As of this writing: canonical primitives, state root v5, replay/idempotency
guard, balance accounting, the fee router, and burn rails are promoted only in the
`public-testnet` profile to `rust_authority_with_python_shadow`.** The
default mode remains `python_authority`, `production-strict` remains all-Python,
and no surface runs pure `rust_authority`.

## Phase 0 inventory — promotion map

`Authority` = who computes the canonical result today. Promoted public-testnet
surfaces run Rust authority with Python shadow; all other surfaces remain Python
authority with a Rust shadow. `1–8/10–11` = the migration plan's met criteria;
`DS` = disaster-state suite; `Fuzz` = fuzz/weird-machine evidence; `Promoted` =
human decision + profile entry.

| Surface | Authority | Rust shadow | 1–8,10–11 | DS (4) | Fuzz (9) | Promoted (12) |
|---|---|---|---|---|---|---|
| Canonical primitives | Rust+Python shadow on public-testnet | `canonical.rs` | ✅ | ✅¹ | ✅ | ✅¹ |
| State root v5 | Rust+Python shadow on public-testnet | `state_root.rs` | ✅ | ✅² | ✅ | ✅² |
| Replay / idempotency guard | Rust+Python shadow on public-testnet | `replay_guard.rs` | ✅ | ✅⁴ | ✅ | ✅⁴ |
| Balance accounting | Rust+Python shadow on public-testnet | `balance_kernel.rs` | ✅ | ✅⁵ | ✅ | ✅⁵ |
| Fee router (4-way + dust) | Rust+Python shadow on public-testnet | `fee_router.rs` | ✅ | ✅⁶ | ✅ | ✅⁶ |
| Burn rails | Rust+Python shadow on public-testnet | `burn_receipts.rs` | ✅ | ✅⁷ | ✅ | ✅⁷ |
| CPMM per-pool settlement | Python | `cpmm_swap.rs` | ✅ | ☐ | ☐ | ☐ |
| zUSD single-vault | Python | `zusd.rs` | ✅ | ☐ | ☐ | ☐ |
| Perp stateless math (E1) | Python | `perp_math.rs` | ✅ | ☐ | ☐ | ☐ |
| Perp stateful (E2, all 10 ops) | Python | `perp_*` (7 modules) | ✅ | ⚠️³ | ✅ | ☐ |

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
remains `python_authority`.

² State root v5 has a disaster-state suite
(`tests/runtime/test_state_root_disaster_state.py`) that documents the bridge
boundaries and the selector wiring. It surfaced SR-DRIFT-001, which has now been
fixed in Rust and locked by regression tests. `tests/runtime/test_state_root_fuzz_gate.py`
adds deterministic valid-state and invalid-state fuzz. `compute_state_root`
itself now routes through the active authority policy, using a private Python
implementation for shadow comparison so the Python shadow cannot recurse through
the selector. `config/deploy/public-testnet.yaml` lists `state_root` in
`promoted_surfaces`; production remains `python_authority`.

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
reject-path parity). It also exercises the generic authority selector in
`rust_authority_with_python_shadow` mode against each perps shadow and fails closed
on injected disagreement, malformed Rust output, and unavailable Rust. This is
test-only selector coverage: today each perp shadow is still a CLI checker, not a
live decision path. Until live wiring + CI + human sign-off exist, perps stays
`python_authority`. No profile flips it.

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
  router, burn rails.
- **Promotable after small missing tests**: CPMM primitive, perp stateless math.
- **Not yet (promote after the small ones)**: zUSD single-vault.
- **Shadowed (E2 complete), awaiting live-path wiring**: the **stateful
  isolated-perps engine (all 10 ops)**. Evidence 1–3 + fuzz + input-disaster are
  green, and the generic selector fail-closed rows are exercised in tests. Stays
  `python_authority` until profile policy, live-path wiring, CI, and human sign-off
  are complete.
- **Intentionally Python-only**: batch-clearing orchestration, multi-vault zUSD,
  intent shape-gate, BLS verification (crypto is wrapped, never reimplemented).

### The one universal blocker

Evidence categories 1–3, 5–6 (golden traces, differential, property tests, CI,
formal) are **green for all 9 surfaces**. The outstanding gate for most
remaining surfaces is **disaster-state (4) + fuzz (9)** plus the human promotion
decision (12). Canonical primitives, state root v5, replay/idempotency guard,
and balance accounting have passed those rows for the public-testnet
shadow-checked Rust lane.

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
  testnet now promotes `canonical`, `state_root`, `replay_guard`, and
  `balances`;
  production remains all-Python.
  `validate_authority_policy` rejects a half-configured Rust authority (and a
  blanket Rust default) under `public-testnet` and `production-strict`;
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
