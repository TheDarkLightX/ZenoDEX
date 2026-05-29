# Rust Authority Migration — Status

Living status for the Python→Rust authority promotion. Pairs with
`RUST_AUTHORITY_PROMOTION_GATE.md` (the gate) and
`RUST_RUNTIME_MIGRATION_PLAN.md` (the phase plan).

**As of this writing: no surface is Rust-authoritative. The default everywhere
is `python_authority`.** This PR adds the *machinery* (authority selector +
gate + deployment-facts wiring), not any promotion.

## Phase 0 inventory — promotion map

`Authority` = who computes the canonical result today. All surfaces are Python
authority with a Rust shadow. `1–8/10–11` = the migration plan's met criteria;
`DS` = disaster-state suite; `Fuzz` = fuzz/weird-machine evidence; `Promoted` =
human decision + profile entry.

| Surface | Authority | Rust shadow | 1–8,10–11 | DS (4) | Fuzz (9) | Promoted (12) |
|---|---|---|---|---|---|---|
| Canonical primitives | Python | `canonical.rs` | ✅ | ✅¹ | ☐ | ☐ |
| State root v5 | Python | `state_root.rs` | ✅ | ⚠️² | ☐ | ☐ (blocked) |
| Replay / idempotency guard | Python | `replay_guard.rs` | ✅ | ☐ | ☐ | ☐ |
| Balance accounting | Python | `balance_kernel.rs` | ✅ | ☐ | ☐ | ☐ |
| Fee router (4-way + dust) | Python | `fee_router.rs` | ✅ | ☐ | ☐ | ☐ |
| Burn rails | Python | `burn_receipts.rs` | ✅ | ☐ | ☐ | ☐ |
| CPMM per-pool settlement | Python | `cpmm_swap.rs` | ✅ | ☐ | ☐ | ☐ |
| zUSD single-vault | Python | `zusd.rs` | ✅ | ☐ | ☐ | ☐ |
| Perp stateless math (E1) | Python | `perp_math.rs` | ✅ | ☐ | ☐ | ☐ |

¹ Canonical primitives (stateless) have the applicable disaster-state rows
(malformed bytes, overflow/underflow, determinism, purity) covered by
`tests/runtime/test_canonical_primitives_disaster_state.py`, plus the
cross-language disaster differential and the first end-to-end authority-selector
exercise over a real surface. This is the first surface with complete
criterion-4 evidence. Fuzz (9) and the human decision (12) remain; no profile
flips it to Rust authority yet.

² State root v5 has a disaster-state suite
(`tests/runtime/test_state_root_disaster_state.py`) that documents the bridge
boundaries and the selector wiring — **but it surfaced a semantic drift that
blocks promotion** (see Findings → SR-DRIFT-001). The suite proves the selector
fails closed on the drift under `rust_authority_with_python_shadow` (safe), so
the *machinery* is sound; pure `rust_authority` for state_root must not be
enabled until the drift is resolved.

## Findings / blockers

### SR-DRIFT-001 — Rust state-root shadow does not enforce the u32 nonce bound `[BLOCKER for state_root]`

**What.** Python's `NonceTable` rejects `last_nonce >= 2^32` (a u32 bound). The
Rust `state_root` shadow accepts and encodes such a nonce. So on the adversarial
input `nonce = 2^32`, Python rejects and Rust accepts — a Python/Rust
divergence.

**Why it was missed.** The existing randomized differential
(`state_root_lib.random_states`) draws nonces from `randint(1, 0xFFFFFFFF)`, so
it never reaches `2^32`. The static corpus uses `0xFFFFFFFF` (max u32) but not
the overflow. Cross-language equality stayed green because the drift point is
outside the generated domain — the classic semantic-drift trap from
`SEMANTIC_DRIFT_CONTROLS.md`.

**Impact.** Under `rust_authority_with_python_shadow` the selector **fails
closed** on this input (verified by
`test_selector_fails_closed_on_nonce_drift`), so live safety holds in the
shadow-checked mode. But it blocks **pure `rust_authority`** for the state-root
surface: a no-shadow Rust authority would accept a nonce Python considers
invalid.

**Resolve before promoting state_root to pure rust_authority, by either:**
- enforcing the u32 nonce bound in the Rust nonce-section decoder (so Rust
  rejects `>= 2^32` like Python), **or**
- documenting in the gate that state_root assumes upstream nonce validation
  (the replay/nonce surface guarantees `nonce <= u32_max` before any state
  reaches the root), and adding a Rust-side debug assertion.

Either way, extend `random_states` to draw nonces up to `2^33` so the
differential covers the boundary going forward.

**Regression guard.** `test_nonce_u32_overflow_is_a_semantic_drift` asserts the
drift currently exists and will flip (with a clear message) the moment the Rust
decoder is fixed — at which point this finding is closed.

### Classification (Phase 0 step 3)

- **Promotable after evidence refresh + selector wiring** (lowest risk, do
  first): canonical primitives, state-root v5, replay guard, balance
  accounting, fee router.
- **Promotable after small missing tests**: burn rails, CPMM primitive, perp
  stateless math.
- **Not yet (promote after the small ones)**: zUSD single-vault.
- **Intentionally Python-only**: batch-clearing orchestration, stateful perps
  engine (E2), multi-vault zUSD, intent shape-gate, BLS verification (crypto is
  wrapped, never reimplemented).

### The one universal blocker

Evidence categories 1–3, 5–6 (golden traces, differential, property tests, CI,
formal) are **green for all 9 surfaces**. The outstanding gate for *every*
surface is **disaster-state (4) + fuzz (9)** plus the human promotion decision
(12). No surface can flip until its disaster-state row in the gate catalog is
filled.

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
  `config/deploy/{local-dev,public-testnet,production-strict}.yaml` (all safe
  all-Python); `validate_authority_policy` rejects a half-configured Rust
  authority (and a blanket Rust default) under `production-strict`;
  `tools/check_deployment_profiles.py` enforces it in CI.
- **Tests** — `tests/runtime/test_authority_selector.py` (27 cases): unsupported
  mode rejects; default is Python; each mode's semantics; disagreement fails
  closed; Rust-unavailable skipped in shadow but fatal under authority;
  state-root unchanged across `python_authority` and
  `rust_authority_with_python_shadow`; strict-profile half-configured rejection;
  real deploy profiles load + validate.
- **Gate** — `RUST_AUTHORITY_PROMOTION_GATE.md`.

Not in this PR (require explicit go-ahead — they change a surface's authority):

- Any surface promotion (Phase 3+).
- The disaster-state test catalog rows (criterion 4) and fuzz harness
  (criterion 9).
- Wiring `decide(...)` into the live transaction path of any surface.

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
