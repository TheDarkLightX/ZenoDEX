# Runtime Disaster Hardening Campaign — 2026-05-31

Hardening campaign (not a feature campaign) to reduce defect rate per LOC and
minimize disaster states across the consensus-critical runtime. Bounded-evidence
language throughout: **Confirmed** = reproduced locally; **Refuted** = the
hypothesized failure could not be reproduced and is rejected by an existing
invariant cited in the finding; **Documented** = verified but not patched, by
scope/risk/design; **Negative receipt** = a disaster hypothesis checked against
the cited guard and not reproduced (bounded by what was read/run, not a proof).

No deployment profile was flipped and no authority mode was promoted. No test,
formal gate, authority check, parser strictness, profile gate, or fail-closed
behavior was weakened. No "proved / safe / bug-free / disaster-free" claim is
made beyond the exact checker/test receipt that backs it.

## Baseline

| Item | Value |
|------|-------|
| Campaign branch | `claude/runtime-disaster-hardening-iso` |
| Base commit | `917d7b1e` = `origin/main` (`d1f9d493`) + 2 concurrent-agent commits (perp materializer dup-account + unknown-field rejects) |
| Worktree | isolated sibling worktree (see *Methodology*) |
| `tools/check_deployment_profiles.py` | local-dev / public-testnet / production-strict all **ok** |
| `pytest -q tests/runtime` | **610 passed** (pre-campaign) → **613 passed** (after +3 regression/lock tests) |
| Rust `cargo fmt --check` | clean |
| Rust `cargo test -q` | **243 passed** (73 core + 170 cli) at baseline; **244** after D-1's +1 |
| Rust `cargo clippy --all-targets -D warnings` | clean |
| `cargo kani --version` | cargo-kani 0.60.0 present |

### Pre-existing failures (recorded, NOT introduced or fixed here)

`pytest -q tests/integration/test_deployment_profiles.py` → **3 failed, 8 passed**
at the clean baseline (verified by reverting all campaign changes):

- `test_public_testnet_profile_rejects_unsafe_boundary_switches`
- `test_production_strict_profile_requires_upba_and_oracle_posture`
- `test_profile_rejects_proof_required_without_enabled_verifier`

These live in `src/integration/deployment_profiles.py`'s
`deployment_profile_violations()` / `validate_deployment_profile()` (the
**`DexEngineConfig`** posture validator — a *different* module from the
`deploy_profile.py` YAML loader touched by fix F-2). Per-test root cause
(reproduced this campaign; corrected after Codex review — they are **not** a
single uniform gate weakness):

- `test_public_testnet_profile_rejects_unsafe_boundary_switches` — **stale test
  (wording drift), NOT a gap.** The validator DOES flag legacy settlement, but as
  `"dex_config.settlement_validation must be strong_proof_carrying"`; the test
  asserts the old phrasing `"dex_config.settlement_validation must not be legacy"`.
- `test_production_strict_profile_requires_upba_and_oracle_posture` — **stale test
  (removed field), NOT a gap.** It errors with
  `TypeError: DexEngineConfig.__init__() got an unexpected keyword argument
  'require_uniform_batch_certificate'` at the `replace(...)` call, before the
  validator runs — it references a removed/renamed dataclass field.
- `test_profile_rejects_proof_required_without_enabled_verifier` — **the one
  likely-real gap.** `validate_deployment_profile(...)` returns `ok=True` where
  the test expects `ok=False` (a profile with `require_proof_when_present=True`
  and no enabled verifier should be rejected).

So 2 of 3 are stale tests (wording / removed field) and 1 is a likely-real
posture-gate gap. Left isolated per campaign rules. Queued P0 — see
`NEXT_RUNTIME_HARDENING_QUEUE.md`.

## Methodology

- **Concurrent-agent isolation.** The campaign's intended branch
  `claude/runtime-disaster-hardening` (in the `…runtime-authority` worktree) was
  being actively committed to by a concurrent agent (two hardening commits
  landed *during* baseline). To avoid racing commits / working-tree / cargo lock,
  this campaign ran in a dedicated isolated worktree on
  `claude/runtime-disaster-hardening-iso`, branched off the concurrent tip
  `917d7b1e` so the two sound prior commits (perp materializer dup-account +
  unknown-field rejects — independently parity-validated below) are inherited,
  not redone.
- **Audit → central confirmation.** Seven parallel read-only adversarial
  auditors (Surfaces A–G) produced candidate findings + negative receipts. Every
  candidate was then **re-confirmed or refuted centrally** by running its repro
  in this worktree (advisory search proposes; checkers decide). The audit ran
  against content-equivalent origin/main snapshots; all file:line references in
  fixes below were re-derived against this worktree.

## Surfaces audited

| Surface | Scope |
|---------|-------|
| A | runtime authority selector (`authority.py`, `canonical_authority.py`), Rust subprocess bridge (`rust_invoker.py`), perps live authority wiring (`perp_engine.py`), Rust CLI boundary (`main.rs`, `perp_isolated_op.rs`) |
| B | state root v5, canonical encoders, receipt hashes, settlement normalization (Python authority + Rust shadow + serde→JsonValue bridge) |
| C | replay guard, balance kernel, nonce tables, transfer/credit sites |
| D | fee router, burn rails, cpmm, zUSD, perps math, perps stateful (Rust↔Python parity) |
| E | batch clearing, settlement orchestration, routing, perps settlement sequencing |
| F | API server, deploy profiles, confidential/sealed-bid flags, profile gates |
| G | formal artifact ↔ running-code linkage (ESSO, Lean, Tau, TLA, Kani receipts) |

**Headline:** across the audited surfaces and the hypotheses listed below, the
runtime behaved fail-closed in every path examined (this is bounded by what was
read and reproduced, not a proof of total fail-closedness). The
authority bridge converts every Rust subprocess timeout / nonzero-exit /
malformed-output / disagreement into `AuthorityError` (hard reject) in every
Rust-authoritative mode; `RustUnavailable` is benign only in `rust_shadow`;
reject-is-no-op holds by construction (functional core builds a fresh post-state,
returned only on accept); per-asset conservation, nonce monotonicity, and the
fee/burn/cpmm/zusd/perp reject order + stable codes match Python; the
half-configured-authority profile gate is enforced at startup. 46 disaster
hypotheses were checked and found safe (see *Negative receipts*).

## Confirmed defects — fixed (one commit each)

### D-1 — `floor_div_i128(i128::MIN, -1)` panics on a consensus path *(low; fixed)*
- **Commit:** `runtime: make floor_div_i128 total on (i128::MIN, -1)`
- **Surface/file:** D — `rust-runtime/crates/zenodex-runtime-core/src/arith.rs:42`
- **Repro (red):** `cargo test -p zenodex-runtime-core floor_div_i128_min_over_neg_one_is_total` → `attempt to divide with overflow` at `arith.rs:46`. `numerator / denominator` (and `%`) overflow for `(i128::MIN, -1)`, guarded only against `denominator == 0` — a panic in debug / arithmetic trap in release, on a `pub` helper in a `#![forbid(unsafe_code)]` crate, violating the no-panic CBC rule.
- **Fix:** add a `denominator == -1` guard returning `numerator.checked_neg()` (None for `i128::MIN`); division by −1 is exact so flooring == negation; behavior unchanged for all other inputs.
- **Reachability:** currently unreachable (callers pass positive constants `PRICE_SCALE`/`BPS_SCALE`); same footgun class as the previously-fixed `abs_val(i128::MIN)`. Hardening, not an exploit.
- **Regression:** `floor_div_i128_min_over_neg_one_is_total` (panics before, passes after).

### F-2 — deploy-profile loader accepted unknown top-level keys (fail-open config) *(medium; fixed)*
- **Commit:** `runtime: reject unknown top-level keys in deploy profiles (fail closed)`
- **Surface/file:** F — `src/integration/deploy_profile.py:load_deploy_profile`
- **Repro (red):** a copy of `production-strict.yaml` with `runtime_policy` mistyped as `runtime_polciy` loaded cleanly (only `schema` was validated); `evaluate_deploy_profile_consistency` then resolved the block to `{}` and silently skipped the `local_only_routes_allowed` conflict check — well-formed profile yields 2 `local_only` conflicts, typo'd profile yields `()`. An operator who believed they had forbidden demo-token auth would have an unenforced policy. Confirmed neither the runtime gate nor the static validator caught the block-name typo.
- **Fix:** explicit `ALLOWED_PROFILE_KEYS` allowlist (the 13 documented top-level blocks); reject any unknown top-level key at load with a stable `ValueError`. Shipped profiles use only allowlisted keys → load behavior unchanged.
- **Regression:** `tests/runtime/test_deploy_profile_unknown_keys.py` (typo'd block + extra key rejected; shipped profiles still load). Full `tests/runtime` 614 passed.
- **Follow-up (commit `00a445e2`, Codex finding #4):** the static CI validator `tools/check_deployment_profiles.py` now reuses the same `ALLOWED_PROFILE_KEYS` allowlist and also rejects unknown top-level keys, so the CI gate cannot pass a profile the runtime loader would refuse.
- **Residual:** within-block key typos (e.g. `local_only_routes_alowed`) are not yet caught — see queue.

## Refutations / false positives

### E-1 — duplicate intent_id "silent mis-binding" — **REFUTED** *(test added)*
- **Commit:** `test: lock fail-closed behavior on duplicate intent_ids (audit E-1 refuted)`
- The audit hypothesized that `compute_settlement`'s re-lookup-by-id
  (`batch_clearing.py:200`) silently binds duplicate-id fills to the first match
  and emits divergent deltas. **Central reproduction refutes the dangerous
  outcome:** the `Settlement` dataclass invariant (`src/core/settlement.py:166`)
  rejects duplicate `included_intents` at construction, so `compute_settlement`
  **fails closed (raises)** rather than producing a mis-bound settlement. In the
  engine path duplicate ids are additionally rejected by
  `validate_settlement_strong` ("duplicate intent_id in input intents") and the
  UPBA validator; legacy mode is unreachable through `apply_ops` (returns
  "unsupported validation mode").
- **No production change** (a code patch would only have altered the reject
  string/timing and risked a consensus-observable reject-code change). A
  characterization test now pins the fail-closed property.

### Auditor-preempted false positives (refuted before reporting)
- **D-CANON-002 redux** (root omits a committed field): refuted — v5 root binds `fee_accumulator.dust`; the spot apply path carries `oracle/vault/perps` through unchanged (exactly the five components the root binds); the dust-excluding support root is only used by v3/v4 schemes that reject any projected snapshot with non-zero dust/vault/oracle.
- Rust state-root rejecting non-canonical pool assets / curve config / zero amounts / LP-mint-without-balance that Python accepts: refuted — Python domain constructors enforce the same invariants before `compute_state_root`; the Rust checks are defensive duplicates, unreachable in the live transition path.
- CPMM CLI bridge admitting `fee_bps > 10000`: refuted — the bridge guards `fee_bps <= BPS_DENOM` before constructing the pool.

## Confirmed defects — documented (not patched, with rationale)

Ranked; full detail + fix recommendations in `NEXT_RUNTIME_HARDENING_QUEUE.md`.

### C-1 — accept path admits non-canonical recipient/asset that `compute_state_root` rejects *(high class; currently latent)*
- **Confirmed:** `SwapIntent` admits `recipient='not_hex_recipient'` (ingress validates recipient only as a non-empty ≤512-char string, `operations.py:531`); `compute_state_root` then raises `pubkey must be a 0x-prefixed 48-byte hex string`. Case-variant pubkeys (`0xAB..` vs `0xab..`) are stored as two raw keys (logical double-count) and the root raises `duplicate decoded (pubkey, asset)`. So the set of *accepted* post-states is strictly larger than the set of *committable* (rootable) post-states — an "accept ⊄ committable" / validate-before-mutate violation.
- **Why latent now:** `dex_state_root_v0` (post-state root) has **no callers in `src/`** — no fully-wired block-producer computes the post-state root on accepted DEX states today. The proof-carrying and snapshot lanes that do compute roots fail closed (raise). A future block-producer would turn this into a liveness/DoS (one signed swap with a non-canonical recipient → un-committable block → stall).
- **Why not patched here:** the clean fix (canonicalize identifiers at ingress) entangles with the system's permissive "friendly-name pubkey" regime used pervasively in tests/local-dev (sender pubkeys are not hex-validated unless `require_intent_signatures=True`). Enforcing canonical hex globally would *weaken tests*, which the campaign forbids. The correct fix is to enforce canonical identifiers in the **consensus/ledger lane** (gate it on the same posture that already requires hex senders, or validate rootability per-tx when the block-producer is wired). **Queued P1.**

### C-2 — snapshot codec dedups by raw string while the root dedups by decoded bytes *(medium; latent)*
- **Confirmed:** `state_from_snapshot` (v4) loads two case-variant pubkey rows for one logical key (sum 150), then `compute_state_root` raises `duplicate decoded`. A loadable snapshot can be un-rootable / double-count one logical pubkey.
- **Why not patched:** same canonicalization-regime entanglement as C-1 (snapshot round-trip tests may use friendly names). Fix = canonicalize/dedup snapshot identifiers on the same key the root uses. **Queued P1** (with C-1).

### F-1 — runtime deploy-profile gate never enforces `allowed_routes` *(medium)*
- **Confirmed:** `allowed_routes` is referenced nowhere in `deploy_profile.py`/`api_server.py`; `enforced_policy_fields()` lists 3 fields and not routes. Under production-strict (`allowed_routes: [health, signed_intents, peer_check]`) any `*_API_ENABLED` flag is honored regardless of profile, so a privileged writer surface not in `allowed_routes` can be enabled.
- **Why not patched:** the fix changes startup acceptance (must pass enabled-surface facts + a profile→surface map and refuse unauthorized surfaces) — a real behavior change needing the surface→route mapping defined and care not to break existing deployments. **Queued P2.**

### G-1 — claim references `perp_epoch_isolated_v2` but the gate verifies only v3 *(medium; assurance integrity)*
- **Confirmed:** `docs/claims_registry.yaml` claim `smt:perp_epoch_isolated_v2:inductive_z3_cvc5` references `…v2.yaml` and runs `tools/run_perps_evidence.sh`, whose `verify-multi` targets only `…v3.yaml` (and 2p/3p/game-theory) — never v2. A separate well-evidenced v3 claim already exists. `check_claims_registry.py` only checks file existence, not that the cmd exercises the named file.
- **Why not patched:** the registry is a sensitive assurance artifact and the fix (repoint the v2 claim to v3 / retire it, and harden the validator to detect cmd↔file drift) should be reviewed in an assurance-focused change to avoid breaking the gate. **Queued P2.**

### Lower-severity / latent (documented; queued P3)
- **A-1** (perp_stateful Rust-authority reachable by profile config; no in-code block beyond the gate) — **downgraded**: `validate_authority_policy` *is* wired at startup (`api_server.py:6918`), the rust-authority materializer is the *intended* sign-off-gated promotion path, and `test_authority_selector.py:415` already pins public-testnet `perp_stateful`=`RUST_SHADOW`. Residual is doc clarity ("blocked regardless of mode" holds by gate+convention, not an extra in-code block). An in-code block was deliberately *not* added to avoid obstructing the designed promotion.
- **A-2** (canonical comparator `diff_results` ignores reject-code on dual-reject) — benign (canonical surface exposes no reject-code contract); **not patched** because making the comparator compare codes would require Python to emit Rust-identical canonical reject codes, else it would turn benign divergence into fail-closed breakage on the *live* canonical rust-authority surface.
- **A-3** (`perp_isolated_op.rs` `as_bool` accepts ints; `req_balance_available` saturates unparseable→`i128::MAX`) — latent (perp_stateful is `rust_shadow`; Python sends strict types). **Not patched** because tightening `as_bool` could break the *live* `rust_shadow` comparison if any bool-ish field is serialized as an int by `_build_isolated_op_request`; requires verifying the request serializer first.
- **B-1** (state-root amount domain: Python accepts `[2^128, 2^256)`, Rust rejects `amount_out_of_domain`) — already fail-closed via shadow disagreement; unreachable for real balances. Fix = a shared explicit `AMOUNT_MAX` on both sides.
- **F-3** (Python per-IP rate limiter keys on socket peer, ignores XFF → one global bucket behind the bundled nginx) — defense-in-depth; nginx does per-`binary_remote_addr` limiting at the edge.
- **G-2** (ESSO perp kernel verified in isolation, not differentially linked to the multi-account engine) — gap-tracking; honestly graded "bounded" in the derivatives matrix.
- **G-3** (Tau spec-mode fallback accepts scraped outputs regardless of exit code) — Tau gate disabled by default; primary REPL path is fail-closed. Fix = require `rc==0` (pending confirmation of tau's clean-EOF exit behavior).
- **G-4** (disaster-coverage "125 unreachable" headline backed by a git-ignored receipt) — info; doc is honest about bounded-tested status; optionally commit a hash-pinned summary.

## Negative receipts (46 — disaster hypotheses checked & found safe)

Selected (full list in the Phase 1 audit transcript):

- **Bridge fail-closed:** every Rust subprocess timeout / nonzero-exit / oversized / malformed-JSON path raises `RustInvocationError`→`AuthorityError` (reject) in Rust-authoritative modes; `_agree` treats `None` as disagreement; reject carries no post-state (invoker enforces accept⇒post present, reject⇒no post).
- **Reject-is-no-op:** spot engine (`apply_ops`/`dex.step`), perps engine (`apply_perp_ops`), and settlement apply all build a fresh post-state on copies and return it only on accept; mid-batch reject leaves the input state untouched (atomicity holds).
- **Replay/nonce:** nonce table canonicalizes pubkeys (casing cannot fork the frontier); strict-increasing + contiguous gate kills duplicates/gaps; u32 bound has no wrap path.
- **Conservation:** per-asset swap net delta is exactly zero including the protocol-fee carve-out; `fee_router` split conservation is Kani-proven on the running `split_with_dust`; burn rails preserve supply; funding nets to the sink (Kani two-account conservation) and insurance cannot go negative.
- **Parity (D):** fee_router 7-step / burn 4-rail / cpmm exact-out reserve-domain-before-gap / funding-auto reject orders + stable codes match Python; signed flooring matches Python `//` via `floor_div_i128`; zUSD MCR/CCR uses `num-bigint` so 1e30-bound products never overflow u128.
- **Canonicalization (B):** uvarint/encode_bytes/domain_sep/sha256/canonical_json are a byte-for-byte Python mirror; serde_json `arbitrary_precision` (no `preserve_order`) rejects floats/exponents and re-sorts keys exactly like `json.dumps(sort_keys=True)`; duplicate JSON keys collapse last-wins identically.
- **API/config (F):** startup auth gate fails closed (refuses sensitive APIs without auth, demo-token in production, in-memory sealed-bid in production); confidential attestation verifier fails closed on every subprocess error; signed `tau_tx_payload` is redacted by default; CORS default-deny (no `*`, no untrusted reflection); confidential status route exposes only hashes/posture.
- **Formal (G):** Lean `PerpEpochSafety` is honestly scoped (ℚ "math-only", not promoted to runtime); `batch_auction_settler_v1` is a genuine fresh fail-closed spec↔adapter↔ref linkage with hash + solver-version pinning; disputed derivatives claims are consistently fenced; Tau gate REPL path is fail-closed.

## Remaining risk by surface

| Surface | Residual risk | Status |
|---------|---------------|--------|
| A authority/bridge | A-2 (canonical reject-code, benign), A-3 (perp_isolated_op leniency, latent) | bridge fail-closed; documented |
| B state/canonical | B-1 (amount domain band `[2^128,2^256)`, fail-closed via disagreement, unreachable) | root coverage closed (D-CANON-002 refuted) |
| C ledger/replay | **C-1 / C-2** (accept ⊄ committable for non-canonical identifiers; latent until a block-producer roots post-state) | **P1** |
| D econ kernels | 3 known unreachable residuals (cpmm gap_bps>10000 code, zusd mcr/ccr>1e30 bound, +D-1 now fixed) | parity strong; D-1 fixed |
| E orchestration | no new defect found (E-1 refuted; double-settle / atomicity / sequence / advance-without-oracle hypotheses each reproduced as fail-closed — see negative receipts) | no new defect |
| F API/config | **F-1** (allowed_routes unenforced, P2), F-2 fixed, within-block typos (P3), F-3 (rate limiter, defense-in-depth) | partly fixed |
| G formal linkage | G-1 (claim/evidence drift, P2), G-2 (kernel not engine-linked), G-3 (Tau spec-mode rc), G-4 (receipt reproducibility) | honest posture; documented |
| pre-existing | **3 red posture-gate tests** in `deployment_profiles.py` (P0) | recorded, isolated |

## Disaster-state classification (per Surface G)

- **Checked (reproducible checker/test/solver receipt):** fee_router conservation (Kani), funding two-account conservation (Kani), CBC core kernels (Kani), `batch_auction_settler_v1` (fresh ESSO validate+shell-lint+verify-shell+verify-multi with hash+solver pinning), perp epoch v3 inductiveness (Z3+CVC5).
- **Bounded-tested / fuzzed:** the 125 disaster axes are `tested_discovery` (bounded replay under a 240s timeout), **not** proven; only a small `SURFACE_FORMAL_LANES` subset (e.g. quote_receipt_certificate, route_canonicalization) has ESSO+Lean+fuzz lanes.
- **Stale / drifted:** G-1 (v2 claim verified only as v3).
- **Unlinked (model ≠ runtime):** G-2 (single-account ESSO perp kernel not differentially linked to the multi-account `perp_engine`); Lean `PerpEpochSafety` is corroborative (ℚ) with no explicit ℚ↔ℤ bridge theorem for this surface.

## Evidence gates (final)

Receipt (captured at code-complete HEAD `00a445e2`):
`docs/runtime/receipts/runtime_disaster_hardening_2026_05_31/evidence_gates.txt`

| Gate | Result |
|------|--------|
| `tools/check_deployment_profiles.py` | ok (all 3 profiles) |
| `pytest -q tests/runtime` | 614 passed (610 baseline + 4 new regression/lock tests) |
| `pytest -q tests/core/test_batch_clearing.py` | 44 passed |
| `pytest -q tests/integration/test_deployment_profiles.py` | 3 **pre-existing** failures (2 stale tests + 1 likely-real gap), 8 passed |
| `cargo fmt --check` | clean |
| `cargo test -q` | 244 passed (73 core + 170 cli + 1 new) |
| `cargo clippy --all-targets -D warnings` | clean |

## Commits

| Commit | Kind | Summary |
|--------|------|---------|
| `c1cb1e2b` | code | D-1: make `floor_div_i128` total on `(i128::MIN, -1)` |
| `451e5e18` | code | F-2: reject unknown top-level keys in deploy profiles (fail closed) |
| `5dce013e` | test | E-1: lock fail-closed behavior on duplicate intent_ids (audit refuted) |
| `5e4ea9b4` | docs | this campaign report + queue additions + evidence receipt |
| `00a445e2` | code | mirror F-2 unknown-key rejection into the CI validator (Codex finding #4) |
| *(this commit)* | docs | Codex-review corrections: per-test characterization of the 3 pre-existing failures, receipt-scoped language, regenerated receipt @ `00a445e2` |

`00a445e2` is the **code-complete** HEAD; the evidence-gate receipt is captured
there and the only later commit is this documentation-correction commit.

(Built on `917d7b1e`, which already carried the concurrent agent's parity-validated
perp materializer dup-account + unknown-request-field rejects.)

## Continuation — P0 resolved (same day)

The campaign's top queue item (P0: the 3 pre-existing red tests in
`tests/integration/test_deployment_profiles.py`) was then taken to closure. With
the per-test root cause confirmed (above), each was resolved to its actual cause:

| Item | Resolution | Commit |
|------|-----------|--------|
| proof-required-without-verifier (**likely-real gap**) | Added the coherence check to `production_config_violations`: `require_proof_when_present=True` with `proof_config.enabled=False` is now rejected at config validation (`"require_proof_when_present requires proof_config.enabled"`). Rationale: the runtime already fails closed (`_verify_proof_if_present` → "proof required but verification disabled" rejects every intent-bearing tx), so such a config would start a node that rejects all traffic — a liveness failure better caught at startup. | `3f8d8bd3` |
| public-testnet boundary-switch test (**stale wording**) | Validator was correct; updated the assertion to the current message `"...must be strong_proof_carrying"`. | `467e5146` |
| production-strict UPBA/oracle test (**stale fields**) | Test passed removed kwargs (TypeError before validation); the rename *expanded* the strict-UPBA check from 3 to 5. Updated the config + assertions to current fields/messages. | `467e5146` |

`tests/integration/test_deployment_profiles.py` is now **11 passed** (was 3
failed / 8 passed at `d1f9d493`). The campaign branch has **no remaining red
tests**; the regenerated receipt (code-complete HEAD `467e5146`) records all gates
green. The proof-verifier coherence check is shipped-profile-safe (shipped
profiles leave `require_proof_when_present=False`).
