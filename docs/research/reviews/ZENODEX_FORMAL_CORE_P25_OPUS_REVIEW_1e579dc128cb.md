# Opus Independent Review — Candidate C8-p8 (PR #532 incorporation)

- **Subject S25** `a18699202381f1766e85b986b730307fad5c1938`
- **Artifact P25** `1e579dc128cb4d7a5c909fc45d3e905165e4aca9`
- **Branch** `codex/formal-core-fable-20260901`
- **Review worktree** `/tmp/zenodex-formal-core-opus-c8p8` (detached at P25)
- **Authority asserted by this review: NONE.** The claim ceiling did not move and this
  review does not move it.

## Grade: A-

Zero P1, zero P2, three P3. The core of this candidate — totalising the post-state
row-ceiling boundary into a closed typed reject in both languages — is correct,
complete on its stated surface, two-sidedly pinned, and mutation-verified by me in
both languages. The supersession of the two deleted tests is honest and loses no
coverage. The envelope is exact. The A- rather than A reflects one confirmed
*surviving* mutant inside a class the new THV1 packet claims to kill (NEW-13), plus a
formatting regression that no gate catches (NEW-14).

---

## Verdict table

| # | Item | Verdict |
|---|------|---------|
| 1 | TOTALIZATION (P21 NEW-6 lineage repaired) | **CLOSED** |
| 2 | NEW-12 (duplicate-declaration masking) | **CLOSED** |
| 3 | CRATE-WIDE PARITY | **PARTIAL** (NEW-13) |
| 4 | SUPERSESSION HONESTY | **CLOSED** |
| 5 | ENVELOPE | **CLOSED** |

---

## Replays (all green)

| Gate | Result |
|------|--------|
| Checker, NOT_RUN mode | exit 0, `ok=true`, `packet_admitted=true`, 0 errors, 0 drift, stderr empty |
| Checker, `--replay` | exit 0, **EXECUTED_PASS, 28 runs**, every run `exit_code 0`, 0 errors, 0 drift |
| `cargo test --all-targets` | **526 passed**, 53 binaries, 0 failed |
| `cargo clippy --all-targets -- -D warnings` | clean |
| `cargo fmt --check` | **exit 1** — see NEW-14 |
| Pinned hygiene node surface (137 node ids) | **158 passed** |
| Module suites + compiled Rust replay (9 files) | **514 passed** (263s) |
| Lean gate 1 `GlobalClaimantCustodyRelationV1.lean` | exit 0, stdout/stderr empty (run alone) |
| Lean gate 2 `GlobalAccountingAllocationCertificateV1.lean` | exit 0, stdout/stderr empty (run alone, after gate 1 exited) |
| `check_test_hygiene_v1.py --base-ref 5c4b5232…` | `ok=true`, 13/13 critical paths covered, 3 packets selected |

Lean gates were run strictly serially; no concurrency, no SIGBUS.

---

## 1. TOTALIZATION — CLOSED

Both transitions return `POST_STATE_RESOURCE_BOUND_EXCEEDED` from `_post_balances` /
`post_balances` before any post-state construction, and both `_reject` helpers emit
`pre_state_root == post_state_root` with `GlobalEconomicEffectPlanV1.empty()`.

**The old uncaught path is gone in both languages, and the new guard is exactly what
removed it.** I did not take this on the tests' word — I removed the guards:

- **M5** (delete the Python guard from both modules) → the two past-ceiling tests fail
  with the *exact* pre-repair error: `ValueError: managed asset lifecycle balances
  exceeds its 4096-item ceiling`.
- **M6** (delete the Rust guard from both modules) → the two past-ceiling Rust tests
  fail with the *exact* pre-repair error:
  `InvalidBounds("managed asset balance rows")`.

So the P21 NEW-6 lineage is repaired at the mechanism, not papered over.

**The suite is non-vacuous in both directions.** M4 (`>` → `>=`, an over-strict
off-by-one) is killed by the two *exact-ceiling accept* cases; M5 (guard deleted, an
under-strict mutant) is killed by the two *past-ceiling reject* cases. Complementary
halves — the boundary is pinned from both sides, which is strictly stronger than the
raise-pinning tests it replaces.

**The totalised surface is complete, not partial.** The docstrings claim only the
balance-row ceiling; I checked whether that is the whole story. `AssetTransferStateV1`
bounds three collections (policies 256, balances 4096, supplies 256) and
`ManagedAssetLifecycleStateV1` likewise. In `_accept_transfer` the post-state carries
`policies=pre_state.policies` and `supplies=pre_state.supplies` unchanged; in the
managed `_accept`, `_post_supply` maps over `pre_state.supplies` and so is
length-preserving. **Balances is the only growable collection in either transition**,
so the balance-row ceiling is the complete surface for this defect class. The
docstrings' narrower wording is accurate, not a hedge.

**Guard placement is correct, and I found the case that proves it.** The check sits
*after* the mutation loop, not inside it. My row-neutral probe — at exactly the
ceiling, send a sender's entire balance to a brand-new owner, so one row is popped and
one is added — **accepts**, with `post rows = 4096`, sender row removed, new owner
present. A guard placed inside the loop would have false-rejected this legitimate
transfer. Neither the Python nor the Rust suite covers this case; it works, but by
construction rather than by pin.

**Reject precedence is parity-correct.** `INSUFFICIENT_BALANCE`, `BALANCE_OVERFLOW`
and (managed) `SUPPLY_OVERFLOW` all precede the new code. My probe at the ceiling with
an oversized amount returns `INSUFFICIENT_BALANCE`, not the resource bound. Rust runs
`authorize → post_supplies → post_balances → accept`; Python runs
`_authorize → _post_supply → _post_balances → _accept`. Identical order.

**Docstrings.** Both now describe the typed reject; the "totalisation is deferred to
lane work" wording is gone. I swept the repo for stale claims of the old behavior:
the only remaining instances are inside *superseded* THV1 packets (v2, v23, v24) and
past review documents, all under explicit `Earlier:` framing. **No current claim
asserts the old non-total behavior.**

## 2. NEW-12 — CLOSED

Both parity tests carry `assert len(rust_matches) == len(rust_dict)`.

**M1**: appended `// pub const MAX_GLOBAL_SUPPLY_ROWS_V1: usize = 999;` (a
trailing-comment duplicate carrying a drifted value) to `canonical.rs`. **Both** tests
fail with `assert 38 == 37`. Last-occurrence-wins masking is closed on both.

## 3. CRATE-WIDE PARITY — PARTIAL

What holds:

- `sorted(crate_src.glob("*.rs"))` — deterministic concatenation, my P24 observation taken.
- **37 bounds, 0 value drift.** I re-derived every bound independently from the Rust
  source and compared against the resolved Python twin: all 37 equal, including the
  expression-valued ones (`u128::MAX`, `<<`, `*`).
- **The twin-module list is principled and minimal.** All 13 modules are load-bearing —
  each resolves at least one bound (`global_settlement_types_v1` 23, the rest 1–2) —
  and 0 bounds are unresolved. No vestigial entries.
- **M2** (a new `pub const MAX_OPUS_PROBE_BOUND_V1` with no Python twin, added to the
  non-canonical top-level `src/state.rs`) → **KILLED**. The extension beyond
  `canonical.rs` genuinely works.

### NEW-13 (P3) — the crate-wide scan is not crate-wide: `glob` does not recurse

`crate_src.glob("*.rs")` matches only the top level of `src/`. The crate has a
subdirectory, `src/economic_command_authentication/` (`witness.rs`, `types.rs`), which
the scan never reads.

**Confirmed with a surviving mutant.** The *identical* bound that M2 killed:

- in `src/state.rs` (top level) → `1 failed` — killed.
- in `src/economic_command_authentication/types.rs` → **`1 passed` — SURVIVES.**

THV1 `resource-bounds-v5` adds the mutation row *"declare a pub MAX_ bound outside
canonical.rs with no Python twin (crate-wide totality)"*. That stated class has a
surviving member — the same shape as P23 NEW-11, which this campaign repaired.

**Severity P3, latent only.** I verified there is zero live drift: the subdirectory
declares no `pub const` at all (it only *imports* `MAX_JOURNAL_BYTES_V1` and
`MAX_COMMAND_SIGNATURE_BYTES_V1`), and `rglob` and `glob` both return exactly 37
bounds today. The exposure is future: a bound added under that subdirectory would join
the ABI silently. The fix is one character — `glob` → `rglob`; `sorted()` keeps
determinism — plus widening the docstring/mutation-row wording to match.

### Observation (not a finding): Python-side resolution is first-match-wins

The twin loop takes the first module that `hasattr`s the name. Three names resolve in
more than one module (`MAX_ATOMS_V1`, `MAX_COMMAND_SIGNATURE_BYTES_V1`,
`MAX_TOKEN_BYTES_V1`). I checked each: **all are re-exports (imports) with exactly one
literal definition**, so an import can never disagree with its source and there is no
drift path today. Recording it as an asymmetry — Rust duplicates now fail loudly,
Python duplicates resolve silently — not as a defect.

## 4. SUPERSESSION HONESTY — CLOSED. No coverage was lost.

The two deleted tests pinned `pytest.raises(ValueError, ...)` *through the transition*.
That behavior is now intentionally unreachable; retaining them would mean a red suite.
Their replacement is strictly stronger: same input scenario, plus the accept side, the
typed code identity, `pre_state_root == post_state_root`, `effects.is_empty`, and a
compiled Rust twin asserting all four.

**The construction-bound behavior they also touched is still pinned elsewhere.** I
checked specifically, because this is where coverage usually leaks:
`tests/core/test_global_accounting_lane_producers_v1.py:561-581` still drives
`AssetTransferStateV1` past `MAX_ASSET_BALANCE_ROWS_V1 + 1` and asserts
`ValueError` for balances, policies, and managed-lifecycle balances. Oversized *input*
states still reject at construction with a pinned message.

**THV1 `resource-bounds-v5` is accurate.** Both killer rows re-point from the deleted
node ids to the totality node ids; both new files join the pinned surface with sha256
and explicit node ids; two new mutation rows are added. `claim_scope` states the
supersession and the deletion openly rather than eliding it.

**The replay's count pin is load-bearing** — I checked it rather than assuming.
Deleting one of the four Rust cases and also removing the now-unused import (so the
file compiles cleanly and reports `3 tests ... ok`) still fails:
`AssertionError: assert '4 passed' in '...running 3 tests...'`. A silently dropped
Rust case cannot pass. (A cruder deletion is caught even earlier by `RUSTFLAGS=-Dwarnings`.)

Both totality THV1 packets (`-v1`, `-v2`) are present because the squash preserved the
PR's own history; `-v2` genuinely strengthens `-v1` by adding the compiled-Rust replay
node and the matching refuted alternative, and hygiene selects `-v2`. Retaining `-v1`
is the tool's documented immutable-record behavior.

## 5. ENVELOPE — CLOSED

- **Chain shape**: `P25 → S25 → 0daf9ef64`, each with exactly one parent. No merge
  commit; the squash-with-provenance approach is stated plainly in the commit message
  and names the PR branch `codex/o008-total-transition-boundary-20260902 @ eaaa9f87a65f`
  as the authorship record.
- **P25 is packet-only**, and tighter than that: a structured diff against the
  predecessor packet shows it changes **exactly four fields** — `subject_commit`,
  `subject_parent`, `subject_tree`, `packet_commit_parent`. No claim text, no
  `completion_scope` change. Correctly, the totalisation is *not* added to the O-008
  completion scope.
- **Claim ceiling byte-identical** to the predecessor packet; all authorities `NONE`,
  `value_movement_gates_closed 0/12`, `whole_value_movement_safe false`.
- The one `tools/` edit is the `EXPECTED_SOURCE_CLOSURE_SHA256_V1` re-pin, appropriate
  given the `src/core` changes, and touches nothing that emits the ceiling.

### Merge-seam hunt (the highest-risk part of this candidate)

The PR was cut at `b6b0652af`, which is an ancestor of S25's parent. Between the two,
four files changed — and **one of them is a file the PR also rewrote**:
`tests/core/test_global_settlement_abi_v1_resource_bounds.py` (82 lines, the P23
NEW-11 regex repair). A wholesale squash of the PR's version would have silently
reverted NEW-11.

I re-ran all seven NEW-11 mutant classes against the post-squash regex:

| Mutant | Result |
|---|---|
| `pub  const` (double space) | KILLED |
| `pub` / newline / `const` | KILLED |
| path-qualified type (`core::primitive::usize`) | KILLED |
| CamelCase alias type (`RowCount`) | KILLED |
| `u32` type | KILLED |
| space before colon + `i64` | KILLED |
| expression-valued (`2 * 3`) | KILLED |

**The seam did not revert the P23 repair.** The other three seam files
(`global_settlement_types_v1.py`, `test_esso_global_settlement_core_v1.py`,
`test_lean_global_claimant_custody_relation_v1.py`) are byte-identical to S25's parent.

---

## New findings

### NEW-13 (P3) — `glob("*.rs")` is not recursive; the "crate-wide" mutation class has a surviving member
Detailed in item 3 above. Reproducible: append
`pub const MAX_OPUS_PROBE_BOUND_V1: usize = 7;` to
`zk/global_settlement_abi_v1/src/economic_command_authentication/types.rs`
and `test_every_canonical_rust_bound_has_a_python_twin` passes. Zero live drift today.
Fix: `glob` → `rglob`, and align the docstring and THV1 mutation-row wording.

### NEW-14 (P3) — the new Rust test file is not rustfmt-clean, and no gate covers this crate
`cargo fmt --check` exits **1** with 6 hunks, **all in the one new file**
`zk/global_settlement_abi_v1/tests/transition_resource_bound_totality.rs`
(import wrapping, `assert_eq!` splitting, call-chain wrapping — purely cosmetic, no
semantic content). Every other file in the crate is clean, so the crate has been
maintained rustfmt-clean by convention and this is the first drift.

Nothing catches it: `tools/run_rust_runtime_parity_gate.sh` runs `cargo fmt --check`
over `RUST_MANIFESTS` (11 kernels) and `RISC0_FORMAT_MANIFESTS` (4 packages), and
`zk/global_settlement_abi_v1/Cargo.toml` is **in neither list**. So this is two things:
a one-command fix (`cargo fmt`), and a standing gap — the O-008 crate, the most
actively edited Rust surface in this campaign, has no formatting gate while eleven
colder kernels do.

### NEW-15 (P3, observation-grade) — the two extended reject enums have no cross-language family-drift pin
This change adds a variant to `AssetTransferRejectCodeV1` and
`ManagedAssetLifecycleRejectCodeV1` in both languages. The *new code* is pinned in both
(the totality suites assert it by name). What is unpinned is the *family shape*: no
test reads `zk/global_settlement_abi_v1/src/asset_transfer_types.rs` or
`managed_asset_lifecycle_types.rs` to check that the Python and Rust variant lists
agree in membership and order. The campaign already built exactly this pin for other
families (`PRODUCER_REJECT_CODES_DRIFT`; `EXPECTED_REJECT_CODES` in the v2 registry),
so the asymmetry is visible. Pre-existing rather than introduced — this change enlarges
it by one variant. Current parity is correct; I verified both languages emit the same
code name for the same input.

---

## Prior findings

- **P21 NEW-6** — repaired at the mechanism (was: documented). Verified by M5/M6.
- **P24 NEW-12** — CLOSED. Verified by M1 against both parity tests.
- **P24 crate-wide parity observation** — taken, and works for `src/*.rs` (M2);
  incomplete for subdirectories (NEW-13).
- **P23 NEW-11** — survived the merge seam intact; all seven classes still killed.

## Scope of this review

I did not modify the fable worktree or the canonical checkout. All mutants were applied
inside my own detached worktree and reverted; `git status --porcelain` is empty and
`HEAD` is `1e579dc128cb4d7a5c909fc45d3e905165e4aca9`. A final NOT_RUN checker pass after
all mutation work confirms `ok=true`, `packet_admitted=true`, 0 errors, 0 drift.
