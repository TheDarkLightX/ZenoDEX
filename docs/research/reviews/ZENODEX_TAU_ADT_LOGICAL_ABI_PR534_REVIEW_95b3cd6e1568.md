# Independent review — PR #534 "feat(tau): add ADT logical ABI specs for asset transfer and lane journals"

**Subject** head `95b3cd6e156840ee36e464c47881e345a45b364b` on `codex/tau-adt-logical-abi-v1-20260902`
(base `codex/o008-total-transition-boundary-20260902` @ `eaaa9f87a`, PR #532's branch).
**Reviewer** Fable 5.1 (this session), independent of the PR author; read-only on the PR branch.
**Review worktree** `/tmp/zenodex-tau-adt-recut-20260902` (child branch `codex/tau-adt-logical-abi-recut-20260902`).
**Authority** NONE. Research-only. Nothing in this receipt moves any claim ceiling.

Files under review: `src/tau_specs/recommended/asset_transfer_adt_contract_v1.tau` (44 lines),
`src/tau_specs/recommended/lane_transition_journal_adt_contract_v1.tau` (31), `config/tau_lang_adt_research.lock`
(pin `1c1e58aea7ddec04e48ce11cb0e6ed0cbe2a0d43`), `tools/build_tau_adt_research_pin_v1.sh`,
`tests/tau/test_tau_adt_logical_abi_v1.py` (248), `tests/evidence/test_hygiene/THV1-20260902-tau-adt-logical-abi-v{1,2,3,4}.json`.

---

## Verdict

**Grade: C+ — REVISE (keep draft, do not merge as-is).**

The harness discipline is right and the ADT schemas are a sound starting point, but (a) no Tau verdict for
these specs has ever been produced by CI — every run failed in the source build before Tau ran — and (b) every
theorem the specs and the test replay is a definitional projection of the predicate it quantifies over. The
evidence packet's invariant ids and its `reject_is_noop: applied` row therefore claim properties of ZenoDEX's
transition that the artifacts cannot observe. The fix is not more theorems of the same shape; it is binding the
specs to vectors produced by the real Python and Rust transitions (the campaign already has a 15/15
Python==Rust==Tau harness on `codex/tau-adt-abi-20260902`), and moving the replay evidence to a committed,
hash-bound receipt that CI verifies offline.

---

## Replay results

| Gate | Result |
|---|---|
| CI `ci` runs 211, 212, 213, 214 (`critical-quality`) | **FAIL** in "Enforce diff-aware test hygiene evidence": `tests/tau/test_tau_adt_logical_abi_v1.py::test_tau_adt_logical_abi_pinned_replay` builds Tau from source inside the hygiene gate; run 214 spent 1405 s (cvc5 at `TAU_BUILD_JOBS=1`) and then failed at `CMakeLists.txt:349` with `Could NOT find Boost (missing: Boost_INCLUDE_DIR log)`. `oracle-mvp-replay` passed (unrelated). |
| CI Tau semantic verdict | **never produced** (no run reached `tau -X`). |
| Local exact-pin replay at `1c1e58ae` (this review) | see the "Local replay" section below (appended when the pinned build completes; the build was started with the PR's own helper, unmodified, under the review worktree's gitignored `external/`). |
| `test_tau_adt_logical_abi_source_contract` | passes offline (string presence checks only; see F4). |

---

## Findings

### F1 — HIGH — The evidence packet pins a replay that has never executed in CI, and the design cannot execute there

`THV1-20260902-tau-adt-logical-abi-v4.json` pins `test_tau_adt_logical_abi_pinned_replay` as evidence for
eight invariant ids and a `harness_verdict` boundary dimension. The test (`:74-95`) clones and builds Tau on
the runner; the runner lacks Boost.Log, so the build fails deterministically after ~23 minutes. Four
consecutive runs prove this is structural, not flaky. The v3→v4 history (memory-bounded helper, `TAU_BUILD_JOBS=1`)
repaired a different failure (OOM) and left this one. Consequence: the packet's `aaa.status: applied` and
`harness_verdict` rows are unsupported by any recorded transcript.

Fix (design, not a workaround): commit a replay receipt (`tests/data/tau_adt_logical_abi_replay_receipt_v1.json`:
lock commit, binary sha256, spec sha256s, ordered query list with verdicts, transcript sha256) and pin an
**offline** test that checks the receipt is hash-consistent with the current specs and lock; keep a separate
**live** test that executes Tau and fails closed with a typed `TAU_PIN_UNAVAILABLE` reason when the binary is
absent (never a skip), recorded in the receipt with its exact command. A hosted-runner job that installs
`libboost-log-dev` and caches the built binary by commit is optional, and belongs outside the hygiene gate.

### F2 — HIGH — Every replayed theorem is a definitional projection; the specs cannot observe a transition bug

For each query, the conclusion is a literal conjunct of the predicate in its own hypothesis:

| Query (test line) | Hypothesis predicate | Clause that already contains the conclusion |
|---|---|---|
| `result_ok(r) → (rejected → pre=post ∧ effects_empty)` (`:210`, spec `:44` clause 1; `:216`) | `asset_transfer_result_ok` spec `:42` | reject branch `(rejected = 1) && (pre_root = post_root) && (effects_empty = 1)` |
| `unsat ex r (result_ok ∧ accepted ∧ code ≠ 0)` (`:218`) | same | accept branch `(accepted = 1) && (code = 0)` |
| `unsat ex r (result_ok ∧ rejected ∧ pre ≠ post)` (`:220`) | same | reject branch `(pre_root = post_root)` |
| `result_ok ∧ code = 12 → rejected ∧ no-op` (`:222`; spec `:44` clause 2) | same | reject branch admits codes `1..12` with the no-op conjuncts |
| `command_shape_ok(c) → sender ≠ recipient ∧ amount ≠ 0` (`:226`) | `asset_transfer_command_shape_ok` `:40` | `(sender != recipient) && (amount != 0)` |
| `context_binding_ok(...) → release = state_release ∧ subject = sender` (`:230`) | `:41` | `(module_release = state_release) && (subject = sender)` |
| envelope theorem (spec `:44` clause 4) | `:40`, `:41`, `:42` | each conclusion is a conjunct of one of the three |
| `journal_ok(j) → header_ok ∧ binding_ok` (`:236`; spec `:31` clause 1) | `lane_module_journal_ok` `:26` | it is defined as that conjunction |
| `unsat ex j (journal_ok ∧ effect_plan_root = 0)` (`:238`) | `journal_binding_ok` `:25` | `(effect_root != 0)` |
| edge continuity (`:240`; spec `:31` clause 2) | hypotheses of the same implication | `next.pre = prev.post` and the two header equalities are the hypotheses `prev.post = next.pre` and `same_journal_header` |

Two queries are not projections and are genuine (small) facts about Tau builtins: `fee_within_cap ↔ required ≤ cap`
(spec `:38-39`, test `:224`) — a property of `min` over `bv[16]`; and the `replay_cursor` saturation family
(spec `:28-29`, test `:242-248`) — a property of the recurrence with `min(1, x')`. Both are **Tau capability
probes**, not ZenoDEX transition facts. The remaining theorems evidence that Tau flattens whole/nested ADT
arguments to the right arity and decides closed formulas — also capability probes.

Consequence: a wrong Python or Rust transition (a rejection that mutates state, a wrong precedence, a
mis-mapped reject code) is invisible to this evidence. The invariant ids `TAU-ADT-ASSET-TRANSFER-REJECT-IS-NOOP`,
`TAU-ADT-ASSET-TRANSFER-RESOURCE-BOUND-CLOSED`, `TAU-ADT-LANE-JOURNAL-STRUCTURAL-BINDING` and the packet row
`reject_is_noop: applied` overclaim. Rename them to capability-probe ids, or bind them (below).

Fix: add a **vector-bound tier** — vectors built by running the real `transition_asset_transfer_v1`
(mirrored by the Rust leg on identical inputs), one Tau program per vector asserting `transition_ok` over the
vector's literal members in the **universal** form (`ex s:St ex c:Cmd ( bindings && all r:Res ( chain(s,c,r) -> expected(r) ) )`)
plus a non-vacuity program (`ex r:Res ( chain )`), exact T/F per program. Verified on Tau `3c24bad9` today:
the universal form answers T for the true expectation, F for a wrong expectation, and F when the guard chain is
weakened to admit every result (so over-permissiveness is visible). Note for implementers: Tau's parser accepts
only **single-letter** names for quantified ADT variables when members are accessed (`s.bal` works; `st.bal`,
`sx.bal`, `state.bal` raise `Syntax Error: Unexpected '='`).

### F3 — MEDIUM — The evidence packet has no mutation killers

`THV1-…-v4.json` `mutations: []`. The specs do kill mutations of **themselves** (drop `pre_root = post_root`
from `result_ok`'s reject branch and clause 1 of `:44` turns F), but no row records that, and no mutation of the
Python/Rust transition can be killed at all (F2). Add named rows for both classes once the vector tier exists:
"perturb a vector's expected code → F", "weaken the guard chain → F", "drop a reject-branch conjunct → F",
"edit a spec without a fresh receipt → offline receipt test red".

### F4 — MEDIUM — The reject-code map is a comment, not a pin

Spec `:20-26` and `code <= {12}` (`:42`) fix codes `1..12` in `AssetTransferRejectCodeV1` declaration order with
`12 = POST_STATE_RESOURCE_BOUND_EXCEEDED`; the source-contract test (`:167`) only asserts the string
`POST_STATE_RESOURCE_BOUND_EXCEEDED` appears in the file. The family grew 11→12 in PR #532 without any Tau
artifact noticing. Pin it: import the enum in the source-contract test and assert the spec's numeric table
(members in declaration order, `index+1`) and the `{12}` ceiling literal; the same test should pin
`command_kind = {1}` to `ASSET_TRANSFER_COMMAND_KIND_V1` (`:40`).

### F5 — LOW — Undocumented idioms and magic constants

`(max_fee = max_fee)`, `(epoch = epoch)`, `(pre_root = pre_root)`, `(private_root = private_root)`,
`(terminal_root = terminal_root)` are the `x:T = x` type-binding idiom for members the predicate does not
constrain; correct, but a reader takes them for missing checks. Say so in the spec comment block. The nonzero
tag conventions (`asset != 0`, `sender != 0`, `chain != 0`, `receipt_root != 0`) are research conventions;
list them as such.

### F6 — INFO — What is right and should be kept

`_run_query` requires exactly one final `T`/`F` (`:152`), rejects any `(Error)` in the transcript (`:151`), and
the replay proves the harness can say `F` before accepting positive verdicts (`:200-206`). The lock is
authoritative for the exact 40-hex revision (`:56-68`). `TAU_BUILD_JOBS=1` is an infrastructure fact; the
`source_build_parallelism` boundary dimension should move out of a semantic evidence packet.

### F7 — INFO — Topology for integration

The base is PR #532's branch, not an ancestor of the campaign head (`codex/formal-core-fable-20260901`
incorporated #532 as the single-parent squash S25 `a18699202`). Any landing into the campaign lineage must be
a single-parent re-cut; the O-008 checker rejects merge commits by design.

---

## What I could not falsify

- The lock/`_ensure_pinned_tau` path: the commit regex, the exact-HEAD check and the helper's post-build
  `rev-parse HEAD == ref` assertion are all real; no way to replay against a mutable branch name.
- The `F` probe (`:200-206`): a deliberately over-strong statement, decided by Tau, not by string matching.

## Recommendation

REVISE. Keep the two ADT schemas and the lock; relabel the definitional theorems as capability probes; add
the vector-bound tier (universal + non-vacuity programs per vector over the real transition's outputs, Rust
leg on identical vectors); replace the in-CI source build with a committed hash-bound replay receipt verified
offline plus a fail-closed live test; pin the reject-code map to the enum; add the mutation rows; then re-review.
The re-cut carrying these repairs is prepared on `codex/tau-adt-logical-abi-recut-20260902` for dual
independent review (Opus 5 + fresh-context Fable 5.1).

## Local replay

PENDING — appended when the exact-pin build of `1c1e58ae` completes (binary sha256, `tau --version`,
transcript sha256, per-query verdicts, wall time).
