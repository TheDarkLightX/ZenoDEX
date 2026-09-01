# Opus review receipt: candidate C2' at P4 = 7de1fee33e39f6a9a7d3657edc9e98ec31662372

Reviewer: Opus 5 (independent reviewer, read-only, detached worktree `/tmp/zenodex-formal-core-review-p-7de1fee33`).
Date: 2026-09-01. Subject: P4 = 7de1fee33e39f6a9a7d3657edc9e98ec31662372 (tree 19418dcd0c4cbc4c653073423897fe7ca88c786b), S4 = a942659f12db43cd1c1d67fec8c5aac5dc6f8272, parent b9963af81b5571622b170bb47930b8915b59a817 (Opus C2 receipt).
Verdict: Grade A-. All seven C2 findings closed and verified adversarially. Disposition: the two new P2 findings (killed_by entries naming the polarity test for implementation mutations; no golden replay command) and the P3 notes (renderer bare assert, stage-3 chain coverage) are repaired by candidate C1''. The grade is advisory and grants no authority.

Verbatim report follows.

---

# C2' Review — Opus 5, read-only at P4 = `7de1fee33e39f6a9a7d3657edc9e98ec31662372`

Reviewer: Opus 5 (independent reviewer, read-only). Date: 2026-09-01.
Subject: P4 = `7de1fee33e39f6a9a7d3657edc9e98ec31662372` (tree `19418dcd0c4cbc4c653073423897fe7ca88c786b`),
S4 = `a942659f12db43cd1c1d67fec8c5aac5dc6f8272` (tree `2655226f3d63dbaeedc2041ca5b9cf6c58b7bd46`),
S4 parent = C2 receipt `b9963af81b5571622b170bb47930b8915b59a817`, whose parent is the C1' packet `52d81ff352296c570a4cf01e6cb4fd0bde1d4d59`.

Worktree `/tmp/zenodex-formal-core-review-p-7de1fee33` left untouched: **0 tracked changes, 0 untracked** at exit, HEAD still `7de1fee33`. `/tmp/zenodex-opus-c2prime-cargo-target` deleted. Adversarial work was done in a standalone shallow clone at `/tmp/opus-c2prime-repo` (its own `.git`, built by `git fetch --depth=3 file://…`) and in `/tmp/opus-c2prime-*` scratch files — nothing was written inside the review worktree or the primary repository.

---

## 1. Grade: A-

All seven C2 findings are closed, and five of them are closed *hard* rather than by assertion: the Rust view's field privacy is a compile-time error (E0451), the mutation-killer polarity guard makes a wrong declaration unrenderable in every renderer mode (exit 1, zero bytes emitted, no output file), the golden fixture is now a pinned source whose hand-edit I reproduced as `current_source_drift` with exit 1, the lifecycle test's stage 3 derives drift from Git blob ids and worktree bytes and I exercised the branch to confirm it is non-vacuous, and the P1-2 precedence statement is *empirically exact* — I replayed the P1 (`28138402b`) guard body against the current one on the precise state the artifacts describe and got `LIABILITIES_EXCEED_SAME_CONTROL_DOMAIN_BACKING` versus `CLAIMANT_BACKING_TOTAL_OVERFLOW`, exactly as written. The chain is exact (P4 has one parent, changes only the two packet paths), all 50 pins across the three selected hygiene packets equal S4 bytes, both hand-recomputed pins match, every packet delta is append-only, and every one of the eleven required commands exits 0. The false unreachability claim and the nonexistent `SETTLED` status are gone, the fixture is 28 vectors, and — decisively for the P3-2 repair — **no pre-existing vector changed at all**, so none of the 27 `expected_view_root` values moved against `52d81ff35`.

What holds it below A is that the campaign's defining discipline — a claim in an evidence packet must be true — is still violated in the same packet, in a different field, and C2' widened the violation rather than closing it. Six of the twelve `killed_by` attributions in the selected `THV1-…-claimant-backing-guard-golden-v2` packet (`risk_class: critical`) name a test that provably cannot fail on the mutation it is attached to: `test_mutation_killers_name_recorded_vectors_with_the_expected_polarity` reads only the committed fixture JSON and two renderer constants and never invokes the guard, so no implementation mutation can fail it. C2' repaired that test's *body* (which was P2-2, correctly) and then attached two more implementation mutations to it, taking the count of references from five to seven. I confirmed this empirically on three separate mutations. Separately, `completion_scope` gained a golden-replay entry while `proof_replay.commands` stayed at eleven and includes neither golden replay test — the only completion-scope item with no corresponding replay command. Neither defect is a safety hole: every mutation named is in fact killed, just by a different node, and the golden replays do exist, are pinned, and pass. These are evidence-metadata accuracy defects, strictly narrower than C2's (no false impossibility, no unstated behavior change, nothing safety-relevant), and each is a one-line-per-entry repair.

### Per-finding disposition — the seven C2 findings

| C2 finding | Claim | Status | Evidence |
|---|---|---|---|
| **P1-1** | Declared-unreachable custody fold overflow is reachable | **CLOSED** | `UNREACHABLE_MUTATIONS_V1` deleted from the renderer; `unreachable_mutations` absent from the fixture top-level keys; vector `rejects_custody_aggregate_overflow` present with custody `[("account-a","USD","perps-margin",MAX),("account-b","USD","perps-margin",1)]` and explicit `supplies=[("USD",MAX)]`, expecting `CLAIMANT_BACKING_TOTAL_OVERFLOW`; fixture is 28 vectors; both replays assert 28; golden-v2 `nonclaims[1]` withdraws the claim explicitly; contract JSON gains `claimant_backing_guard.custody_fold_overflow: "reachable: …"`. Rust `Fixture` carries `deny_unknown_fields`, so reintroducing `unreachable_mutations` breaks the Rust replay. |
| **P1-2** | Precedence changed while described as unchanged | **CLOSED** | `precedence_change` present in `ZENODEX_ACCOUNTING_SOURCE_CLASSIFICATION_CONTRACT_V1.json:188` and as a paragraph in the `.md`; restated in golden-v2 `claim_scope`. **Statement verified empirically**: a P1-body replica reports `…liabilities exceed same-domain custody backing`, current reports `…claimant backing total overflows`, on the exact state class described. Code-level: P1 folded custody+liabilities → checked R1 → folded terminals; S4 folds all four in `derive_claimant_backing_view_v1` before `require_claimant_backing_v1` evaluates anything. |
| **P2-1** | Nonexistent `SETTLED` terminal status | **CLOSED** | `grep -c SETTLED` on golden-v2 = **0** (v1 retains 2, correctly, as append-only history). `DRAINED` at `:162` and `:209`. |
| **P2-2** | Test name overclaims its body | **CLOSED** | `MUTATION_KILLERS_V1` is now `mutation -> (vector, expected_code)`; `_mutation_killers_v1` raises `ValueError` on polarity drift; both Python (`:89-101`) and Rust (`histories_and_mutation_killers_name_recorded_vectors`) assert every declared polarity and that `seen_codes` equals all three reject codes. **Probe**: flipping one declared code makes `--check`, `--output`, and the default mode all exit 1 with zero bytes emitted and no file created. |
| **P2-3** | O-008 packet does not pin C2's headline evidence | **CLOSED** | `source_pins` 20 → 26 with roles `claimant_backing_guard_golden_{renderer,fixture,python_replay,rust_replay}`; the same four paths added to `THV1_REQUIRED_PIN_PATHS_V1` (`tools/o008_formal_cycle_admission_v1.py:138-145`); `COMPLETION_SCOPE_V1` gained a golden-replay entry (`:199`). **Probe**: hand-editing one `expected_outcome.code` in the fixture yields `current_source_drift == ["tests/data/global_claimant_backing_guard_v1_golden.json"]`, `ok:false`, `current_applicable:false`, exit 1 — plus three independent test failures. |
| **P3-1** | Lifecycle stage 3 is vacuous ("return h") | **CLOSED** | `tests/test_check_o008_formal_cycle_v1.py:1069-1086` now recomputes `drifted` from `git rev-parse HEAD:<path>` and `sha256(worktree bytes)` per pin, never from the report, and asserts the fail-closed direction plus `set(report["current_source_drift"]) >= drifted`. **Exercised**: I made a source commit after P in the standalone clone that touched a pinned source; the checker reported the drift and the test passed with `drifted` non-empty (non-vacuous). See P3-2 below for the residual that it is not reached at a packet commit. |
| **P3-2** | Rust view not validated by construction | **CLOSED** | All five fields private; `ClaimantBackingViewV1::new` validates token shape (`validate_token_v1`: non-empty, ≤ max, bytes in `0x21..=0x7e`) and strict `(asset,key)` increase per table, and sets `schema` itself; getters added; `derive_` routes through `new`. **Probes**: `new` rejects duplicates, unsorted keys, non-token/empty/non-ASCII keys, and duplicates in each of the four tables (5/5 pass); struct-literal construction from outside the module is `error[E0451]`; no `Deserialize` derive, so there is no deserialization back door; zero external construction sites in the crate. **Bytes/roots unchanged**: 0 of 27 pre-existing vectors differ in any field against `52d81ff35`, and the Rust replay passes. |
| **P3-3** | Whole-packet re-pin per candidate (design note) | Acknowledged, not a blocker | C2 recorded it as addressed by C1' newest-matching selection; I confirmed `selected_evidence_ids` = the **v2/v3/v5** packets, so the v1 packet's withdrawn claims are not selected. The directory now holds six near-duplicate claimant-backing/restage/admission packets; the design note stands. |

---

## 2. Findings

### P0 — none

No state makes Python and Rust disagree on code, message, view bytes, or view root (49 Rust tests pass against the Python-rendered fixture, including the new 28th vector). No reject path mutates state. No reserve or balance column can enter the view (`view column names` across all vectors = `schema`, `custody_by_control_domain`, `entitlements_by_control_domain`, `entitlements_by_claimant`, `open_terminals_by_claimant`). The chain, the pins, and the claim ceiling are exact. Nothing here blocks the candidate on safety grounds.

### P1 — none

There is no unsupported impossibility claim, no undocumented behavior change, and no pin or chain defect in this candidate. Both C2 P1 findings are closed and I could not construct a new one.

### P2-1 — Six of twelve `killed_by` attributions in the selected golden packet are provably false

`tests/evidence/test_hygiene/THV1-20260901-claimant-backing-guard-golden-v2.json:185-224` — mutation entries at `:185`, `:189`, `:205`, `:209`, `:213`, `:221`.

Exact statement: each of these six mutation entries declares
`"killed_by": "tests/core/test_global_claimant_backing_guard_v1_golden.py::test_mutation_killers_name_recorded_vectors_with_the_expected_polarity"`, and that node cannot fail on any of them.

The named test (`tests/core/test_global_claimant_backing_guard_v1_golden.py:89-101`) reads exactly three things: `_fixture()` (`:37-40`, which is `json.loads(FIXTURE.read_text())` — the committed JSON, not a re-render), `renderer.MUTATION_KILLERS_V1` / `renderer.ACCEPT_V1` (module-level constants), and `ClaimantBackingRejectCodeV1` (an enum of code strings). It never calls `derive_claimant_backing_view_v1`, `require_claimant_backing_v1`, or `evaluate_v1`. Therefore **no** mutation of the guard implementation can make it fail; only a fixture edit or a renderer-constant edit can. That is a proof, not a sample. The six affected mutations are all implementation mutations:

- `:185` "drop the same-domain check (R1)"
- `:189` "drop the open-terminal check (R2)"
- `:205` "use unchecked addition in a backing fold"
- `:209` "count DRAINED or TOMBSTONED terminals as open"
- `:213` "use unchecked addition in the custody fold"
- `:221` "fold entitlements across control domains"

Only `:217` ("declare a mutation killer with the wrong outcome polarity") is genuinely killed by that node.

Empirically confirmed on three of them, in `/tmp/opus-c2prime-repo`:

| Mutation applied to `src/core/global_economic_state_effect_refinement_v1.py` | Declared killer | Actual killers |
|---|---|---|
| drop the overflow check in `_fold_backing_totals_v1` (`:357`) | **PASSES** (1 passed) | `test_fixture_is_the_renderer_output`, `test_vector_replays_…[rejects_custody_aggregate_overflow]`, `[rejects_entitlement_aggregate_overflow]`, `[rejects_open_terminal_aggregate_overflow]`, `[precedence_entitlement_overflow_before_domain]`, `[precedence_terminal_overflow_before_domain]` (6 failed) |
| replace `status is TerminalObligationStatusV1.OPEN` with `status is not None` | **PASSES** (1 passed) | `test_fixture_is_the_renderer_output`, `test_vector_replays_…[ignores_drained_terminal_amount]`, `[ignores_tombstoned_terminal_amount]` (3 failed) |
| delete the R1 branch from `require_claimant_backing_v1` | **PASSES** (1 passed) | 9 failures, none of them the declared node |

Reproducing command (worked example for the second row):

```bash
git clone-free standalone: git init /tmp/probe && git -C /tmp/probe fetch --depth=3 \
  file:///tmp/zenodex-formal-core-review-p-7de1fee33 7de1fee33e39f6a9a7d3657edc9e98ec31662372 \
  && git -C /tmp/probe checkout --detach FETCH_HEAD
cd /tmp/probe && python - <<'EOF'
import pathlib
p = pathlib.Path('src/core/global_economic_state_effect_refinement_v1.py')
s = p.read_text()
p.write_text(s.replace("        if obligation.status is TerminalObligationStatusV1.OPEN\n",
                       "        if obligation.status is not None\n"))
EOF
"$PY" -m pytest -q -p no:cacheprovider \
  "tests/core/test_global_claimant_backing_guard_v1_golden.py::test_mutation_killers_name_recorded_vectors_with_the_expected_polarity"
# -> 1 passed   (declared killer does not fire)
```

Calibration and history: this is not a safety hole — every one of the six mutations *is* killed, by `test_vector_replays_state_view_root_and_outcome[<vector>]` and/or `test_fixture_is_the_renderer_output`, both of which re-render through the implementation. The defect is that the packet's machine-readable attribution is wrong, in a `risk_class: critical` packet, in exactly the field a reader would use to re-verify a mutation claim. It is also the same class C2 raised as P2-2 (name/body mismatch), one level up: C2' fixed the test body and then attached two *more* implementation mutations (`:209`, `:213`) to the same node, taking the reference count from five to seven. Five of the six false attributions predate C2'; two of the seven references are new.

Required repair: point each entry at a node that actually fails. Concretely — `:185`/`:189` → `tests/core/test_global_claimant_backing_guard_v1_golden.py::test_precedence_is_overflow_then_domain_then_claimant` or the specific `test_vector_replays_state_view_root_and_outcome[…]` id; `:205`/`:213` → `…[rejects_entitlement_aggregate_overflow]` / `…[rejects_custody_aggregate_overflow]`; `:209` → `…[ignores_drained_terminal_amount]`; `:221` → `…[rejects_claimant_swap_hidden_by_asset_aggregate]`. Alternatively add a mechanical gate that applies each declared mutation and asserts the named node fails — which would make the attribution self-checking rather than asserted. If neither is done, say in the packet that `killed_by` names the *suite* rather than the failing node, and stop naming a specific node id.

### P2-2 — `completion_scope` grew without a matching replay command

`docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.json` `completion_scope[2]`, generated from `tools/o008_formal_cycle_admission_v1.py:199-200`.

Exact statement: the packet asserts as completion scope *"Python and Rust replay one rendered claimant-backing golden vector: states, view bytes, view roots, closed reject codes with fixed precedence, and byte-identical messages"*, but `proof_replay.commands` is unchanged at eleven entries — `lean_version`, `lean_direct_check`, `lean_axioms_probe`, `lean_binding_gate`, `esso_validate`, `esso_verify_multi`, `esso_gate`, `prior_restage_gate`, `python_version`, `python_projection_gate`, `rust_projection_gate` — and none of them runs `tests/core/test_global_claimant_backing_guard_v1_golden.py` or the Rust `--test claimant_backing_guard_golden`. Every other completion-scope item has a replay command behind it; this is the only one that does not.

Repro:
```bash
"$PY" -c "import json;p=json.load(open('docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.json'));\
s=json.dumps(p['proof_replay']['commands']);\
print([n for n in ['claimant_backing_guard_golden','test_global_claimant_backing_guard_v1_golden'] if n in s])"
# -> []
```

Calibration: mitigated, not unsupported. The two replay tests are now pinned sources (so an edit is drift — I demonstrated it), they are `test_pins` in the selected hygiene packet, and they pass (35 Python + 3 Rust). What is missing is that the packet's own reproducibility mechanism cannot re-execute the item it now claims.

Required repair: add two commands to `REPLAY_COMMANDS` — `<PYTHON> -m pytest -q -p no:cacheprovider tests/core/test_global_claimant_backing_guard_v1_golden.py` and `cargo test --offline --locked --test claimant_backing_guard_golden` (cwd `zk/global_settlement_abi_v1`) — and rebuild with `--replay`. If that is deliberately deferred, state in the packet that `completion_scope[2]` is covered by source pinning and hygiene test pins rather than by proof replay.

### P3-1 — Two declared mutations name one source location; one of them is not realizable as worded

`tools/render_global_claimant_backing_guard_v1_golden.py:385-386`, mirrored at golden-v2 `:205` and `:213`.

Exact statement: `"use unchecked addition in the entitlement fold"` and `"use unchecked addition in the custody fold"` are declared as two mutations, but there is no separate custody fold to mutate. Python `_fold_backing_totals_v1` (`src/core/global_economic_state_effect_refinement_v1.py:357`) and Rust `fold_backing_totals_v1` (`zk/global_settlement_abi_v1/src/global_economic_state_effect_refinement.rs:276`) are each a single shared helper called four times. One edit removes the check from all four folds simultaneously — as my first probe showed, it fails five vector replays at once.

Repro: `grep -n 'def _fold_backing_totals_v1' src/core/global_economic_state_effect_refinement_v1.py` returns one definition; `derive_claimant_backing_view_v1` calls it four times.

Required repair: none strictly required — the two entries name two distinct *vectors*, and both vectors are real and pinned. If precision is wanted, reword to "use unchecked addition in the shared backing fold (custody-keyed witness)" and "(entitlement-keyed witness)", or fold them into one mutation with two killers.

### P3-2 — The repaired lifecycle stage 3 is not reached at a packet commit

`tests/test_check_o008_formal_cycle_v1.py:1069-1086`.

Exact statement: at P4, `report["head_commit"] == report["packet_commit"] == 7de1fee33…`, so the test takes the stage-2 branch and the newly repaired stage-3 code never runs in the committed state. The C2 finding said stage 3 was vacuous; it is now non-vacuous, but only when a source commit sits after P — which is by construction never true at a packet commit.

Repro / positive result: in the standalone clone I appended a comment to `tools/render_global_claimant_backing_guard_v1_golden.py` and committed it as a child of P4. The checker then reported `ok:false`, `packet_admitted:true`, `current_applicable:false`, `current_source_drift: ["tools/render_global_claimant_backing_guard_v1_golden.py"]`, exit 1, and `pytest …::test_committed_packet_lifecycle_at_repository_head` passed with `drifted` non-empty — so the branch works and its assertions bite. (Note this also demonstrates the P2-3 repair paying off: the renderer only became a drift-detectable path in C2'.)

Required repair: none. Drift detection is separately covered by synthetic-fixture tests (`test_cli_worktree_packet_edit_is_drift`, `test_executing_tool_drift_fails_closed[checker_blob_ne_subject]`, and the `test_packet_mutations_fail_closed[…]` family). Recording in the packet or the test docstring that stage 3 is exercised only between P and the next packet commit would make the coverage claim self-describing.

### P3-3 — Bare `assert` in the evidence renderer

`tools/render_global_claimant_backing_guard_v1_golden.py:429` — `assert isinstance(vector, dict)` inside `_mutation_killers_v1`.

Exact statement: the polarity guard's type narrowing uses `assert`, which is stripped under `python -O`. The load-bearing polarity check on the next lines is a real `raise ValueError`, so the refusal survives `-O`; only the type narrowing is lost, and a non-dict vector would then fail on the following subscript anyway. This is evidence tooling, not the consensus path, so the repo's no-`assert` rule applies only by analogy.

Repro: `grep -n 'assert isinstance' tools/render_global_claimant_backing_guard_v1_golden.py`

Required repair: none. If the renderer is ever run under `-O` in CI, replace with an explicit `if not isinstance(...): raise TypeError(...)`.

### P3-4 — The Python golden replay remains self-referential (carried forward from C2)

`tests/core/test_global_claimant_backing_guard_v1_golden.py:41-42` and the `test_vector_replays_…` family.

Exact statement: `test_fixture_is_the_renderer_output` compares the committed bytes to `renderer.render_bytes_v1()` — the same function that produced them — and the per-vector replay goes through `renderer.evaluate_v1`. The Python side is therefore self-consistent rather than independent; the differential content lives entirely in the Rust replay, which re-derives from the recorded canonical state through its own implementation. C2 recorded this and it is unchanged.

Required repair: none — it is correctly scoped and the Rust side supplies the independence. Worth keeping in the packet's nonclaims if it is not already implied.

---

## 3. Verification record

`PY="/home/trevormoc/Downloads/Autonomous Tau DEX/.venv/bin/python"`, cwd `/tmp/zenodex-formal-core-review-p-7de1fee33` unless noted.

| Command | Exit | Key output |
|---|---|---|
| `git status --porcelain \| grep -v '^??'` | 1 (empty) | **0 tracked changes**, before and after the review; 0 untracked shown (the expected `external/*`, `lean-mathlib/.lake/packages/*` symlinks are ignored) |
| `git rev-list --parents -n1 HEAD` | 0 | `7de1fee33… a942659f12…` — exactly one parent |
| `git rev-list --parents -n1 HEAD^` | 0 | `a942659f12… b9963af81b…` — S4's parent is the C2 receipt |
| `git rev-list --parents -n1 HEAD^^` | 0 | `b9963af81b… 52d81ff352…` — receipt's parent is the C1' packet |
| `git diff-tree --no-commit-id --name-status -r HEAD^ HEAD` | 0 | `M docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.json`, `M …V1.md` — **exactly the two packet paths** |
| `git diff --stat HEAD^^ HEAD^` | 0 | 15 files changed, **+1611 / -114**; 3 added (the three new THV1 packets), 12 modified, **0 deleted** |
| `"$PY" tools/check_o008_formal_cycle_v1.py --root "$PWD"` | **0** | `ok:true, packet_admitted:true, current_applicable:true, current_source_drift:[], errors:[], head_commit==packet_commit==7de1fee33…, subject_commit=a942659f12…, formal_core_complete:false, all seven authorities NONE, value_movement_gates_closed 0/12, proof_replay NOT_RUN` |
| `"$PY" tools/render_global_claimant_backing_guard_v1_golden.py --check` | **0** | `{"ok": true, "mode": "check"}` |
| `"$PY" -m pytest -q … (4 files: golden, contract, o008 gate, lean gate)` | **0** | `249 passed in 69.88s` |
| `PYTHONPATH=/home/trevormoc/Downloads/ESSO ZENO_ESSO_PYTHON=/usr/bin/python3 "$PY" -m pytest -q … test_esso_global_settlement_core_v1.py` | **0** | `136 passed in 45.92s` |
| `cargo test --offline --locked --test claimant_backing_guard_golden` | **0** | `3 passed` (`every_vector_replays_state_view_root_and_outcome`, `histories_and_mutation_killers_name_recorded_vectors`, `reject_message_table_is_shared_with_python`) |
| `cargo test … --test global_economic_state_effect_refinement` | **0** | `41 passed`, incl. `claimant_relation_accepts_u128_boundary_and_rejects_aggregate_overflow` |
| `cargo test … --test v1_projection_gate` | **0** | `5 passed` |
| `cargo clippy --offline --locked --all-targets -- -D warnings` | **0** | clean |
| `"$PY" tools/check_test_hygiene_v1.py --base-ref fd409ba6f7… --json` | **0** | `ok:true, changed_path_count:34, critical_path_count:13, evidence_packet_count:84, selected_evidence_ids:[claimant-backing-guard-golden-**v2**, semantic-restage-**v3**, o008-formal-cycle-admission-**v5**]` |
| `"$PY" -m ruff check tools/o008_formal_cycle_admission_v1.py tools/render_…_golden.py` | **0** | `All checks passed!` |
| `"$PY" -m mypy --strict` (same two files) | **0** | `Success: no issues found in 2 source files` |
| `pytest --collect-only` (5 files spanning every `killed_by` node) | 0 | `463 tests collected`; **all 53 `killed_by` references across the three selected packets resolve** (the one bare-function id, `…::test_refinement_rejects_fee_residue_aliases`, is a valid parametrized selector — confirmed `2 passed`) |

### Hand-recomputed pins

`git cat-file blob HEAD^:<path> | sha256sum` against the values recorded in `docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.json`:

| Path | Recomputed sha256 | In packet | Git blob (recomputed / in packet) | Match |
|---|---|---|---|---|
| `zk/global_settlement_abi_v1/src/global_economic_state_effect_refinement.rs` | `e91f27cd2f38db434b1d8c77ef72a34508ec4ab744dff3843261fe263139316f` | identical | `81afccc0f4157672e2ac1a04e348f740f49d350c` / identical | **YES** |
| `tests/data/global_claimant_backing_guard_v1_golden.json` | `5caab921045b7023e8f76447d8a20a9f966985e8c3da8f265dba35ea3994a50e` | identical | `dc375342c05f047633f90c7cf70703f4eb8dd059` / identical | **YES** |

Four further pins recomputed and matched: renderer `1118f36960a5f884006694d1aac908c652d17b75683e862271333c649094778f`, Python replay `7439b01af9b5d5d89b960ec4bdf372141860c2de083fa93b486afab65bb2e919`, Rust replay `3d52352ccd9fe613910c6abdddad153cea418f53dbf2004e7a9b7ca2234f2077`, Python refinement `abf60faacdcd45def5163e618494a2202c9c1ab7e11bde1f44b7b29cd0057697` (unchanged — S4 did not touch the Python source).

### Chain, pins, and packet integrity

- `subject_commit` = S4, `subject_parent` = C2 receipt `b9963af81b…`, `subject_tree` = `2655226f3d…` = `git rev-parse HEAD^^{tree}`, `packet_commit_parent` = S4, `packet_write_set` = exactly the two packet paths. All exact.
- **Executing checker bytes equal S4**: all four `executing_tools` hashes recomputed from `HEAD^` blobs and from the P4 worktree are identical (`check_o008_formal_cycle_v1.py 3b148d47…`, `o008_formal_cycle_admission_v1.py 6165808c…`, `o008_formal_cycle_shell_v1.py f1ae83b4…`, `scan_lean_proof_placeholders_v1.py 44a7c671…`).
- **All 50 pins in the three selected hygiene packets equal S4 bytes** (24 + 14 + 12 checked, 0 mismatches).
- **No selected hygiene packet pins either packet path** — verified for all three; the O-008 packet → v5 packet → admission tool reference remains well-founded, not a hash cycle.
- **Append-only**: for each of v4→v5, restage v2→v3, golden v1→v2 the key set is identical, `removed_paths` is `[]` on both sides, and no pin path was removed. v5 adds 4 source pins + 2 hash updates + 2 test-pin hash updates; restage v3 changes 3 hashes; golden v2 changes 7 hashes and adds 2 net mutations (SETTLED→DRAINED replacement plus two new entries).
- **Re-pins moved exactly one hash**: Lean gate `PINNED_SOURCES[RUST_REFINEMENT]`, restage `ENFORCED_PINS[…refinement.rs]`, and the blueprint row all move `0a63e93e58f0a1b8…` → `e91f27cd2f38db43…` and nothing else. The blueprint's `THV1` admission id moves v2→v3 and the restage gate's `THV1_PACKET`/`THV1_EVIDENCE_ID` move to `semantic-restage-v3`, as specified.
- **`proof_replay` honesty**: the packet records `author_record.status = "EXECUTED"` with 11 runs *and* `admission_semantics = "AUTHOR_RECORD_IS_OBSERVATION_ONLY_CHECKER_REPORTS_NOT_RUN_UNLESS_IT_EXECUTES"`, while the checker independently reports `NOT_RUN`. The commit message's "all eleven replay commands EXECUTED_PASS" refers to the author record and does not conflict with the checker. Good discipline, not a finding.

### Adversarial probes (all in `/tmp/opus-c2prime-repo` or `/tmp/opus-c2prime-*`)

| Probe | Result |
|---|---|
| Hand-edit `expected_outcome.code` in the pinned fixture | checker exit **1**, `current_source_drift: ["tests/data/global_claimant_backing_guard_v1_golden.json"]`, `ok:false`, `current_applicable:false`; renderer `--check` exit 1; 3 Python tests fail. Restored → `ok:true, drift:[]`. |
| Flip one declared killer polarity in the renderer (`_R1`→`_R2`) | `--check` exit **1**, `--output <file>` exit **1** with **no file created**, default mode exit **1** with **0 bytes on stdout**. `ValueError: mutation killer polarity drift: … yields LIABILITIES_EXCEED_SAME_CONTROL_DOMAIN_BACKING, declared OPEN_TERMINAL_EXCEEDS_CLAIMANT_ENTITLEMENTS`. Wrong polarity is **unrenderable**. |
| Rust `ClaimantBackingViewV1::new` with duplicate / unsorted / non-token / empty / non-ASCII keys, and duplicates in each of the four tables | 5/5 probe tests pass — every case is `Err` |
| Rust struct-literal construction from outside the module | `error[E0451]: fields … are private` — compile error |
| P1-body replica vs current guard on a state where the OPEN-terminal fold overflows *and* R1 fails | P1: `liabilities exceed same-domain custody backing`; current: `claimant backing total overflows` — the `precedence_change` text is exact |
| Drop the fold overflow check / drop the OPEN filter / drop the R1 branch | Declared killer `test_mutation_killers_…with_the_expected_polarity` **passes in all three cases** (finding P2-1); real killers are the vector replays and `test_fixture_is_the_renderer_output` |
| Source commit after P4 touching a pinned source | checker exit 1 with correct drift; `test_committed_packet_lifecycle_at_repository_head` exercises stage 3 and passes with `drifted` non-empty |
| 27 pre-existing vectors vs `git show 52d81ff35:tests/data/global_claimant_backing_guard_v1_golden.json` | **0 differ in any field**; `expected_view_root` moved for none; only addition is `rejects_custody_aggregate_overflow`; `unreachable_mutations` removed from top-level keys |

---

## 4. Nonclaims and residual risks

- I verified the guard, the fixture, the cross-language parity, the pins, the chain, the hygiene selection, and the seven claimed repairs. I did **not** re-run the Lean or ESSO proof replay (`proof_replay.status` is `NOT_RUN`, correctly reported), did not read `GlobalClaimantCustodyRelationV1.lean`, and did not audit the twelve-lane reconciliation or the sidecar contract.
- I did not re-verify C2's own findings against P2 (`3feaa6224`); I took the C2 receipt's statements as the specification to check C2' against, and independently re-derived P1-1, P1-2, P3-1, and P3-2 from source rather than trusting the receipt.
- The Python golden replay remains self-referential (P3-4); the differential content is the Rust replay alone. A Python-only mutation to `evaluate_v1` would change the rendered bytes and be caught, but by the renderer-equality test rather than by an independent oracle.
- `derive_claimant_backing_view_v1` is still `pub` in Rust and callable on a state that never had `validate()` run — the golden test does exactly this. C2' narrows the residual: the view constructor now enforces token shape and ordering, so Python and Rust agree on what a token is (`0x21..=0x7e`, non-empty, bounded), closing the non-ASCII sort-order asymmetry C2 flagged. The entry points are still not equally defended at the state level.
- `exceeds_backing_v1` still collects into a `BTreeMap` that would silently keep the last of duplicate keys; that path is now unreachable through `new`, but the function itself carries no guard.
- The guard proves two necessary inequalities only. It cannot bind an opaque lane root to its private claimant projection, nor recover a terminal obligation's omitted control domain and principal. Both docstrings and the packet nonclaims say so accurately.
- The new vector `rejects_custody_aggregate_overflow` uses an explicit `supplies` override, so its state has `supply ≠ Σ owned`. That is legitimate and correctly documented — the vector's obligation text and the contract's `custody_fold_overflow` both state that `GlobalEconomicStateV1` validates rows, not supply equality — and C2 established that the backing guard runs before `_require_conservation_refinement_v1` end-to-end, so the overflow really does fire first. I did not re-verify that end-to-end ordering at S4; the Python refinement source is byte-identical to P2, where C2 verified it.
- My grade is advisory and grants no authority.

Disclosure: early in the review I made a `cp -a` copy of the worktree at `/tmp/opus-c2prime-clone` and ran `git status` in it before noticing its `.git` file still pointed at `/home/trevormoc/Downloads/Autonomous Tau DEX/.git/worktrees/…`. That command can refresh the linked worktree's index stat cache; it changes no content and no tracked or untracked file. I deleted that copy immediately and did all subsequent adversarial work in a standalone shallow clone with its own `.git` under `/tmp`. The review worktree ends with 0 tracked changes at `7de1fee33`.

---

## 5. User decisions — honored

All six hold.

1. **Reserves are the claimant-free term.** The view's five columns are `schema`, `custody_by_control_domain`, `entitlements_by_control_domain`, `entitlements_by_claimant`, `open_terminals_by_claimant` across all 28 vectors — no reserve or balance column exists. `derive_claimant_backing_view_v1` reads only `state.custody`, `state.liabilities`, `state.terminal_obligations` in both languages. Enforced structurally by `test_view_has_no_reserve_or_balance_column`, which is the `killed_by` node for "count reserves or balances as claimant backing" — and that one is a correct attribution.
2. **Control-domain vocabulary in new code, V1 wire names byte-stable.** The new vector's state rows still serialize `custody_domain`; the derived view columns use `control_domain`. All nine `v1_alias_table` rows carry `byte_stable: true`. No wire field is renamed; the golden-v2 nonclaims say so explicitly. The docstring change in `_require_state_only_necessary_claimant_backing_v1` ("custody domain" → "control domain") is documentation only.
3. **O-008A unattested.** `ZENODEX_O008A_DEPENDENCY_POLICY_BLOCKER_V1.json` is untouched by S4/P4 and still carries `dependency_safe: false`, `proof_validity: "NOT_CLAIMED"`, `qualification_complete: false`, `release_ready: false`, every authority `NONE`. It is not referenced from the O-008 packet.
4. **UP-01..UP-20 unresolved and never fixture-selected.** Zero `UP-\d\d` occurrences in the fixture or the golden packet. They appear only in the contract's `blocked_pending_policy` as named blockers. The new vector's values are `u128::MAX` and `1` — boundary integers, not a fee split or ratio.
5. **Authority NONE.** `claim_ceiling` reports `migration/production/publication/release/settlement/value_movement/verifier_authority: "NONE"`, `whole_value_movement_safe: false`, `value_movement_gates_closed: 0/12`. The fixture header carries `"authority": "NONE"` and both replay tests assert it.
6. **`formal_core_complete` false.** Confirmed in the checker output and the committed packet; `o008_status: "OPEN_EXACT_ALL_12_RECONCILIATION_MISSING"`.

---

**Recommendation.** Land after repairing the six `killed_by` attributions (P2-1) — that is the one defect that a future reviewer will find mechanically and that would discount the packet, and it is a six-line edit. P2-2 (two replay commands plus a `--replay` rebuild) is worth doing in the same pass since it re-freezes the packet anyway. With both closed, this reaches A: the mechanism work in C2' is already at that level, and the chain, pins, and parity evidence are the strongest I have seen in this campaign.
