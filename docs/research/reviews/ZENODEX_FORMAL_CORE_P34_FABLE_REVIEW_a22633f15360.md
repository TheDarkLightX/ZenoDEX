# Second independent review: candidate C9a'''' (P34), with the unreviewed C9a''' (P33) claims graded in the same tree

| Field | Value |
| --- | --- |
| Subject (S34) | `9fb38be6aa5d6f593e0ee564ebeb2d61528d5a31` "security: pin the exact-type gates positively and bring the candidate chain into the repository", child of R32 `a3183f54651d7ae0f2f3408c7083f464c45502f3` (the last P32 receipt) |
| Artifact (P34) | `a22633f153608809148cadf3983ee7dec9426dfb` "docs: freeze the O-008 formal-cycle packet at C9a''''", direct child of S34; diff limited to `docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.{json,md}` |
| Packet sha256 | json `d888b962413e22f39f7c431890bec85916cc54b5000c0730b6cff5f18256bf00` (matches the brief), md `bb0563a1c0d574c1f697c1c66e21fa566d616c4436186dce221b4e59dcfa2684` |
| Also graded | C9a''' (S33 `28fbe52dd`, P33 `b2c1f12cf`, tag formal-core-c9a3-p-candidate-20260902), which received no independent review; its claims are verified in the P34 tree over the source range `165c04d2f..9fb38be6a` |
| Worktree | `/tmp/zenodex-formal-core-fable-review-c9a4`, detached at P34, `git status --short` empty before and after every replay. Mutation experiments ran in `git archive` copies under a private `fable-review-c9a4` subdirectory of the session scratch directory, never in the review worktree, except the three checker-suite runs of section 5.4, which ran in the worktree with the file restored by `git checkout --` and the tree verified empty afterwards. |
| Reviewer | Fable 5.1, fresh-context session at maximum effort. Independence caveat: the author is also a Fable 5.1 session, so reviewer and author share a model family; they share no transcript, worktree, scratch files, or notes. The author's scratch files under `/tmp/claude-1000` were not opened. The parallel Opus reviewer was not consulted. |
| Date | 2026-09-02 (replays ran 2026-09-03 02:40Z to 04:12Z) |
| Authority | None granted. The verdict below is advisory; the claim ceiling stays where P33 left it and must not move. |

## Verdict

**REVISE (advisory), grade B+.** 0 P1, 4 P2, 6 P3, 4 INFO.

Everything the candidate replays was reproduced on the P34 tree: the no-replay and replay checker admissions (30 runs, `EXECUTED_PASS`, comparables equal to the prior receipts), the builder round trip byte-identical, the Rust gate, every Python suite, all three Lean gates under the shared lock, all 50 O-008 pins and 47 hygiene selections, every pin and node id of the ten live THV1 packets, the re-pinned closure digest, and a claim ceiling byte-identical to P32 and P33. The security substance of both C9a''' and C9a'''' is real: every nested-row forgery from the P31 review is refused at the entry rebuild, check (0) rebuilds every caller value, all four Opus P32 evasions and the F-4 rewrite are caught, the F-2 shadowing case is refused before selection in both gates, and giving the twelfth Lean guard content breaks the challenge build. What earns REVISE is evidence accuracy, the same class the P32 reviews flagged: two declared killers do not kill (P2-1), the F-2 rule's two call sites are observed by no test (P2-2), the "pinned in both directions" claim is presence-only and 62 of the 86 pinned gates can be made inert with every importing suite green (P2-3), and no gating step of the committed chain executes this candidate's own killers (P2-4).

## 1. Replay ledger

All commands ran in the review worktree with `PY="/home/trevormoc/Downloads/Autonomous Tau DEX/.venv/bin/python"`, `PYTHONDONTWRITEBYTECODE=1`, `CARGO_TARGET_DIR=/tmp/zenodex-fable-review-c9a4-cargo`, `CARGO_INCREMENTAL=0`; every Lean-bearing command ran under `flock -w 7200 /tmp/zenodex-lean.lock`.

Environment note, recorded because it produced a red first pass that is NOT a finding against the candidate: the worktree as handed over carried `external/ESSO` and the eight mathlib package symlinks but not `external/mathlib4`, which `lean-mathlib/lakefile` requires (`require mathlib from "../external/mathlib4"`). The first pass failed every Lean-bearing command with `mathlib: package directory not found` (checker replay `EXECUTED_FAIL` with `REPLAY_EXIT_CODE` on the eight Lean commands, builder `REPLAY_EXECUTED_FAIL`, both Lean gates `4 passed, 2 errors`, the transfer-refinement gate `9 passed, 31 errors`). The author's worktree links `external/mathlib4 -> /home/trevormoc/deps/mathlib4`; the same gitignored symlink was added to the review worktree (tree still clean) and the whole Lean-bearing chain was re-run. Rows 2, 3, 23, 24, 25 are from the second pass; the first pass is kept under `first_red_run/` in the reviewer scratch directory. The prompt's worktree recipe should include that symlink.

| # | Command | Exit | Result |
| --- | --- | --- | --- |
| 1 | `"$PY" tools/check_o008_formal_cycle_v1.py --root "$PWD" --packet-commit a22633f15…` | 0 | ok true, packet_admitted true, current_source_drift [], proof_replay NOT_RUN, errors []; head = packet = P34, subject = S34; report sha256 `21cfe841ed665c2ad46984d9fff341a3f45ae6d039aafb18303f8fee9e57251b` |
| 2 | same with `--replay --esso-python /usr/bin/python3 --esso-pythonpath /home/trevormoc/Downloads/ESSO` (under lock, 02:57:39Z to 03:13:47Z) | 0 | proof_replay `EXECUTED_PASS`, 30 runs all exit 0, errors []; comparables: lean 4.27.0, probe hashes `3e5079…` over 25 theorems and `598646…` over 16, binding gates 6 and 6, ESSO ir hashes `918526…`/`01a34e…`, fingerprints `256b0d…`/`7387e9…`, z3 4.15.4, cvc5 1.1.2, ESSO code `7f80c6…`, gates 20/24/136/40/17/13/7/41/35/3/1/37/3/4/30/7, python 3.12.3, cargo 1.87.0, rustc `17067e9…`; report sha256 `796cfb5fb880ac3a7eaa8adedd81875aff5ff9ff8464287cc5ace809843d1f90` |
| 3 | `"$PY" tools/build_o008_formal_cycle_v1.py --root "$PWD" --subject-commit 9fb38be6a… --created-date 2026-09-02 --check --replay … --output-json … --output-md …` (under lock, 03:13:47Z to 03:23:09Z) | 0 | `{"drift":[],"mode":"check","ok":true}`; worktree still clean; regenerated json/md sha256 equal the committed `d888b962…` / `bb0563a1…` |
| 4 | `cargo fmt --all -- --check` in `zk/global_settlement_abi_v1` | 0 | clean |
| 5 | `cargo clippy --locked --all-targets -- -D warnings` | 0 | clean |
| 6 | `cargo test --locked` | 0 | 54 targets, every `test result: ok`, 0 failed |
| 7 | `pytest tests/core/test_transition_resource_bound_totality_v1.py` | 0 | 10 passed |
| 8 | `pytest tests/core/test_global_settlement_abi_v1_resource_bounds.py` | 0 | 17 passed (= `PARITY_GATE_EXPECTED_PASSED_V1`) |
| 9 | `pytest tests/core/test_global_settlement_abi_v1.py` | 0 | 75 passed |
| 10 | `pytest tests/test_check_global_settlement_canonical_manifest_v1.py` | 0 | 8 passed |
| 11 | `pytest tests/test_check_test_hygiene_v1.py` | 0 | 17 passed |
| 12 | `pytest tests/core/test_global_settlement_fcis_exact_ownership_v1.py` | 0 | 20 passed |
| 13 | `pytest tests/core/test_asset_transfer_receipt_admission_v1.py` | 0 | 27 passed |
| 14 | `pytest tests/core/test_global_accounting_lane_producers_v1.py` | 0 | 30 passed |
| 15 | `pytest tests/core/test_asset_transfer_lane_module_v1.py` | 0 | 3 passed |
| 16 | `pytest tests/core/test_asset_transfer_refinement_v1.py` (collects again, Opus P30 NEW-5) | 0 | 113 passed |
| 17 | `pytest tests/test_check_o008_formal_cycle_v1.py` | 0 | 390 passed (246 s) |
| 18 | `"$PY" tools/check_test_hygiene_v1.py --json` | 0 | ok, 0 changed, 182 packets |
| 19 | `… --base-ref a3183f546 --json` (parent of S34) | 0 | ok; 19 changed / 7 critical; selected exact-ownership-v4, admission-v30, canonical-exact-admission-v5, receipt-admission-v5, lineage-ordering-v2 |
| 20 | `… --base-ref 42ccb6624 --json` | 0 | ok; 73 changed / 23 critical; the five above plus transfer-refinement-v3 and totality-v7 |
| 21 | `… --base-ref fd409ba6f7da8f0ec3e0220a04b7406d69a8cb85 --json` (campaign base) | 0 | ok; 348 changed / 61 critical; the seven above plus certificate-v16 and semantic-restage-v6 |
| 22 | `"$PY" tools/check_global_settlement_canonical_manifest_v1.py --json` | 0 | ok, `source_closure_sha256` = `20fdc9912198118d17ef61ae2c73c802ec92d37f05d53f9e3d65446bbbe8b4ce` = the re-pinned constant at `tools/check_global_settlement_canonical_manifest_v1.py:41` |
| 23 | `flock … pytest tests/formal/test_lean_global_claimant_custody_relation_v1.py` | 0 | 6 passed |
| 24 | `flock … pytest tests/formal/test_lean_global_accounting_allocation_certificate_v1.py` (serially after row 23) | 0 | 6 passed |
| 25 | `flock … pytest tests/formal/test_lean_asset_transfer_refinement_v1.py` (serially after row 24) | 0 | 40 passed |

Excluded as instructed: `tests/core/test_zusd_liquidation_partition.py` (pre-existing unrelated collection error). `/tmp/zenodex-fable-review-c9a4-cargo` was deleted after the ledger was recorded.

## 2. Chain and packet checks

- P34 is the sole child of S34 and changes only the two packet files (100 changed md lines: subject fields, three re-pinned sources, two new script pins, moved hygiene selections, the reworded nonclaim, the third accepted gap). S34 changed 17 paths: two `src/core` docstrings, the exact-ownership test, seven new THV1 packets (append-only respected), the hygiene loader and its test, the O-008 admission core, the manifest-checker digest, the two chain scripts (mode `100644`), and the Rust producer docstring.
- O-008 packet: 48 source pins at P33, 50 at P34 (`tools/formal_core_candidate_chain_v1.sh` as `candidate_chain_script`, `tools/formal_core_battery_v1.sh` as `candidate_battery_script`; both in `SOURCE_PIN_ROLES_V1` and `THV1_REQUIRED_PIN_PATHS_V1`); three pins changed sha (`global_accounting_lane_producers_v1.py`, the Rust producer, `o008_formal_cycle_admission_v1.py`), none removed. Hygiene selections 47 (45 at P32); admission-v30 pins the two scripts. `packet_commit_parent` = S34, `subject_parent` = R32.
- Claim ceiling: the canonical JSON of `claim_ceiling` is byte-identical at P32, P33, and P34 (`formal_core_complete=false`, every authority NONE, 0 of 12 value-movement gates, supported claim `O008_RELATION_NECESSARY_CHECKS_AND_INFORMATION_LOSS_PROVED`). Nonclaims stay at 13 (one reworded, F-8). `v1_information_loss.accepted_known_gaps` grew from 2 to 3 (`exact_type_audit_epoch_path`). Nothing else in the packet moved except pins, selections, and subject fields.
- Ten live THV1 packets (the seven of C9a'''' plus resource-bounds-v9, transfer-refinement-v3, totality-v7 from C9a''', which S34 did not re-cut): every `source_pins`/`test_pins` sha256 recomputed from the worktree matches (3, 8, 43, 3, 26, 5, 12, 13, 8, 11 pins, 132 in all), every `evidence_id` equals its file stem, and all 769 distinct node ids named in `test_pins.node_ids` and `mutations.killed_by` resolve under `pytest --collect-only` (917 collected, 0 missing; parametrized bases accepted).
- S33 and S34 declared 16 new mutation rows (4 + 3 exact-ownership, 5 + 1 receipt-admission, 1 lineage-ordering, 1 transfer-refinement, 1 totality); the other 231 rows are carried forward on re-pinned packets. Every new row was applied, its named killer run, and the file restored and sha-verified (section 5.1). Of the carried rows, the 17 on the receipt-admission lineage target a module S33 rewrote, so nine of them with unambiguous edit sites were re-applied as well (section 5.2); the remaining carried rows sit on sources unchanged since the P31/P32 reviews that applied them, or are checker-suite tests that perform their own mutation on fake records, and were not re-applied.

## 3. Verdicts on the C9a'''' claims

### 3.1 Positive gate pin and widened negative scan (Opus P32 F-1, Fable P32 P3-1): PARTIAL

What holds. `_ADMISSION_PATH_EXACT_TYPE_GATES` (`tests/core/test_global_settlement_fcis_exact_ownership_v1.py:613`) freezes the exact-type gates of nine modules by `(module, definition, expression, type)`; an independent AST walk finds 86 `type(x) is / is not T` compares on those modules mapping onto exactly the pinned key set, and the pin passes in the pristine tree. Every Opus evasion and the F-4 rewrite now fail a named test:

| Evasion (applied at the composition post-state gate, `src/core/asset_lane_projection_v1.py:378`) | positive pin | negative scan | behavioural killer |
| --- | --- | --- | --- |
| `_isinst = isinstance` + `if not _isinst(x, T)` | **fails** | passes (P3-1) | fails |
| `import builtins` + `builtins.isinstance` | fails | **fails** | fails |
| `if not issubclass(type(x), T)` | fails | **fails** | fails |
| `match x: case T(): … case _: raise` | fails | **fails** | fails |
| `x.__class__ is not T` | **fails** | **fails** | passes (a plain subclass has the right `__class__`) |
| control: `if not isinstance(self.code, …)` at `asset_transfer_types_v1.py:250` | fails | n/a | inventory pin fails |
| Opus F-4: `if not (isinstance(produced, ReceiptBackedProducerRejectedV1) and False)` | n/a | n/a | `test_admission_path_isinstance_inventory_is_pinned` **fails** |

Why PARTIAL: the fifth evasion exists and is stronger than a spelling. The positive pin records that the comparison is *present* in the definition, not that it is the *sole guard of a raise*. Keeping the compare and making it inert keeps all three scans green: `if type(x) is not T and False:` (N1), `… and not _isinst(x, T)` with a module-level alias (N2), `… and not _b.isinstance(x, T)` after `import builtins as _b` (N3), and `… and T not in type(x).__mro__` (N4) each pass `test_admission_path_exact_type_gates_are_pinned_positively`, `test_admission_path_has_no_isinstance_spelling_variants`, and `test_admission_path_isinstance_inventory_is_pinned`. At the composition post-state gate they are caught only by the behavioural killer that P2-1 isolated. At a gate without a behavioural killer they are caught by nothing: N5 makes the `type(prior.enabled) is not bool` gate of `_rebuild_prior_fragment_v1` inert and the three scans, the 27-test admission suite, and the 20-test exact-ownership suite all pass. Section 5.3 quantifies this over all 86 gates. Finding P2-3.

### 3.2 Negation propagation (Opus P32 F-4): CLOSED

`_isinstance_sites` carries `negated_parent` through every expression node and resets at statement boundaries (`:389-394`); the Opus rewrite is refused. Informational: `isinstance(...) is False` / `== False` are not negation nodes and are not detected; the licensed sites discriminate values produced by internal calls, so the flag is a form check rather than a security property.

### 3.3 Module set bound to the import closure (Opus P32 F-5): CLOSED for `src.core`, two honesty gaps (P3-4, P3-5)

`_src_core_import_closure("asset_transfer_receipt_admission_v1")` yields 49 modules; the nine scanned are a subset and the other 40 equal `_ADMISSION_CLOSURE_OUT_OF_SCOPE_ISINSTANCE_COUNTS` with their bare-name isinstance counts. Adding an `isinstance` call to a listed module (`global_settlement_types_v1`, count 0) fails the binding test. A runtime import of the entry module in a fresh interpreter confirms the AST closure over-approximates the runtime `src.core` closure (it also follows `TYPE_CHECKING` imports, the conservative direction); the extra runtime modules come from `src/core/__init__.py` importing the whole DEX and are not called on the path.

Gaps. (a) The walker follows only `from .x import` and `from src.core.x import`; three closure modules (`global_settlement_types_v1`, `economic_command_authentication_v1`, `economic_command_signature_verifier_deployment_v1`) import `..state.canonical` with a level-2 relative import, so `src/state/canonical.py` is on the real path (every root hash on the path goes through `canonical_json_bytes`, 22 isinstance sites) and is neither scanned nor listed. Safe in substance because `_canonical_value` (`global_settlement_types_v1.py:167-201`) exactifies every value before that encoder sees it. (b) The licence comment says the listed modules are "lanes and services the admission never reads rows from"; `global_economic_proof_v1` (13 sites) is listed, yet its `LaneModuleTransitionJournalV1.__post_init__` runs on the path for every rebuilt journal (`isinstance(self.lane_id, LaneIdV1)` at `:178`, Enum-safe). The substance is fine; the sentence is not.

### 3.4 Isolated composition killer (Opus P32 F-3, Fable P32 P2-1): CLOSED

`test_asset_lane_composition_accepted_rejects_root_bearing_subclasses` (`:429`) passes `_wave_b_accepted().effects` and matches `"post-state must be the exact typed value"`. Deleting the gate at `asset_lane_projection_v1.py:378-379` fails the test (and the positive pin); the exact-ownership-v4 packet declares exactly that mutation with that killer.

### 3.5 Lineage key with a load-time monotonicity rule (Opus P32 F-2/F-9): CLOSED, with its killer defective (P2-2)

The key keeps the date (`(date-and-stem, numeric version, name)`); `require_lineage_versions_monotone_with_dates_v1` runs in `load_packets` before any packet is parsed (`tools/test_hygiene_evidence_v1.py:337`) and `_require_hygiene_lineage_versions_monotone_v1` runs at the top of `_select_hygiene_packets` before ordering (`tools/o008_formal_cycle_admission_v1.py:3257`), so a violating set is refused before any selection in both gates. Reproduction of the Opus F-2 case: sorting the four names still ranks `…20260902…-v3.json` last, but both rules refuse the set (`versions must rise with the date prefix` / `THV1_LINEAGE_VERSION_REGRESSES_ACROSS_DATES`), and at repository scale a copy of canonical-exact-admission-v5 saved as `THV1-20260901-…-canonical-exact-admission-v6.json` turns `check_test_hygiene_v1.py --json` red at load (exit 1, naming v6 before v2) and green again once removed. Judgment: the date-inclusive key plus the monotone rule closes the recency defect without merging lineages, because a stem is the lineage identity in this corpus and the date is a cut date; the rule is strict (equal versions under two dates are refused too), which is fail-closed. The key-parity test covers repo-relative paths. Residuals: a mis-dated packet that ever lands keeps every gate invocation red until the loader or the append-only rule changes (deletion is refused by `_reject_packet_rewrites`), informational; and the declared killer does not observe either call site (P2-2).

### 3.6 Wording and registry (Opus P32 F-6/F-7/F-8): CLOSED, one artifact missed (P3-3)

F-6: the `_select_hygiene_packets` docstring (`:3240-3255`) names the contract-rule divergence (evidence families, risk class) and the refuse-not-reorder rule; it matches the code. F-7: `exact_type_audit_epoch_path` is in `ACCEPTED_KNOWN_GAPS_V1` (`:1033-1037`) and projected into the packet's `accepted_known_gaps`; that list is the only registry the other two accepted gaps live in either (the Plan V2 registry carries none of the three), so this is consistent, though not the UP-xx registry the Opus finding named. F-8: the module docstring, both producer docstrings (py `:228-236`, rs `:227-235`), and `NONCLAIMS_V1` say "no acceptance path carries this producer's rows into it"; the wording matches `_check_entitlement_rows`, which does run for the registered-empty certificate. Missed: the receipt-admission-v5 packet, re-cut in the same commit, still carries the pre-F-8 sentence in its fourth nonclaim.

### 3.7 Unobservable mutation half withdrawn (Fable P32 P3-2): CLOSED

The v5 row reads "drop receipt_root from the minted witness (populating it early is unobservable …)"; exporting `journal.journal_root` instead of `journal.receipt_root` fails `test_admitted_witness_exports_the_rebuilt_receipt_root`.

### 3.8 The process claim is in the repository (Fable P32 INFO): PARTIAL

Both scripts are committed at mode `100644`, pinned as roles, and invoked as `bash tools/…`. Read for correctness: the chain script gates commit S, both hygiene runs, the packet build with replay, and commit P on exit codes (`|| exit 1`), so "any red step stops the chain before P exists" is literally true. Three things it does not do. (a) The post-P checker replay and builder round trip (`tools/formal_core_candidate_chain_v1.sh:41-45`) only `echo` their exit codes; `git push` and `git tag` (`:46-47`) run unconditionally, so a red re-check is logged into the report file and the candidate is pushed and tagged anyway. (b) The battery (`tools/formal_core_battery_v1.sh:44,49,50,51`) echoes its four exit codes and always exits 0; the chain script never runs it. Fourteen battery suites are absent from `REPLAY_COMMANDS_V1`, and they include every suite that carries the 16 new killers (`test_global_settlement_fcis_exact_ownership_v1.py`, `test_asset_transfer_receipt_admission_v1.py`, `test_transition_resource_bound_totality_v1.py`, `test_check_test_hygiene_v1.py`, `test_check_o008_formal_cycle_v1.py`, `test_asset_transfer_refinement_v1.py`, and eight more); the THV1 hygiene gate pins their bytes and node ids but does not execute them (`_validate_current_packet` checks shas only). So no gating step of the committed chain executes this candidate's own killers; "battery green" is an author-read log line. (c) There is no clean-tree precondition: `git add -A` covers six path prefixes (`:30`), the builder refuses replay only when one of the 50 pinned paths differs from S (`tools/build_o008_formal_cycle_v1.py:52-59`), and the hygiene gate diffs commits only (`collect_git_changed_paths`), so an uncommitted edit to any of the eight admission-path modules that are not O-008 pins (all but `global_accounting_lane_producers_v1.py`) would run in the replay without being in S. Findings P2-4 for (a)+(b), P3-6 for (c). Whether this very candidate was built by the scripts cannot be verified from the tree (no chain report is committed); the replays above are the evidence that stands.

## 4. Verdicts on the C9a''' claims (unreviewed at P33)

### 4.1 Every caller-supplied value rebuilt at check (0): CLOSED

`verify_asset_transfer_fragment_receipt_v1` (`src/core/asset_transfer_receipt_admission_v1.py:278-289`) validates the witness scalars (`require_verified_lane_module_transition_scalars_v1`: exact fields record, exact primitives, five well-formed roots, three non-empty digests, closed kind), refuses a non-exact `lane_root` then rebuilds it, rebuilds the prior fragment (`_rebuild_prior_fragment_v1`: exact class, explicit enum/bool/root scalar checks, exact tuples, every row family through `_snapshot_dataclass_tuple_v1`, then `replace` re-running the fragment's own `__post_init__`), rebuilds the entitlement rows, then takes `accepted` through the deep snapshot. `_VerifiedFragmentFieldsV1.__post_init__` validates its own scalars. The four S33 tests exist; three of their declared mutations are killed (M10, M11, M12) and the lane-root one is not (M9, P2-1). Hunting for an un-rebuilt caller value: every witness field is read after the scalar validation, `lane_root.state_root` and `.lane_id` after the rebuild, and nothing else of the caller's is read. Object-forgery residuals are declared (4.9).

### 4.2 Deep rebuild at the transfer transition entry: CLOSED

`rebuild_asset_transfer_state_v1` (`src/core/asset_transfer_module_v1.py:65-89`) is the single definition; the lane wrapper's `_snapshot_asset_transfer_state_v1` delegates to it; the transition entry calls it (`:346`). All P31 nested probes re-run against the P34 tree through the totality suite's `_forged_state` helper: N1 `fee_owner=123` → `TypeError: asset transfer policy fee owner must be a string`; N2 `enabled=1` → `TypeError: … enabled must be bool`; N2b fee `-5` → `ValueError` at the policy constructor (no longer late, by the effect row); N3 supply `2**200` → `ValueError: supply atoms must fit an unsigned 128-bit integer`; N3b supply `True` → `ValueError`; N7 (`rich = MAX_ATOMS_V1 - 5` + supply `2**130`) → `ValueError` at the supply constructor before any fold; N8/N9 still refused; the control template is accepted. This equals the managed sibling's per-row reconstruction (`managed_asset_lifecycle_lane_module_v1.py:112-160`: policies by `replace` per row, balances and supplies through `_snapshot_dataclass_tuple_v1`). The BALANCE_OVERFLOW witness uses an in-width delta on a row past half width (`test_transition_resource_bound_totality_v1.py:270-283`). M16 (shallow rebuild) is killed.

### 4.3 Third F1 site and the nine-module inventory: CLOSED for the gates, PARTIAL for the killers

`receipt_backed_asset_lane_composition_v1.py:83,295,306` are exact and the module is in `_ADMISSION_PATH_MODULES`. Behavioural killers: accepted state/effects/journal subclasses (M2a-c killed), both projection sources (M1a/M1b killed), both port projections (M3 killed). The composition-candidate killer is vacuous (M4, P2-1): `__post_init__` (`:62-85`) checks `profile` first and the test passes `profile=object()`, which `isinstance` refuses too with the same message, so the spoofed `private_port` is never reached; only the positive pin catches the revert. The S33 packet sentence "every declared construction gate on the receipt-admission path has a behavioural killer" is therefore false for this gate and for the admission lane-root gate.

### 4.4 Spoofed-journal test sharpened: CLOSED

The test (`test_asset_transfer_receipt_admission_v1.py:276`) varies `pre_lane_root` and recomputes `receipt_root` through `_receipt_root`. Under the isinstance revert at `asset_transfer_types_v1.py:226` the spoofed journal is admitted (`Failed: DID NOT RAISE <class 'TypeError'>`), so in the pristine tree the refusal is the type gate and not a `ValueError`. Loosening only the lane-module gate at `asset_transfer_lane_module_v1.py:242` leaves the test green (the accepted constructor's gate fires first), consistent with the mutation as declared.

### 4.5 Lean claim surface: CLOSED

`rejectCode_ne_postStateResourceBoundExceeded` is in `CORE_CLAIMS` and `report_vectors_cover_every_emittable_code` replaces the name-exempting theorem in `CHALLENGE_CLAIMS`; the challenge discharges the twelfth constructor with the lemma (`exact absurd h (rejectCode_ne_postStateResourceBoundExceeded ctx pre cmd)`) rather than `absurd rfl hc`. The axioms probe (`#print axioms` over every named claim) covers it, and row 25 ran it (40 passed). Probe, under the lock in a copy with the same mathlib links: control `lake env lean -DwarningAsError=true` of V1, `lake build` of V1, and `lake env lean` of the challenge all exit 0; with the guard given content (`| .postStateResourceBoundExceeded => cmd.amountAtoms ≤ 1000` and the matching `Decidable` arm) V1 fails at `AssetTransferRefinementV1.lean:956` (`Application type mismatch` on `trivial` in the licence lemma, plus two fixture `decide` failures at `:1159,1165`) and `lake build Proofs.AssetTransferRefinementV1Challenge` fails on the V1 target, so the coverage proof cannot be built; no constructor-name exemption survives. The V1 file was restored (sha equal).

### 4.6 Corpus oracle: CLOSED, honest

`tools/check_asset_transfer_refinement_v1.py:565-569` skips an adjacent precedence pair only when the corpus itself declares the second code unreachable; the corpus row for `POST_STATE_RESOURCE_BOUND_EXCEEDED` names `tests/core/test_transition_resource_bound_totality_v1.py` as the runtime witness in both languages. The suite collects and runs (113 passed) and re-demanding the discriminator stops collection (M15, exit 4, as the row says).

### 4.7 Packet-side selector mirror: CLOSED

`THV1_SELECTED_PACKET_STALE` runs as a second pass after per-path selection (`:3284-3288`), so `THV1_PIN_DRIFT` on a changed required path still reports first; the docstring says so; `test_hygiene_selection_refuses_a_partly_stale_selected_packet` exists. Scoping is right: the pure core sees only the 50 snapshot blobs, and pins outside them are the repository gate's job (rows 19-21 exercise it against three bases).

### 4.8 Thirtieth replay command: CLOSED

`python_rust_bound_parity_gate` is the sixteenth of 30 `REPLAY_COMMANDS_V1` entries, graded by `_grade_pytest` against `PARITY_GATE_EXPECTED_PASSED_V1 = 17`; every observation is first gated on `exit_code == 0` (`:4051-4052`), a summary containing `failed` is unparseable (`REPLAY_PYTEST_SUMMARY_UNPARSEABLE`), and a count drift is `REPLAY_PASSED_COUNT_DRIFT`, so a red parity test fails the replay three ways; the checker suite's fake record carries the row. Row 2 shows 30 executed runs with the parity gate at 17.

### 4.9 Declared residuals and wording: CLOSED

The module docstring's DECLARED RESIDUALS paragraph, the receipt-admission-v5 nonclaims, and the O-008 nonclaims state the three residuals in the same terms (object.__new__ forgery with well-formed consistent scalars is indistinguishable from minting; the prior fragment is bound only through `STALE_JOURNAL` until C9b; Python raises at check (0) where the Rust producer returns `ACCEPTED_INVALID`, decided, parity vectors well-formed only). The v5 claim_scope carries the S30 correction ("the S30 message said asset_transfer_types_v2 keeps isinstance; it contains none").

## 5. Mutation and evasion results

### 5.1 The 16 new declared rows

| Packet | Mutation (as declared) | Named killer | Result |
| --- | --- | --- | --- |
| exact-ownership-v3 | loosen a projection-source gate to isinstance (transfer / managed) | `test_projection_sources_reject_state_subclasses` | killed / killed |
| exact-ownership-v3 | loosen any AssetTransferAcceptedV1 nested gate (post_state / effects / module_journal) | `test_asset_transfer_accepted_rejects_root_bearing_subclasses[…]` | killed ×3 |
| exact-ownership-v3 | loosen the port pre_state gate | `test_asset_lane_private_port_rejects_projection_subclasses[pre_state]` | killed |
| exact-ownership-v3 | loosen the receipt-backed composition candidate gates | `test_receipt_backed_composition_candidate_rejects_subclasses` | **NOT killed** (passes; the exact-ownership suite minus the pin tests passes; positive pin fails) |
| exact-ownership-v4 | delete the composition post-state gate | `test_asset_lane_composition_accepted_rejects_root_bearing_subclasses` | killed |
| exact-ownership-v4 | spell a gate as issubclass / builtins.isinstance / match-class | `test_admission_path_has_no_isinstance_spelling_variants` | killed ×3 |
| exact-ownership-v4 | weaken a gate to issubclass / `__class__` / alias | `test_admission_path_exact_type_gates_are_pinned_positively` | killed ×3 |
| receipt-admission-v4 | loosen the accepted journal gate (spoofed journal, recomputed receipt root) | `test_subclassed_journal_with_a_spoofed_journal_root_is_refused` | killed |
| receipt-admission-v4 | loosen the lane-root gate to isinstance | `test_lane_root_subclass_is_refused` | **NOT killed** (passes; whole 27-test admission suite passes; positive pin fails) |
| receipt-admission-v4 | entitlement rows un-rebuilt | `test_planted_entitlement_row_scalar_is_refused` | killed |
| receipt-admission-v4 | prior fragment un-rebuilt | `test_forged_prior_fragment_is_rebuilt_before_the_producer` | killed |
| receipt-admission-v4 | skip witness scalar validation | `test_forged_witness_with_hostile_scalars_is_refused` | killed |
| receipt-admission-v5 | drop receipt_root from the minted witness | `test_admitted_witness_exports_the_rebuilt_receipt_root` | killed |
| lineage-ordering-v2 | accept a version cut under an older date prefix | `test_lineage_key_matches_the_o008_checker_key` | killed only when the rule *function* is weakened; **NOT killed** when either gate stops calling it (section 5.4) |
| transfer-refinement-v3 | demand a discriminator for a model-unreachable pair again | `test_committed_corpus_passes_the_independent_oracle` | killed (collection error, exit 4) |
| totality-v7 | entry rebuild shallow again | `test_transfer_refuses_same_type_forged_nested_rows` | killed |

### 5.2 Carried receipt-admission rows re-applied on the rewritten module

Rows 2 (witness type gate deleted), 3 (private-port subclass at construction), 4 and 7 (exact-typed snapshot dropped before the binding), 8 (witness-kind check deleted), 9 (binding-root check deleted), 11 (producer reject swallowed), 16 (producer `binding_root` from `post_lane_root`), 17 (last member dropped from `RECEIPT_WITNESS_REJECT_CODES_V1`): all killed by their named tests. Row 6 is the S33 journal row above.

### 5.3 Per-gate liveness audit (basis of P2-3)

Method: for each of the 86 `type(x) is/is not T` compares on the nine modules, make it inert in place (`(<compare> and False)`, so the positive pin still sees it) and run every `tests/core` suite that imports one of the nine modules (21 suites, 601 tests, baseline green). "Live" means some suite fails; "inert-undetected" means the whole set stays green. Single-gate inertness only: two gates in series mask each other (the transition entry gate at `asset_transfer_module_v1.py:335` and the rebuild gate at `:76` are each inert-undetected alone but not jointly), so the inert count is an upper bound on gates with no coverage and an exact count of gates whose individual removal no suite observes.

| module | gates | live | inert-undetected |
| --- | --- | --- | --- |
| `asset_transfer_receipt_admission_v1` | 13 | 1 | 12 |
| `global_accounting_lane_producers_v1` | 11 | 2 | 9 |
| `asset_transfer_lane_module_v1` | 16 | 1 | 15 |
| `asset_transfer_module_v1` | 4 | 0 | 4 |
| `asset_lane_projection_v1` | 12 | 6 | 6 |
| `asset_transfer_types_v1` | 5 | 3 | 2 |
| `lane_module_receipt_verification_v1` | 13 | 3 | 10 |
| `lane_module_release_route_binding_v1` | 9 | 6 | 3 |
| `receipt_backed_asset_lane_composition_v1` | 3 | 2 | 1 |
| **total** | **86** | **24** | **62** |

Of the 62, twelve guard internally constructed reject values (`*RejectedV1.__post_init__` code/lane_id/detail/effects gates) and 50 guard caller-supplied inputs, snapshots, or rebuilds, among them every gate of `_snapshot_asset_transfer_lane_module_input_v1`, `_snapshot_asset_transfer_lane_module_accepted_v1`, and `_rebuild_prior_fragment_v1`, the admission lane-root gate (`:281`), the producer's lane-root, prior-fragment, entitlement-tuple and row gates (`:242-247`), and all three gates of `require_verified_lane_module_transition_scalars_v1` (`:250,253,267`). The full per-gate list is in the reviewer scratch file `liveness_summary.md`. The 24 live gates are the accepted-value constructors, the projection sources, the port projections, the composition post-state gate, the candidate and route-binding constructors, and the admission witness gate.

### 5.4 Rule-wiring mutations in the worktree

Loader call removed (`tools/test_hygiene_evidence_v1.py:337` → `pass`): `tests/test_check_test_hygiene_v1.py` + `tests/test_check_o008_formal_cycle_v1.py` = **407 passed**. O-008 selector call removed (`tools/o008_formal_cycle_admission_v1.py:3257` → `pass`): 2 failed, 241 passed, 164 errors, all `EXECUTING_CORE_DRIFT` (the committed packet pins the admission core's bytes); a comment-only edit of the same file gives exactly the same 2 failed and 164 errors, so the redness is the executing-tool self-pin, not a test observing the rule. Files restored by `git checkout --`, tree empty after each run.

## 6. Findings

### P1

None.

### P2

**P2-1 Two declared killers do not kill (carried into the S34 packets).**
- `tests/evidence/test_hygiene/THV1-20260830-global-settlement-exact-ownership-v4.json`, row "loosen the receipt-backed composition candidate gates back to isinstance" → `tests/core/test_global_settlement_fcis_exact_ownership_v1.py::test_receipt_backed_composition_candidate_rejects_subclasses` (`:576-602`). Cause: `ReceiptBackedAssetLaneCompositionCandidateV1.__post_init__` (`src/core/receipt_backed_asset_lane_composition_v1.py:62-85`) checks `profile` first and the test passes `profile=object()`, refused by `isinstance` too with the same `"exact typed value"` message; the spoofed port is never reached.
- `tests/evidence/test_hygiene/THV1-20260902-o008-asset-transfer-receipt-admission-v5.json`, row "loosen the lane-root gate to isinstance (Opus P30 NEW-2)" → `tests/core/test_asset_transfer_receipt_admission_v1.py::test_lane_root_subclass_is_refused` (`:532`). Cause: with `asset_transfer_receipt_admission_v1.py:281` loosened, the plain subclass passes `replace`, every witness check runs, and `produce_asset_transfer_fragment_v1` refuses it at `global_accounting_lane_producers_v1.py:243` with a message containing the same `"exact LaneStateRootV1"` substring; the whole admission suite passes.
- Repro: in a copy, apply `if not isinstance(value, expected_type):` at `:83` (resp. `if not isinstance(lane_root, LaneStateRootV1):` at `:281`), run the named node, restore.
- Minimal fix: build the candidate test from genuine profile, occurrence, context and witness values (fixtures exist in `test_global_accounting_lane_producers_v1.py`) so the port gate is the only one that can fire, and match the port label; for the lane root, match `"fragment admission requires the exact LaneStateRootV1"` and monkeypatch the producer to raise if reached. Re-cut both packets; correct the S33 sentence "every declared construction gate … has a behavioural killer".

**P2-2 The F-2 rule is enforced at two call sites that no test observes.**
- `tools/test_hygiene_evidence_v1.py:337` and `tools/o008_formal_cycle_admission_v1.py:3257`. The lineage-ordering-v2 killer (`tests/test_check_test_hygiene_v1.py:497-514`) calls both rule functions directly; it never loads a mis-dated evidence directory or projects a snapshot holding a mis-dated packet. Section 5.4: replacing the loader call with `pass` keeps 407 tests green; replacing the selector call is indistinguishable from a comment edit.
- Repro: replace `:337` with `pass`; run `tests/test_check_test_hygiene_v1.py` (green); drop a copy of canonical-exact-admission-v5 named `THV1-20260901-…-canonical-exact-admission-v6.json` into the evidence directory and run `tools/check_test_hygiene_v1.py --json` (green under the mutation, red in the pristine tree).
- Minimal fix: one loader test over a `tmp_path` evidence directory holding a consistent split plus the mis-dated cut, asserting `load_packets` raises `versions must rise with the date prefix` before any packet is parsed; one checker-suite test using `_with_packet` to add a mis-dated packet to the snapshot and asserting `_project_code(...) == "THV1_LINEAGE_VERSION_REGRESSES_ACROSS_DATES"`; name both in the packet row.

**P2-3 The positive pin certifies presence, not liveness, and the negative scan does not detect aliases.**
- `tests/core/test_global_settlement_fcis_exact_ownership_v1.py:751-775` (`_exact_type_gate_sites` records any `Compare(type(x), Is/IsNot, T)` wherever it sits) and `:814-836` (the alias check at `:833-835` refuses only assignments *to* the names `isinstance`/`issubclass`, so `_isinst = isinstance` passes; `import builtins as _b` passes the import check; `AnnAssign`/`NamedExpr` are not inspected). Evidence: N1-N5 (section 3.1) survive all three scans; 62 of 86 gates are inert-undetected (section 5.3). The claim that the discipline is "pinned in both directions" and that "a gate weakened … disappears from the scan" holds for pure replacement and not for conjunction; the packet, commit message, and test docstrings should say so.
- Repro: apply N2 (`_isinst = isinstance` at module top; `:378` → `if type(self.post_state) is not AssetLaneStateProjectionV1 and not _isinst(self.post_state, AssetLaneStateProjectionV1):`) and run the three scan tests (all pass); apply N5 (`if type(prior.enabled) is not bool and False:` in `_rebuild_prior_fragment_v1`) and run the three scans plus the admission and exact-ownership suites (all pass).
- Minimal fix (structural, about a dozen lines): record a gate only when the compare is the entire test of an `If` whose body is a single `Raise` (80 of the 86 compares already have that shape; the other six are two `and`-guarded optional-price gates and four `any(...)` generator gates, which get their own licensed shape), and fail the pin if a `type(x) is/is not T` compare appears anywhere else in the nine modules. Separately refuse any `Name` load of `isinstance`/`issubclass` that is not the func of a call, any `Import` of `builtins` under an alias, and `AnnAssign`/`NamedExpr` targets bound to those names. Then pick behavioural killers for the 50 inert input gates by family (one forged-input test per snapshot/rebuild function), or state the 24-gate behavioural scope in the packet.

**P2-4 No gating step of the committed chain executes this candidate's own killers.**
- `tools/formal_core_battery_v1.sh` cannot fail (`:44,49,50,51` echo the exit codes; the script exits 0); `tools/formal_core_candidate_chain_v1.sh` never runs it, and its own post-P checker replay and builder round trip (`:41-45`) do not gate `git push`/`git tag` (`:46-47`). Fourteen battery suites are outside `REPLAY_COMMANDS_V1` and hold all 16 new killers; the THV1 gate pins but does not run them.
- Repro: `bash tools/formal_core_battery_v1.sh /tmp/x.log; echo $?` prints 0 regardless of the log's `python exit 1`; read `:41-47` of the chain script.
- Minimal fix: make the battery exit non-zero when any step's exit is non-zero; in the chain script, run the battery before commit S with `|| exit 1`, capture the exit codes of `:41` and `:43` and refuse to push or tag unless both are 0; commit the chain report (or its sha) in the P message so "built by these scripts" is checkable.

### P3

**P3-1** `test_admission_path_has_no_isinstance_spelling_variants` docstring claims "no isinstance aliases"; the check at `:833-835` refuses rebinding *of* `isinstance`, not aliasing *to* it (M7b passes it). Fix as in P2-3 or reword.

**P3-2** The exact-ownership-v4 packet's `claim_scope` says the positive pin freezes gates "on the eight path modules"; the test scans nine (`src/core/asset_transfer_module_v1.py` joined at S34) and the pinned set has keys on all nine; the S34 commit message says eight as well. Re-cut with the right count.

**P3-3** `THV1-20260902-o008-asset-transfer-receipt-admission-v5.json` fourth nonclaim still reads "a check no acceptance path reaches while ASSET_TRANSFER stays at NO_PRODUCER", the wording F-8 replaced everywhere else in the same commit. Re-cut.

**P3-4** `_src_core_import_closure` (`:777-800`) ignores level-2 relative imports, so `src/state/canonical.py` (on the path through `canonical_json_bytes`, 22 isinstance sites) is neither scanned nor listed; safe today because `_canonical_value` exactifies first. Follow `..` imports into `src/state`, or state the `src.core`, level-1-only scope in the docstring and list the module with its count.

**P3-5** The licence comment above `_ADMISSION_CLOSURE_OUT_OF_SCOPE_ISINSTANCE_COUNTS` (`:702-706`) says the listed modules are ones "the admission never reads rows from"; false for `global_economic_proof_v1`, whose journal validator runs on the path for every rebuilt journal (Enum-safe sites at `:178,242`; the dataclass sites are the registered epoch-path gap). Say "modules whose on-path isinstance sites are Enum-base or Enum-member checks, plus lanes and services the admission never reads rows from".

**P3-6** The chain script has no clean-tree precondition after commit S (`tools/formal_core_candidate_chain_v1.sh:30-35`); the builder refuses replay only for the 50 O-008 pins (`tools/build_o008_formal_cycle_v1.py:52-59`), eight of the nine admission-path modules are not among them, and the hygiene gate diffs commits only. Add `[ -z "$(git status --porcelain)" ] || exit 1` after the commit, and widen `_require_worktree_equals_subject` to the hygiene-selected pins.

### INFO

- The monotone rule refuses equal versions under two dates and, once a mis-dated packet lands, keeps every invocation red until the loader or the append-only rule changes; fail-closed, worth a sentence in the loader docstring.
- `exact_type_audit_epoch_path` is registered in the packet's `accepted_known_gaps` like the other two gaps, not in the Plan V2 registry; consistent, but not where Opus F-7 asked.
- The negation flag misses `isinstance(...) is False` forms; cosmetic, the licensed sites discriminate internally produced values.
- The review worktree as handed over lacked `external/mathlib4`; a fresh `lake env lean` also re-unpacked the mathlib cache into the shared `/home/trevormoc/deps/mathlib4/.lake/build` (under the lock), which every fresh campaign worktree presumably does; the setup recipe should include the symlink.

## 7. What I could not fault

- Every replay the packet declares reproduces on the P34 tree once the environment is complete: 30 runs, comparables equal to the prior receipts, the builder round trip byte-identical, the Rust gate clean, every Python suite green, three Lean gates green under the lock.
- The claim ceiling is byte-identical across P32, P33, and P34; nonclaims did not shrink; the accepted-gap list grew by the one gap the Opus review asked to register.
- Check (0) rebuilds every caller value, and every nested-row forgery from the P31 review is refused at the entry rebuild the way the managed sibling refuses it.
- All four Opus evasions and the F-4 rewrite are caught; the F-2 shadowing case is refused before selection in both gates; the F-6/F-8 wording matches the code where it was applied; giving the Lean guard content breaks the challenge build.
- All 769 node ids resolve and all 132 pins across the ten live packets are current; 14 of the 16 new mutation rows and all nine re-applied carried rows are killed as declared.

## 8. Recommendation

**REVISE (advisory), grade B+.** The candidate closes what the two P32 reviews asked for, and the unreviewed C9a''' work underneath it is sound; the defects are in what the evidence says about itself. P2-1 and P2-2 are two small test changes plus three re-cut packets; P2-3 is a dozen lines of structural pin plus either per-family forged-input killers or an honest 24-gate behavioural scope in the packet; P2-4 is a handful of `|| exit 1` lines and a non-zero battery exit. A child candidate carrying those, with the three P3 wording re-cuts, would be a straightforward ACCEPT candidate on this evidence. Authority stays NONE; the claim ceiling must not move.

## 9. Cleanup

`/tmp/zenodex-fable-review-c9a4-cargo` was deleted after the ledger was recorded; the three `git archive` copies were deleted; the review worktree was left detached at P34 and clean (`external/mathlib4` symlink added, gitignored). Reviewer-only records (checker reports, mutation specs and results, the liveness audit and its summary, the node-id check, the Lean probe outputs, the first red pass) are under the private subdirectory `fable-review-c9a4` of the session scratch directory.
