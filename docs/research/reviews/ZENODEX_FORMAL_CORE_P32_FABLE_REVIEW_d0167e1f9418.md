# Second independent review: candidate C9a'' (P32)

| Field | Value |
| --- | --- |
| Subject (S32) | `83f786130572dcfc4c572a6f6f63e4255ad60615` "security: close the isinstance class mechanically and fix hygiene packet ordering", child of P31 `a4258d9891d1cd738f014c87c7eaa8de8cd6576a` |
| Artifact (P32) | `d0167e1f9418f9a6bc8d7b5b2dcd739a9f0da185` "docs: freeze the O-008 formal-cycle packet at C9a''", direct child of S32; diff limited to `docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.{json,md}` |
| Packet sha256 | json `5ddf3d88f76ddf1114c4250bd60a75185ca2797c5b491960afa7b0efa844c6f3`, md `ed342313bb6b62ade8325c08e64e587119c98d965fb25c3a40f68145c995be56` (both verified at P32 and reproduced byte-identically by the builder replay) |
| Worktree | `/tmp/zenodex-formal-core-fable-review-c9app`, detached at P32, `git status --short` empty before and after every replay; mutation experiments ran in a `git archive` copy at `/tmp/zenodex-fable-review-c9app-mut` (deleted after this report), never in the review worktree |
| Reviewer | Fable 5.1, fresh-context session at maximum effort. Independence caveat: the author is also a Fable 5.1 session, so reviewer and author share a model family; they share no transcript, worktree, scratch files, or notes. The author's scratch files under `/tmp/claude-1000` were not opened (the assigned scratch directory turned out to be shared with the author's session; all reviewer files were written to a private subdirectory and no author file was read). The parallel Opus reviewer was not consulted. |
| Date | 2026-09-02 |
| Authority | None granted. ACCEPT below is advisory; the claim ceiling stays where P31 left it. |

## Verdict

**ACCEPT (advisory), grade A-.** 0 P1, 1 P2, 3 P3, 4 INFO.

Everything the candidate claims was reproduced: the no-replay and replay checker admissions, the builder byte-identical regeneration, the Rust gate, the Python suites, both Lean gates under the shared lock, all 48 O-008 source pins and all 45 hygiene selections, every pin and node id of the eight THV1 packets, the closure-digest re-pin, and a byte-identical claim ceiling. The hygiene ordering defect is real and is fixed: with the parent's lexicographic loader the repository gate at P32 bytes fails against the campaign base on the stale admission-v9 packet; with the P32 loader it selects the nine expected packets and passes. The single P2 is an evidence-accuracy defect, not a runtime one: the new subclass-refusal test for `AssetLaneCompositionAcceptedV1` cannot observe its own gate, so the declared mutation "admit a root-spoofing projection subclass" survives when that gate is deleted outright.

- **P2-1** Non-isolating killer: `tests/core/test_global_settlement_fcis_exact_ownership_v1.py:418-446` passes a subclassed effect plan and an `object()` journal, so the effects gate raises the same "exact typed value" message before the post-state gate can matter; deleting the post-state gate at `src/core/asset_lane_projection_v1.py:378-379` survives both named killers.
- **P3-1** The AST inventory pin catches only a bare-name `isinstance(...)` call; `issubclass(type(x), T)`, `builtins.isinstance`, an alias, a `match` class pattern, and `x.__class__ is not T` all survive it, and its scope is the seven modules while the path transitively re-runs isinstance gates in `global_economic_proof_v1.py:178,242` (Enum-safe). "The class cannot regrow silently" is overstated.
- **P3-2** The receipt-admission-v3 mutation "drop receipt_root from the minted witness or populate it before check (4)" is only half-observable: populating the export from `produced.binding_root` survives the named killer because check (4) has already forced equality.
- **P3-3** Hygiene selection is still "first packet in a global name order whose pin matches, then every pin must be current": a later-named lineage with one current pin and one stale pin turns the gate red instead of falling through to an older fully current packet (fail-closed brittleness, not a false green). Numeric-within-lineage ordering is the right rule; cross-lineage order is name order and is only recency-monotone while date prefixes stay honest.
- **INFO** The prompt's expected count for `tests/test_check_test_hygiene_v1.py` is 20; the suite collects and passes 17 (the two new tests are among them). The candidate never claims 20.
- **INFO** `tests/core/test_asset_transfer_refinement_v1.py` still fails collection (Opus P30 NEW-5, scheduled); confirmed, not re-graded.
- **INFO** The certificate's `BINDING_ROOT_DRIFT` rule (`global_accounting_allocation_certificate_v1.py:653-657`) still requires `binding_root == lane_state_root`, so a receipt-backed fragment (binding_root = receipt root) is unreachable at the certificate until C9b changes that rule; consistent with the nonclaim, noted for C9b.
- **INFO** The commit message says the author's chain now runs the hygiene gate against the campaign base after every source commit; that chain script is not in the repository and cannot be verified here. The in-repo evidence (four green gate runs) stands on its own.

## Replay ledger

All commands ran in the review worktree with `PY="/home/trevormoc/Downloads/Autonomous Tau DEX/.venv/bin/python"`, `PYTHONDONTWRITEBYTECODE=1`; every Lean-bearing command ran under `flock -w 7200 /tmp/zenodex-lean.lock`.

| # | Command | Exit | Result |
| --- | --- | --- | --- |
| 1 | `"$PY" tools/check_o008_formal_cycle_v1.py --root "$PWD" --packet-commit d0167e1f…` | 0 | ok true, packet_admitted true, current_source_drift [], proof_replay NOT_RUN, errors []; report sha256 `a63bd579d4417b997cfcc0582d386340a033aa099e4056f3c9e51862ce020536` |
| 2 | same with `--replay --esso-python /usr/bin/python3 --esso-pythonpath /home/trevormoc/Downloads/ESSO` (under lock, 16:35:29Z to 16:46:35Z) | 0 | proof_replay EXECUTED_PASS, 29 runs all exit 0; comparables equal the author record (lean 4.27.0; probe hashes `3e5079…` over 25 theorems and `598646…` over 16; ESSO ir hashes `918526…` and `01a34e…`, fingerprints `256b0d…` and `7387e9…`, z3 4.15.4 and cvc5 1.1.2, ESSO code hash `7f80c62…`; gate counts 6, 6, 20, 24, 136, 40, 13, 7, 41, 35, 3, 1, 37, 3, 4, 30, 7; rustc 1.87.0 `17067e9…`); report sha256 `5051caed918a1a86c02ba18f327b024cc464f4399d41f51591cd83314cf564a1` |
| 3 | `"$PY" tools/build_o008_formal_cycle_v1.py --root "$PWD" --subject-commit 83f78613… --created-date 2026-09-02 --check --replay … --output-json … --output-md …` (under lock, 16:46:35Z to 16:53:51Z) | 0 | `{"drift":[],"mode":"check","ok":true}`; worktree still clean; regenerated json/md sha256 equal the committed `5ddf3d88…` / `ed342313…` |
| 4 | `cargo fmt --all -- --check` in `zk/global_settlement_abi_v1` (`CARGO_TARGET_DIR=/tmp/zenodex-fable-review-c9app-cargo`, `CARGO_INCREMENTAL=0`) | 0 | clean |
| 5 | `cargo clippy --locked --all-targets -- -D warnings` | 0 | clean |
| 6 | `cargo test --locked` | 0 | every target ok (includes the 7-test producers target and the 41-test refinement target) |
| 7 | `pytest tests/core/test_asset_transfer_receipt_admission_v1.py` | 0 | 23 passed |
| 8 | `pytest tests/core/test_global_settlement_fcis_exact_ownership_v1.py` | 0 | 10 passed |
| 9 | `pytest tests/core/test_global_accounting_lane_producers_v1.py` | 0 | 30 passed |
| 10 | `pytest tests/core/test_asset_transfer_lane_module_v1.py` | 0 | 3 passed |
| 11 | `pytest tests/core/test_global_settlement_abi_v1.py` | 0 | 75 passed |
| 12 | `pytest tests/test_check_o008_formal_cycle_v1.py` | 0 | 389 passed (267 s) |
| 13 | `pytest tests/test_check_test_hygiene_v1.py` | 0 | 17 passed (prompt expected 20; 17 collected, see INFO) |
| 14 | `pytest tests/test_check_global_settlement_canonical_manifest_v1.py` | 0 | 8 passed |
| 15 | `"$PY" tools/check_test_hygiene_v1.py --json` | 0 | ok, 0 changed paths, 166 packets |
| 16 | `… --base-ref a4258d9891d1cd738f014c87c7eaa8de8cd6576a --json` (parent of S32) | 0 | ok; 23 changed, 12 critical; selected exact-ownership-v2, admission-v28, canonical-exact-admission-v3, receipt-admission-v3, totality-v6, lineage-ordering-v1 |
| 17 | `… --base-ref 42ccb6624 --json` | 0 | ok; 47 changed, 21 critical; selected the six above plus transfer-refinement-v2 |
| 18 | `… --base-ref fd409ba6f7da8f0ec3e0220a04b7406d69a8cb85 --json` (campaign base) | 0 | ok; 322 changed, 59 critical; selected the seven above plus certificate-v14 and semantic-restage-v6 (red at P31, green now) |
| 19 | `flock … pytest tests/formal/test_lean_global_claimant_custody_relation_v1.py` | 0 | 6 passed |
| 20 | `flock … pytest tests/formal/test_lean_global_accounting_allocation_certificate_v1.py` | 0 | 6 passed (run serially after row 19 under the same lock, finished 16:59:24Z) |
| 21 | `"$PY" tools/check_global_settlement_canonical_manifest_v1.py --json` | 0 | ok, source_closure_sha256 `3a8f76f01454f51cd65fc7b54e9be7ce6ae14dd70f63128d44ddbb50f84d16de` = the re-pinned constant at `tools/check_global_settlement_canonical_manifest_v1.py:41` |

Excluded as instructed: `tests/core/test_zusd_liquidation_partition.py` (pre-existing unrelated collection error).

## Chain and packet checks

- S32 is the sole parent of P32; P32 changes only the two packet files. S32 changed 21 paths: 5 `src/core` modules, 2 test files, 8 new THV1 packets (all status `A`, append-only respected), 2 checker/tool modules, the hygiene loader, the manifest-checker digest, and the Rust producer docstring.
- O-008 packet: 48 source pins at P31 and P32; 4 pins changed (`global_accounting_lane_producers_v1.py`, the Rust producer, `o008_formal_cycle_admission_v1.py`, `tests/test_check_o008_formal_cycle_v1.py`), none added or removed. 45 hygiene selections at both; the selected packets moved admission-v27 to v28, canonical-exact-admission-v2 to v3, receipt-admission-v2 to v3, transfer-refinement-v2 unchanged. `packet_commit_parent` = S32, `subject_parent` = P31.
- Claim ceiling: canonical JSON of `claim_ceiling` at P31 and P32 is identical (`formal_core_complete=false`, every authority NONE, 0 of 12 value-movement gates). Nonclaims grew from 11 to 13; nothing was removed; the json and md carry the same two new lines.
- Eight THV1 packets (receipt-admission-v3, exact-ownership-v2, canonical-exact-admission-v3, certificate-v14, totality-v6, admission-v28, backing-v22, lineage-ordering-v1): every `source_pins` and `test_pins` sha256 recomputed from the worktree matches (6+1, 2+1, 3+2, 21+5, 9+2, 37+4, 9+3, 2+1 pins), `evidence_id` equals the file stem, and all 643 distinct node ids named in `test_pins.node_ids` and `mutations.killed_by` resolve under `pytest --collect-only` (three are parametrized bases, which pytest accepts).

## Claim verdicts

### 1. Isinstance class closed mechanically (Opus P28 F1, third site): CLOSED for the stated scope, PARTIAL for the "cannot regrow silently" strength

Evidence: a grep over the seven path modules finds exactly two surviving `isinstance` calls, both result discrimination on a closed `*RejectedV1` return (`asset_transfer_lane_module_v1.py:345`, `asset_transfer_receipt_admission_v1.py:243`), and the inventory test pins exactly those two keys. Mutation experiments (applied in the copy, named test run, file restored and sha-verified):

| Mutation | Named killer | Result |
| --- | --- | --- |
| post-state gate of `AssetLaneCompositionAcceptedV1` reverted to `isinstance` | inventory pin | killed |
| effects gate reverted to `isinstance` | inventory pin | killed |
| journal gate reverted to `isinstance` | inventory pin | killed |
| `AssetTransferRejectedV1.code` reverted to `isinstance` | inventory pin | killed |
| `ReceiptWitnessRejectedV1.detail` reverted to `isinstance` | inventory pin | killed |
| `LaneModuleReceiptEnvelopeV1.receipt_kind` reverted to `isinstance` | inventory pin | killed |
| producer entitlements tuple gate reverted to `isinstance` | inventory pin | killed |
| private-port gate reverted to `isinstance` (certificate-v14 killer) | `test_subclassed_private_port_with_a_spoofed_root_is_refused_at_construction` and the inventory pin | killed by both |
| post-state gate replaced by `issubclass(type(x), T)` | inventory pin + composition test | survived both |
| post-state gate replaced by `builtins.isinstance` | same | survived both |
| post-state gate replaced by `_exact = isinstance; _exact(...)` | same | survived both |
| post-state gate replaced by `match x: case T(): ...` | same | survived both |
| post-state gate replaced by `x.__class__ is not T` | same | survived both |
| post-state gate deleted | same | survived both (P2-1) |

Adding an isinstance gate anywhere on the seven modules fails the pin (seven distinct sites tried). The pin's key `(module, innermost enclosing definition, second-argument source)` is not evadable by moving the call between scopes, and set equality means any new site fails until licensed. It is evadable by every isinstance-equivalent that is not a bare-name `isinstance` call (P3-1).

### 2. Check (4) given work (Opus P28 F4): CLOSED

`VerifiedLaneAllocationFragmentV1.receipt_root` (`asset_transfer_receipt_admission_v1.py:156-159`) is populated from `journal.receipt_root` where `journal = owned.module_journal` and `owned` is the exact-typed snapshot rebuilt through `AssetTransferLaneModuleAcceptedV1(...)` (`asset_transfer_lane_module_v1.py:250-273`). Soundness chain: the rebuilt journal is the exact `LaneModuleTransitionJournalV1` with exact-`str` `receipt_root` (snapshot at lines 261-266); `journal_root` is a property hashing the canonical preimage that includes `receipt_root` (`global_economic_proof_v1.py:181-202`); check (2) requires that root to equal `witness.module_journal_root`; the witness is token-minted only by `_verify_rebound_module_receipt_v1` (`lane_module_receipt_verification_v1.py:329-371`) from the recomputed journal whose canonical bytes the succinct receipt was verified against; and the accepted constructor re-derives `receipt_root` from the statement root, lane roots, effect-plan root, and port root (`asset_transfer_lane_module_v1.py:186-249`). So the export is the rebuilt journal's root, bound to the receipt through the journal-root equality, and a forged witness cannot influence it beyond selecting which genuine journal it was minted for (and forging requires `object.__new__`, which the tests already use as the only way to vary a scalar). The producer's `binding_root=journal.receipt_root` is AST-pinned; mutating it to `committed` is killed; rebinding the local `journal` before the constructor evades the AST pin but is killed at runtime by check (4) (`test_receipt_admitted_fragment_carries_the_witness_binding`). Dropping the export (returning the journal root instead) is killed by `test_admitted_witness_exports_the_rebuilt_receipt_root`; populating it from `produced.binding_root` survives (P3-2).

### 3. Scoped F2 nonclaim: CLOSED

`_check_entitlement_rows` (`global_accounting_allocation_certificate_v1.py:684-691`) derives rows by folding every lane's `claimant_entitlements` by `(asset, claimant, control_domain)` (`derive_canonical_allocation_rows_v1`, lines 518-533) and requires the tuple `(asset, claimant, control_domain, amount)` to equal `state.liabilities` as `(asset, owner, custody_domain, amount)` exactly, else `ENTITLEMENT_ROWS_DRIFT`. It sits sixth in `CHECK_ORDER_V1` (line 811-824); an enabled ASSET_TRANSFER lane is rejected earlier at `BLOCKED_LANE_PRODUCER_MISSING` because the registry keeps it at `NO_PRODUCER` (line 99), so no acceptance path reaches the check today, exactly as the nonclaim states. The same wording is present in the admission module docstring, both producer docstrings (Python and Rust), the THV1 receipt-admission-v3 packet, and O-008 `NONCLAIMS_V1` (now 13 entries, count pinned at `tests/test_check_o008_formal_cycle_v1.py:1397-1398`). The second new nonclaim is factually accurate: `global_economic_proof_v1.py` still has 13 `isinstance` sites.

### 4. F5 family pin: CLOSED

`RECEIPT_WITNESS_REJECT_CODES_V1` (`asset_transfer_receipt_admission_v1.py:76-82`) equals the enum in order; dropping the last member is killed by `test_witness_reject_family_tuple_matches_the_enum`. Trivial but correct; the Rust twin it anticipates does not exist yet (declared nonclaim).

### 5. Hygiene ordering defect: CLOSED

Reproduction at repository scale in the copy, using the 59 critical paths the campaign-base run reports as `--changed-file M:<path>` arguments: with the P32 loader the gate returns ok with the nine expected packets; with the parent's loader (`git show a4258d989:tools/test_hygiene_evidence_v1.py`, `sorted(evidence_dir.glob("*.json"))`) it fails with `THV1-20260901-o008-formal-cycle-admission-v9: source sha256 drift for tools/check_o008_formal_cycle_v1.py`, which is precisely the reported class (a stale v9 packet whose pin for some changed path still matched, selected ahead of v28, then failing on another pin). Reverting the loader key to `path.name` is killed by `test_stale_lower_version_packet_cannot_shadow_a_newer_one`; changing the unversioned sentinel from -1 to 0 is killed by `test_lineage_key_matches_the_o008_checker_key`. Both implementations use the identical regex `^(.*?)(?:-v([0-9]+))?(\.json)?$`; the repository loader keys on the file name and the O-008 checker on the blob path, which share one directory prefix, so relative order is the same.

Judgment on the rule: numeric ordering within a lineage is correct (the live corpus has `resource-bounds` unversioned then v2..v8, ordered as -1 < 2 < ... < 8). Two lineages differing only by date prefix are distinct lineages ordered by the prefix; the live case `THV1-20260901-...-canonical-exact-admission` (unversioned) versus `THV1-20260902-...-v2/-v3` resolves to v3 by date, and would resolve correctly for any honest date. Unversioned ranks below `-v1`. A renamed packet is refused: `collect_git_changed_paths` splits renames into `D` plus `A` and `_reject_packet_rewrites` rejects any non-`A` status under the evidence prefix; probed directly, `D:` and `M:` on a packet path both fail with "evidence packets are append-only" and `A:` passes. The append-only rule holds. Residual brittleness is P3-3.

## Findings

### P2-1 The composition-accepted subclass test cannot observe its own gate

- Where: `tests/core/test_global_settlement_fcis_exact_ownership_v1.py:418-446` (`test_asset_lane_composition_accepted_rejects_root_bearing_subclasses`); gate at `src/core/asset_lane_projection_v1.py:378-379`; declared killer in `tests/evidence/test_hygiene/THV1-20260830-global-settlement-exact-ownership-v2.json` mutation "admit a root-spoofing projection subclass into AssetLaneCompositionAcceptedV1".
- Why: the test passes `effects=_BehaviorBearingEffectPlan(...)`, a real subclass (line 94), and `lane_journal=object()`, and matches only `"exact typed value"`, a substring of all three gate messages. The effects gate raises first whenever the post-state gate does not, so the test passes with the post-state gate deleted.
- Reproduction: in a copy, delete lines 378-379 of `src/core/asset_lane_projection_v1.py`; run the named test and the inventory test; both pass (my `M4c` record). Replacing the gate with `issubclass(type(self.post_state), AssetLaneStateProjectionV1)` also passes both.
- Minimal fix (validated): change the match to `match="post-state must be the exact typed value"`; with the gate deleted the test then fails, with the gate intact it passes. Better: build the genuine `lane_journal` and `effects` through the coordinator fixture so the post-state gate is the only one that can fire, and add the same isolation to the effects and journal gates. Re-cut exact-ownership-v3.

### P3-1 The AST inventory is a literal-name pin, and its scope is narrower than the path

- Where: `tests/core/test_global_settlement_fcis_exact_ownership_v1.py:371-386` (`_isinstance_sites` matches `getattr(child.func, "id", None) == "isinstance"` only); scope list at lines 346-354.
- Evidence: five equivalent rewrites of the post-state gate survive the pin (`issubclass(type(x), T)`, `builtins.isinstance`, a local alias, a `match ... case T():` class pattern, `x.__class__ is not T`); `x.__class__` is additionally spoofable by a subclass property. The path also re-runs `isinstance(self.lane_id, LaneIdV1)` at `src/core/global_economic_proof_v1.py:178` (module journal validate, executed by the snapshot's `replace(accepted.module_journal)`) and `isinstance(item, Enum)` at `src/core/global_economic_refinement_snapshot_v1.py:45,54`; both are Enum-safe because member-bearing enums cannot be subclassed, but neither module is in the inventory.
- Minimal fix: add a positive pin per gate (assert the AST contains `Compare(Call(Name('type'), [x]), IsNot, Name(T))` for each of the licensed input gates), extend `_isinstance_sites` to `ast.Attribute` whose attr is `isinstance`/`issubclass`, `ast.MatchClass`, and `__class__` attribute reads, and either add the two transitive modules to the inventory with their Enum licences or state the seven-module scope in the packet claim. Reword "cannot regrow silently" to "cannot regrow as a bare isinstance call".

### P3-2 The receipt_root mutation is half-observable

- Where: `tests/evidence/test_hygiene/THV1-20260902-o008-asset-transfer-receipt-admission-v3.json` mutation "drop receipt_root from the minted witness or populate it before check (4)"; test at `tests/core/test_asset_transfer_receipt_admission_v1.py:448-457`.
- Evidence: replacing `receipt_root=journal.receipt_root` with `receipt_root=produced.binding_root` survives the named killer because check (4) already made them equal. The "drop" half is killed.
- Minimal fix: split the mutation into the killed half and either delete the unobservable half or make it observable with the drifted-producer monkeypatch already used at lines 460-475 (assert that a drifted producer yields the reject and never a witness carrying the drifted root).

### P3-3 Selection is still first-match-then-all-pins-current

- Where: `tools/check_test_hygiene_v1.py:106-142` (`_select_packet` returns on the first packet whose pin for the path is current and then requires every pin of that packet to be current, raising otherwise).
- Evidence: cross-lineage order is name order (date prefix first), so a later-named lineage with one current pin and one stale pin turns the gate red for that path even when an older fully current packet exists. This is fail-closed (spurious red, never a false green: a green result always names a packet whose every pin matches current bytes) and is the same shape the P31 defect had one level up. Also, the key relies on the naming convention; a lineage whose stem legitimately ends in `-v<digits>` would be parsed as a version and `_EVIDENCE_ID_RE` does not forbid that.
- Minimal fix: either document the rule as intended (newest by name, must be fully current, cut a new version otherwise) in the loader docstring and the lineage-ordering packet, or iterate on to the next fully current packet and report the skipped stale one in the JSON. If the intent is recency, key on `created_date` then evidence id, and forbid stems ending in `-v[0-9]+` in `_EVIDENCE_ID_RE`.

## Known items confirmed, not re-graded

- `tests/core/test_asset_transfer_refinement_v1.py` fails collection (Opus P30 NEW-5).
- `replace()`-based re-validation at the transfer entry is shallow for nested rows (Fable/Opus P31); the snapshot helper's `isinstance(item, Enum)` acceptance for `kind/lane_id/receipt_kind/status` fields is the same family and is caught downstream by each row's own gate or by the canonical encoder's exact enum admission.
- The parity gate has no replay command (Opus P31 NEW-27); the unreachability lemma is not in CORE_CLAIMS (Opus P31 NEW-29).

## Nonclaims and ceiling

No production, release, settlement, verifier, migration, publication, or value-moving authority is granted or implied by this review. The claim ceiling at P32 is byte-identical to P31; `O008_RELATION_NECESSARY_CHECKS_AND_INFORMATION_LOSS_PROVED` remains the supported claim; ASSET_TRANSFER remains `NO_PRODUCER`; the admission witness is consumed on no acceptance path.

## Cleanup

`/tmp/zenodex-fable-review-c9app-cargo` and `/tmp/zenodex-fable-review-c9app-mut` were deleted after this report was written; the review worktree was left detached at P32 and clean. Reviewer-only records (mutation spec and results, node-id check, hygiene reports) are under the private subdirectory `fable-review-c9app` of the session scratch directory.
