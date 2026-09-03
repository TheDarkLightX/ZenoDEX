# Opus 5 independent review — ZenoDEX Formal Functional Core Closure, candidate C9b-1

| field | value |
|---|---|
| subject (S35) | `6c1950e1bfcd073bdcd5cdcea4c9a12994ad1a46` "security: land the Rust receipt-admission twin behind the pinned reject family" |
| subject parent (P34) | `a22633f153608809148cadf3983ee7dec9426dfb` |
| artifact (P35) | `3d235623244a6076e89ec029b02b95360f1620e4` (direct child of S35) |
| subject tree | `76a3ac20b75762a394fb07e6f7f63d5717fe8530` (matches packet `subject_tree`) |
| packet sha256 | `85bfb9b6a1ba03bfc96d19e89b141cdcdafa868999b81866d6f40b866dfb769d` (recomputed, matches the declared value) |
| packet markdown sha256 | `f5a1304b0f771d6ced786941a42fd8fe7267ac0c469d498a2ea0c76c2f1215a3` |
| branch | `codex/formal-core-fable-20260901` |
| worktree | `/tmp/zenodex-formal-core-opus-c9b1` (detached, clean at start and end) |
| reviewer | Opus 5, independent (did not author C9b-1) |
| date | 2026-09-03 |
| verdict | **REVISE** — grade **A-** |
| authority | unchanged: NONE on every axis; `formal_core_complete=false`; claim ceiling byte-identical to P34 |

ACCEPT/REVISE here is advisory. This review does not move any gate.

## 0. Scope and method

Reviewed exactly P35. The P34 dual review runs separately and is not folded in.
Every Lean-bearing command ran under `flock -w 7200 /tmp/zenodex-lean.lock`.
Cargo work used `CARGO_TARGET_DIR=/tmp/zenodex-opus-c9b1-cargo`, `CARGO_INCREMENTAL=0`.
The author worktree `/tmp/zenodex-formal-core-fable-20260901`, the canonical checkout, other
reviewers' worktrees, and the author scratchpad were never touched.

Mutation experiments applied edits to the review worktree, ran the named gate, and restored
the file from a byte copy; `git status --short` was empty before and after each.

## 1. Replay evidence (exact commands, exits, results)

All commands run from `/tmp/zenodex-formal-core-opus-c9b1` with
`PY="/home/trevormoc/Downloads/Autonomous Tau DEX/.venv/bin/python"`, `PYTHONDONTWRITEBYTECODE=1`.

| # | command | exit | result |
|---|---|---|---|
| 1 | `"$PY" tools/check_o008_formal_cycle_v1.py --root "$PWD" --packet-commit 3d23562…` | 0 | `ok=true`, `packet_admitted=true`, `current_source_drift=[]`, `errors=[]`, `proof_replay.status=NOT_RUN`, `runs=0` |
| 2 | same `--replay --esso-python /usr/bin/python3 --esso-pythonpath /home/trevormoc/Downloads/ESSO` | 0 | `ok=true`, `packet_admitted=true`, drift `[]`, `proof_replay.status=EXECUTED_PASS`, **31 runs, every `exit_code=0`** including the new `rust_admission_gate` |
| 3 | `cargo fmt --all -- --check` (in `zk/global_settlement_abi_v1`) | 0 | clean |
| 4 | `cargo clippy --locked --all-targets -- -D warnings` | 0 | no warnings |
| 5 | `cargo test --locked` (full crate) | 0 | every binary `test result: ok`, 0 failed; doc-test compile-fail case ok |
| 6 | `cargo test --offline --locked --test lane_module_release_route_binding receipt_admission_` | 0 | **4 passed; 0 failed; 67 filtered out** |
| 7 | `"$PY" -m pytest -q tests/core/test_asset_transfer_receipt_admission_v1.py` | 0 | 28 passed |
| 8 | `… tests/formal/test_lean_asset_transfer_refinement_v1.py` | 0 | 40 passed (run inside the replay as `transfer_refinement_gate`) |
| 9 | `… tests/core/test_transition_resource_bound_totality_v1.py` | 0 | 10 passed |
| 10 | `… tests/core/test_global_settlement_abi_v1_resource_bounds.py` | 0 | 17 passed |
| 11 | `… tests/core/test_global_settlement_abi_v1.py` | 0 | 75 passed |
| 12 | `… tests/test_check_o008_formal_cycle_v1.py` | 0 | **391 passed** in 241s |
| 13 | `… tests/test_check_global_settlement_canonical_manifest_v1.py` | 0 | 8 passed |
| 14 | `"$PY" tools/check_test_hygiene_v1.py --json` | 0 | `ok=true`, 0 findings |
| 15 | `… --base-ref a22633f15 --json` (parent of S35) | 0 | `ok=true`, 0 findings |
| 16 | `… --base-ref 42ccb6624 --json` | 0 | `ok=true`, 0 findings |
| 17 | `… --base-ref fd409ba6f7da8f0ec3e0220a04b7406d69a8cb85 --json` (campaign base) | 0 | `ok=true`, 0 findings |
| 18 | `… tests/formal/test_lean_global_claimant_custody_relation_v1.py` (under the lock, serially) | 0 | 6 passed |
| 19 | `… tests/formal/test_lean_global_accounting_allocation_certificate_v1.py` (under the lock, serially) | 0 | 6 passed |
| 20 | `tools/build_o008_formal_cycle_v1.py … --created-date 2026-09-02 --check --replay …` | **1** | drift on both artifact files — see **P3-3** |
| 21 | same with `--created-date 2026-09-03` | **0** | `{"drift":[],"mode":"check","ok":true}` — the artifact is byte-reproducible from S35 under a fresh replay |

**Fresh replay observation for the new 31st command** (from my own `--replay`, not the author record):

```json
{"command_id": "rust_admission_gate", "exit_code": 0, "comparable": {"passed": 4},
 "stdout_sha256": "0098d795c02606f92ce5efbe7743613b0b18189cca7dd99e5daaa44807731e3e",
 "stderr_sha256": "760966812eff31364ec54426132669cd1967abd8c93a64ef336cd4f72b058e18"}
```

`tests/core/test_zusd_liquidation_partition.py` was excluded (pre-existing unrelated collection error).

**Note (INFO-1).** The review prompt states the checker suite is 390 tests; the actual count at
P35 is **391**. S35 adds one `pytest.param` (`rust_admission_count`) to
`tests/test_check_o008_formal_cycle_v1.py:1337`, so 390 was the P34 number. Not a defect;
the campaign's expected-count note should be updated to 391.

## 2. Envelope and pin verification

- **P35 is a clean artifact-only child.** `git diff --name-only S35 P35` returns exactly
  `docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.json` and `…V1.md`, matching the declared
  `packet_write_set` (both `"M"`). `packet_commit_parent` = S35. `subject_parent` = P34.
  `subject_tree` = `76a3ac20b75762a394fb07e6f7f63d5717fe8530` = `git rev-parse S35^{tree}`.
- **52 source pins**, up from 50 at P34; the two additions are exactly
  `zk/global_settlement_abi_v1/src/asset_transfer_receipt_admission.rs` (role
  `admission_rust_twin`) and `zk/global_settlement_abi_v1/tests/lane_module_release_route_binding.rs`
  (role `admission_rust_replay`). No other pin added, removed, or re-roled.
- **Recomputed both new pins independently**: sha256
  `fc860531273a5d8b8b38ec030a0ea00ace259ccbb07119d9b95167a2015459fb` and
  `d6189e4607fc7d59964d465ab6f97da15aa26ce9c692936e929822592a2a83ea`; git blobs
  `31f63dbcd8275962a7ca186f4797885acca7679d` and `2c909f2985761d8b68fe84cfe3fce0f92844ca1d`.
  All four match the packet JSON and the Markdown pin table.
- **All 71 source pins across the three THV1 packets recomputed from the working tree: 0 mismatches.**
- **Claim ceiling, nonclaims, completion_scope, v1_information_loss, required_sidecar are
  byte-identical to P34** (compared as sorted JSON). `formal_core_complete=false`;
  `production/release/settlement/verifier/migration/publication/value_movement_authority = NONE`;
  `value_movement_gates_closed = 0 / 12`; `whole_value_movement_safe=false`.
- **Lean certificate gate.** `tests/formal/test_lean_global_accounting_allocation_certificate_v1.py:34`
  moves `RUST_TWIN` from `f7452d9a…` to `eaf857b1a410367adc73de17f31e9576a62160c20e6d337e78e5858aa4babdaf`;
  I recomputed the file's sha256 and it matches. That pin bump is the gate's only change, and the
  pinned file's only change is 3 lines (`fn validate` → `pub(crate) fn validate` plus one comment).

## 3. Verdict on each C9b-1 claim

### 3.1 The Rust admission twin exists and is sealed — **CLOSED**

Verified positively, not by reading. I compiled a probe test outside the defining module
(`zk/global_settlement_abi_v1/tests/zz_opus_sealing_probe.rs`, deleted afterwards) that tried to
build both witnesses by struct literal and to deserialise the fragment witness:

```
error[E0451]: fields `fragment`, `module_journal_root`, `receipt_root`, `receipt_digest` and
  `expected_image_id` of struct `VerifiedLaneAllocationFragmentV1` are private
error[E0451]: fields `authenticated_command_binding_root`, `release_route_binding_root`,
  `expected_image_id`, `module_journal_root`, `module_journal_digest`, `statement_root`,
  `command_occurrence_id`, `receipt_digest` and `receipt_kind` of struct
  `VerifiedLaneModuleTransitionV1` are private
error[E0277]: the trait bound `VerifiedLaneAllocationFragmentV1: serde::Deserialize<'de>` is not
  satisfied
```

- All five fields of `VerifiedLaneAllocationFragmentV1`
  (`asset_transfer_receipt_admission.rs:111-117`) are private; derives are
  `Clone, Debug, Eq, PartialEq` only — no `Serialize`/`Deserialize`.
- Exactly **one** construction site in the crate (`asset_transfer_receipt_admission.rs:238`);
  `grep -rn "VerifiedLaneAllocationFragmentV1" --include=*.rs` shows no other literal.
- The module witness it consumes is equally sealed: all nine fields of
  `VerifiedLaneModuleTransitionV1` (`lane_module_receipt_verification.rs:105-115`) are private,
  no serde derives, one construction site (`lane_module_receipt_verification.rs:264`).
- The return type `AbiResultV1<Result<witness, AssetTransferFragmentAdmissionRejectedV1>>` is
  exactly as claimed: outer `Err` is the type boundary, inner `Err` the closed
  `Witness | Producer` union.
- **No ACCEPTED_INVALID through the admission.** `validate_admission_boundary_v1`
  (`asset_transfer_receipt_admission.rs:157-175`) calls `accepted.validate()?` first, and the
  producer's only `ACCEPTED_INVALID` branch (`global_accounting_lane_producers.rs:245`) fires on
  `accepted.validate().is_err()`. That branch is therefore unreachable through the admission.
  The equivalent Python path raises in the snapshot.

  I confirmed this by execution rather than by reading. A throwaway probe took the same forged
  value the existing boundary test uses (`private_port.module_release_id = root(5)`) and called
  the producer directly and then through the admission:

  ```
  producer alone            -> Err(ReceiptBackedProducerRejectCodeV1::ACCEPTED_INVALID)
  through the admission     -> Err(AbiErrorV1::InvalidBinding(
                                  "asset transfer lane module accepted output"))
  test result: ok. 1 passed
  ```

  So the value that *does* produce `ACCEPTED_INVALID` is intercepted as an outer `Err` and never
  surfaces as an inner reject. Claim holds in both languages, and holds by demonstration in Rust.
  The existing shipped test asserts only `is_err()` on that input; it does not check that the
  producer would otherwise have returned `ACCEPTED_INVALID`, so it does not by itself establish
  the interception. That is a strengthening opportunity, not a defect.

Verified non-issue: `journal.journal_root()?` runs before the kind check in Rust and after it in
Python, which would be a reject-precedence divergence if it could fail. It cannot:
`LaneModuleTransitionJournalV1::journal_root` (`proof.rs:125`) begins with `self.validate()?`, and
`accepted.validate()` has already validated the same journal, so the `?` is dead on this path.

**The single load-bearing binding really does reach the rows.** Both modules say check (2)
(journal-root equality) is "the one equality that binds the caller's value to the proof", and the
other four are defensive. I traced whether that one equality is actually sufficient to bind the
custody rows the producer folds, and it is:

```
witness.module_journal_root == journal.journal_root()          (check 2)
  journal.journal_root()  hashes  journal.private_port_root
  accepted.validate() requires    journal.private_port_root == private_port.port_root()
  private_port.port_root() hashes AssetLanePrivatePortV1 { …, post_state, … }
  the producer folds              accepted.private_port.post_state.custody
```

`accepted.validate()` is enforced at the boundary as an error, so the chain cannot be skipped.
A foreign `accepted` value would have to collide the journal root, and through it the private-port
root, to present different custody rows. The "one load-bearing check" framing is therefore accurate
rather than a shortcut.

### 3.2 Same check order and family as Python — **PARTIAL** (see P2-1)

Holds:
- the numbered order (0)…(4) is identical in both files;
- the five variants, the `ALL` array, the `as_str` wire strings, and the schema string agree;
- `tests/core/test_asset_transfer_receipt_admission_v1.py:498-527` pins the enum body order, the
  `ALL` order, the `as_str` arms, the schema literal, and the textual order of code identifiers
  and detail strings inside both function bodies.

Does not hold: the test pins the *textual order of the reject labels*, not the binding between
each label and the condition that guards it. See P2-1: a Rust check reorder survives.

### 3.3 Reachability stated honestly — **CLOSED**

The declared divergence is exactly what the code does. `ClaimantEntitlementRowV1::validate`
(`global_accounting_allocation_certificate.rs:342-347`) validates only the three tokens; it does
not check `amount_atoms`, and the admission validates the caller's `claimant_entitlements` slice
row-by-row without an ordering check (`validate_ordered` for entitlements lives inside
`LaneAllocationFragmentV1::validate`, which covers `prior_fragment` only). So non-canonical
ordering and zero amounts do reach the producer's `ENTITLEMENT_ROWS_NOT_CANONICAL`
(`global_accounting_lane_producers.rs`, "entitlement ordering" and "zero amount" details), while
the Python snapshot raises. The Rust module header
(`asset_transfer_receipt_admission.rs:27-36`) and the Python docstring
(`src/core/asset_transfer_receipt_admission_v1.py:55-61`) both state this in those terms.
Reachability of each code through minted Rust witnesses is stated correctly:
`WITNESS_JOURNAL_ROOT_DRIFT` is the only one exercised by a Rust test, and it is the only one a
minted witness can trigger.

Gap, not a contradiction: the **packet's** `nonclaims` are byte-identical to P34 and mention
neither the Rust twin nor this divergence (P3-1).

### 3.4 The four Rust tests, the replay command, and the count gate — **CLOSED**

- `cargo test --offline --locked --test lane_module_release_route_binding receipt_admission_`
  gives `4 passed; 0 failed; 67 filtered out`.
- **The filter cannot silently match fewer.** `_grade_observation`
  (`tools/o008_formal_cycle_admission_v1.py:4116`) routes `rust_admission_gate` to
  `_grade_cargo(obs, ADMISSION_RUST_GATE_EXPECTED_PASSED_V1)` with the constant fixed at 4
  (`:1091`), and `COMPARABLE_SCHEMA_V1` (`:3358`) carries the same 4. A renamed or dropped test
  changes the passed count and raises `REPLAY_PASSED_COUNT_DRIFT`; so does an added fifth.
  The source pin on the test file (`d6189e46…`) catches a same-count rename-and-replace.
- `RUST_CRATE_MODULES_V1` (`:2582`) lists `asset_transfer_receipt_admission`, and
  `src/lib.rs` declares and re-exports it.

### 3.5 Registry, consumers, authority — **CLOSED**

- `LANE_ALLOCATION_PRODUCER_REGISTRY_V1` keeps `ASSET_TRANSFER` at `NO_PRODUCER` in Rust
  (`global_accounting_allocation_certificate.rs:51-55`) and Python
  (`src/core/global_accounting_allocation_certificate_v1.py:99`), both blocked on
  "VM-04 wave B asset-transfer fragment producer".
- No consumer: `grep` for `VerifiedLaneAllocationFragmentV1` across `src/` and for
  `verify_asset_transfer_fragment_receipt_v1` across `zk/` outside the defining module and its
  tests returns nothing. Neither witness is read on any acceptance path.
- Claim ceiling unchanged and all authorities NONE (section 2).

## 4. Findings

### P2-1 — A declared mutation killer does not kill on the Rust half

**Where.** `tests/evidence/test_hygiene/THV1-20260902-o008-asset-transfer-receipt-admission-v6.json`
declares:

```json
{"description": "reorder a witness check or change a detail string in either the Python or the
  Rust admission",
 "killed_by": "tests/core/test_asset_transfer_receipt_admission_v1.py::test_witness_reject_family_and_check_order_match_the_rust_twin"}
```

The test (`tests/core/test_asset_transfer_receipt_admission_v1.py:498-527`) pins the **textual
order of the reject labels and detail strings** inside each function body. It does not pin which
condition guards which label. Reordering the checks while leaving the labels in place is therefore
invisible to it.

**Reproduction.** In `zk/global_settlement_abi_v1/src/asset_transfer_receipt_admission.rs:204-217`,
swap the two conditions and leave both reject blocks textually where they are:

```rust
if witness.command_occurrence_id() != &journal.command_occurrence_id {
    return Ok(Err(reject_witness(
        ReceiptWitnessRejectCodeV1::WITNESS_STATEMENT_ROOT_DRIFT, lane_root, "statement root")));
}
if witness.statement_root() != &accepted.statement_root {
    return Ok(Err(reject_witness(
        ReceiptWitnessRejectCodeV1::WITNESS_OCCURRENCE_DRIFT, lane_root, "command occurrence")));
}
```

Then:

```
pytest -q tests/core/test_asset_transfer_receipt_admission_v1.py   -> 28 passed
cargo test --locked                                               -> exit 0, 0 failed
```

The occurrence check now runs before the statement-root check and each drift reports the other's
code, and **nothing in either language fails**.

**The Python half of the same claim does hold.** Applying the mirror-image swap to
`src/core/asset_transfer_receipt_admission_v1.py:313-326` fails two tests:

```
FAILED …::test_defensive_witness_checks_have_forgery_witnesses[statement_root]
FAILED …::test_defensive_witness_checks_have_forgery_witnesses[occurrence]
2 failed, 26 passed
```

Python has a per-code forgery witness (built through `object.__new__`); Rust has no per-code
reject test, because its witness cannot be forged.

**Scope of the gap, measured.** I checked the neighbouring mutations so the finding is not
overstated:

| mutation | killed? | by what |
|---|---|---|
| swap the statement-root / occurrence conditions (Rust) | **no** | nothing |
| hoist the producer above every witness check (Rust) | yes | `receipt_admission_passes_producer_rejects_through_after_the_witness_binds` panics: "expected WITNESS_JOURNAL_ROOT_DRIFT, got Producer(… LANE_DISABLED …)" |
| move a reject block (changing label order) | yes | the pin test's family-order assertion |
| delete a check | yes | the pin test's family-order assertion |
| swap the kind / journal-root conditions | yes | `receipt_admission_rejects_a_witness_minted_for_another_occurrence` |

So the unkilled region is exactly the three codes that no minted Rust witness can trigger
(`WITNESS_KIND_DRIFT`, `WITNESS_STATEMENT_ROOT_DRIFT`, `WITNESS_OCCURRENCE_DRIFT`). No acceptance
path is affected, nothing consumes the witness, and authority is NONE — this is an
evidence-strength defect, not a soundness defect. It is P2 rather than P3 because the campaign's
own rule is that a declared killer must kill, and this one is declared over "either the Python or
the Rust admission".

**Minimal fix.** A Rust test cannot mint a witness that differs only in statement root or
occurrence: the journal preimage binds the receipt root, which binds the statement root, and the
module witness's fields are private to `lane_module_receipt_verification`, so even an in-module
test cannot forge one. So the honest repair is to narrow the claim, not to add an unwritable test:
change the v6 mutation to say "reorder a witness check or change a detail string in the **Python**
admission", and add a second entry stating that in Rust the code-to-condition binding for the three
forgery-only codes is pinned by the `admission_rust_twin` source pin alone. If a stronger gate is
wanted, extend the pin test to assert the guarded expression next to each label (for example that
the line above `WITNESS_STATEMENT_ROOT_DRIFT` matches `statement_root`), which would kill the swap
in both languages.

### P3-1 — The packet nonclaims never mention the Rust twin or its declared divergence

`docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.json` `nonclaims` is **byte-identical to P34** (13
entries, verified as sorted JSON). Its receipt-admission entry describes the C9a Python module
only. The divergence that C9b-1 introduces — the Python snapshot raises on non-canonical or
zero-amount entitlement rows where the Rust twin returns the producer's
`ENTITLEMENT_ROWS_NOT_CANONICAL` — is stated in
`zk/global_settlement_abi_v1/src/asset_transfer_receipt_admission.rs:33-36` and in
`src/core/asset_transfer_receipt_admission_v1.py:55-61`, but not in the packet. A reader of the
packet alone cannot learn that the twin exists or that its reject behaviour differs.

**Fix.** Add one nonclaim naming the twin and the entitlement divergence, in the same words the two
module docs already use.

### P3-2 — v31 attributes a mutation to a test that passes under it

`THV1-20260901-o008-formal-cycle-admission-v31.json` declares:

```json
{"description": "drop the rust_admission_gate replay command while keeping its grade branch",
 "killed_by": "tests/test_check_o008_formal_cycle_v1.py::test_closed_constants_are_internally_consistent"}
```

Deleting the `ReplayCommandV1("rust_admission_gate", …)` entry
(`tools/o008_formal_cycle_admission_v1.py:1569-1576`) while leaving the grade branch, the
constants, and the `COMPARABLE_SCHEMA_V1` row in place gives:

```
pytest -q tests/test_check_o008_formal_cycle_v1.py::test_closed_constants_are_internally_consistent
  -> 1 passed
```

The mutation **is** defended, twice over, just not by the named test. The rest of the same suite
kills it loudly:

```
pytest -q tests/test_check_o008_formal_cycle_v1.py
  -> 2 failed, 224 passed, 165 errors in 188.67s
```

and the packet checker refuses admission outright:

```
tools/check_o008_formal_cycle_v1.py --packet-commit 3d23562… ->
  ok=false, packet_admitted=false, exit_code=1,
  errors: EXECUTING_CORE_DRIFT (tools/o008_formal_cycle_admission_v1.py),
          REPLAY_COMMANDS_DRIFT ("differs from the closed command list", proof_replay.commands),
          REPLAY_RECORD_SHAPE ("one run per command in order")
```

So the risk is closed twice; only the attribution is wrong. By contrast the sibling entries are
correctly attributed. I checked each declared killer in the two new packets by applying the
mutation, running the named gate, and restoring:

| declared mutation | packet | named killer | verdict |
|---|---|---|---|
| drop the `rust_admission_gate` grade branch | v31 | `test_new_gate_observation_mutations_are_executed_fail` | **kills** (21 errors) |
| drop its `COMPARABLE_SCHEMA_V1` row | v31 | same | **kills** (21 errors) |
| mis-set its expected count 4 → 3 | v31 | same | **kills** (21 errors) |
| drop the `rust_admission_gate` replay command | v31 | `test_closed_constants_are_internally_consistent` | **does not kill** (1 passed) — killed elsewhere |
| rename a variant of the Rust reject family | v6 | `test_witness_reject_family_and_check_order_match_the_rust_twin` | **kills** (assert at line 513) |
| reorder two entries of the `ALL` array | v6 | same | **kills** (assert at line 515) |
| reorder a witness check (Python) | v6 | same suite | **kills** (2 failed via the forgery-witness tests) |
| reorder a witness check (Rust) | v6 | same | **does not kill** — see P2-1 |

**Fix.** Point `killed_by` at the packet-admission check (`REPLAY_COMMANDS_DRIFT`) instead of
`test_closed_constants_are_internally_consistent`.

### P3-3 — The recorded rebuild command does not reproduce the artifact

The builder command specified for this candidate uses `--created-date 2026-09-02`. Run exactly as
specified with `--check --replay`, it exits **1**:

```
{"drift":["docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.json",
          "docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.md"],
 "mode":"check","ok":false,"subject_commit":"6c1950e1bfcd073bdcd5cdcea4c9a12994ad1a46"}
```

Cause: the committed packet carries `created_date: "2026-09-03"`. P35 was committed
2026-09-02 23:39:03 -0400, which is 2026-09-03 UTC, so the artifact's own date is defensible — the
recorded command is what is stale. Regenerating with `--created-date 2026-09-03` and no `--replay`
leaves `proof_replay` as the **only** differing top-level key (the author record, which `--replay`
supplies); with `--created-date 2026-09-02` both `created_date` and `proof_replay` differ. The
checker does not bind `created_date` to the commit date, so packet admission is unaffected
(`ok=true`, `packet_admitted=true`).

**Confirmed by re-running the full check with the corrected date.** With
`--created-date 2026-09-03 --check --replay`, the builder exits **0**:

```
{"drift":[],"mode":"check","ok":true,"subject_commit":"6c1950e1bfcd073bdcd5cdcea4c9a12994ad1a46"}
```

So the date is the *sole* cause, and the stronger fact is worth stating plainly: **the committed
artifact is byte-reproducible from S35 by an independent reviewer under a fresh 31-command
replay**, including the author record. That is the outcome the candidate wanted; only the recorded
command is wrong.

**Fix.** Record `--created-date 2026-09-03` for C9b-1 in the handoff, or have the builder derive
the date from the packet commit.

### P3-4 — The sealing premise rests on an unpinned file with no compile-fail test

The admission's security argument is that `VerifiedLaneModuleTransitionV1` is "mintable only by
`verify_asset_transfer_lane_module_receipt_v1`". I confirmed that holds today (section 3.1). But
`zk/global_settlement_abi_v1/src/lane_module_receipt_verification.rs`, which defines that type, is
**not** a packet source pin — it appears in `tools/o008_formal_cycle_admission_v1.py:2610` only as a
module *name* inside `RUST_CRATE_MODULES_V1`, which pins the crate's module list, not the file's
bytes. And no test in the crate asserts the field privacy of either witness; the four
`receipt_admission_` tests exercise behaviour, not visibility.

Consequence: changing those nine fields to `pub` would make the module witness forgeable by any
crate consumer, break the twin's stated premise, and produce **no** pin drift and **no** failing
test. The same is true, one step weaker, for `VerifiedLaneAllocationFragmentV1`: its file is pinned,
so a visibility change is caught as drift at check time, but nothing states the property as a test.

**Fix.** Add `lane_module_receipt_verification.rs` to `SOURCE_PIN_ROLES_V1`, and add a
`compile_fail` doc-test on each witness asserting that an out-of-module struct literal does not
compile. The crate already uses that pattern
(`src/zdex_buyback_shadow_composer_v2.rs:50`, which the full `cargo test` run exercises as a
passing compile-fail doc-test).

### P3-5 — `RECEIPT_ADMISSION_SCHEMA_V1` binds nothing

`asset_transfer_receipt_admission.rs:56` and `src/core/asset_transfer_receipt_admission_v1.py:101`
both declare `"zenodex/asset-transfer-receipt-admission/v1"`. Neither is read anywhere: the only
consumer in the repository is the parity assertion at
`tests/core/test_asset_transfer_receipt_admission_v1.py:518`. The constant is not hashed into a
journal, a root, or either witness, so the "same schema string" parity is a declaration-only pin.
Presumably it is reserved for the C9b-2 registry flip.

**Fix.** One sentence in both module headers saying the schema string is reserved and binds no
value yet, so no reader mistakes the parity for a binding.

## 5. Adversarial probes that found nothing (bounded refutations)

These are recorded because a bounded negative result is evidence too.

| probe | result |
|---|---|
| Construct `VerifiedLaneAllocationFragmentV1` by struct literal from outside its module | refused, `E0451` on all five fields |
| Deserialise `VerifiedLaneAllocationFragmentV1` | refused, `E0277`: no `Deserialize` impl |
| Construct `VerifiedLaneModuleTransitionV1` from outside its module | refused, `E0451` on all nine fields |
| A second construction site for either witness anywhere in the crate | none (`grep` over `--include=*.rs`) |
| Reach the producer's `ACCEPTED_INVALID` through the admission | unreachable: the boundary runs `accepted.validate()?` and the producer's branch requires `accepted.validate().is_err()` |
| Reject-precedence divergence from `journal.journal_root()?` running earlier in Rust than in Python | none: `journal_root` begins with `self.validate()?` and `accepted.validate()` already validated the same journal, so the `?` is dead here |
| Time-of-check/time-of-use between the Rust boundary and the producer (Rust borrows the caller's values where Python passes rebuilt copies) | none: all field types are plain `String`/`Vec`/`u128`/enums with no interior mutability, and the shared `&` borrows forbid aliased mutation |
| `receipt_admission_` used as a substring filter matching unrelated tests | none: 4 matched, 67 filtered out; an added or dropped match trips `REPLAY_PASSED_COUNT_DRIFT` |
| A consumer of either witness on an acceptance path | none in `src/` or `zk/` outside the defining module and its tests |
| `include!` / `include_str!` / `macro_rules!` / `#[path]` in either newly pinned Rust file | none present |
| The pin test's `rust.split(anchor)` anchors matching more than once (which would silently scan the wrong region) | none: each of the two anchors occurs exactly once in the file |
| The pin test's `dict(...)` over `as_str` arms hiding a duplicate arm with a different wire string | not reachable: a duplicate match arm is an unreachable pattern, and `cargo clippy -D warnings` is part of the gate |
| A `Default` impl or other trait giving a back door into either witness | none: neither derives nor implements `Default`, `From`, or any deserialiser |

## 6. Grade and verdict

**Grade: A-. Verdict: REVISE** (advisory; authority stays NONE and the claim ceiling does not move).

What is genuinely strong here:

- the sealing is real and I proved it by compilation, not by reading;
- the boundary genuinely makes the producer's `ACCEPTED_INVALID` unreachable through both admissions;
- the reachability story is accurate down to which single code a minted Rust witness can trigger;
- the count gate on the new replay command is exact in both directions, and the packet checker
  rejects a dropped replay command outright;
- all 52 packet pins and all 71 THV1 pins recompute; the envelope is a clean artifact-only child;
- the full replay is `EXECUTED_PASS` at 31/31, hygiene is green at HEAD and at all three base refs,
  and `cargo fmt`/`clippy -D warnings`/`cargo test --locked` are clean;
- and the artifact rebuilds **byte-identically** from the subject commit under an independent fresh
  replay (`--check --replay` exits 0 with empty drift), which is the strongest reproducibility
  result available to this campaign.

Why not A: one declared mutation killer demonstrably does not kill over half its stated scope
(P2-1), a second is attributed to the wrong mechanism (P3-2), the packet's own nonclaims never
mention the twin this candidate is about (P3-1), the recorded rebuild command does not reproduce
the artifact (P3-3), and the premise the whole module rests on is pinned nowhere and tested nowhere
(P3-4). Every one of these is an evidence defect rather than a soundness defect: no acceptance path
changes, nothing consumes either witness, and the unkilled region is exactly the set of codes no
minted Rust witness can reach.

**Counts: 0 P1, 1 P2, 5 P3, 1 INFO.**

The 100% exit rule is untouched: 0 of 12 value-movement gates are closed, `formal_core_complete`
stays false, and every authority axis stays NONE.
