# Opus review P29 / C8-p11 — ZenoDEX Formal Functional Core Closure Campaign

| Field | Value |
| --- | --- |
| Subject (S29) | `22ee86783ea8c07145c6b780392353accc208530` "security: repair the Opus P27 review findings" |
| Subject parent | `42ccb6624c253afd2f6811c6e58f17ff5c8f83b7` (R25, committed Opus C9a receipt) |
| Subject tree | `0b3d2ab29089d8d52620339bd7a974f72ecc4252` |
| Artifact (P29) | `e5f8cd4231821dda1e9a44ae87c9cd5fc66076a8` "docs: freeze the O-008 formal-cycle packet at C8-p11" |
| Packet sha256 | `1c821881e3dd78caa45f5c9618ae888c9d66b0101754a2cc94b3c56d5adf95b1` |
| Branch | `codex/formal-core-fable-20260901` |
| Review worktree | `/tmp/zenodex-formal-core-opus-c8p11` (detached, `git status --short` empty at start and end) |
| Reviewer | Opus 5 (independent proof / refinement / authority reviewer) |
| Date | 2026-09-02 |
| Authority granted | **NONE** (advisory review; claim ceiling unmoved) |

**Verdict: REVISE — grade B-.** 1 P1, 1 P2, 2 P3.

The headline P1 from P27 (NEW-19) is genuinely closed, and its durable fix is the
strongest structural work in this candidate: I verified it bites in both
directions. But this candidate also ships one repair that does not work and
whose in-code comment asserts that it does, and it leaves a repository gate red
that was green at its own parent commit. Both are the same failure shape the P1
was about: a change lands, a machine-checked gate goes red, and nothing in the
candidate notices.

---

## 1. Environment and provenance

Worktree HEAD equals P29; `git status --short` was empty before any probe and
empty again after every probe was restored. `external/ESSO` and the eight
`lean-mathlib/.lake/packages` symlinks were in place.

Toolchain: Python `/home/trevormoc/Downloads/Autonomous Tau DEX/.venv/bin/python`,
`PYTHONDONTWRITEBYTECODE=1`, `CARGO_TARGET_DIR=/tmp/zenodex-opus-c8p11-cargo`,
`CARGO_INCREMENTAL=0`, ESSO via `/usr/bin/python3` with
`PYTHONPATH=/home/trevormoc/Downloads/ESSO`.

Commit-shape checks, all passing:

| Check | Result |
| --- | --- |
| `subject_parent` in packet vs `git rev-parse S29^` | `42ccb6624…` = `42ccb6624…` |
| `subject_tree` in packet vs `git rev-parse S29^{tree}` | `0b3d2ab29…` = `0b3d2ab29…` |
| P29 is a direct child of S29 | yes (`git rev-parse HEAD^` = S29) |
| P29 diff is artifact-only | yes, exactly `ZENODEX_O008_FORMAL_CYCLE_V1.{json,md}` |
| `packet_write_set` vs actual P29 diff | identical, both `M` |
| 47 `source_pins` sha256 recomputed from disk | 0 mismatches |
| 47 `source_pins` `git_blob` recomputed via `git hash-object` | 0 mismatches |

### Claim ceiling

Canonical-JSON sha256 of `claim_ceiling`, computed over three packets:

| Packet | claim_ceiling sha256 |
| --- | --- |
| `1dd572ba1` (C8-p10, the P27 subject packet) | `12c5b5f0cb3b2fd1ff8dd76304c18cd595f7b8dd833ebb621cc7571f561c738a` |
| `8d86d6248` (C9a, P28) | `12c5b5f0cb3b2fd1ff8dd76304c18cd595f7b8dd833ebb621cc7571f561c738a` |
| `e5f8cd423` (C8-p11, P29) | `12c5b5f0cb3b2fd1ff8dd76304c18cd595f7b8dd833ebb621cc7571f561c738a` |

**Byte-identical. The ceiling did not move.** Every authority field remains
`NONE`, `formal_core_complete` false, `value_movement_gates_closed` 0 of 12,
`o008_status` `OPEN_EXACT_ALL_12_RECONCILIATION_MISSING`.

---

## 2. Replays executed

```
$ "$PY" tools/check_o008_formal_cycle_v1.py --root "$PWD" \
    --packet-commit e5f8cd4231821dda1e9a44ae87c9cd5fc66076a8
exit 0 — ok true, packet_admitted true, current_source_drift [], errors [],
         proof_replay.status NOT_RUN, runs []
```

```
$ "$PY" tools/check_o008_formal_cycle_v1.py --root "$PWD" \
    --packet-commit e5f8cd4231821dda1e9a44ae87c9cd5fc66076a8 --replay \
    --esso-python /usr/bin/python3 --esso-pythonpath /home/trevormoc/Downloads/ESSO
exit 0 — ok true, packet_admitted true, current_source_drift [], errors [],
         proof_replay.status EXECUTED_PASS, runs 29, every command exit 0
```

The 29 commands ran in the recorded order with `transfer_refinement_gate` at
index 14 (the P27 durable fix), confirming the count moved 28 → 29.

Direct gate runs:

| Command | Result |
| --- | --- |
| `cargo fmt --all -- --check` (zk/global_settlement_abi_v1) | exit 0 |
| `cargo clippy --locked --all-targets -- -D warnings` | exit 0 |
| `cargo test --locked` | exit 0 |
| `tests/formal/test_lean_asset_transfer_refinement_v1.py` | 40 passed (expected 40) |
| `tests/core/test_transition_resource_bound_totality_v1.py` | 8 passed |
| `tests/core/test_global_settlement_abi_v1_resource_bounds.py` | 17 passed |
| `tests/test_check_o008_formal_cycle_v1.py` | 389 passed (expected 389) |
| `tests/core/test_global_accounting_lane_producers_v1.py` | 30 passed |
| `tests/core/test_asset_transfer_receipt_admission_v1.py` | 8 passed |
| `tests/formal/test_lean_global_claimant_custody_relation_v1.py` | 6 passed |
| `tests/formal/test_lean_global_accounting_allocation_certificate_v1.py` | 6 passed |
| `tools/check_test_hygiene_v1.py --json` | exit 0, ok true |
| `tools/check_test_hygiene_v1.py --base-ref 42ccb6624 --json` | **exit 1 — see NEW-25** |
| `tools/build_o008_formal_cycle_v1.py … --check --replay` | see §6 |

The two Lean gates were run strictly serially and never concurrently with any
other `lake env lean` process I started. Note an environmental hazard I
observed but did not cause: a second agent's replay
(`--root /tmp/zenodex-formal-core-fable-review-c8p11`, pid 1916656) was running
`lake env lean` and a mathlib `cache get` against the same shared
`/home/trevormoc/deps/mathlib4/.lake` tree while my replay was in flight. My
replay completed EXECUTED_PASS, so no corruption reached my evidence, but the
shared-olean SIGBUS hazard is real whenever two campaign worktrees replay at
once.

---

## 3. Verdicts on the P27 findings

### NEW-19 (P1) — **CLOSED**

All four artifacts moved in lock-step, and the durable fix is real.

**Is the scope-honest treatment sound?** Yes. The `guardPasses … = True` arm at
`lean-mathlib/Proofs/AssetTransferRefinementV1.lean:340` does not smuggle
anything, for three independent reasons:

1. The file's Scope section already excluded row finiteness *before* this
   change: "Row finiteness, the canonical row ordering, and zero-balance
   elision (`if post_atoms == 0: values.pop(...)`) are not modeled"
   (`AssetTransferRefinementV1.lean:24-26`). The new guard is consistent with a
   pre-existing, independently stated exclusion rather than an exclusion
   invented to accommodate it.
2. The file explicitly disclaims refinement: "No refinement between this model
   and the Python or Rust runtime is claimed" (`:84-86`). So an always-passing
   guard cannot make a false refinement claim true.
3. `rejectCode` is `firstFailing guardPasses allRejectCodes`, which returns the
   first code whose guard *fails*. A guard that is definitionally `True` can
   never be returned, so the constructor is inert rather than
   permission-granting. No existing theorem is weakened by it except the
   coverage theorem, which was explicitly weakened and annotated.

The weakened `report_vectors_cover_every_code`
(`AssetTransferRefinementV1Challenge.lean:213-224`) states the exclusion in its
own statement rather than hiding it in a comment, which is the honest form.

**Durable fix, verified in both directions.** This is the part I probed hardest,
since the P27 finding was precisely that the drift stayed green.

*Direction 1 — the lineage drifts.* I deleted the twelfth constructor
(line 149) in my worktree:

```
$ sed -i '149d' lean-mathlib/Proofs/AssetTransferRefinementV1.lean
$ "$PY" tools/check_o008_formal_cycle_v1.py --root "$PWD" --packet-commit e5f8cd423…
exit 1 — ok false, current_source_drift
         ["lean-mathlib/Proofs/AssetTransferRefinementV1.lean"]
```

and the replayed gate errors out too (the Lean build fails: `rfl` on
`allRejectCodes_length` and the `decide` instances no longer reduce). Restored.

*Direction 2 — the runtime grows and the lineage does not.* This is the exact
mutation the THV1 declares. I appended a thirteenth code to the live enum at
`src/core/asset_transfer_types_v1.py:45`:

```
$ sed -i '44a\    THIRTEENTH_CODE_V1 = "THIRTEENTH_CODE_V1"' src/core/asset_transfer_types_v1.py
$ "$PY" -m pytest -q tests/formal/test_lean_asset_transfer_refinement_v1.py \
    ::test_lean_guard_order_matches_python_enum_and_transition_source \
    ::test_report_reject_code_rows_match_python_enum
2 failed
```

Both fail because the gate imports the live `AssetTransferRejectCodeV1` and
compares it to the parsed Lean order and the report's `CODE` table
(`tests/formal/test_lean_asset_transfer_refinement_v1.py:496`, `:584`).
Restored.

So the drift class genuinely cannot stay green through a full replay any more:
the file pin catches an edit to the lineage, and the replayed gate catches
runtime growth that the lineage does not follow. The five new pinned roles
(`tools/o008_formal_cycle_admission_v1.py`, `SOURCE_PIN_ROLES_V1` and
`THV1_REQUIRED_PIN_PATHS_V1`) and the 29th replay command are all present, and
the grading is strict: `_grade_pytest` (`:3908`) demands an exact passed count,
`parse_pytest_summary_v1` (`:3792`) returns `None` if the last line contains
`failed` or `error`, and `:3984` rejects any non-zero exit or timeout.

One residual, filed as **NEW-22 (P3)** below: the unreachability that licenses
the coverage exemption is asserted in prose but never proved.

**Corpus treatment.** `tests/data/asset_transfer_refinement_v1.json` gained the
twelfth precedence entry and a second `unreachable_codes` row. The pattern is
pre-existing (`BALANCE_OVERFLOW` already had one), the case count is unchanged
at 37, and a whole-file JSON comparison against the parent shows only those two
fields differ semantically — the rest of the 2779/415 line diff is
reformatting. That is honest, though the reformatting makes the diff
unreviewable by eye.

**Fixture repair — sound, cannot mask a failing real gate.** The
`transfer_refinement_gate` row added to `_passing_observations`
(`tests/test_check_o008_formal_cycle_v1.py:1132`) is
`f"{core.TRANSFER_REFINEMENT_GATE_EXPECTED_PASSED_V1} passed in 1.00s\n"`,
which mirrors the real pytest summary shape and is derived from the same
constant `_grade_pytest` grades against. It cannot mask a real failure for two
reasons: these observations are synthetic inputs to the checker's own unit
tests and never reach the real replay path, and the real path rejects both a
non-zero exit and any summary line containing `failed`/`error` before the count
is even compared.

### NEW-20 (P3) — **NOT CLOSED**

The repair does not do what it says. `tests/core/test_global_settlement_abi_v1_resource_bounds.py:231`
reads:

```python
assert len(list(crate_src.rglob("*.rs"))) > len(list(crate_src.glob("*.rs")))
```

This re-derives both globs from the filesystem. It says nothing about the scan
actually used, which is a separate expression at line 205:

```python
rust_source = "\n".join(
    rust_file.read_text(encoding="utf-8") for rust_file in sorted(crate_src.rglob("*.rs"))
)
```

Reverting *the scan* leaves the suite green:

```
$ sed -i '205s/rglob/glob/' tests/core/test_global_settlement_abi_v1_resource_bounds.py
$ "$PY" -m pytest -q tests/core/test_global_settlement_abi_v1_resource_bounds.py
17 passed in 0.93s
```

The comment at `:229-230` — "reverting rglob to glob must fail here even while
the bound sets coincide" — is therefore false as written, and so is the commit
message's "Pin the crate-scan recursion structurally (NEW-20)". Filed as
**NEW-23 (P2)**, elevated above the original P3 because the candidate asserts a
closure it does not have.

Crate layout, for the record: 88 top-level `.rs` files, 90 recursive, the two
nested ones being `economic_command_authentication/{witness,types}.rs`, neither
of which currently declares a `MAX_` constant. That is exactly why the bound
sets coincide and why the original finding was P3.

### NEW-21 (P3) — **PARTIAL**

The declared class is closed and the killer works. The broader class the fix
was introduced to close is not.

*What is closed.* `src/core/asset_transfer_module_v1.py:305-312` now uses
`type(...) is not T` for all three inputs, and the subclass forgery is refused:

```
$ "$PY" -m pytest -q tests/core/test_transition_resource_bound_totality_v1.py::test_transfer_refuses_state_subclasses
1 passed
```

Reverting the three checks to `isinstance` makes that test fail, so the killer
is real (verified; restored).

*What remains.* The essential ingredient of the P27 witness was *skipping
`__post_init__`*, not *subclassing*. Exact-type checks close the subclass
vector but not same-type unvalidated instances, which `object.__new__` +
`object.__setattr__` (and `copy.copy` on a frozen dataclass) produce with
`type(x) is AssetTransferStateV1` exactly true. Under such a pre-state the
transition **accepts** and silently relabels an untouched row's custody domain:

| Probe | Forged pre-state balance rows | Outcome |
| --- | --- | --- |
| F1 | duplicate `(sender, USD)` rows | refused (`owned-and-custodied conservation mismatch`) |
| F2 | a zero-amount row | refused (`state must omit zero balances`) |
| F3 | `("aaa","USD","custody",100)` + valid sender row | **ACCEPTED**; post-state row is `("aaa","USD","accounts",100)` |
| F4 | rows in non-canonical order | **ACCEPTED**; post-state silently canonicalized |
| F5 | policies/supplies asset mismatch | refused (`must cover the same assets`) |

F1/F2/F5 are caught only incidentally, by the post-state constructor
re-running `__post_init__` inside `_accept_transfer`
(`asset_transfer_module_v1.py:247`) — not by any pre-state re-validation. F3
and F4 slip through because `_post_balances` discards the domain label when it
builds its working dict (`:77`) and hardcodes `ACCOUNT_CUSTODY_DOMAIN_V1` when
it rebuilds rows (`:92`). So 100 atoms labelled `custody` are laundered into
`accounts` by a transfer that never touches that row.

Severity is bounded honestly: this needs in-process arbitrary object
construction, and I confirmed no constructor-bypassing deserializer for
`AssetTransferStateV1` exists anywhere under `src/` (the only construction site
is `asset_transfer_module_v1.py:247`). It is defense-in-depth, not a live
protocol path. But the managed sibling — the stated model for this repair —
does go further, re-validating every field and row type
(`managed_asset_lifecycle_module_v1.py:279-390`), which is why the review note
asked whether exact-type alone suffices. It does not. Filed as **NEW-24 (P3)**.

### Honest reframing — **CONFIRMED**

`THV1-20260901-o008-formal-cycle-admission-v25.json` leads its `claim_scope`
with the C8-p11 paragraph and describes NEW-19 as "the transfer reject family
grew 11 to 12 at the PR #532 incorporation and the machine-checked refinement
lineage was left behind, red and invisible to the packet replay". That is drift
language, not deferral language. The word "deferred" survives in the packet
only in the older C8''''' paragraph, where it refers to a different item
(row-ceiling totalisation), and that usage is accurate.

---

## 4. THV1 packets, pins, and mutation killers

| Packet | Pins checked | Result |
| --- | --- | --- |
| `THV1-20260902-o008-transfer-refinement-v1.json` | 7 | all sha256 match |
| `THV1-20260901-o008-formal-cycle-admission-v25.json` | 40 | all sha256 match |
| `THV1-20260901-claimant-backing-guard-golden-v19.json` | 12 | all sha256 match |

All 17 `killed_by` node IDs across the new and updated packets collect under
pytest (verified by `--collect-only`). The closure digest re-pin in
`tools/check_global_settlement_canonical_manifest_v1.py:41`
(`ea34424c57fbbf539d2620cacac42a0e18db26d75d6be4ba1cde78400f463b36`) is
exercised green by
`tests/test_check_global_settlement_canonical_manifest_v1.py::test_repository_canonical_manifest_source_closure_passes`.

**Every declared mutation in the new THV1 actually kills.** I applied each
mutation, ran the named test, and restored:

| Declared mutation | Named killer | Applied mutation | Result |
| --- | --- | --- | --- |
| grow the reject family in the runtime without extending the Lean model | `…::test_lean_guard_order_matches_python_enum_and_transition_source` | added `THIRTEENTH_CODE_V1` to the live enum | **FAILED** ✓ |
| leave the report code table at the old cardinality | `…::test_report_reject_code_rows_match_python_enum` | same | **FAILED** ✓ |
| present the model-unreachable code as vector-covered | `…::test_report_covers_exactly_the_vector_table` | removed `- model_unreachable` from the assertion | **FAILED** ✓ |
| admit a `__post_init__`-skipping state subclass | `…::test_transfer_refuses_state_subclasses` | reverted exact-type to `isinstance` | **FAILED** ✓ |

The tree was clean (`git status --short` empty) after every restore.

---

## 5. Findings

### NEW-25 (P1) — the candidate leaves the repository test-hygiene gate red, and it was green at its own parent

`tools/check_test_hygiene_v1.py --base-ref 42ccb6624 --json` exits 1:

```
error: test sha256 drift for changed path tests/core/test_global_settlement_abi_v1_resource_bounds.py
```

The NEW-20 edit changed that file. It is a *critical path* under the Test
Hygiene Contract V1, and a packet does claim it — the newest,
`THV1-20260901-global-settlement-v1-resource-bounds-v7.json` — but that packet
pins the pre-change bytes. No `v8` was shipped. The checker's branch at
`tools/check_test_hygiene_v1.py:140` fires on exactly this: a claimed critical
path whose pinned sha256 is stale.

This is a regression introduced by this candidate, not a pre-existing red:

| Artifact | sha256 |
| --- | --- |
| file content at parent `42ccb6624` | `f923f12c2dda2666f63bf5cd27f2241e5a8a371064f932c4397036ad730d32fd` |
| `…resource-bounds-v7.json` pin | `f923f12c2dda2666f63bf5cd27f2241e5a8a371064f932c4397036ad730d32fd` |
| file content at P29 | `bd9f82ca4c59b7496129758d16ffe7f28242408e6a477afc2cd48e4ceead6251` |

The pin matched the parent exactly, so the gate was green at `42ccb6624` and is
red at P29. No packet anywhere in `tests/evidence/test_hygiene/` pins the
current bytes (I checked all seven `…resource-bounds*` packets).

The author clearly knew the workflow — three hygiene packets were shipped in
S29 (`backing-v19`, `admission-v25`, `transfer-refinement-v1`), and
`tests/core/test_transition_resource_bound_totality_v1.py`, the other test file
touched, *is* correctly re-pinned. Only this fourth path was missed.

Why the packet replay does not catch it: the O-008 packet's `hygiene_selection`
covers only the packet's own pinned paths, and
`tests/core/test_global_settlement_abi_v1_resource_bounds.py` is not among the
47 `source_pins`. The repository-wide contract covers *changed* paths, so a
changed critical test outside the packet's pin set escapes the packet and only
the repo gate sees it. That gap is itself worth noting: the candidate that was
built to close "a gate goes red and the packet stays green" reproduces that
exact shape one level out.

**Reproduction** (clean worktree at P29):

```
$ "$PY" tools/check_test_hygiene_v1.py --base-ref 42ccb6624 --json ; echo $?
error: test sha256 drift for changed path tests/core/test_global_settlement_abi_v1_resource_bounds.py
1
```

**Repair:** ship `THV1-20260901-global-settlement-v1-resource-bounds-v8.json`
pinning `bd9f82ca…` (and, if NEW-23 is fixed in the same round, pin the
corrected bytes instead). Consider adding the path to the O-008 packet's
`source_pins` so the packet replay sees this class directly.

### NEW-23 (P2) — the NEW-20 "structural pin" does not bind the scan, and the code says it does

Detail and reproduction in §3 above. `tests/core/test_global_settlement_abi_v1_resource_bounds.py:231`
asserts a property of the crate layout, not of the scan at `:205`; reverting the
scan to `glob` leaves 17/17 green. The comment at `:229-230` and the commit
message both claim the opposite.

**Repair:** bind the assertion to the scan itself, e.g.

```python
rust_files = sorted(crate_src.rglob("*.rs"))
rust_source = "\n".join(f.read_text(encoding="utf-8") for f in rust_files)
...
assert len(rust_files) > len(list(crate_src.glob("*.rs")))
```

Then the `glob` revert fails, because `rust_files` is the value the scan used.
Note this repair changes the file again and so must ship with the NEW-25
hygiene packet.

### NEW-22 (P3) — the coverage exemption's licence is asserted, never proved

`AssetTransferRefinementV1Challenge.lean:213-218` excuses
`postStateResourceBoundExceeded` from coverage on the stated ground that
"`rejectCode` can never return it". That ground is stated in a docstring and in
the guard note at `AssetTransferRefinementV1.lean:337-339`, but no theorem
asserts it. The file already owns the idiom — `balanceOverflow_unreachable`
(`:915`) is exactly an unreachability theorem — and the proof here is two lines
from machinery already present, since `rejectCode_eq_some_iff` (`:507`) gives
`rejectCode … = some c ↔ ¬ guardPasses … c ∧ …` and the guard is
definitionally `True`:

```lean
theorem rejectCode_ne_postStateResourceBoundExceeded
    (ctx : Context) (pre : TransferState) (cmd : Command) :
    rejectCode ctx pre cmd ≠ some .postStateResourceBoundExceeded := by
  intro h
  exact ((rejectCode_eq_some_iff ctx pre cmd _).mp h).1 trivial
```

As it stands, the exemption is unconditional on the constructor name, so if a
future edit gives that guard real content the coverage theorem will keep
exempting a now-reachable code and nothing will notice. Proving the lemma and
citing it in the challenge docstring converts a prose licence into a
machine-checked one.

### NEW-24 (P3) — exact-type does not close the `__post_init__`-skipping class it was introduced to close

Detail, probe table, and mechanism in §3 above. The sharp witness is F3: a
forged pre-state carrying `EconomicAmountV1("aaa","USD","custody",100)` is
accepted, and the post-state relabels that untouched row to `"accounts"`,
because `_post_balances` drops the domain at
`src/core/asset_transfer_module_v1.py:77` and hardcodes it at `:92`. F4 shows
the same for canonical ordering, which additionally means the emitted
`LaneWriteV1` binds a `pre_lane_root` (`:233`) that no constructible state
could produce.

Bounded honestly: reachable only with in-process arbitrary object construction;
no constructor-bypassing deserializer for this type exists under `src/`.

**Repair options, in increasing cost:** re-snapshot the pre-state through the
dataclass constructor at entry (one line, re-runs `__post_init__` and refuses
F1–F5 uniformly); or adopt the managed sibling's per-field re-validation; or,
narrowest, make `_post_balances` carry each row's `custody_domain` through
instead of hardcoding it, so a non-`accounts` row cannot be relabelled.

---

## 6. Builder regeneration

```
$ "$PY" tools/build_o008_formal_cycle_v1.py --root "$PWD" \
    --subject-commit 22ee86783ea8c07145c6b780392353accc208530 \
    --created-date 2026-09-02 --check --replay \
    --esso-python /usr/bin/python3 --esso-pythonpath /home/trevormoc/Downloads/ESSO \
    --output-json docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.json \
    --output-md docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.md
exit 0
{"drift":[],"mode":"check","ok":true,"subject_commit":"22ee86783ea8c07145c6b780392353accc208530"}
```

`git status --short` immediately after the regeneration was **empty**. The
builder rewrote both packet files from the subject commit and produced bytes
identical to the committed P29 artifact, including the 29-command replay record
and the author record. That is the strongest determinism result available here:
the artifact is reproducible from S29 alone, and the committed packet is
exactly the projection the builder computes.

---

## 7. What I did not re-grade

The C9a findings F1–F5 (receipt R25) are being repaired in S30/P30 and were out
of scope here. None of the C8-p11 repairs makes any of them worse: this
candidate touches the transfer-refinement lineage, the crate-scan assertion,
the transfer transition's input typing, and three hygiene packets, and none of
those surfaces overlaps the C9a receipt-admission fragment.

## 8. Authority statement

This review grants no authority. Authority remains NONE across production,
release, settlement, verifier, migration, publication, and value movement. The
claim ceiling is byte-identical to the P27 and P28 packets and must stay there.
ACCEPT would be advisory in any case; this review returns REVISE.
