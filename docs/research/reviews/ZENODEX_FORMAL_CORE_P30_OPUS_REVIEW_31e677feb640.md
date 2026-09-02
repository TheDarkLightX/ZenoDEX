# Opus independent review — candidate C9a'

| | |
|---|---|
| **Subject** | `S30 = fe5a6de6fa994704cc3387b582525650417c2ad3` ("security: repair the Opus P28 review findings") |
| **Artifact** | `P30 = 31e677feb640bf1b577bf38750c1b8b5e8e3cd92` ("docs: freeze the O-008 formal-cycle packet at C9a'") |
| **Parent chain** | `P29 e5f8cd423` → `S30 fe5a6de6f` → `P30 31e677feb` (P30 is a direct child of S30) |
| **Branch** | `codex/formal-core-fable-20260901` |
| **Review worktree** | `/tmp/zenodex-formal-core-opus-c9ap` (detached at P30, `git status --short` empty at start and at end) |
| **Packet sha256** | `2eb993461e232dcd6ef64ff8f4aca5c7e297645042d2f098816855acbfdf3a50` (matches the declared value) |
| **Prior review** | R25 `42ccb6624` = P28 Opus review, grade C+, REJECT_PENDING_REPAIR |
| **Reviewer** | independent Opus; authority NONE; ACCEPT is advisory; the claim ceiling does not move |
| **Date** | 2026-09-02 |

---

## Verdict

**Grade: A−. ACCEPT (advisory).**

All five P28 findings are closed, and closed with behavioural evidence rather than
assertion. I re-ran both P28 proofs of concept against P30 and both are refused at the
type boundary. I deleted each of the five witness checks in turn and each deletion now
fails a named test — the three arms that had zero evidence at P28 now have forgery
witnesses that actually kill. I verified all 90 pin hashes across the five new packets,
resolved all 603 pinned node ids, and applied every one of the ten genuinely new
mutation killers by hand. The canonical-admission count repair (92/30 → 104/35) is
honest: I recounted the manifest independently and confirmed the old assertion was red
at P29. The claim ceiling is byte-identical to P29 and every authority remains NONE.

It is not an A for three reasons, in descending weight. The `object.__new__` witness
forgery that defeats the packet's headline invariant is declared in no nonclaim, and the
one packet line that made the technique visible was removed by this candidate;
the value it yields is also the one type on this path with no construction invariants, so
the minted `VerifiedLaneAllocationFragmentV1` will carry `receipt_digest=None` verbatim.
The repair introduced one new gate with no test (`lane_root`). One declared mutation
killer is half-demonstrated (the port's `pre_state` gate). It is not lower because the
central property the candidate exists to establish is now true as implemented against
every construction-legal caller, the containment story still holds exactly (registry
`NO_PRODUCER`, zero consumers), and I could not falsify the repaired binding by any means
short of that forgery primitive, which this candidate did not introduce.

**Findings: 0 × P1, 1 × P2, 4 × P3, 7 × INFO. All five P28 findings CLOSED.**

---

## Replay results

| Gate | Command | Result |
|---|---|---|
| Packet check (no replay) | `check_o008_formal_cycle_v1.py --root "$PWD" --packet-commit 31e677feb…` | exit 0; `ok: true`, `packet_admitted: true`, `current_source_drift: []`, `errors: []`, `proof_replay.status = NOT_RUN`, stderr empty |
| Packet check (`--replay`) | `… --replay --esso-python /usr/bin/python3 --esso-pythonpath /home/trevormoc/Downloads/ESSO` | exit 0; `ok: true`, `packet_admitted: true`, `current_source_drift: []`, `errors: []`, **`proof_replay.status = EXECUTED_PASS`, 29 runs, all exit 0**, stderr empty |
| Builder (`--check --replay`) | `build_o008_formal_cycle_v1.py --root "$PWD" --subject-commit fe5a6de6f… --created-date 2026-09-02 --check --replay …` | exit 0; `{"drift":[],"mode":"check","ok":true,"subject_commit":"fe5a6de6…"}`, stderr empty; worktree clean after the run (the regenerated packet is byte-identical to the committed one) |
| `cargo fmt --all -- --check` | in `zk/global_settlement_abi_v1` | exit 0, no output |
| `cargo clippy --locked --all-targets -- -D warnings` | same | exit 0 |
| `cargo test --locked` | same | exit 0; **527 passed, 0 failed**, no `FAILED`/`panicked` lines across 54 test binaries |
| Python suites (7 named files) | `pytest -q tests/core/test_asset_transfer_receipt_admission_v1.py tests/core/test_global_accounting_lane_producers_v1.py tests/core/test_asset_transfer_lane_module_v1.py tests/core/test_global_settlement_abi_v1.py tests/core/test_global_settlement_canonical_admission_v1.py tests/test_check_global_settlement_canonical_manifest_v1.py tests/test_check_o008_formal_cycle_v1.py` | **535 passed** in 267.74s |
| Remaining pinned non-Lean suites | `pytest -q tests/core/test_global_accounting_allocation_certificate_v1_golden.py tests/core/test_global_claimant_backing_guard_v1_golden.py tests/test_accounting_source_classification_contract_v1.py tests/test_o008_v1_projection_runtime_gate.py` | **90 passed** |
| Pinned ESSO suites | same two files with `ZENO_ESSO_PYTHON=/usr/bin/python3 PYTHONPATH=/home/trevormoc/Downloads/ESSO:.` | **44 passed** in 66.19s |
| Manifest checker | `tools/check_global_settlement_canonical_manifest_v1.py` | exit 0, `global-settlement canonical manifest: PASS` |
| Test hygiene | `tools/check_test_hygiene_v1.py --json` | exit 0, `ok: true`, `changed_path_count: 0` |
| Test hygiene vs P29 | `… --base-ref e5f8cd4231821dda1e9a44ae87c9cd5fc66076a8 --json` | exit 0, `ok: true`, 16 changed paths, **9/9 critical paths covered** |
| Lean gates (serial) | `pytest -q tests/formal/test_lean_global_claimant_custody_relation_v1.py` then `pytest -q tests/formal/test_lean_global_accounting_allocation_certificate_v1.py` | exit 0 / exit 0; **6 passed** and **6 passed** |

`tests/core/test_zusd_liquidation_partition.py` is excluded as instructed (pre-existing
`ModuleNotFoundError` on a gitignored generated module). The ESSO gates are fail-closed
on a missing interpreter (`RuntimeError: ESSO is unavailable; set ZENO_ESSO_PYTHON`)
rather than skipping — correct behaviour, not a defect; the 31 failures I first saw were
entirely that missing environment variable and all clear once it is set.

A second, **undeclared** pre-existing red is recorded as NEW-5 below.

**A note on the replay, because the numbers matter.** My first `--replay` attempt ran
concurrently with another reviewer's replay of the same packet and returned
`EXECUTED_FAIL`: 26 of 29 runs exit 0, and exactly three Lean runs died —
`lean_version` timed out, `lean_direct_check` exit 139 (SIGSEGV), `lean_axioms_probe`
exit 135 (SIGBUS). That is the documented shared-mathlib-olean hazard, not a candidate
defect. Re-run alone, the same command is clean. I am recording the clean run as the
result and this paragraph as the reason there were two.

---

## The five P28 findings

### F1 — HIGH — subclass-minted fragment contradicting the receipt — **CLOSED**

Both P28 proofs of concept, re-run verbatim against P30 with `PYTHONPATH=.` from the
review worktree:

```
$ python /tmp/zenodex-opus-c9a-poc.py
  File ".../src/core/asset_lane_projection_v1.py", line 213, in __post_init__
TypeError: asset lane port post-state must be the exact typed value

$ python /tmp/zenodex-opus-c9a-poc2.py
  File ".../src/core/asset_transfer_lane_module_v1.py", line 217, in __post_init__
TypeError: asset transfer lane module private port must be the exact typed value
```

Both are refused at construction, before any binding is read. The five declared
exact-type gates are all present and all load-bearing:

| Gate | Location | Mutation → `isinstance` |
|---|---|---|
| accepted private port | `src/core/asset_transfer_lane_module_v1.py:216` | KILLED by `test_subclassed_private_port_with_a_spoofed_root_is_refused_at_construction` |
| port `post_state` projection | `src/core/asset_lane_projection_v1.py:212` | KILLED by `test_subclassed_projection_is_refused_by_the_port_gate` |
| port `pre_state` projection | `src/core/asset_lane_projection_v1.py:210` | **survives the named test** — see NEW-3 |
| accepted journal | `src/core/asset_transfer_types_v1.py:226` | KILLED by `test_subclassed_journal_with_a_spoofed_journal_root_is_refused` |
| accepted state / effects | `src/core/asset_transfer_types_v1.py:220,224` | KILLED (whole `tests/core` suite) |
| projection sources | `src/core/asset_lane_projection_v1.py:165,183` | KILLED (whole `tests/core` suite) |

Check (0), the exact-typed snapshot, is genuinely load-bearing rather than decorative.
Replacing `owned = _snapshot_asset_transfer_lane_module_accepted_v1(accepted)` with
`owned = accepted` fails three named tests at once
(`test_planted_subclass_port_is_refused_by_the_admission_snapshot`,
`test_validation_bypassed_accepted_is_refused_by_the_snapshot`,
`test_subclassed_journal_with_a_spoofed_journal_root_is_refused`). The snapshot is not
merely a type check: it rebuilds every nested value through the public constructors, so
every construction invariant re-runs on the rebuilt value, and — decisively — it
recomputes `port_root` from the port's actual content, which is what defeats the P28
attack rather than the type gate alone.

**Class audit.** I hunted for any remaining root-bearing value on the accepted path
admitted by `isinstance` or by a duck-typed method, and for any way to reach the
producer with a value the snapshot did not rebuild. Twelve probes
(`/tmp/zenodex-c9ap-hunt.py`, `hunt4.py`):

| Probe | Result |
|---|---|
| tuple subclass entitlements with a stateful `__iter__` (honest for four passes, foreign on the fifth) | contained — reject value `FRAGMENT_INVALID` |
| `object.__new__` `prior_fragment` with a foreign `lane_state_root` | reject `STALE_JOURNAL` (pre root) |
| `object.__new__` `prior_fragment` with a non-tuple `controlled_locations` | admitted, but nothing of it reaches the output — see INFO-1 |
| `object.__new__` `lane_root` with a non-`str` `state_root` | `TypeError` from the producer |
| `str` subclass with a lying `__eq__` inside an entitlement row | refused at row construction (`_require_token` is exact) |
| `bool` as `amount_atoms` | refused at row construction |
| entitlements exceeding the receipt-proved total | reject `ENTITLEMENT_COVERAGE_DRIFT` |
| `GlobalEconomicEffectPlanV1` subclass planted into `accepted.effects` | refused by the snapshot |
| `EconomicAmountV1` subclass planted into the port's custody rows | refused by the snapshot |

I could not reach a `VerifiedLaneAllocationFragmentV1` whose fragment contradicts the
receipt by any route. The one remaining route is `object.__new__` on the module witness
itself, which the candidate's own tests use openly — and which, contrary to how P28
characterised it, is not declared anywhere. See NEW-1.

**Raising vs returning a reject.** Consistent with the path's contract. The function
already raised `TypeError` for its witness type gate before this candidate, and
`produce_asset_transfer_fragment_v1` raises `TypeError` for all four of its exact-type
gates. The docstring now states the rule explicitly ("the type-boundary refusals of (0)
raise, as every type boundary on this path does") and separately preserves "every
witness reject is a value". Both claims are true of the code. The one wrinkle is
recorded as INFO-5.

**`asset_transfer_types_v2.py`.** The premise in my brief is not true at P30: that file
contains **zero** `isinstance` calls and uses exact `type(...) is not` gates throughout
(lines 73, 75, 122, 129, 341, 411, 426, 439, 452, 476 …). There is no v2 scoping
question to judge.

### F2 — MEDIUM — claimant entitlements undeclared as a nonclaim — **CLOSED**

The nonclaim appears, in materially identical wording, in all five declared places: the
THV1 packet `nonclaims[0]`, a dedicated `NONCLAIMS` block in the admission module
docstring, both producer docstrings (Python `global_accounting_lane_producers_v1.py:226`
and Rust `global_accounting_lane_producers.rs:227`), and the pin test. The wording is
precise about *both* dimensions I raised — claimant identity **and** the split between
claimants — and correctly scopes the coverage to the `(asset, control_domain)` total.

The pin is honest rather than legitimising. `test_claimant_identity_is_not_bound_by_the_receipt_until_c9b`
demonstrates the hole rather than papering over it: it asserts that an entitlement
naming `attacker` is admitted for the custodian's receipt-proved 100 atoms, and asserts
in the same breath that `controlled_locations` still names `custodian`. Its docstring
says C9b must invert it. Mutating the coverage key to include the claimant kills it, so
the current semantics are locked. See INFO-3 for the one limitation.

### F3 — MEDIUM — three witness reject codes with no behavioural evidence — **CLOSED**

Deleting each check block in turn from
`src/core/asset_transfer_receipt_admission_v1.py` and running the named test:

| Deleted check | Named test | Result |
|---|---|---|
| (1) `WITNESS_KIND_DRIFT` | `test_defensive_witness_checks_have_forgery_witnesses` | **KILLED** (1 failed, 2 passed) |
| (2) `WITNESS_JOURNAL_ROOT_DRIFT` | `test_foreign_accepted_value_is_rejected_at_the_journal_root` | **KILLED** |
| (3a) `WITNESS_STATEMENT_ROOT_DRIFT` | `test_defensive_witness_checks_have_forgery_witnesses` | **KILLED** |
| (3b) `WITNESS_OCCURRENCE_DRIFT` | `test_defensive_witness_checks_have_forgery_witnesses` | **KILLED** |
| (4) `WITNESS_BINDING_ROOT_DRIFT` | `test_binding_root_drift_is_producer_drift_protection` | **KILLED** |

At P28 the first, fourth and fifth of these survived deletion with all 8 tests green.
The forged-witness technique (`object.__new__` + `replace(witness._fields, …)`) and the
monkeypatched drifted producer are the right witnesses: they are the only constructions
that can vary the quantity under test while holding the journal root fixed, and the test
docstrings say exactly that.

### F4 — LOW — check (4) mislabelled — **CLOSED**

The module docstring, the packet `claim_scope`, and the packet boundary point now all
describe check (4) as "defensive producer-drift protection … the witness carries no
receipt root, so this binds nothing to the witness". I verified the wording against the
code: `produced.binding_root` is compared with `journal.receipt_root`, and the producer
assigns `binding_root=journal.receipt_root` from that same journal, so only a drifted
producer can make them differ. The claim "the witness carries no receipt root" is
accurate — `VerifiedLaneModuleTransitionV1` exposes `binding_root`, but that is a hash
over the witness's own scalars (`hash_global_v1("verified-lane-module-transition-v1", …)`),
not the module journal's `receipt_root`. Wording matches the code. See INFO-3 on the
name collision.

### F5 — INFO — stale forward references and no Rust twin — **CLOSED**

Both producer docstrings are present tense at P30 (Python: "receipt admission lives one
layer up in `asset_transfer_receipt_admission_v1` (C9a), which takes the module witness
… and re-runs this producer on it"; Rust: "the Python authority admits fragments one
layer up"). The missing Rust twin is recorded both as a packet nonclaim and as a
declared open gap for C9b, and the Rust side's compensating control (the producer
validates `accepted` at its check 0) is named.

---

## Packet integrity

**Pins.** All 90 `source_pins` + `test_pins` sha256 values across the five packets match
the worktree bytes exactly (0 mismatches, 0 missing files).

| Packet | pins | node ids | mutations |
|---|---|---|---|
| `THV1-20260902-o008-asset-transfer-receipt-admission-v2` | 7 | 16 | 15 |
| `THV1-20260901-o008-formal-cycle-admission-v26` | 40 | 428 | 103 |
| `THV1-20260901-global-accounting-allocation-certificate-v13` | 26 | 117 | 59 |
| `THV1-20260901-claimant-backing-guard-golden-v20` | 12 | 48 | 13 |
| `THV1-20260902-global-settlement-v1-canonical-exact-admission-v2` | 5 | 16 | 7 |

**Node ids.** All 603 unique pinned node ids resolve against pytest collection (603
collected across the 13 pinned files, exact set match under `LC_ALL=C`). Three are
pinned by base id for a parametrized test
(`test_defensive_witness_checks_have_forgery_witnesses`,
`test_producer_rejects_pass_through_unchanged`,
`test_canonical_bytes_and_roots_match_exact_base_goldens`); pytest accepts the base id as
a selector, so they resolve, though other packets pin parametrized ids with the
parameter included. All 603 pass across my runs: 11 of the 13 pinned files in the
Python, golden and ESSO batches above, and the two `tests/formal/test_lean_*` files in
the serial Lean gates (6 + 6 passed).

**Mutation killers.** Diffing each packet against its immediate predecessor version
isolates ten genuinely new killers (nine in receipt-admission-v2, one in
certificate-v13); the other 187 are carried forward unchanged from previously reviewed
versions. I applied every new one by hand, ran the named test, and restored:

| # | Declared mutation | Result |
|---|---|---|
| 1 | admit a subclassed private port reporting a spoofed port root at construction | KILLED |
| 2 | drop the exact-typed snapshot before the binding | KILLED (3 tests) |
| 3 | loosen the port's projection gates back to `isinstance` | **PARTIAL** — post_state KILLED, pre_state SURVIVES (NEW-3) |
| 4 | loosen the accepted journal gate back to `isinstance` | KILLED |
| 5 | skip re-validation of a validation-bypassed accepted value | KILLED |
| 6 | delete the witness-kind, statement-root, or occurrence check | KILLED (all three) |
| 7 | delete the binding-root check | KILLED |
| 8 | emit foreign controlled rows for a receipt-proved custody row | KILLED |
| 9 | silently change claimant coverage semantics before C9b | KILLED |
| 10 | loosen a root-bearing nested-value gate on the accepted path (certificate-v13) | KILLED |

**Claim ceiling.** Byte-identical to P29 under `json.dumps(..., sort_keys=True)`. Every
authority is `NONE`; `formal_core_complete: false`;
`o008_status: OPEN_EXACT_ALL_12_RECONCILIATION_MISSING`;
`value_movement_gates_closed: 0 / 12`. The only changed top-level packet keys are
`subject_commit`, `subject_parent`, `subject_tree`, `packet_commit_parent`,
`source_pins` (two entries: the two producer files) and `hygiene_selection` (v25→v26,
receipt-admission v1→v2, plus the new canonical-exact-admission-v2 row). That is exactly
the declared admission envelope.

**Artifact envelope.** P30's complete diff against S30 is the two packet files and
nothing else; `packet_write_set` declares exactly those two paths; P30's parent is S30.

**Canonical-admission count repair.** Honest. I recounted the manifest independently:
104 serializer types and 35 enum types, sorted, unique, and disjoint. I then restored
the P29 version of the test and confirmed it was genuinely red
(`AssertionError: assert 104 == 92`), so the claim that it was red since C8 S17 is
supported at least for the P29 boundary.

**Canonical closure digest re-pin.** `EXPECTED_SOURCE_CLOSURE_SHA256_V1` moves from
`ea34424c…` to `9d761af4…` in `tools/check_global_settlement_canonical_manifest_v1.py`.
The digest is recomputed by the checker from the actual defining and calling source
files, and the checker passes at P30, so the re-pin matches the tree rather than being
hand-typed.

---

## New findings

### NEW-1 — P2 — the witness-forgery residual is undeclared, and the minted fragment witness has no construction invariants

Two halves that only matter together.

**Half one: the residual is not declared where it is load-bearing.** The packet's headline invariant
`C9A-FRAGMENT-ADMITTED-ONLY-THROUGH-MODULE-WITNESS` is defeatable by `object.__new__` on
`VerifiedLaneModuleTransitionV1`, bypassing the verifier construction token entirely.
The candidate knows this — `_forge_witness` at
`tests/core/test_asset_transfer_receipt_admission_v1.py:114` does exactly that, and the
three `test_defensive_witness_checks_have_forgery_witnesses` parameters that close F3
depend on it working.

Being precise about what *is* written down, because the distinction is the finding.
Two code comments acknowledge `object.__new__` — `global_accounting_lane_producers_v1.py:198`
and its Rust twin at `global_accounting_lane_producers.rs:245` — but both are about the
**accepted value's** `__post_init__`, and this candidate's snapshot closes exactly that
bypass on the admission path. Nothing acknowledges the bypass of the **witness
construction token**, which is what the headline invariant actually rests on: not the
C9a packet's five nonclaims, not the O-008 formal-cycle packet's eleven, not the
admission module docstring, not `lane_module_receipt_verification_v1.py`, and not
`ZENODEX_VALUE_MOVEMENT_CLOSURE_STATUS_V1.json`. Outside Opus review receipts and test
docstrings, it is unrecorded.

The one place it was visible in a *packet* has been removed by this candidate. The v1
receipt-admission packet carried the mutation description "vary the statement root while
keeping the journal (object.__new__ forgery)"; v2 drops that entry (it is the single
removed mutation in the v1→v2 diff) and replaces it with three forged-witness mutations
whose descriptions say only "delete the witness-kind, statement-root, or occurrence
check". The repair is correct and the removal is defensible on its own terms — but the
net effect is that a reader of the v2 packet alone would conclude the witness gate is
unconditional. P28 called this "the campaign's long-declared residual"; on this evidence
it is a long-*known* residual that was never declared.

**Half two: nothing downstream compensates.**
`src/core/asset_transfer_receipt_admission_v1.py:115-119`. `_VerifiedFragmentFieldsV1` is
a bare frozen dataclass with **no `__post_init__`**. Every other value type on this path
validates at construction — `ReceiptWitnessRejectedV1` (`:95-106`) checks its code, lane
id, root and detail; `LaneAllocationFragmentV1`, the journal and the port all validate.
The three scalars the admission copies out of the witness (`module_journal_root`,
`receipt_digest`, `expected_image_id`) are stored verbatim and never checked.

**Reproduction** (`/tmp/zenodex-c9ap-hunt4.py`, using the candidate's own helper):

```
receipt_digest=None          -> *** MINTED *** witness carries receipt_digest=None
expected_image_id=12345      -> *** MINTED *** witness carries expected_image_id=12345
receipt_digest='not-a-root'  -> *** MINTED *** witness carries receipt_digest='not-a-root'
```

So a caller at the Python API can obtain a `VerifiedLaneAllocationFragmentV1` — the value
C9b is specified to consume — that names itself receipt-verified and carries `None` where
a proof digest belongs, with no receipt anywhere in the picture.

This is a claim-precision and defence-in-depth defect, not a falsified property: the
surface is inert (registry `NO_PRODUCER`, zero consumers, authority `NONE`), nothing
moves value, and this candidate did not introduce the primitive. That is why it is P2 and
not P1. It is not lower because it is the one thing in this candidate that a C9b author
reading the packet would get wrong.

**Minimal fix, both halves.**

1. Add a nonclaim: `VerifiedLaneModuleTransitionV1` and
   `VerifiedLaneAllocationFragmentV1` are token-gated against ordinary construction but
   not against `object.__new__`; the admission-only-through-the-witness invariant holds
   against every construction-legal caller, not against in-process forgery.
2. Give `_VerifiedFragmentFieldsV1` a `__post_init__` running `_require_root` on
   `module_journal_root`, `receipt_digest` and `expected_image_id`, plus an exact-type
   gate on `fragment`.

I did not apply or test this fix — I only checked its inputs. On the honest path all
three scalars are canonical 32-byte roots (`receipt_digest = 0xa79e4357…`,
`expected_image_id = 0x0000…0075`, which is nonzero and so passes `_require_root` with
`allow_zero=False`), and the three F3 forgery cases vary `receipt_kind`,
`statement_root` and `command_occurrence_id` — none of the three proposed fields — and
reject before minting. So I expect no honest-path or F3 regression, but that is reasoning
rather than a replay.

### NEW-2 — P3 — the new `lane_root` exact-type gate has no test

`src/core/asset_transfer_receipt_admission_v1.py:183-184`. This gate was added by this
candidate. Deleting it leaves the entire admission suite green:

```
DEL lane_root exact-type gate: SURVIVED (rc=0) :: 20 passed in 2.77s
```

This is the same defect class the candidate was repairing under F3: a check with no
behavioural evidence, shipped alongside checks that now have it. The gate does earn its
place — the admission reads `lane_root.state_root` and `lane_root.lane_id` into the
reject constructors of checks (1) through (3) *before* the producer's own identical gate
is reached, so a duck-typed lane root would otherwise flow into a returned reject value.
I confirmed the gate stops that (`TypeError: fragment admission requires the exact
LaneStateRootV1` for a plain duck-typed object). It simply has no test.

**Minimal fix.** One negative test passing a duck-typed lane root and asserting the
`TypeError`, added to the packet's mutation list.

### NEW-3 — P3 — one declared mutation killer is only half-demonstrated

The packet declares the mutation "loosen the port's projection gates back to isinstance
(Opus P28 F1)" — plural — killed by
`test_subclassed_projection_is_refused_by_the_port_gate`. That test constructs a port
with `post_state=loose` only. Loosening the *other* gate:

```
src/core/asset_lane_projection_v1.py:210
-  if type(self.pre_state) is not AssetLaneStateProjectionV1:
+  if not isinstance(self.pre_state, AssetLaneStateProjectionV1):

test_subclassed_projection_is_refused_by_the_port_gate: SURVIVED (1 passed)
```

It is killed only incidentally, and only as a *collection* error in an unrelated file
(`tests/core/test_asset_transfer_refinement_v1.py`, and see NEW-5 — that file is red
anyway, so it kills nothing reliably). The admission path itself is not exposed: the
snapshot's `_snapshot_asset_lane_state_projection_v1(port.pre_state)` exact-type gate
still refuses a `pre_state` subclass, so this is evidence precision rather than a hole.

**Minimal fix.** Parametrize the existing test over `pre_state` and `post_state`.

### NEW-4 — P3 — the F1 class is still live in the sibling receipt-backed boundary (not falsified)

`src/core/receipt_backed_asset_lane_composition_v1.py:80-82` gates all seven fields of
`ReceiptBackedAssetLaneCompositionCandidateV1` — including `module_journal`,
`private_port` and `module_effects`, all root-bearing — with `isinstance` in a loop, and
`:293` / `:304` gate the candidate and the composition result the same way.
`src/core/asset_lane_projection_v1.py:373-380` does the same for
`AssetLaneCompositionAcceptedV1`'s three root-bearing values, five lines below the gates
this candidate tightened, and then compares `lane_journal.post_lane_root` against the
*reported* `post_state.state_root` — the exact P28 F1 shape. This boundary mints an
opaque, token-gated witness (`ReceiptBackedAssetLaneCompositionV1`) carrying journal
roots, structurally identical to C9a's output.

**What I demonstrated** (`/tmp/zenodex-c9ap-hunt2.py`, `hunt3.py`): an
`AssetLanePrivatePortV1` subclass overriding `port_root` passes the `isinstance` gate and
a composition witness is minted.

**What I could not do:** falsify it. Two independent controls held.

* Substituting a *different* but fully valid projection (same per-asset totals, one
  balance row reassigned from `alice` to `attacker`) is refused with
  `asset lane composition rejected: STATE_EFFECT_MISMATCH` — the coordinator reconciles
  post-state against effects rather than trusting the reported root.
* A `LaneModuleTransitionJournalV1` subclass overriding `journal_root` is refused at
  `TypeError: unsupported canonical value type` — `canonical_global_bytes_v1` dispatches
  on exact type through the manifest, so no subclass can be canonically encoded.

So this is hardening with an explicit non-falsification, not an exploit. It matters for
one reason: the packet's new invariant id
`C9A-ROOT-BEARING-NESTED-VALUES-EXACT-TYPED-AT-CONSTRUCTION` is unqualified, while the
`claim_scope` sentence that supports it names five specific gates in two specific files.
Read against the scope the invariant is true; read as its own name suggests, it is not.
Invariant ids travel further than claim scopes.

**Minimal fix.** Change the loop's `isinstance` to `type(value) is not expected_type`,
and the three gates at `asset_lane_projection_v1.py:373-380` likewise; or state the scope
limit in the packet.

### NEW-5 — P3 — a second, undeclared pre-existing red at the exact subject (inherited)

`tests/core/test_asset_transfer_refinement_v1.py` cannot be **collected** at P30:

```
tools.check_asset_transfer_refinement_v1.RefinementCorpusErrorV1:
adjacent precedence pair ('BALANCE_OVERFLOW', 'POST_STATE_RESOURCE_BOUND_EXCEEDED')
has no witness case
```

This is a fail-closed corpus-coverage guard firing, not an import problem. It is
**inherited, not introduced**: `tools/check_asset_transfer_refinement_v1.py` and
`tests/data/asset_transfer_refinement_v1.json` are byte-identical at P29 and P30
(`fe028fc1c5dd1957`, `e80f1c9c4863d873`) and were last touched by `22ee86783`, the C8-p11
subject. It is plausibly the same root cause as Opus P29 NEW-25 — a
`POST_STATE_RESOURCE_BOUND_EXCEEDED` reject code introduced without a corpus witness —
but it is a different file with a different symptom, so the C8-p11 repair should be
checked against it explicitly rather than assumed to cover it.

Two things make it worth recording here. It is not the pre-existing exclusion my brief
named (`test_zusd_liquidation_partition.py`), and neither the packet's 29 replay commands
nor the hygiene gate touch this file, so the candidate is green on everything it
measures while a tracked test in `tests/core/` is red at the subject. I checked the near
miss explicitly: the packet's `transfer_refinement_gate` runs
`tests/formal/test_lean_asset_transfer_refinement_v1.py` (40 passed, exit 0), a different
file that never imports the corpus checker. The red file is genuinely uncovered.

### INFO-1 — the entitlement tuple gate is still `isinstance`, contained only by a catch-all

`src/core/global_accounting_lane_producers_v1.py:242` gates the entitlement tuple with
`not isinstance(claimant_entitlements, tuple)` while its three siblings on the same lines
use exact `type(x) is not T`. A `tuple` subclass with a stateful `__iter__` (honest for
the type gate, the key fold, the zero check and the coverage fold; foreign afterwards) is
accepted by the producer and stopped only at `LaneAllocationFragmentV1.__post_init__`,
where `_require_tuple`'s exact check raises and is swallowed by the defensive
`except (TypeError, ValueError)` at `:353`, returning `FRAGMENT_INVALID`. I confirmed
this end to end. The outcome is a correct reject value, so nothing leaks — but the
containment runs through a catch-all the code itself calls "unreachable in intent".

Relatedly, a validation-bypassed `prior_fragment` (`object.__new__` with a non-tuple
`controlled_locations`) is admitted: `accepted` is now snapshot-rebuilt but
`prior_fragment` and `lane_root` are only type-gated. Nothing from `prior_fragment`
reaches the output — only its `lane_state_root`, `lane_id`, `producer_kind`, `enabled`
and `module_release_id` are read, and every field of `lane_root` that reaches the emitted
fragment is pinned by a journal equality — so this is an asymmetry to close in C9b, not a
hole today.

### INFO-2 — `asset_transfer_types_v2.py` needs no scoping judgment

Recorded because my brief asked me to judge it: the file has zero `isinstance` calls at
P30 and uses exact `type(...) is not` gates throughout.

### INFO-3 — the F2 nonclaim pin cannot force C9b to invert it

`test_claimant_identity_is_not_bound_by_the_receipt_until_c9b` asserts that the hole
exists. If C9b lands without binding claimants, the test still passes and nothing flags
the omission; the obligation lives only in prose ("C9b must invert this pin"). Consider a
registered open obligation in the O-008 packet, whose 11 nonclaims currently say nothing
about C9a or claimant binding.

### INFO-4 — `binding_root` names two different quantities

`LaneAllocationFragmentV1.binding_root` is the module journal's `receipt_root`;
`VerifiedLaneModuleTransitionV1.binding_root` is a hash over the witness's own scalars.
Check (4) compares the first against the journal, not against the second, and a reader
scanning the code will reasonably assume otherwise. The docstring pre-empts this
correctly, which is why F4 is closed — but the collision itself remains and will be read
again at C9b.

### INFO-5 — the snapshot widens the raised exception family to `ValueError`

Check (0) can raise `ValueError` as well as `TypeError`, because it re-runs construction
invariants (`test_validation_bypassed_accepted_is_refused_by_the_snapshot` expects
`ValueError, match="receipt root mismatch"`). `ValueError` is also this codebase's class
for ordinary domain violations, so a caller cannot distinguish "your object was forged"
from a domain error by exception class alone. On a research-only surface that raises and
stops this is acceptable, and the docstring declares it; it would matter if C9b wraps the
admission in a `try/except`.

### INFO-6 — the packet's `aaa` reason over-generalises

`aaa.reason` says "Each test arranges one witness/accepted pair through the real ABI
fixture chain, invokes the verifier once, and asserts the exact type, code, detail, and
carried binding scalars." Five of the sixteen pinned tests do not fit that description:
`test_witness_token_is_verifier_only`,
`test_subclassed_private_port_with_a_spoofed_root_is_refused_at_construction` and
`test_subclassed_projection_is_refused_by_the_port_gate` never call the verifier (they
assert at construction), `test_witness_reject_family_is_closed_and_ordered` asserts an
enum listing only, and `test_claimant_identity_is_not_bound_by_the_receipt_until_c9b`
calls it twice in a loop. The AAA structure itself holds throughout; only the prose
generalises past the evidence. The `reject_is_noop` reason, by contrast, is exactly
accurate.

### INFO-7 — the pass-through evidence widened but the file-hash claim did not

The packet's boundary point "eleven producer codes untouched" is still satisfied by the
file hash rather than by behaviour, but pass-through is now exercised for three producer
codes (`LANE_DISABLED`, `MODULE_RELEASE_DRIFT`, `JOURNAL_ROOT_DRIFT`) instead of one, and
the packet says "three codes" rather than implying eleven. Accurate as written.

---

## What I could not falsify

* No route to a `VerifiedLaneAllocationFragmentV1` whose fragment contradicts the receipt
  — not through subclassing, `object.__new__` on the accepted value, its port, its
  journal, its effects, its custody rows, a tuple subclass, a `str` subclass with a lying
  `__eq__`, a forged `prior_fragment`, or a forged `lane_root`.
* No drift in the claim ceiling, the certificate registry (`ASSET_TRANSFER` remains
  `NO_PRODUCER`), or the packet write set.
* No exploit of the sibling composition boundary despite its loose gates (NEW-4).
* No dishonest pin, node id, count, or digest anywhere in the five packets.

---

## Recommendation

**ACCEPT (advisory).** The candidate does what it says. Before C9b, and in priority
order:

1. Declare the `object.__new__` witness-forgery residual as a nonclaim and add
   `__post_init__` validation to `_VerifiedFragmentFieldsV1` (NEW-1). This is the one
   finding that touches the value C9b will consume, and the one a C9b author reading the
   packet alone would get wrong.
2. Add the missing `lane_root` gate test and parametrize the projection-gate test over
   both `pre_state` and `post_state` (NEW-2, NEW-3), then re-pin the packet's mutation
   list.
3. Decide whether the sibling receipt-backed composition boundary gets the same exact-type
   audit or an explicit scope statement (NEW-4).
4. Confirm the C8-p11 repair also closes the asset-transfer refinement corpus coverage
   guard (NEW-5); if it does not, that file is red on the branch head.
5. Register the claimant-binding obligation somewhere a checker can see it (INFO-3).

Authority remains NONE. The claim ceiling did not move and must not move on this
candidate.
