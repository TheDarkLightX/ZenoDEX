# Opus 5 independent review — ZenoDEX Formal Functional Core Closure Campaign, candidate C9b-2a

| Field | Value |
|---|---|
| Subject (S36) | `c2eae0e07219479934e68ba364e31bd1b290cd92` — "security: gate the certificate on twelve receipt-witness slots before any lane is registered receipt-backed" |
| Artifact (P36) | `41b36ec080b044fbf9818674c54e0dbfcfb6bf6b` — "docs: freeze the O-008 formal-cycle packet at C9b-2a" |
| Parent chain | P36 → S36 → P35 `3d2356232` |
| Packet json sha256 | `8301353be2142e3368d7407b8515ab083c6461a9d5e66508b743f52d0917d204` |
| Branch | `codex/formal-core-fable-20260901` |
| Worktree | `/tmp/zenodex-formal-core-opus-c9b2a` (detached, `git status --short` empty at start and at end) |
| Reviewer | Opus 5 (independent; advisory only) |
| Date | 2026-09-03 |
| Toolchain | Python 3.12.3, Lean 4.27.0, cargo/rustc 1.87.0, z3 4.15.4, cvc5 1.1.2 |

**Verdict: REVISE (advisory). Grade B+. 0 P1, 3 P2, 4 P3, 1 INFO.**

Authority stays NONE. `formal_core_complete` stays false. The claim ceiling is byte-identical
to P35 (sha256 of the canonicalised `claim_ceiling` object: `f5079f053ca822fed1a3f983e48966a0…`)
and the registry still keeps `ASSET_TRANSFER` at `NO_PRODUCER` in both languages. Nothing in
this review moves any gate.

---

## 1. Replays

Every Lean-bearing command was run under `flock -w 7200 /tmp/zenodex-lean.lock`. `PY` is
`/home/trevormoc/Downloads/Autonomous Tau DEX/.venv/bin/python`; `PYTHONDONTWRITEBYTECODE=1`;
`CARGO_TARGET_DIR=/tmp/zenodex-opus-c9b2a-cargo CARGO_INCREMENTAL=0`.

| Command | Exit | Result |
|---|---|---|
| `"$PY" tools/check_o008_formal_cycle_v1.py --root "$PWD" --packet-commit 41b36ec08…` | 0 | `ok=true`, `packet_admitted=true`, `current_applicable=true`, `current_source_drift=[]`, `errors=[]`, `proof_replay=NOT_RUN` |
| same `--replay --esso-python /usr/bin/python3 --esso-pythonpath /home/trevormoc/Downloads/ESSO` | 0 | `EXECUTED_PASS`, **31 runs, every run `exit_code=0`** |
| `"$PY" tools/build_o008_formal_cycle_v1.py … --check --replay …` | 0 | `{"drift":[],"mode":"check","ok":true,"subject_commit":"c2eae0e07…"}`; tree still clean afterwards (round trip byte-identical) |
| `cargo fmt --all -- --check` | 0 | clean |
| `cargo clippy --locked --all-targets -- -D warnings` | 0 | clean |
| `cargo test --locked` | 0 | all suites green (incl. doc-tests) |
| `tests/test_check_o008_formal_cycle_v1.py` | 0 | **391 passed** in 242.77s |
| `tests/core/{test_transition_resource_bound_totality_v1,test_global_settlement_abi_v1_resource_bounds,test_global_settlement_abi_v1,test_global_accounting_allocation_certificate_v1_golden,test_global_settlement_fcis_exact_ownership_v1,test_asset_transfer_receipt_admission_v1,test_global_accounting_lane_producers_v1}.py` + `tests/test_check_global_settlement_canonical_manifest_v1.py` | 0 | 608 passed (see note below) |
| `tools/check_test_hygiene_v1.py --json` | 0 | `ok=true`, 0 changed paths |
| `… --base-ref 3d2356232 --json` | 0 | `ok=true`, 27 changed paths, 488 node ids |
| `… --base-ref 42ccb6624 --json` | 0 | `ok=true`, 94 changed paths, 545 node ids |
| `… --base-ref fd409ba6f7da8f0ec3e0220a04b7406d69a8cb85 --json` (campaign base) | 0 | `ok=true`, 359 changed paths, 663 node ids |

Selected replay counters, matching the values the packet declares:
`rust_admission_gate passed=5`, `python_certificate_golden_gate passed=38`,
`transfer_refinement_gate passed=40`, `python_rust_bound_parity_gate passed=17`,
`prior_restage_gate passed=136`, `esso_gate passed=20`, `esso_certificate_gate passed=24`,
`esso_verify_multi` and `esso_certificate_verify_multi` both `VERIFIED` with z3 4.15.4 +
cvc5 1.1.2, `lean_axioms_probe theorems_probed=25`,
`lean_certificate_axioms_probe theorems_probed=16`.

Lean gates (serial, under the shared lock, on a clean tree): recorded in §6.

**Self-inflicted red, disclosed.** An earlier batch run of the Python suites and an earlier
queued Lean-gate run overlapped my own mutation experiments, which temporarily edited
`src/core/global_accounting_allocation_certificate_v1.py`. That produced 10 spurious
`LEAN_GATE_PIN_DRIFT` errors in `tests/test_check_o008_formal_cycle_v1.py` and one spurious
`test_exact_sources_are_pinned` failure. Both were re-run on a verified-clean tree
(`sha256(src/core/global_accounting_allocation_certificate_v1.py) =
f74e5cfc4a8276585b9814fdffc389d733d301ae4416cd0c182e4f7f4eab2bf3`, equal to the Lean gate's
`PYTHON_CHECKER` pin) and are green. No red in this report is caused by my own edits; the
working tree was restored and verified empty after every experiment.

---

## 2. Claim-by-claim verdicts

### 2.1 Twelve witness slots — **CLOSED**

`check_global_accounting_allocation_certificate_v1(certificate, state, witnesses)` takes the
slots as a third positional argument. The boundary refusals are at
`src/core/global_accounting_allocation_certificate_v1.py:1009-1013`: a non-`tuple` or a tuple
whose length differs from `len(ALL_LANE_IDS_V1)` raises `TypeError`, and each slot must be
`None` or exactly `VerifiedLaneAllocationFragmentV1` (`type(...) is not`, not `isinstance`).
Position ↔ lane correspondence is safe because `_check_lane_order` runs first and pins
`ordered_lane_fragments` to `ALL_LANE_IDS_V1`, and the pairing itself uses
`zip(..., strict=True)` (line 781).

Every call site passes slots. The complete set of Python call sites is
`tools/render_global_accounting_allocation_certificate_v1_golden.py:284`,
`tests/formal/test_esso_global_accounting_allocation_certificate_v1.py:516,521`,
`tests/core/test_global_accounting_lane_producers_v1.py:77,83`,
`tests/core/test_global_accounting_allocation_certificate_v1_golden.py:79,95,100,308,313,335`;
all pass `cert.EMPTY_LANE_WITNESS_SLOTS_V1` or a tuple derived from it. **No two-argument call
survives** anywhere in the repository.

The Rust twin takes `witnesses: &[Option<&VerifiedLaneAllocationFragmentV1>]` and returns
`AbiErrorV1::InvalidBounds("certificate witness slots must hold twelve entries in lane order")`
on any other length
(`zk/global_settlement_abi_v1/src/global_accounting_allocation_certificate.rs:1295-1300`),
exercised at `zk/global_settlement_abi_v1/tests/lane_module_release_route_binding.rs:6279-6282`.

### 2.2 Four closed codes in one check-major family — **PARTIAL**

The four codes are added to `AllocationCertificateRejectCodeV1` (lines 138-141) and to the
message table (lines 161-164) in the same positions as the Rust `ALL: [Self; 20]` array
(`…/global_accounting_allocation_certificate.rs:155-158`), the `as_str` arms (179-182) and
the message arms (206-216). `CHECK_ORDER_V1` gains `receipt_witness_slots_bind_fragment_and_header`
at index 3, directly after `enabled_lane_supported_receipt_backed_producer` (line 975), and the
golden fixture `tests/data/global_accounting_allocation_certificate_v1_golden.json` carries the
thirteen-entry check order and the four new messages verbatim. The sidecar check list and
`CERTIFICATE_REJECT_CODES_V1` in `tools/o008_formal_cycle_admission_v1.py` moved with them.

**The precedence claim ("witness pass after BLOCKED") holds as written** — the family runs at
lines 781-799, strictly after the `PRODUCER_KIND_DRIFT` and `BLOCKED_LANE_PRODUCER_MISSING`
passes and strictly before `DISABLED_LANE_NOT_EMPTY`.

**The subsumption argument for `BINDING_ROOT_DRIFT` is correct.** The witness exports
`receipt_root = journal.receipt_root` and `fragment = produced`, and the admission's check (4)
(`src/core/asset_transfer_receipt_admission_v1.py:280-287`) rejects unless
`produced.binding_root == journal.receipt_root`. `LaneAllocationFragmentV1` is a frozen
dataclass, so the `RECEIPT_WITNESS_FRAGMENT_DRIFT` pass (`witness.fragment != fragment`) is
field-wise equality and therefore implies `fragment.binding_root == witness.receipt_root`. A
hypothetical witnessed branch `fragment.binding_root != witness.receipt_root` genuinely could
never fire. Note the docstring's phrasing is easy to misread: what "could never fire" is the
*receipt-root* form of the check, not the shipped `lane_state_root` form — the shipped form
would fire on every witnessed lane, which is exactly why witnessed lanes are exempted.

Marked PARTIAL rather than CLOSED for the two structural gaps in **F-4** and **F-5**: two of
the four codes share one pass, and no test pins the runtime order of the four passes.

### 2.3 The witness moved into the certificate module — **PARTIAL**

The type now lives at `src/core/global_accounting_allocation_certificate_v1.py:487-544` with
the private token at line 446 and the fields record at 450-484; the two modules no longer
import each other in both directions (the admission imports the certificate, not the reverse).
The `InitVar` token is genuinely never stored — `assert not hasattr(verified, "token")` at
`tests/core/test_asset_transfer_receipt_admission_v1.py:633` — and the admission now records
the rebuilt journal header (`asset_transfer_receipt_admission_v1.py:295-299`).

Minting without the token is refused: `VerifiedLaneAllocationFragmentV1(fields, object())`
raises `TypeError("VerifiedLaneAllocationFragmentV1 is verifier-constructed")`, and
`(fields.fragment, _VERIFIED_FRAGMENT_TOKEN)` raises `TypeError("… must be the exact record")`.
A plain subclass carrying genuine fields is refused by the slot gate's exact-type check
(golden test, lines 319-336).

**The `__dict__` consequence of dropping `slots` is a regression, and the stated reason for
dropping it is false — see F-1.** This is the single most important finding in this review.

### 2.4 Inert while no lane is registered receipt-backed — **CLOSED**

`LANE_ALLOCATION_PRODUCER_REGISTRY_V1` is unchanged by S36 (verified by diff), and
`test_producer_registry_is_exhaustive_and_has_no_receipt_backed_lane` still passes. Both
golden replays still accept only the registered-empty certificate over an all-disabled state:
Python at `tests/core/…_golden.py:313-316` and Rust at
`lane_module_release_route_binding.rs:6268-6277`. The only reachable witness code is
`RECEIPT_WITNESS_UNEXPECTED`, and both tests exercise it with a **real minted witness**, not a
stub. The killers-reachability set excludes the other three with that reason recorded.

I found no acceptance-path widening. The one behavioural change reachable today is strictly a
new refusal.

### 2.5 The certificate module joins the scanned exact-ownership set — **PARTIAL**

The module is added to `_ADMISSION_PATH_MODULES` and contributes 15 pins to the 99-pin
positive set; the manifest closure digest and the Lean certificate gate pins moved with it
(`CERTIFICATE_PYTHON_GATE_EXPECTED_PASSED_V1` 37→38,
`ADMISSION_RUST_GATE_EXPECTED_PASSED_V1` 4→5, and all three source hashes in
`tests/formal/test_lean_global_accounting_allocation_certificate_v1.py` updated).

**PARTIAL because the file ships the same 255-line block three times, and the first copy
carries a pin that contradicts the shipped source — see F-2.**

### 2.6 Process repairs from the P34 reviews — **CLOSED**

`tools/formal_core_battery_v1.sh` now sets `RED=1` on each of the four parts and ends with
`exit "$RED"` (the `{ … }` group runs in the current shell, so the variable survives).
Verified directly:

```
FORMAL_CORE_PY=/bin/false bash tools/formal_core_battery_v1.sh <log>
→ BATTERY EXIT=1
  python exit 1 / esso exit 1 / lean1 exit 1 / lean2 exit 1 / battery done red=1
```

The deselection is exactly one node id,
`tests/test_check_o008_formal_cycle_v1.py::test_committed_packet_lifecycle_at_repository_head`,
and the docstring states why. That test is **not** Lean-bearing — it calls
`cli.run_checker_v1` without `--replay` and asserts `proof_replay.status == "NOT_RUN"`
(`tests/test_check_o008_formal_cycle_v1.py:1646,1676`) — so running it outside the lock at
chain step 4 is correct, not a serialization violation.

`tools/formal_core_candidate_chain_v1.sh` stops before push and tag on each of the three
re-checks at P: `CHK` (line 45), `BLD` (line 48) and `LC` (line 49) each `exit 1` with a named
message. The pre-P steps also stop the chain (lines 33, 35, 36, 39, 41), leaving S committed
locally only, which matches the docstring and matches what the commit message reports about
this candidate's first chain attempt. `git push` and `git tag` now also fail closed (lines
50-51).

### 2.7 Authority — **CLOSED**

`claim_ceiling` is byte-identical to P35. `formal_core_complete=false`; every authority field
is `NONE`; `value_movement_gates_closed=0 / 12`; `whole_value_movement_safe=false`. The only
top-level packet keys that differ from P35 are `hygiene_selection`, `packet_commit_parent`,
`proof_replay`, `required_sidecar`, `source_pins`, `subject_commit`, `subject_parent`,
`subject_tree` — exactly the envelope, no claim movement.

---

## 3. Evidence packets

All six in-scope THV1 packets verified mechanically.

| Packet | source pins | all sha256 match | test-pin file sha256 |
|---|---|---|---|
| `THV1-20260830-global-settlement-exact-ownership-v5` | 2 | yes | matches |
| `THV1-20260901-claimant-backing-guard-golden-v25` | 9 | yes | matches |
| `THV1-20260901-global-accounting-allocation-certificate-v18` | 21 | yes | matches |
| `THV1-20260901-o008-formal-cycle-admission-v32` | 41 | yes | matches |
| `THV1-20260902-global-settlement-v1-canonical-exact-admission-v6` | 3 | yes | matches |
| `THV1-20260902-o008-asset-transfer-receipt-admission-v7` | 10 | yes | matches |

632 distinct node ids are declared across the six packets (`test_pins[].node_ids` plus every
`mutations[].killed_by`). `pytest --collect-only` over all 632 exits 0 and collects 635 items
(three parametrised parents expand). **No dangling node id.**

The four mutation killers new in C9b-2a were applied, run, and restored. Each kills:

| Mutation | Named killer | Result |
|---|---|---|
| `type(slot) is not …` → `not isinstance(slot, …)` | `test_admission_path_exact_type_gates_are_pinned_positively` | FAILED (also fails the golden witness test) |
| delete the `RECEIPT_WITNESS_UNEXPECTED` `_fail` | `test_witness_slots_refuse_a_witness_for_an_unregistered_lane_and_bad_shapes` | FAILED |
| slot-length gate → `if False:` | same | FAILED |
| `chain_id=journal.chain_id` → a literal | `test_minted_witness_exports_the_rebuilt_journal_header` | FAILED |

Working tree verified clean after each restore.

---

## 4. Findings

### F-1 (P2) — `slots` was dropped on a claim that is false on the pinned interpreter, opening a `__dict__` forgery of a genuine witness

`src/core/global_accounting_allocation_certificate_v1.py:487` and the docstring at 499-503.

The class is `@dataclass(frozen=True)` — no `slots`. The docstring justifies this: *"It is
frozen without `slots`: CPython 3.12's frozen-slots `__setattr__` **cannot refuse** an
assignment to a property of the re-created class, and the `__dict__` this leaves is already
covered by the in-process forgery residual."*

**The first half is false and the second half is an assertion, not an argument.**

On the interpreter the packet pins (CPython 3.12.3), a frozen **slots** dataclass *does*
refuse a property assignment. It refuses with the wrong exception type — `TypeError:
super(type, obj): obj must be an instance or subtype of type`, raised by the stale `cls`
closure cell that `@dataclass(slots=True)` leaves behind when it re-creates the class — but
the assignment does not land:

```
frozen+slots: setattr 'value'  -> TypeError (refused)
frozen+slots: setattr '_fields'-> FrozenInstanceError (refused)
frozen+slots: __dict__ mutation-> AttributeError: no attribute '__dict__'
frozen only : setattr 'value'  -> FrozenInstanceError (refused)
frozen only : setattr '_fields'-> FrozenInstanceError (refused)
frozen only : __dict__['_fields'] = forged -> ALLOWED
```

Dropping `slots` therefore did not buy a refusal that slots lacked; it bought a *nicer
exception type* and paid for it with a `__dict__`. The result is a strict regression against
the C9a shape, which had `__slots__ = ("_fields",)` and a custom `__setattr__`.

Reproduction (worktree root, clean tree):

```python
from src.core.asset_transfer_receipt_admission_v1 import verify_asset_transfer_fragment_receipt_v1
from tests.core.test_asset_transfer_receipt_admission_v1 import _admission_fixture
import src.core.global_accounting_allocation_certificate_v1 as cert
import tools.render_global_accounting_allocation_certificate_v1_golden as renderer
from src.core.global_settlement_types_v1 import ALL_LANE_IDS_V1, LaneIdV1
from dataclasses import replace

accepted, module_witness, lane_root, prior = _admission_fixture()
w = verify_asset_transfer_fragment_receipt_v1(module_witness, accepted, lane_root, prior, ())
empty = renderer.build_state_v1(renderer._spec())
certificate = cert.build_registered_empty_certificate_v1(empty)
idx = ALL_LANE_IDS_V1.index(LaneIdV1.ASSET_TRANSFER)
w.__dict__["_fields"] = replace(
    w._fields,
    fragment=certificate.ordered_lane_fragments[idx],
    chain_id=empty.chain_id, deployment_root=empty.deployment_root,
    profile_root=empty.profile_root, writer_epoch=empty.writer_epoch,
)
```

Observed: `type(w) is cert.VerifiedLaneAllocationFragmentV1` stays `True`, `w.fragment`
becomes the certificate's own fragment, and the header tuple becomes equal to the state's.
The forged witness therefore **passes the exact-type slot gate, passes
`RECEIPT_WITNESS_FRAGMENT_DRIFT`, and passes `RECEIPT_WITNESS_HEADER_DRIFT`**. Today it is
still refused, but only by `RECEIPT_WITNESS_UNEXPECTED`, because `ASSET_TRANSFER` is
`NO_PRODUCER`. After the C9b-2b registry flip the same object is accepted.

Three aggravating points:

1. The existing immutability test
   (`tests/core/test_asset_transfer_receipt_admission_v1.py:169-180`) still passes, so the
   suite cannot see the regression. It covers `setattr` on a property and on the field and
   nothing else.
2. The declared residual is *in-process `object.__new__` forgery* — constructing a fresh
   object. Re-pointing an already-minted, legitimately-obtained handle is a different
   operation, and folding it into the existing residual by assertion widens a disclosed
   residual without saying so.
3. The commit message presents the move as a hardening ("the witness is a frozen **slots**
   dataclass" — the message says slots, the code does not).

**Minimal fix, verified in this worktree.** Restore `slots=True` at line 487 and widen the one
test line that then breaks:

```
src/core/global_accounting_allocation_certificate_v1.py:487
-@dataclass(frozen=True)
+@dataclass(frozen=True, slots=True)

tests/core/test_asset_transfer_receipt_admission_v1.py:178
-    with pytest.raises(AttributeError, match="cannot assign|immutable"):
+    with pytest.raises((AttributeError, TypeError), match="cannot assign|immutable|super\\(type, obj\\)"):
```

With `slots=True` applied I measured: `hasattr(w, "__dict__")` is `False`, the `__dict__`
forgery raises `AttributeError`, `setattr(w, "_fields", …)` still raises `FrozenInstanceError`,
and **exactly one** test in the three relevant suites fails
(`test_receipt_admitted_fragment_carries_the_witness_binding`, 1 failed / 86 passed) — the
property line above. The docstring should then say what is actually true: frozen-slots refuses
the assignment but reports `TypeError` from a stale closure cell, which is a cosmetic defect,
not a sealing defect. No `__setattr__` is added, so the packet's static-binding rule
(`tools/o008_formal_cycle_admission_v1.py:1950` forbids `__setattr__`, `__delattr__`,
`__dict__` in pinned source) is respected.

### F-2 (P2) — the exact-ownership gate file ships the same 255-line block three times; the first copy pins a symbol that no longer exists

`tests/core/test_global_settlement_fcis_exact_ownership_v1.py`, blocks at lines **609-865**,
**866-1122** and **1123-1377** (file is 1377 lines).

All three copies begin with the identical header comment
`# --- S36 (C9b-2a; S34 Opus P32 F-1/F-5, Fable P32 P3-1): …` and each redefines the same five
top-level names: `_ADMISSION_PATH_EXACT_TYPE_GATES` (lines 614 / 871 / 1128),
`_ADMISSION_CLOSURE_OUT_OF_SCOPE_ISINSTANCE_COUNTS` (721 / 978 / 1235), `_exact_type_gate_sites`,
`_src_core_import_closure`, `test_admission_path_exact_type_gates_are_pinned_positively`,
`test_admission_path_has_no_isinstance_spelling_variants`, and
`test_admission_path_module_set_is_bound_to_the_import_closure`. Python module-level rebinding
means **only the third copy is live**; `pytest --collect-only` confirms each of those test names
is collected exactly once. Roughly 512 lines are dead.

The two dead copies are not identical to the live one. Copy 1 and copy 3 differ in exactly one
pin:

```
copy1 (line 670): ('src/core/global_accounting_allocation_certificate_v1.py',
                   'VerifiedLaneAllocationFragmentV1.__init__',      'fields',     '_VerifiedFragmentFieldsV1')
copy3 (line 1184):('src/core/global_accounting_allocation_certificate_v1.py',
                   'VerifiedLaneAllocationFragmentV1.__post_init__', 'self._fields','_VerifiedFragmentFieldsV1')
```

Copy 1 pins the pre-C9b-2a shape (`__init__(self, token, fields)`), which the shipped
dataclass no longer has. The gate asserts set equality between the discovered sites and the
pinned set, so **if copy 1 were the live binding the positive gate would fail**. Copy 2 is
byte-identical to copy 3 apart from two trailing blank lines. This is the pattern of an
accidental double paste during the S34→S36 pin refresh, and it is exactly the failure mode a
mechanical positive-pin file exists to prevent: a future edit landing in copy 1 or 2 would be
silently ignored, and a reviewer reading top-down reads a stale pin first.

Reproduction:

```bash
python - <<'EOF'
import ast; from pathlib import Path; from collections import Counter
m = ast.parse(Path("tests/core/test_global_settlement_fcis_exact_ownership_v1.py").read_text())
print(Counter(n.name for n in m.body if isinstance(n, ast.FunctionDef)).most_common(5))
EOF
```

**Minimal fix:** delete lines 609-1122 (copies 1 and 2), keeping only the block at 1123-1377,
then refresh the file's sha256 in `THV1-20260830-global-settlement-exact-ownership-v5.json`,
in the Lean certificate gate's `PINNED_SOURCES`, and in the packet's `source_pins`. No pin
values change; the live set already has the correct 99 entries.

### F-3 (P2) — the new header pass binds four of the witness's nine scalars and leaves the verifier image id unbound, with no argument for the choice

`src/core/global_accounting_allocation_certificate_v1.py:792-799` and the Rust twin at
`…/global_accounting_allocation_certificate.rs:810-823`.

The witness exports nine values. The certificate binds `fragment` (by equality) and four
header scalars (`chain_id`, `deployment_root`, `profile_root`, `writer_epoch`). `receipt_root`
is implied by fragment equality (§2.2). `module_journal_root`, `receipt_digest` and
**`expected_image_id`** are bound to nothing.

`expected_image_id` is the identity of the RISC0 guest image the receipt was actually verified
against: `lane_module_receipt_verification_v1.py:386` sets it from
`release.guest_image_id`, where `release = candidate.profile.lane_registry.release_for(lane_id)`
(line 373). That is a **host-side** choice made from the caller's profile object. By contrast
`profile_root`, which the certificate does bind, is a **guest-committed scalar carried in the
module journal**. Nothing I could find establishes that the two agree:
`lane_module_receipt_verification_v1.py` never mentions `profile_root` at all, the admission
never sees a profile (`AssetTransferLaneModuleAcceptedV1` has no `.profile` — verified
empirically on the admission fixture), and no test in this candidate asserts the implication.

The candidate's own rationale for the header pass is *"a witness minted under another
deployment cannot vouch for an identical lane root elsewhere."* The same sentence with
"deployment" replaced by "verifier image" is equally true and is not enforced. Two states that
agree on chain id, deployment root, profile root and writer epoch but whose active lane release
pins a different guest image are indistinguishable to this pass.

This is inert today (no witness reaches the pass on an acceptance path), which is why it is P2
and not P1. It must be settled **before** the C9b-2b registry flip, in one of two ways:

- **If `profile_root` does pin `guest_image_id`:** state the derivation in the module docstring
  and add the missing equality as a checked invariant plus a pinned test, so the transitive
  argument is executable rather than assumed.
- **Otherwise:** add `expected_image_id` to the header tuple, bound to the release-selected
  image for the lane in the state being checked, and give it a fifth reject detail or fold it
  into `RECEIPT_WITNESS_HEADER_DRIFT`.

Either way the module docstring should say explicitly which of the nine exported scalars the
certificate binds and why the rest need no binding. Today it says neither.

### F-4 (P3) — two of the four new codes share one pass, so their precedence is lane-major while every other code in the function is check-major

`src/core/global_accounting_allocation_certificate_v1.py:782-788` (Rust: `…:782-798`).

`_check_lane_bindings` is documented as check-major: *"every lane passes one binding check
before any lane is tried against the next."* Every other code in the function gets its own
pass over the twelve lanes — `LANE_STATE_ROOT_DRIFT`, `PRODUCER_KIND_DRIFT`,
`BLOCKED_LANE_PRODUCER_MISSING`, `DISABLED_LANE_NOT_EMPTY`, `REGISTERED_EMPTY_ROOT_DRIFT`,
`BINDING_ROOT_DRIFT` (Rust: line 853). `RECEIPT_WITNESS_REQUIRED` and
`RECEIPT_WITNESS_UNEXPECTED` share a single loop, so between those two codes the ordering is by lane index, not by check.

Observable consequence once lanes are registered receipt-backed: a certificate with an
unexpected witness at lane 0 and a missing required witness at lane 5 reports `UNEXPECTED`;
under a check-major reading with `REQUIRED` first it would report `REQUIRED`. Both languages
share the shape, so this is not a parity bug — it is an undocumented precedence rule inside a
family the packet describes as ordered.

**Minimal fix:** split into two passes (`REQUIRED` over all lanes, then `UNEXPECTED` over all
lanes) in both languages, or add one sentence to the `CHECK_ORDER_V1` entry stating that the
presence check is a single check with two complementary codes resolved lane-major.

### F-5 (P3) — no test pins the runtime order of the four new witness passes

I swapped the `RECEIPT_WITNESS_FRAGMENT_DRIFT` pass (lines 789-791) with the
`RECEIPT_WITNESS_HEADER_DRIFT` pass (lines 792-799) and ran
`tests/core/test_global_accounting_allocation_certificate_v1_golden.py`,
`tests/core/test_asset_transfer_receipt_admission_v1.py` and
`tests/core/test_global_settlement_fcis_exact_ownership_v1.py`: **87 passed, 0 failed.**

`CHECK_ORDER_V1` is a list of labels compared against the golden fixture
(`tests/core/…_golden.py:48`) and one index assertion at line 337; neither observes runtime
behaviour, and the four codes collapse into a single label. The certificate has no analogue of
the admission's `test_witness_reject_family_and_check_order_match_the_rust_twin`, which pins
the in-function order across both languages. Since no witnessed vector can be carried in the
JSON fixture (a sealed witness is not serialisable), the golden vectors cannot cover it either.

**Minimal fix:** add a Python-side ordering test that mints one real witness, constructs the
two-condition case, and asserts which code fires — plus the Rust twin assertion — before the
registry flip makes these codes reachable.

### F-6 (P3) — the load-bearing subsumption has no executable evidence

`src/core/global_accounting_allocation_certificate_v1.py:807-812`. Deleting the `witness is
None and` guard (i.e. reverting the exemption that this commit introduces) survives
`tests/core/test_global_accounting_allocation_certificate_v1_golden.py`,
`tests/core/test_asset_transfer_receipt_admission_v1.py`,
`tests/core/test_global_settlement_fcis_exact_ownership_v1.py` and
`tests/core/test_global_accounting_lane_producers_v1.py`: **117 passed, 0 failed.**

The reasoning in §2.2 is sound, and I am not disputing it. The point is that the security
argument for the one *weakening* in this commit — a witnessed lane is no longer required to
commit `binding_root == lane_state_root` — currently lives only in a source comment and a
commit message. No mutation killer names it, and the packet does not list it as a mutation.

**Minimal fix:** record it as a declared mutation with a named killer that mints a real witness
whose `fragment.binding_root != fragment.lane_state_root` (the true receipt-backed shape) and
asserts the certificate accepts it while the same fragment without a witness is rejected with
`BINDING_ROOT_DRIFT`. That test is writable today with `ASSET_TRANSFER` still `NO_PRODUCER` by
calling `_check_lane_bindings` directly, as the golden suite already does for other passes.

### F-7 (P3) — Rust doc comment detached from its function and reattached to the new constant

`zk/global_settlement_abi_v1/src/global_accounting_allocation_certificate.rs:1282-1290`.

```rust
/// Total function: accept with the derived roots, or reject with the first failing closed code.
///
/// The certificate and state are validated first (`AbiErrorV1` on malformed input is
/// a parse-level failure, not a certificate reject). A reject never mutates and
/// carries the pre-state root twice.
/// Twelve empty witness slots in lane order: what every caller passes while no lane is witnessed.
pub const EMPTY_LANE_WITNESS_SLOTS_V1: [Option<&VerifiedLaneAllocationFragmentV1>; 12] = [None; 12];

pub fn check_global_accounting_allocation_certificate_v1(
```

The constant was inserted between the entry function's doc block and the function. Rustdoc now
renders the four-line contract of the checker as the documentation of a `[None; 12]` array, and
the public entry point of the Rust certificate twin has **no** doc comment at all. `cargo doc`
output for this module is wrong for both items.

**Minimal fix:** move the `pub const` (with only its own one-line doc) above the function's doc
block.

### INFO — Python/Rust zip strictness asymmetry

Python pairs fragments with slots using `zip(..., strict=True)` (line 781); Rust uses
`.zip(witnesses.iter().copied())` (`…:776-781`), which truncates silently. This is currently
unreachable — the entry point rejects any length other than twelve, and `certificate.validate()`
pins twelve fragments — so it is not a finding. Worth a comment noting that the private helper
relies on both length checks having already run.

---

## 5. What I checked and did not find a problem with

- Position ↔ lane correspondence of the slots tuple (guarded by `_check_lane_order` running
  first plus `strict=True`).
- Rejects still carry the unchanged pre-state root and no effects on the new codes (asserted in
  both the Python and Rust witness tests).
- `EMPTY_LANE_WITNESS_SLOTS_V1` length equals `len(ALL_LANE_IDS_V1)` equals 12 in both languages.
- The registry is untouched by S36; both golden replays still accept only the registered-empty
  certificate over an all-disabled state.
- The `InitVar` token is not retained on the instance.
- The private token is importable from the certificate module by any caller — unchanged in kind
  from C9a, where it was importable from the admission module; the declared residual covers it.
- The chain script's un-locked lifecycle test is genuinely not Lean-bearing.
- All 52 packet source pins, all six THV1 packets' source pins and test-pin file hashes, and all
  632 declared node ids.
- The claim ceiling, authority fields and `formal_core_complete`.

## 6. Lean gates

Run serially inside one `flock -w 7200 /tmp/zenodex-lean.lock` acquisition, on a tree verified
empty by `git status --short` at the start of the locked block, with Lean 4.27.0.

| Gate | Exit | Result |
|---|---|---|
| `tests/formal/test_lean_asset_transfer_refinement_v1.py` | 0 | **40 passed** in 17.16s |
| `tests/formal/test_lean_global_claimant_custody_relation_v1.py` | 0 | **6 passed** in 11.34s |
| `tests/formal/test_lean_global_accounting_allocation_certificate_v1.py` | 0 | **6 passed** in 8.70s |

The certificate gate's `test_exact_sources_are_pinned` compares
`sha256(src/core/global_accounting_allocation_certificate_v1.py)` against the pin
`f74e5cfc4a8276585b9814fdffc389d733d301ae4416cd0c182e4f7f4eab2bf3`; the worktree file hashes to
exactly that, so the gate's move to the new checker/twin/fixture hashes is consistent with the
subject.

`tests/core/test_zusd_liquidation_partition.py` was excluded throughout, as instructed
(pre-existing unrelated collection error).

## 7. Recommendation

**REVISE.** None of the findings invalidates the artifact, the replay, or the claim ceiling,
and none of them is reachable on an acceptance path today. But two of them must be resolved
*before* the C9b-2b registry flip, because the flip is what makes the new family live:

1. **F-1** — restore `slots=True` and correct the docstring. The commit hardens a gate while
   quietly softening the object the gate depends on, and the justification given for the
   softening does not hold on the pinned interpreter. Fix verified in-place: one line of source,
   one line of test.
2. **F-3** — settle whether `profile_root` pins the guest image id, and either prove it or bind
   `expected_image_id`.

**F-2** should be fixed in the same child candidate: a positive-pin file that contains two dead
copies of itself, one of them pinning a symbol that no longer exists, undercuts the mechanism
the whole exact-ownership gate is for.

F-4 through F-7 are cheap and can ride along.

Grade **B+**. The replay evidence is complete and clean, the type-boundary work is careful, the
subsumption argument is correct, the process repairs from P34 are genuinely closed and I
verified them directly rather than by reading. What holds the grade below A- is that the
headline object of the commit became strictly more forgeable than the version it replaced, on a
stated premise that is false; that the file whose entire job is mechanical pinning shipped two
dead copies of itself with a stale pin in one; and that three behaviours of the new family
(intra-family precedence, the presence-check precedence, and the binding-root exemption) have no
executable evidence.

Authority remains NONE. This ACCEPT/REVISE is advisory and moves no gate.
