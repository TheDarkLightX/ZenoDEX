# Opus 5 independent review — ZenoDEX Formal Functional Core Closure Campaign, candidate C9a'''' (P34)

| | |
|---|---|
| Subject | `9fb38be6aa5d6f593e0ee564ebeb2d61528d5a31` ("security: pin the exact-type gates positively and bring the candidate chain into the repository") |
| Artifact | `a22633f153608809148cadf3983ee7dec9426dfb` (P34; packet sha256 `d888b962413e22f39f7c431890bec85916cc54b5000c0730b6cff5f18256bf00` — matches) |
| Worktree | `/tmp/zenodex-formal-core-opus-c9a4` (detached, HEAD = P34, `git status --short` empty before and after) |
| Reviewer | Opus 5 (independent; advisory only — authority stays NONE, the claim ceiling does not move) |
| Date | 2026-09-02 |

**Grade: A-.  0 P1, 4 P2, 6 P3, 3 INFO.**

The candidate is sound and every repair it claims lands. All four P32 evasions I filed are now
killed by named tests, the composition killer is genuinely isolating, the lineage repair works and
is reached from the admission pipeline, and the Lean coverage exemption is load-bearing. The four
P2s are (a) a fifth evasion class the new positive pin cannot see, with a measurement of how thin
the behavioural coverage behind it is, (b) an import idiom the new closure binding does not follow,
and (c,d) two fail-open defects in the two shell scripts the packet has just pinned as its process
claim.

---

## 1. Replays and gates (all run in this worktree; commands and results)

Setup note (INFO-1): the documented worktree recipe omits `external/mathlib4`. Without it every
Lean-bearing replay command fails with `mathlib: package directory not found` and the checker
reports `EXECUTED_FAIL` with eight `REPLAY_EXIT_CODE` errors. After
`ln -sfn /home/trevormoc/deps/mathlib4 external/mathlib4` everything below is green. The recipe in
the reviewer prompt should list that symlink.

| Command | Result |
|---|---|
| `check_o008_formal_cycle_v1.py --root "$PWD" --packet-commit a22633f15` | exit 0, `ok true`, `packet_admitted true`, `current_source_drift []`, `proof_replay NOT_RUN` |
| same `--replay --esso-python /usr/bin/python3 --esso-pythonpath …/ESSO` | exit 0, `EXECUTED_PASS`, **30 runs**, `errors []`, no run with non-zero exit |
| `build_o008_formal_cycle_v1.py … --check --replay …` | exit 0, `{"drift":[],"mode":"check","ok":true,"subject_commit":"9fb38be6a…"}` |
| `cargo fmt --all -- --check` (zk/global_settlement_abi_v1) | exit 0 |
| `cargo clippy --locked --all-targets -- -D warnings` | exit 0 |
| `cargo test --locked` | exit 0 (unit + doc tests) |
| `tests/formal/test_lean_asset_transfer_refinement_v1.py` | **40 passed** (matches `TRANSFER_REFINEMENT_GATE_EXPECTED_PASSED_V1`) |
| `tests/formal/test_lean_global_claimant_custody_relation_v1.py` | 6 passed |
| `tests/formal/test_lean_global_accounting_allocation_certificate_v1.py` | 6 passed |
| `tests/core/test_transition_resource_bound_totality_v1.py` | 10 passed |
| `tests/core/test_global_settlement_abi_v1_resource_bounds.py` | **17 passed** (matches `PARITY_GATE_EXPECTED_PASSED_V1`) |
| `tests/core/test_global_settlement_abi_v1.py` | 75 passed |
| `tests/test_check_o008_formal_cycle_v1.py` | **390 passed** |
| `tests/test_check_global_settlement_canonical_manifest_v1.py` | 8 passed |
| `tests/core/test_asset_transfer_refinement_v1.py` | 113 passed (collects and runs) |
| `check_test_hygiene_v1.py --json` | exit 0 |
| `--base-ref a3183f546 --json` (parent of S34) | exit 0, ok, 19 changed / 7 critical, 182 packets |
| `--base-ref 42ccb6624 --json` | exit 0, ok, 73 changed / 23 critical |
| `--base-ref fd409ba6f7…cb85 --json` (campaign base) | exit 0, ok, 348 changed / 61 critical |
| Full pinned battery python list (18 files, one run) | **903 passed** |

Every Lean-bearing command ran under `flock -w 7200 /tmp/zenodex-lean.lock`. No SIGBUS.
`tests/core/test_zusd_liquidation_partition.py` excluded as instructed.

**Packet integrity.** All 100 `source_pins`/`test_pins` sha256 across the seven THV1 packets
(exact-ownership-v4, receipt-admission-v5, o008-formal-cycle-admission-v30,
test-hygiene-lineage-ordering-v2, certificate-v16, canonical-exact-admission-v5,
claimant-backing-guard-golden-v24) equal the bytes in the tree — no drift. All **213** distinct
`killed_by` node ids collect (222 tests; no dangling reference). `claim_ceiling` is
**byte-identical to P33** (every authority NONE, 0/12 value-movement gates). Source pins 48 → 50
(`tools/formal_core_candidate_chain_v1.sh`, `tools/formal_core_battery_v1.sh`), 30 replay commands,
13 nonclaims, `accepted_known_gaps` gains `exact_type_audit_epoch_path`.

---

## 2. Verdict per C9a'''' claim

### 2.1 Positive gate pin and widened negative scan (Opus P32 F-1, Fable P32 P3-1) — **CLOSED** for the declared spellings; see P2-1

I re-ran all four P32 evasions against the four scan tests. Each now fails a named test:

| Evasion (applied to `asset_lane_projection_v1.py:378`) | Failing tests |
|---|---|
| `from builtins import isinstance as _ii` then `not _ii(x, T)` | `…exact_type_gates_are_pinned_positively`, `…has_no_isinstance_spelling_variants` |
| `builtins.isinstance(x, T)` | both |
| `issubclass(type(x), T)` | both |
| `match self.post_state: case AssetLaneStateProjectionV1(): …` | both |

The mechanism is right: the pin is a set **equality** on `(module, definition, expression, type)`,
so any rewrite the scanner cannot see removes an element and fails. The licensed isinstance
inventory is now a multiset (`observed.setdefault(key, []).append(negated)`) with the two
enum-typed result-discrimination sites licensed on `asset_transfer_module_v1`, and
`arg.endswith("RejectedV1") or arg.endswith("RejectCodeV1")` is the correct widening.

### 2.2 Negation propagation (Opus P32 F-4) — **CLOSED**

`tests/core/test_global_settlement_fcis_exact_ownership_v1.py:389` propagates negation from the
`ast.UnaryOp`/`Not` down through every descendant, resetting at statement boundaries. My P32
rewrite `if not (isinstance(prepared, AssetTransferRejectCodeV1) and False):` now fails
`test_admission_path_isinstance_inventory_is_pinned` at line 419 (`assert not any(negations)`).
Residual: P3-1.

### 2.3 Module set bound to the import closure (Opus P32 F-5) — **PARTIAL**; see P2-2

Half is closed: adding a new bare-name `isinstance` to a listed out-of-scope module
(`asset_lane_coordinator_v1`, 4 → 5) fails
`test_admission_path_module_set_is_bound_to_the_import_closure` at line 848, because the test
asserts a dict **equality** on module → count. The 40 listed modules and their counts match the
tree today, and the walker's result is complete for the current source (I recomputed the closure
with a corrected walker: identical, 49 modules).

The other half is not: the walker at line 792 follows only `ImportFrom` nodes that *have* a
`module`, so three live idioms are invisible. See P2-2.

### 2.4 Isolated composition killer (Opus P32 F-3, Fable P32 P2-1) — **CLOSED**

`test_asset_lane_composition_accepted_rejects_root_bearing_subclasses` now feeds
`_wave_b_accepted().effects` (genuine) and matches `"post-state must be the exact typed value"`.
Deleting `asset_lane_projection_v1`'s post-state gate makes it fail with
`Actual message: 'asset lane accepted journal must be the exact typed value'` — the killer is
genuinely isolating, and the same test also kills a widening of that gate. Exactly what P2-1 of the
Fable review asked for.

### 2.5 Lineage key with a load-time monotonicity rule (Opus P32 F-2/F-9) — **CLOSED**

- The key keeps the date (`(lineage-with-date, version, path)`), so recency across lineages is
  date-first. My F-2 repro (`THV1-20260101-…-v99` against the current `THV1-20260902-…-v30`) cannot
  outrank: `sorted(..., reverse=True)[0]` is the newer-dated packet.
- The rule is reached **before any selection** and from the real pipeline, not only in a unit test.
  I built a subject snapshot carrying a same-lineage, older-dated, higher-version packet (with its
  `evidence_id` corrected so it clears `THV1_SHAPE` first) and
  `core.project_packet_v1` rejects with `THV1_LINEAGE_VERSION_REGRESSES_ACROSS_DATES`.
  `load_packets` calls the twin rule at `tools/test_hygiene_evidence_v1.py:337`, before
  `load_packet`.
- All 182 committed packets satisfy the rule today; exactly one stem spans two dates
  (`global-settlement-v1-canonical-exact-admission`: 20260901 v-less, then 20260902 v2..v5) and it
  is consistent.
- Distinct lineages that share a stem are **not** merged in the ordering (the sort key keeps the
  date); the rule does group them, which is a strictness, not an unsoundness. Residuals P3-3, P3-4,
  INFO-2.

### 2.6 Wording and registry (Opus P32 F-6/F-7/F-8) — **CLOSED**

Checked sentence against code, all three accurate:
- `_select_hygiene_packets` docstring now names the divergence ("additionally requires the selected
  packet to satisfy the contract rules for the changed path (evidence families, risk class), which
  this checker does not model").
- `exact_type_audit_epoch_path` is in `ACCEPTED_KNOWN_GAPS_V1` and in the packet's
  `v1_information_loss.accepted_known_gaps` (P33 had two entries, P34 has three).
- The entitlement nonclaim is now true. `_check_entitlement_rows`
  (`global_accounting_allocation_certificate_v1.py:684`) runs over
  `certificate.ordered_lane_fragments`; with ASSET_TRANSFER at NO_PRODUCER the check executes for
  the registered-empty certificate but this producer's rows never enter it. The same corrected
  sentence appears in the module docstring, both producers, the Rust twin, and `NONCLAIMS_V1`.

### 2.7 Unobservable mutation half withdrawn (Fable P32 P3-2) — **CLOSED**

receipt-admission-v5 declares only the killable half: *"drop receipt_root from the minted witness
(populating it early is unobservable: the value equals the fragment's binding_root after check
(4))"*, killed by `test_admitted_witness_exports_the_rebuilt_receipt_root`.

### 2.8 The process claim is in the repository (Fable P32 INFO) — **PARTIAL**; see P2-3, P2-4

Both scripts are committed at mode `100644` (`git ls-files -s` confirms), joined as
`candidate_chain_script` / `candidate_battery_script` in `SOURCE_PIN_ROLES_V1` and
`THV1_REQUIRED_PIN_PATHS_V1`, and pinned by admission-v30. I read both for correctness and found
two fail-open defects, below.

---

## 3. Verdict per C9a''' claim (P33 received no independent review; verified here in the P34 tree)

| Claim | Verdict | Evidence |
|---|---|---|
| Every caller value rebuilt at check (0) | **CLOSED** | `_rebuild_prior_fragment_v1` covers all 11 fields of `LaneAllocationFragmentV1` (3 explicit exact scalars, 3 exact `str` + `_require_root`, 5 exact tuples rebuilt row-by-row), then `replace(prior, **rebuilt)` re-runs `__post_init__`. `_require_exact_dataclass_scalars_v1` enforces `type(item) in {str,int,bool}` or a licensed `Enum` field name; `_snapshot_dataclass_tuple_v1` enforces `type(row) is expected_type`. The named forgery tests pass. |
| Deep rebuild at the transfer transition entry | **CLOSED** | `rebuild_asset_transfer_state_v1` is the single definition; `asset_transfer_lane_module_v1._snapshot_asset_transfer_state_v1` delegates to it. `context` and `command` are pure-scalar dataclasses and every base validator (`_require_token`, `_require_root`, `_require_atoms_u128`, `_require_nonnegative_int`, `_require_bool`) is `type(v) is not X`, so `replace()` is a full rebuild — no int-subclass or str-subclass survives. |
| Third F1 site and the module inventory | **CLOSED** for the declared killers | `receipt_backed_asset_lane_composition_v1` is in `_ADMISSION_PATH_MODULES` (now nine); neutering its candidate gate at line 83 is killed. General gap: P2-1. |
| Spoofed-journal test sharpened (Fable P30 P3-3) | **CLOSED** | The test varies `pre_lane_root` and recomputes `receipt_root` via `_receipt_root(...)` so every cross-check passes; only the exact-type gate can refuse. Minor: P3-5. |
| Lean claim surface | **CLOSED** | `rejectCode_ne_postStateResourceBoundExceeded` is in the core claim list, `report_vectors_cover_every_emittable_code` in `CHALLENGE_CLAIMS`; the coverage proof discharges the twelfth arm by `exact absurd h (rejectCode_ne_postStateResourceBoundExceeded …)` with no constructor-name exemption. **Verified by mutation**: giving the guard content (`… => cmd.amountAtoms ≠ 0` with the matching `Decidable`) breaks the lemma at `AssetTransferRefinementV1.lean:956` and the gate goes red (9 passed, 31 errors). `FORBIDDEN_PROOF_TOKENS` includes `native_decide`. |
| Corpus oracle exemption (Opus P30 NEW-5) | **CLOSED and honest** | `_check_corpus_coverage` skips an adjacent pair only when `pair[1] in unreachable`; the corpus row for `POST_STATE_RESOURCE_BOUND_EXCEEDED` gives a checkable reason and names the runtime witness suite `tests/core/test_transition_resource_bound_totality_v1.py`. `_parse_case` refuses any case that expects a code declared unreachable, so the declaration cannot silently coexist with a witness. |
| Packet-side selector mirror | **CLOSED** | `THV1_SELECTED_PACKET_STALE` fires as a second pass after `THV1_PIN_DRIFT`; `test_hygiene_selection_refuses_a_partly_stale_selected_packet` passes. The scoping limitation is stated in the docstring. |
| Thirtieth replay command | **CLOSED** | `python_rust_bound_parity_gate` is in `REPLAY_COMMANDS_V1:1439`, `COMPARABLE_SCHEMA_V1:3323`, `_grade_observation:4067`, and the checker suite's fake record. `_grade_pytest` rejects `REPLAY_PASSED_COUNT_DRIFT`; a non-zero exit is `REPLAY_EXIT_CODE`. I saw both surfaces fire empirically (my pre-symlink replay produced `EXECUTED_FAIL` with eight `REPLAY_EXIT_CODE` + `REPLAY_AUTHOR_RECORD_DRIFT` errors). Residual P3-6. |
| Declared residuals and wording | **CLOSED** | The module's DECLARED RESIDUALS block states all three precisely (`object.__new__` with well-formed consistent scalars; prior fragment bound only through `STALE_JOURNAL` until C9b; Python raises at check (0) where Rust returns `ACCEPTED_INVALID`, decided). The S30 correction is accurate: `src/core/asset_transfer_types_v2.py` contains 0 `isinstance`. |

---

## 4. Findings

### P2-1 — The positive pin is syntactic: a gate can be widened or emptied with the pinned text intact, and 70 of 84 gates have no behavioural killer

`tests/core/test_global_settlement_fcis_exact_ownership_v1.py:751` (`_exact_type_gate_sites`) records
only the shape `(module, definition, expression, type)` of each `type(x) is[ not] T` comparison. It
does not observe what the enclosing statement does with the result, and it does not observe any
*additional* disjunct. Two mutations therefore keep all four scan tests green:

```python
# (a) effect removed — pinned text unchanged
if type(self.post_state) is not AssetLaneStateProjectionV1:
    pass
# (b) widened with an alias the negative scan does not spell-check
import builtins as _b
...
if type(prior) is not LaneAllocationFragmentV1 and not _b.isinstance(
    prior, LaneAllocationFragmentV1
):
    raise TypeError("prior fragment must be the exact typed value")
```

Reproduction. Apply (b) to `src/core/asset_transfer_receipt_admission_v1.py:209`, then:

```
pytest tests/core/test_global_settlement_fcis_exact_ownership_v1.py -k \
  "inventory_is_pinned or exact_type_gates_are_pinned_positively or spelling_variants or module_set_is_bound"
# 4 passed
pytest <the 18 python files of tools/formal_core_battery_v1.sh>
# 903 passed
```

The alias survives because `test_admission_path_has_no_isinstance_spelling_variants:814` rejects
`builtins.isinstance` by unparsed text and rejects `import`/`from` aliases whose `alias.name` is
`isinstance`, but `import builtins as _b` has `alias.name == "builtins"`, and `_b.isinstance` is
neither a bare-name call (invisible to `_isinstance_sites`) nor one of the three rejected texts.

How much this matters depends on how many gates have a behavioural killer behind the syntactic pin.
I measured it: I neutered each of the 84 `if type(...) is[ not] T:` statements on the nine scanned
modules one at a time (body replaced with `pass`, pinned text untouched) and ran seven of the
battery's suites each time.

| | |
|---|---|
| Gate statements neutered | 84 |
| Killed by some test | **14** |
| Survived | **70** |

Survivors include every gate in `_rebuild_prior_fragment_v1` (lines 209, 219, 221, 225, 229), the
three transfer-transition entry gates (`asset_transfer_module_v1.py:333/335/337`), the deep-rebuild
gate (line 76), all six `_snapshot_asset_transfer_lane_module_input_v1` gates, all of
`lane_module_receipt_verification_v1` and all of `lane_module_release_route_binding_v1`.

**I did not find an exploitable instance, and I want that stated plainly.** I widened *both*
prior-fragment gates (admission line 209 and producer line 244) and tried the P28 F1 attack shape —
a `LaneAllocationFragmentV1` subclass with a `lane_state_root` property returning the genuine root
over a foreign stored field. It cannot even be constructed: the base is `slots=True`, so the
property shadows the slot descriptor and `__init__` raises
`property 'lane_state_root' … has no setter`. Every value the producer reads off the prior fragment
(`lane_id`, `producer_kind`, `enabled`, `module_release_id`, `lane_state_root`) is a stored field,
not a derived property. So this is a **detection gap, not a demonstrated bypass**.

The packet's own mutation wording ("weaken any exact-type gate on the path to
`issubclass`/`__class__`/alias") and the test docstring are accurate about what they cover. What is
missing is the statement of what they do not cover.

Minimal fix (two parts): (1) in `_exact_type_gate_sites`, also record the enclosing `ast.If`'s body
shape (e.g. that `body[0]` is a `Raise`) and whether the `If.test` is exactly the Compare rather
than a Boolean combination, and pin that too; (2) in
`test_admission_path_has_no_isinstance_spelling_variants`, reject any `ast.Call` whose unparsed func
ends in `.isinstance`/`.issubclass`, and reject `import builtins` on these modules outright. Then
record in the packet nonclaims that the pin is structural and that 14 of 84 gates carry a
behavioural killer.

### P2-2 — The import-closure binding does not follow `from . import X`, `from src.core import X`, or `import src.core.X`

`tests/core/test_global_settlement_fcis_exact_ownership_v1.py:792`:

```python
if isinstance(node, ast.ImportFrom) and node.module:
    if node.level == 1:
        frontier.append(node.module)
    elif node.module.startswith("src.core."):
        frontier.append(node.module.split(".")[-1])
```

`from . import X` parses as `ImportFrom(module=None, level=1)`, so `and node.module` skips it
entirely. `from src.core import X` has `module == "src.core"`, which fails
`startswith("src.core.")`. Plain `ast.Import` is never examined. `from . import X` is a live idiom
in this package (`amm_dispatch.py:28`, `routing.py:35-39`, `zdex_spot_buyback_transition_v2.py:19`
and others).

Reproduction — the admission entry module gains a real `src.core` dependency and the binding stays
green:

```python
# src/core/asset_transfer_receipt_admission_v1.py
from . import zdex_tokenomics_buyback_transition_v1 as _unscanned   # 3 isinstance, invisible
_UNSCANNED = _unscanned
```
```
pytest tests/core/test_global_settlement_fcis_exact_ownership_v1.py -k \
  "inventory_is_pinned or exact_type_gates_are_pinned_positively or spelling_variants or module_set_is_bound"
# 4 passed
```

Today's closure is complete (I recomputed it with a corrected walker: the same 49 modules, no
misses), so this is a latent evasion, not a present unsoundness — but it defeats precisely the
"forces an inventory decision" property F-5 asked for.

Minimal fix, same function:

```python
if isinstance(node, ast.ImportFrom):
    if node.level == 1 and node.module is None:
        frontier.extend(a.name for a in node.names)
    elif node.level == 1 and node.module:
        frontier.append(node.module)
    elif node.module == "src.core":
        frontier.extend(a.name for a in node.names)
    elif node.module and node.module.startswith("src.core."):
        frontier.append(node.module.split(".")[-1])
elif isinstance(node, ast.Import):
    frontier.extend(a.name.split(".")[-1] for a in node.names if a.name.startswith("src.core."))
```

### P2-3 — `tools/formal_core_battery_v1.sh` exits 0 with every gate red

The script sets `set -u` only. Each of the four gate groups ends in
`echo "… exit $?"` (lines 44, 49, 50, 51) and nothing propagates. The whole body is a `{ … } > "$OUT"`
group, so the script's exit status is the status of the final `echo`.

Reproduction (decisive, ~1 s, runs no real tests):

```
$ FORMAL_CORE_PY=/bin/false FORMAL_CORE_LEAN_LOCK=/tmp/x.lock \
    bash tools/formal_core_battery_v1.sh /tmp/battery.log ; echo "EXIT=$?"
EXIT=0
$ cat /tmp/battery.log
battery start … head=a22633f15
python exit 1
esso exit 1
lean1 exit 1
lean2 exit 1
battery done …
```

Any caller writing `bash tools/formal_core_battery_v1.sh log && <next step>` proceeds on a fully red
battery. The packet now pins this script as `candidate_battery_script` and the candidate message
asserts the battery was run, so the artifact carries a process claim that the script cannot enforce.

Minimal fix: accumulate, e.g. `rc=0`, then `… ; s=$?; echo "python exit $s"; rc=$((rc|s))` for each
group, and `exit $rc` after the group (moving the redirect so the status survives).

### P2-4 — `tools/formal_core_candidate_chain_v1.sh` pushes and tags on a red checker replay or a red builder round trip

Lines 41-47:

```
41  flock … check_o008_formal_cycle_v1.py --packet-commit "$P" --replay … > "$REPORT" 2>&1
42  echo "checker replay exit $?"
43  flock … build_o008_formal_cycle_v1.py … --check --replay … 
45  echo "builder check exit $?"
46  git push -q origin "$BRANCH" && echo pushed
47  git tag "$TAG" "$P" && echo "tagged $TAG"
```

The two independent verification steps — the checker's admission of P, and the builder round trip
that detects packet drift — have their exit codes consumed by `echo` and never tested. The chain
then pushes and tags unconditionally, and (having no `set -e` and ending in `echo`) returns 0.

The steps that *are* guarded stop correctly: the two hygiene gates (lines 32, 33) and the build-time
`--replay` (line 36) each carry `|| exit 1`, and `_author_record` raises `REPLAY_EXECUTED_FAIL` when
the replay is not `EXECUTED_PASS`, so a red replay genuinely prevents P from existing. The script's
docstring line *"Any red step stops the chain before P exists"* is therefore literally true and
materially misleading: an author/checker disagreement after P is committed — exactly the defect
class this campaign exists to catch — is pushed, tagged, and reported as success.

Minimal fix: add `|| { echo "CHECKER RED"; exit 1; }` to line 41 and
`|| { echo "BUILDER CHECK RED"; exit 1; }` to lines 43-44, and correct the docstring to say the
chain also refuses to push or tag when the post-commit verification is red.

### P3-1 — Negation detection covers only `not`, not `is False` / `== False`

`_isinstance_sites` (line 389) treats only `ast.UnaryOp`/`Not` as negation. Rewriting a licensed
site as `if isinstance(prepared, AssetTransferRejectCodeV1) is False:` reports `negated=False` and
all four scan tests pass. Low impact: the two licensed sites are result discrimination on closed
returns, so inverting them breaks behaviour that the battery catches. Fix: also set `negated` when
the call is the `left` of a `Compare` against `ast.Constant(False)` under `Is`/`Eq`.

### P3-2 — The out-of-scope licence comment gives a rationale that is not true of every listed module

The comment block at `tests/core/test_global_settlement_fcis_exact_ownership_v1.py:702-706` says the 40 listed modules are
"lanes and services the admission never reads rows from, plus the shared helpers whose
`isinstance(..., Enum)` checks are against the abstract base". Only two modules match the second
clause (`global_economic_refinement_snapshot_v1`, `global_economic_profile_snapshot_v1`), and the
first clause is a claim about read *direction* that does not address the listed modules' own gates:
`asset_lane_coordinator_v1` uses `isinstance` on `AssetLanePrivatePortV1`,
`LaneModuleTransitionJournalV1` and `GlobalEconomicEffectPlanV1`, and `epoch_effect_composition_v1`
on `GlobalEconomicEffectPlanV1` — the very types the admission path exact-gates. The packet's
nonclaim ("Exact-type gating is audited and mechanically pinned only on the receipt-admission
path") is correct; the comment should say "outside the audited scope" rather than offering a safety
argument that reads stronger than it is.

### P3-3 — The monotone rule refuses a version reset the ordering key already handles

`require_lineage_versions_monotone_with_dates_v1` raises whenever `date_a < date_b and
version_a >= version_b` within a date-stripped stem. That covers the F-2 shape, but it also refuses
a legitimate fresh cut:

```
THV1-20260830-global-settlement-exact-ownership-v4.json   (v4)
THV1-20260903-global-settlement-exact-ownership.json      (fresh lineage, v-less)
→ TestHygieneError: versions must rise with the date prefix
```

yet `sorted(..., key=hygiene_lineage_key_v1, reverse=True)[0]` is already the 20260903 packet — the
date-first key orders it correctly. The rule is accurately documented, so this is a strictness the
campaign now has to live with (version numbers must rise forever within a stem); it will surface the
first time a stem is re-cut without carrying the version.

### P3-4 — The monotone rule's wiring is not covered by a repository test

`tests/test_check_test_hygiene_v1.py:500-514` calls
`require_lineage_versions_monotone_with_dates_v1` and
`o008._require_hygiene_lineage_versions_monotone_v1` **directly**. No test drives
`_select_hygiene_packets`, `project_packet_v1`, or `load_packets` with a mis-dated packet set, so
deleting either call site (`o008_formal_cycle_admission_v1.py:3257`,
`test_hygiene_evidence_v1.py:337`) leaves the suite green. I verified the wiring by hand — a
poisoned snapshot rejects with `THV1_LINEAGE_VERSION_REGRESSES_ACROSS_DATES` — so the code is right;
it is the regression lock that is missing. Fix: assert the projection reject code, as
`test_hygiene_selection_refuses_a_partly_stale_selected_packet` already does for its sibling.

### P3-5 — The spoofed-journal test still matches the generic message

`tests/core/test_asset_transfer_receipt_admission_v1.py:303/312` matches `"exact typed value"`,
which every gate in `AssetTransferLaneModuleAcceptedV1.__post_init__` emits. Fable P32 P2-1 asked
for exactly this sharpening on the composition killer and it was done there; the same one-word
change (`match="accepted journal must be the exact typed value"`) makes this test isolating too.

### P3-6 — Seven of the thirty replay commands have no per-command drift parametrization

`lean_certificate_direct_check`, `lean_certificate_axioms_probe`, `lean_certificate_binding_gate`,
`prior_restage_gate`, `transfer_refinement_gate`, `python_rust_bound_parity_gate`,
`python_golden_gate` appear only in the fake-record fixture
(`tests/test_check_o008_formal_cycle_v1.py:1120-1147`), not in the
`pytest.param(... "REPLAY_PASSED_COUNT_DRIFT" ...)` families. They share the covered `_grade_pytest`
/ `_grade_lean` paths and `COMPARABLE_SCHEMA_V1` catches a missing grader (an ungraded command
yields `comparable {}` → `REPLAY_AUTHOR_RECORD_DRIFT`), so the risk is small — but the newest
command of the thirty is the one without its own drift case.

### INFO

- **INFO-1** — the reviewer worktree recipe omits `external/mathlib4 -> /home/trevormoc/deps/mathlib4`;
  without it every Lean replay command fails and the checker reports `EXECUTED_FAIL`. Worth adding
  to the handoff so a reviewer does not mistake it for a candidate defect.
- **INFO-2** — a `-vN-vM` stacked name (`THV1-20260101-…-admission-v30-v99.json`) forms a *different*
  date-stripped lineage (`o008-formal-cycle-admission-v30`) and so escapes the monotone rule; it
  cannot outrank, because the date-first key still puts the 20260902 packet first. No action needed;
  noting it so a future reader does not assume the rule groups every variant of a stem.
- **INFO-3** — `tools/test_hygiene_evidence_v1.py:83` — `_PACKET_FIELDS` follows the new function
  with no blank line separation.

---

## 5. What this review does not claim

I ran every replay, gate, and suite listed in section 1 in an isolated detached worktree and left it
byte-clean. I did not modify the author's worktree, the canonical checkout, or any other reviewer's
worktree. This review is advisory: it grants no authority, and the claim ceiling it examined is
byte-identical to P33 with every authority field at NONE and 0 of 12 value-movement gates closed.
The four P2s are gaps in *detection and process*, not demonstrated bypasses of the admission path;
I looked for an exploitable instance of P2-1 and could not construct one.
