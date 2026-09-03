# ZenoDEX Formal Functional Core Closure — C9c-4 (P41) independent review

| field | value |
|---|---|
| subject | S41 `f111ec292f01dbaede9cf0cdfee8d1594989f456` — "fix: make the evidence standard real, and say what UNDETERMINED actually means" |
| artifact | P41 `d2195c5e872bd89c098fa9b5abd5ff3db9820674` (artifact-only child; complete diff = `docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.{json,md}`) |
| packet json sha256 | `c269a5f2b19a4627ea0aad25cfd06d85e776aeab277b71352ea72a50d9598456` (recomputed; matches the expected value) |
| worktree | `/tmp/zenodex-formal-core-opus-c9c4` (detached at P41; `git status --short` empty at start and at end) |
| reviewer | independent Opus 5 session, fresh context |
| date | 2026-09-03 |
| verdict | **B** — 1 P1, 6 P2, 7 P3, 1 INFO. ACCEPT is **not** advised until the P1 is closed. Authority stays NONE; the claim ceiling did not move. |

**Independence caveat.** The campaign's second reviewer is normally Fable 5.1, which is out of credit until
2026-09-06, so this round's reviewers and the author again share a model family. I did not read the author's
worktree or scratchpad, the other reviewer's worktree, or the canonical checkout.

---

## 1. Replays

Every Lean-bearing command ran under `flock -w 7200 /tmp/zenodex-lean.lock`.
`PY=/home/trevormoc/Downloads/Autonomous Tau DEX/.venv/bin/python`, `PYTHONDONTWRITEBYTECODE=1`,
`CARGO_TARGET_DIR=/tmp/zenodex-opus-c9c4-cargo`, `CARGO_INCREMENTAL=0` (deleted at the end).

| command | result |
|---|---|
| `check_o008_formal_cycle_v1.py --root $PWD --packet-commit d2195c5e8` | exit 0; `ok true`, `packet_admitted true`, `current_source_drift []`, `errors []`, `proof_replay NOT_RUN` |
| same `--replay --esso-python /usr/bin/python3 --esso-pythonpath .../ESSO` | exit 0; **`EXECUTED_PASS`, 38 runs**, `ok true`, `errors []`, `current_source_drift []`. Result sha256 `df95fa4f22a23d1b165978f940f01abebff5b601b8882f472280a28e76902883`. Lean 4.27.0, `lean_axioms_probe` 25 theorems / certificate 16, both binding gates 6, `transfer_refinement_gate` 40; both ESSO models VERIFIED with deterministic fingerprints, gates 20 / 24 |
| — the six ledger runs inside it | `ledger_projection_rows` **24**, `ledger_tool_rows` **18**, `ledger_admission_rows` **31**, `ledger_ownership_rows` **21**, `ledger_certificate_rows` **2**, `ledger_lineage_rows` **1** = **97 killed, 0 survived, 0 errors**, each exit 0 and each `mechanical == killed` — exactly the declared figures |
| `build_o008_formal_cycle_v1.py ... --subject-commit f111ec292 --created-date 2026-09-03 --check --replay ...` | exit 0; `{"drift":[],"mode":"check","ok":true,"subject_commit":"f111ec292..."}`; `git status --short` empty afterwards and the packet still hashes to `c269a5f2...` — it regenerates byte-for-byte from S41 |
| `cargo fmt --all -- --check` (`zk/global_settlement_abi_v1`) | exit 0 |
| `cargo clippy --locked --all-targets -- -D warnings` | exit 0 |
| `cargo test --locked` | exit 0; 54 `test result: ok` summaries, **536 passed**, 0 failed — the declared figure (535 at P40, +1 for the new unit test) |
| `tests/core/test_global_accounting_allocation_projection_v1.py` | **79 passed** (`PROJECTION_GATE_EXPECTED_PASSED_V1 = 79`) |
| `tests/formal/test_lean_asset_transfer_refinement_v1.py` (under the lock) | exit 0; **40 passed** in 17 s |
| `tests/core/test_transition_resource_bound_totality_v1.py`, `…abi_v1_resource_bounds.py`, `…abi_v1.py`, `test_check_global_settlement_canonical_manifest_v1.py`, `test_thv1_mutation_ledger_v1.py` | one run, **129 passed** |
| `tests/test_check_o008_formal_cycle_v1.py` | **398 passed** in 242 s (392 at P40; +6, the new ledger-grader tests) |
| `check_test_hygiene_v1.py --json` | exit 0; `ok true`, `evidence_packet_count 231`, `changed_path_count 0` |
| `--base-ref ad91dbae4 --json` (parent of S41) | exit 0; `ok true`, 231 packets, 17 changed |
| `--base-ref fd409ba6f7d… --json` (campaign base) | exit 0; `ok true`, 231 packets, 414 changed — **the campaign base is green** |

`tests/core/test_zusd_liquidation_partition.py` excluded as instructed.

**Environment note (mine, not the candidate's).** The symlink recipe in the review brief is incomplete, as
both P40 reviewers recorded: `lean-mathlib/lakefile.lean:7` does `require mathlib from "../external/mathlib4"`,
so `external/mathlib4` **and** `lean-mathlib/.lake/packages/mathlib` must both point at
`/home/trevormoc/deps/mathlib4`. My first `--replay` was launched before I added them and returned
`EXECUTED_FAIL` with seven `REPLAY_EXIT_CODE` + seven `REPLAY_AUTHOR_RECORD_DRIFT` errors on exactly the seven
Lean commands. With the two symlinks in place the replay is the row above. Both symlinks are gitignored;
`git status --short` stayed empty. **Not a finding against the candidate.**

**Concurrency check on the ledger runs.** The six ledger replay commands declare no `--workdir`, so
`_default_workdir()` (`tools/thv1_mutation_ledger_v1.py:424-426`) resolves to `$TMPDIR/thv1-ledger`, and with
`TMPDIR` unset that is the shared `/tmp/thv1-ledger`; `run_ledger_v1` `rmtree`s an existing
`<workdir>/<packet>` before recreating it, and another reviewer was replaying the same packet names
concurrently. My two replays agreed exactly, but I re-ran this candidate's own three Python ledger packets a
third time under an isolated `TMPDIR=/tmp/zenodex-opus-c9c4-tmp`:

| packet | isolated re-run |
|---|---|
| `THV1-20260903-global-accounting-allocation-projection-v4` | exit 0; mechanical 24, **killed 24**, survived 0, errors 0, every verdict `KILLED` |
| `THV1-20260903-thv1-mutation-ledger-v5` | exit 0; mechanical 18, **killed 18**, survived 0, errors 0 |
| `THV1-20260902-test-hygiene-lineage-ordering-v5` | exit 0; mechanical 1, **killed 1**, survived 0, errors 0 (3 legacy) |

Identical to both replays. `THV1-…-certificate-v23`'s two rows I verified by hand instead (the Rust row by
deletion, §1 table); `ledger_admission_rows` and `ledger_ownership_rows` are unchanged from P40 and replayed
identically twice. See INFO-1 for the hazard itself.

### Pin and node-id audit — clean

* O-008 packet: **58** `source_pins`, **58** distinct roles, every one byte-exact on `sha256`, `size` and
  `git_blob` (`git hash-object`); 0 mismatches. **38** replay commands, six of them ledger runs.
  `hygiene_selection`: 55 rows over 7 distinct packets, all `packet_sha256` / `packet_git_blob` exact.
* The five THV1 packets this candidate cuts: **87** `source_pins` + `test_pins`, 0 bad; **707** pinned node
  ids, **0 orphans**. No duplicate `(path, needle, replacement)` triple in any of the five.
* `subject_tree 1e82e689c5412ab5a3cbdd3ee6d1a2c3955b6ee8` = `git rev-parse f111ec292^{tree}`;
  `subject_parent` = `ad91dbae4`; `packet_commit_parent` = `f111ec292`. P41's complete diff is the two packet
  files. All ten `created_date` fields are `2026-09-03`.
* Claim ceiling byte-identical to P40: every authority axis `NONE`, `formal_core_complete false`,
  `o008_status OPEN_EXACT_ALL_12_RECONCILIATION_MISSING`, `value_movement_gates_closed 0 / 12`.
  **The ceiling did not move.**
* The four required nonclaims are present in `THV1-…-projection-v4`: no Rust twin (6), the fixture partition
  is not a general property (9), a refusal does not say the state is invalid (10), nothing consumes it (2).

### Mutation spot-checks (applied by hand, run, restored; `git status --short` empty after each)

| row | needle → replacement | named killer | observed |
|---|---|---|---|
| projection-v4 #21 `ROWS_BEYOND_PRODUCER` | `                if beyond:` → `… and False:` | `test_which_row_cases_the_entry_point_reaches_is_pinned[…]` (I ran all twelve params) | **10 failed**, 2 passed — kills |
| projection-v4 #22 `TERMINAL_WITHOUT_BACKING` | `        if not principals:` → `… and False:` | `test_a_terminal_with_no_controlling_principal_…` | **1 failed** — kills |
| projection-v4 #24 `REGISTERED_EMPTY_ROOT_DRIFT` | `        if registered_root is not None and …:` → `… and False:` | `test_the_two_state_level_shapes_are_refused_not_derived[…]` (both params) | **1 failed**, 1 passed — kills |
| certificate-v23 #2 (Rust) | the six-line guard → `        let _ = controlled;` | `…certificate.rs::global_accounting_allocation_certificate::tests::the_source_principal_guard_refuses_and_the_check_is_what_refuses` | `cargo test --locked` **exit 101**, 0 ok-summaries, 1 FAILED; the declared `--lib` filter selects exactly 1 test and it fails — **kills** |

---

## 2. One verdict per claim

### C1. The evidence standard is executed, not declared — **CLOSED**

`_no_certificate_reconciles` (`tests/core/test_global_accounting_allocation_projection_v1.py:237`) is now
called from `test_an_unreconcilable_row_case_has_its_state_consistent_candidate_refused` (`:799`) for the
eight `_ROW_CASES` whose code is in `_UNRECONCILABLE_ROW_CODES`. The primary P40 reviewer's falsification now
kills:

```bash
sed -i 's/^def _no_certificate_reconciles(state) -> str:$/&\n    raise AssertionError("MUTANT")/' \
    tests/core/test_global_accounting_allocation_projection_v1.py
"$PY" -m pytest -q tests/core/test_global_accounting_allocation_projection_v1.py -p no:randomly | tail -1
#   -> 8 failed, 71 passed        (at P40 the same mutant left the suite at 53 passed)
```

The commit's arithmetic is exact. I re-ran the eight cases with the terminal rows stripped and
`_check_terminal_bindings`/`_check_terminal_totals` removed, and **four** of the eight return `"ACCEPTED"`
without them (`one terminal over-claiming its entitlement`, `two terminals over-claiming together`,
`a claimant with no entitlement at all`, `an OPEN obligation naming another lane`); with them the same four
return `TERMINAL_BINDING_DRIFT`. So the added rows and checks are load-bearing, not decoration.

**What it establishes, judged rather than taken.** For those eight states the candidate is refused by a
checker pass, not by the projection's own answer — that is a real change of standard. Two limits survive.
(a) `_no_certificate_reconciles` still omits `_check_reserve_rows`, which `CHECK_ORDER_V1`
(`…certificate_v1.py:1005-1019`) places between the entitlement and external passes. The omission is
conservative (it can only make the helper return `"ACCEPTED"` and fail the test), so it is not a soundness
hole, but the helper's returned code is still not necessarily the code the full checker returns. (b) The
stated limitation is stated **wrongly** — see P2-1.

### C2. UNDETERMINED no longer claims two ACCEPTED certificates — **PARTIAL** (P1)

The exhibition is real, and stronger than the test asserts. I rebuilt it independently: state with custody
`(USD, pool-a, spot-pool, 6)` + `(USD, pool-b, spot-pool, 4)` and one PENDING outbox entry, two candidates
differing only in `source_principal`:

```
pool-a  0x611cd6ed0b43c02a…  exactly_once:PASS entitlement:PASS reserve:PASS external:PASS
                             terminal_bindings:PASS lane_aggregates:PASS terminal_totals:PASS
pool-b  0xb4fecce221699c58…  (same seven PASS)
distinct allocation roots: 2      full checker over both: RECEIPT_WITNESS_REQUIRED
```

Two different roots, both passing **all seven** row/partition/aggregate passes — the test itself runs only
four of the seven (`exactly_once`, `entitlement`, `external`, `lane_aggregates`), so the exhibition holds a
claim the test does not fully check (P3-1).

The correction landed in five places: the module docstring
(`src/core/global_accounting_allocation_projection_v1.py:17-36`), the enum docstring (`:98-136`), the test
module docstring (`:12-26`), the two new test docstrings (`:799-817`, `:825-838`) and the projection packet's
`claim_scope`. It did **not** land in the two places both P40 reviews named by number: THV1 nonclaim 7 and
O-008 nonclaim 5. Both still say "accepted"; nonclaim 7 additionally still says "the checker would take
either", which the candidate's own new test refutes on the same state. **P1.**

### C3. Which row cases the entry point reaches is pinned — **CLOSED for the pin, NOT for the claim** (P1)

`test_which_row_cases_the_entry_point_reaches_is_pinned` (`:869`) is accurate. I ran all twelve cases through
`project_allocation_certificate_v1` myself: exactly two reach their own code (`entitlements exceeding
custody` → `PROJECTION_NEGATIVE_RESIDUAL`, `controlled atoms no obligation can absorb` →
`PROJECTION_UNASSIGNED_CONTROLLED_ATOMS`); the other ten are masked by `PROJECTION_ROWS_BEYOND_PRODUCER`.
That is exactly the set the test fixes.

**The reviewer's Falsification B is closed.** The new `_state_level_refusals_v1` gate
(`…projection_v1.py:277-311`, run at `:527` before the binding roots) refuses every enabled lane whose
registry entry is not `RECEIPT_BACKED`. I swept all twelve lanes with an OPEN terminal on the enabled lane:
`ASSET_TRANSFER` → `PROJECTION_BINDING_ROOT_MISSING`, the other eleven → `PROJECTION_ENABLED_LANE_WITHOUT_PRODUCER`.
The `SPOT_LIQUIDITY` probe that reached `PROJECTION_TERMINAL_EXCEEDS_ENTITLEMENT` at P40 no longer does. I
also checked the gate is sound rather than merely convenient: any certificate that survives the checker's
first lane-binding pass must copy `enabled` and `lane_state_root` off the state, so `BLOCKED_LANE_PRODUCER_MISSING`
and `REGISTERED_EMPTY_ROOT_DRIFT` are unavoidable for those states — the projection refuses nothing the
checker would have accepted.

But the falsified sentence itself survives verbatim in THV1 nonclaim 8 and in `_derive_rows`'s docstring
(`tests/core/…_projection_v1.py:92`, "and they are not reachable through the public entry today"). **P1.**

### C4. The headline guard has a mechanical row — **CLOSED**

`projection-v4` row #21 mutates `                if beyond:` and kills (above). I enumerated every guard in
the module that feeds `_fail` (22 of them) and matched each against the packet's 24 needles: every refusal
guard is covered, including the three new ones. The only two `if` lines with no row are
`if owning_lane is not None:` / `if owning_lane is None:`, which are scoping conditions whose inner guards
are covered.

**Other guards added in C9c-3/C9c-4 that still have none — yes, three, all in the tooling** (P2-5).

### C5. The Rust guard is tested by something that calls it — **CLOSED**

`the_source_principal_guard_refuses_and_the_check_is_what_refuses`
(`zk/global_settlement_abi_v1/src/global_accounting_allocation_certificate.rs:1454-1510`) calls
`check_external_obligations` directly and asserts both the reject code and that the detail ends with
`source binding`. Deleting the guard body now fails the crate (`cargo test --locked` exit 101, the only
FAILED summary being the lib target). The integration test was rewritten to pin the structural reason a unit
test was necessary. The new killer form is declared and executes.

**The brief's attack on the new form.** No, a filter cannot qualify a mutant it does not exercise: a filter
that selects no test, or only passing tests, leaves `cargo test --lib` at exit 0, and `mutant_verdict_v1`
(`tools/thv1_mutation_ledger_v1.py:254-264`) returns `SURVIVED` on exit 0 and `UNVIABLE` when no summary
reports a failure. A `KILLED` verdict still requires a test that actually fails under the mutation. What the
form **does** lose is the binding between the row's declared file and the test that runs (P2-4).

### C6. The ledger grader refuses three more shapes — **CLOSED**, and the two follow-on questions check out

`_grade_ledger` (`tools/o008_formal_cycle_admission_v1.py:4092-4165`) now refuses non-hex-64 digests
(`REPLAY_LEDGER_ROW_WITHOUT_MUTATION`), repeated `(path, needle_sha256, replacement_sha256)` triples
(`REPLAY_LEDGER_ROW_NOT_DISTINCT`) and unportable paths (`REPLAY_LEDGER_ROW_PATH_UNPORTABLE`). I re-ran the
primary P40 reviewer's own bypass — 20 identical KILLED rows with `path "/etc/passwd"` and digests `"a"`/`"b"`
— and every variant is now refused; uppercase hex is refused too. Six new tests
(`tests/test_check_o008_formal_cycle_v1.py:1205-1297`) cover the three codes plus a green complement.

(a) **The deduplication is real and the numbers went the right way.** I scanned all 231 packets for repeated
mechanical triples: exactly three carry them, and all three are the *superseded* cuts this candidate replaced
(`thv1-mutation-ledger-v3` 19/18, `-v4` 22/18, `test-hygiene-lineage-ordering-v4` 2/1). The five new packets
carry none, and no other packet in the tree does. The commit's arithmetic — "the previous 97 contained five
repeats, so this is 92 distinct rows before this candidate and 97 after" — is exactly right (v4's four
repeats plus lineage-v4's one). The new totals 24+18+31+21+2+1 = 97 replay as 97 KILLED, 0 SURVIVED, 0 errors.

(b) **The disclosure about the withdrawn path guard is accurate.** `_grade_ledger` says it cannot check that
the mutated path is one the THV1 packet pins, and that this binding belongs to the packet validator. Both
halves check out: I fed the grader 24 rows whose path is `src/core/definitely_not_a_real_file.py` and it
accepted them, and `tools/test_hygiene_evidence_v1.py:289` is where `mutant path is not a pinned source path`
is enforced, in a tool the O-008 checker's 38 commands do not run (O-008 nonclaim 14 says so). The *test*
helper's docstring, however, still describes the withdrawn guard as if it shipped (P3-3).

### C7. A terminal with zero candidate principals — **CLOSED as code, NOT as claim** (P2-2)

`PROJECTION_TERMINAL_WITHOUT_BACKING` exists, sits in the `unreconcilable` kind, and its row kills. The
entry-point half of the unreachability claim holds (I could not reach it through
`project_allocation_certificate_v1` on any lane). The **harness** half is false: a zero-atom entitlement row
reaches it through `_derive_rows`, because the residual is then exactly 0 and the negative-residual check the
docstring names as the pre-empting check does not fire.

### C8. The three kinds are held as data and pinned as a partition — **PARTIAL** (P2-3)

`ALLOCATION_PROJECTION_REFUSAL_KINDS_V1` (`…projection_v1.py:165-186`) is a genuine partition of all sixteen
codes, `test_the_three_refusal_kinds_partition_the_family` (`:500`) pins it, and it additionally requires
every code to be named in the enum docstring — a real repair of both reviews' P3-1. The two `caller_input`
codes are correctly placed (they are about the supplied `lane_binding_roots`, not the state), and
`PROJECTION_ROWS_BEYOND_PRODUCER` is correctly `unreconcilable`.

One code is in the wrong kind: `PROJECTION_EXTERNAL_RESIDUAL_AMBIGUOUS` is raised for a state class whose
row-checked certificate is **unique** (P2-3).

### C9. Stated-open items — **both confirmed open, as stated; opus2 P2-7 reproduces unchanged**

* Opus P40 P2-4: `THV1-20260902-global-settlement-v1-canonical-exact-admission-v10` and
  `THV1-20260901-claimant-backing-guard-golden-v29` are each referenced only by their own file. Confirmed open.
* opus2 P40 P2-7: I reproduced it at S41. Take `_witnessed(with_rows=True)`, add one atom to the single
  custody row and the matching liability row, keep the lane root: the projection **derives** a certificate,
  which the only minted witness for that root refuses `RECEIPT_WITNESS_FRAGMENT_DRIFT` and empty slots refuse
  `RECEIPT_WITNESS_REQUIRED`. So module docstring claim 2 — "Where NO certificate over the state can be
  accepted, the projection refuses" — is still false, and the exception is disclosed only in the commit
  message, nowhere in the code or the packets (P3-7).

### C10. The packet — **CLOSED except for nonclaim 5**

58 pin roles, 38 replay commands, authority NONE, `formal_core_complete false`, required nonclaims present.
Nonclaim 5 carries the P1.

---

## 3. Findings

### P1 — The two sentences this candidate exists to correct survive **verbatim** in the evidence packets it cuts, including the top-level nonclaim the author edited in the same commit

**Where.** Three places, one fix:

1. `tools/o008_formal_cycle_admission_v1.py:557-571` → `docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.json`
   nonclaim 5 (and `.md:227`): *"**Two kinds** of refusal share that family … UNDETERMINED means more than
   one **acceptable** certificate exists"*.
2. `tests/evidence/test_hygiene/THV1-20260903-global-accounting-allocation-projection-v4.json:509`
   (nonclaim 7): *"a cell controlled by two principals admits **two accepted certificates** over one state
   with different allocation roots. The projection refuses such a state rather than choosing; **the checker
   would take either**."*
3. the same packet, `:510` (nonclaim 8): *"Under the current registry the reserve, external and terminal
   derivation is **unreachable through the public entry point**…"*, repeated at
   `tests/core/test_global_accounting_allocation_projection_v1.py:92`.

**Why this is the P1 and not a P3.** These are not incidental restatements. opus2 P40 P1-1 named
"`…projection-v3.json` `claim_scope` **and nonclaim 7**, and `ZENODEX_O008_FORMAL_CYCLE_V1.json` **nonclaim
5**" and asked for the fix "in all six places"; Opus P40 P1-2 named "THV1 packet **nonclaim 8**" first and
`_derive_rows`'s docstring third. The candidate fixed the module docstring, the enum docstring, two test
docstrings and the `claim_scope` — and left the two numbered nonclaims and the one numbered docstring line
untouched. All ten nonclaims of `projection-v4` are byte-identical to `projection-v3`:

```bash
"$PY" -c "
import json
a=json.load(open('tests/evidence/test_hygiene/THV1-20260903-global-accounting-allocation-projection-v3.json'))['nonclaims']
b=json.load(open('tests/evidence/test_hygiene/THV1-20260903-global-accounting-allocation-projection-v4.json'))['nonclaims']
print([i+1 for i,(x,y) in enumerate(zip(a,b)) if x!=y] or 'all ten identical')"
#   -> all ten identical
grep -n "more than one acceptable certificate\|Two kinds of refusal" tools/o008_formal_cycle_admission_v1.py
#   -> 559, 561   (S41 edits lines 566-569 of the SAME string and leaves these two untouched)
```

**Each is falsified by this candidate's own code.**

* Nonclaim 7's "the checker would take either" is refuted by `test_an_undetermined_state_admits_two_row_checked_certificates_with_different_roots`
  (`tests/core/…_projection_v1.py:825`), whose own assertion is `assert full == {"RECEIPT_WITNESS_REQUIRED"}`
  — the checker takes neither. This is the exact word opus2 P40 P1-1 was about.
* Nonclaim 8 is refuted by `test_which_row_cases_the_entry_point_reaches_is_pinned` (`:869`), which pins that
  two of the twelve row cases reach `_external_rows_v1` — the "external derivation" — through
  `project_allocation_certificate_v1`. I reproduced both sides independently (§1, §2 C3).
* Nonclaim 5's "Two kinds" is refuted by the enum docstring and
  `test_the_three_refusal_kinds_partition_the_family`: there are three kinds and sixteen codes.

The S41 commit message says "Six places now say 'passes every row, partition and aggregate check'". Five do.
The sixth — the pinned nonclaim — does not, and the O-008 nonclaim was **edited in this very commit**: S41
appends the two lane-configuration codes at lines 566-569 of that string and leaves the false clauses at
559 ("Two kinds") and 561 ("acceptable") standing five and seven lines above its own edit. That is the failure mode named in three consecutive reviews, occurring inside the
repair for it, in the durable artifact rather than in a docstring.

**Minimal fix (five lines).** In `tools/o008_formal_cycle_admission_v1.py:559-561`: "Two kinds" → "Three
kinds", and "more than one acceptable certificate exists" → "more than one certificate that passes every
row, partition and aggregate check exists; under the current registry none of those states has an accepted
certificate at all". In `projection-v4` nonclaim 7: "two accepted certificates" → "two certificates that pass
every row, partition and aggregate check", and delete "the checker would take either". In nonclaim 8 and at
`…_projection_v1.py:92`: replace with what `test_which_row_cases_the_entry_point_reaches_is_pinned` pins —
ten of the twelve are masked by `PROJECTION_ROWS_BEYOND_PRODUCER`, two reach their own code. Re-cut the
packet.

### P2-1 — The limitation the candidate states on its own evidence standard is stated with a false reason, in both places it appears

**Where.** `tests/core/test_global_accounting_allocation_projection_v1.py:125-128` (the
`_state_consistent_candidate` docstring): *"it **builds no terminal binding rows**, so for a state with an
OPEN terminal obligation it is one candidate among more than one"*; and `:810-814` (the test docstring):
*"For a state with an OPEN terminal obligation the **builder omits terminal rows**, so other candidates exist
and this is evidence about one of them, not a quantifier over all."*

The builder **does** build terminal rows — `:152-198`, added by this candidate, and the S41 commit message
says so ("it builds the terminal rows and runs the terminal checks it used to omit"). Reproduction:

```bash
"$PY" -c "
import sys; sys.path.insert(0,'.')
import tests.core.test_global_accounting_allocation_projection_v1 as T
st = T._backed_state((T._terminal('terminal-1', 99),))
print(len(T._state_consistent_candidate(st).ordered_lane_fragments[0].terminal_bindings))"
#   -> 1
```

The *limitation* is real — the builder picks the first domain and first principal in canonical order
(`:175`, `:190`), so where the state leaves that choice open it is one candidate — but the sentence that
states it is false, and it is the sentence the review brief asks to be carried everywhere. It is carried
into the packet `claim_scope` in the correct form ("does not quantify over every certificate for a state with
an OPEN terminal") and is missing from the module docstring's claim 2, the enum docstring's "For each row
case in the UNRECONCILABLE kind a test BUILDS the certificate the state implies and shows the checker
refusing it" (`…projection_v1.py:131-133`) and the test module docstring (`:20-22`).

**Minimal fix.** Replace "builds no terminal binding rows" / "omits terminal rows" with "chooses the first
control domain and controlling principal in canonical order", and append the same clause to the module and
enum docstrings. Worth noting alongside: the builder also omits `_check_reserve_rows`, which is in
`CHECK_ORDER_V1` and is not mentioned in any of the three.

### P2-2 — `PROJECTION_TERMINAL_WITHOUT_BACKING` is reachable through the row harness, so the unreachability the test asserts is false

**Where.** `tests/core/test_global_accounting_allocation_projection_v1.py:467-470`: *"The branch is
DEFENSIVE: it cannot be reached through the entry point **or through the row harness**, because a state
entitling a claimant in a domain it controls nowhere fails the negative-residual check first."*

A zero-atom entitlement makes the residual exactly 0, so the negative-residual check does not fire:

```bash
"$PY" -c "
import sys; sys.path.insert(0,'.')
import tests.core.test_global_accounting_allocation_projection_v1 as T
st = T._backed_state((T._terminal('terminal-1', 1),),
    custody=(('pool-a','USD','vault',10),),
    liabilities=(('bob','USD','vault',10), ('alice','USD','spot-pool',0)))
print(T._derive_rows(st))"
#   -> (PROJECTION_TERMINAL_WITHOUT_BACKING, 'terminal-1: no controlled location in spot-pool')
```

`EconomicAmountV1(..., amount_atoms=0)` and `ClaimantEntitlementRowV1(..., 0)` are both constructible; the
state is a well-typed `GlobalEconomicStateV1`. The entry-point half of the claim still holds (on
`ASSET_TRANSFER` the OPEN terminal is masked by `PROJECTION_ROWS_BEYOND_PRODUCER`, on the other eleven lanes
by `PROJECTION_ENABLED_LANE_WITHOUT_PRODUCER`) — I checked all twelve. The classification is right; only the
"cannot be reached" sentence and the reason given for it are wrong, and the row harness is exactly the
surface `_ROW_CASES` treats as the contract.

**Minimal fix.** Add the zero-atom fixture as a thirteenth `_ROW_CASES` entry (it is a three-line addition
and gives the code a case in the table like every other), and restate the docstring: unreachable through the
entry point; reachable through the harness only with a zero-atom entitlement.

### P2-3 — `PROJECTION_EXTERNAL_RESIDUAL_AMBIGUOUS` is placed in the `undetermined` kind, and one of its branches fires for a state with a **unique** row-checked certificate

**Where.** `src/core/global_accounting_allocation_projection_v1.py:369-375` (`if len(pending) != 1 or
len(open_cells) != 1:`), against `ALLOCATION_PROJECTION_REFUSAL_KINDS_V1["undetermined"]` (`:169-172`) and
the enum docstring's *"UNDETERMINED — V1 state leaves more than one certificate open that passes every row,
partition and aggregate check, so deriving one would be a guess"*.

Take a state with exactly one controlled cell, fully claimed, and one PENDING outbox entry: `open_cells == 0`,
`pending == 1`, so the branch fires with detail `1 pending rows for 0 residual cells`. But exactly **one**
certificate over that state passes the row checks — the external row must carry 0 atoms (any other amount
breaks the exactly-once partition), its `control_domain` must be one the fragment controls (only
`(USD, vault)`), and its `source_principal` must control that cell (only `pool-a`):

```bash
# state: custody (pool-a,USD,vault,10), liabilities (alice,USD,vault,10), one PENDING entry
#   _derive_rows -> PROJECTION_EXTERNAL_RESIDUAL_AMBIGUOUS "1 pending rows for 0 residual cells"
# the unique candidate (zero-atom external row over the single controlled cell):
#   exactly_once:PASS entitlement:PASS reserve:PASS external:PASS
#   terminal_bindings:PASS lane_aggregates:PASS terminal_totals:PASS
```

(the full script is in §5). The obvious alternative — omit the external row altogether — is not a second
candidate: the same fragment with `pending_external_obligations=()` is refused
`EXTERNAL_OBLIGATION_BINDING_DRIFT`. Nor can the row differ: a non-zero amount breaks `_check_exactly_once`
(claimed 11 > controlled 10), `alice` is a claimant and not a controlling principal, and `vault` is the only
control domain the fragment carries. Deriving that certificate would not be a guess, so the state is
*determined*, and
the code that refuses it claims it is not. This is the same class of defect as Opus P39 P1-1 and opus2 P40
P1-1 — a taxonomy sentence falsified by a short probe — surviving one level down, inside the repair that made
the taxonomy data. The refusal is conservative (nothing bad is derived) and it is masked at the entry point
by `PROJECTION_ROWS_BEYOND_PRODUCER`, which is why this is P2 and not P1.

**Minimal fix.** Split the branch: when `open_cells` is empty and the fragment controls exactly one
`(asset, domain)` cell with exactly one principal, the assignment is determined — either derive it or refuse
it with an UNRECONCILABLE/`NOT_SUPPORTED` code rather than an `..._AMBIGUOUS` one. Failing that, narrow the
kind's docstring: "UNDETERMINED means the state does not pin the row content; for one branch
(`pending ≥ 1, open_cells = 0`) a unique zero-atom candidate can still exist and the projection refuses it."

### P2-4 — In the new `--lib` killer form the declared file path is decorative: two different pinned crate sources produce byte-identical commands

**Where.** `tools/thv1_mutation_ledger_v1.py:144-155` (`CargoKillerV1.crate_dir` for `lib=True`) and
`:187-191` (`cargo_argv_v1`), with `tools/test_hygiene_evidence_v1.py:342-345` widening `rust_test_paths` to
every pinned `.rs` under `/src/`.

```bash
"$PY" -c "
import sys; sys.path.insert(0,'.')
from tools import thv1_mutation_ledger_v1 as L
f='::global_accounting_allocation_certificate::tests::the_source_principal_guard_refuses_and_the_check_is_what_refuses'
a=L.parse_killer_v1('zk/global_settlement_abi_v1/src/global_accounting_allocation_certificate.rs'+f)
b=L.parse_killer_v1('zk/global_settlement_abi_v1/src/state.rs'+f)
print(L.cargo_argv_v1(a)==L.cargo_argv_v1(b), a.crate_dir==b.crate_dir)"
#   -> True True
```

For the pre-existing `/tests/<target>.rs::<filter>` form the path selects the cargo `--test` target, so it is
load-bearing; for `--lib` only `crate_dir` survives and the filter runs across the whole crate. Consequences:
a row may name a source file that does not contain the killing test, and `_pin_drift`
(`tools/thv1_mutation_ledger_v1.py:468`) then checks the pin of the wrong file. The declared row is
honest today — I confirmed the filter selects exactly one test and that test lives in the declared file — so
this is a weakening of the form, not a false row.

**Minimal fix.** In `parse_killer_v1`, require the `--lib` filter's leading module segment to equal the
declared file's module path (`…/src/foo.rs` → filter must start `foo::`), or add a post-run check that the
one `running N tests` line reports exactly the expected count.

### P2-5 — Three guards added by this candidate carry no mechanical row, in two files that ARE ledger-gated and one that has never carried a row at all

**Where.**

* `tools/o008_formal_cycle_admission_v1.py:4145-4157` — the three new `_grade_ledger` refusals
  (`REPLAY_LEDGER_ROW_WITHOUT_MUTATION` for a non-digest, `REPLAY_LEDGER_ROW_PATH_UNPORTABLE`,
  `REPLAY_LEDGER_ROW_NOT_DISTINCT`). Across all **231** packets **no mechanical row mutates this file**:

```bash
"$PY" -c "
import json,pathlib,collections
c=collections.Counter()
for f in pathlib.Path('tests/evidence/test_hygiene').glob('*.json'):
    for m in json.loads(f.read_text()).get('mutations',[]):
        if isinstance(m,dict) and 'mutant' in m: c[m['mutant']['path']]+=1
print(c.get('tools/o008_formal_cycle_admission_v1.py', 0))"
#   -> 0
```
* `tools/thv1_mutation_ledger_v1.py:174-179` (`parse_killer_v1`'s `/src/` branch) and `:188-189`
  (`cargo_argv_v1`'s `--lib` branch) — `thv1-mutation-ledger-v5` declares 11 rows over this file, none over
  these lines.
* `tools/test_hygiene_evidence_v1.py:344-345` (the `or "/src/" in pin.path` widening) — 4 rows over this
  file in the same packet, none over this line.

All three are covered by tests (six new ones for the grader, two new assertions for the killer form), so this
is a gap in the *declared mechanical evidence*, exactly the shape of both P40 reviews' P2 on
`PROJECTION_ROWS_BEYOND_PRODUCER` — repaired for the projection and reintroduced in the tooling that gates it.

**Minimal fix.** Add three rows to `thv1-mutation-ledger-v5` (`if not _portable_repo_path_v1(...)`,
`if identity in seen:`, the `_SHA256_HEX_RE_V1` loop) and two for the killer form, and raise the gated counts.
The grader rows need `tools/o008_formal_cycle_admission_v1.py` to become a pinned source of some gated packet
first; if that is out of scope for this cut, say so in the packet rather than leaving the file at zero rows.

### P2-6 — "the projection's code names the code the checker would raise first" is false whenever a receipt-backed lane is enabled

**Where.** `src/core/global_accounting_allocation_projection_v1.py:287-292` (the `_state_level_refusals_v1`
docstring) and `tests/core/test_global_accounting_allocation_projection_v1.py:269-276` (`_no_certificate_binds`:
*"a code returned here is the code **EVERY** certificate over this state receives"*).

`_check_lane_bindings` (`…certificate_v1.py:775-833`) runs `RECEIPT_WITNESS_REQUIRED` **between**
`BLOCKED_LANE_PRODUCER_MISSING` and `REGISTERED_EMPTY_ROOT_DRIFT`. A state with `ASSET_TRANSFER` enabled and
`PROOF_REWARDS` at a foreign root:

```bash
"$PY" -c "
import sys; from dataclasses import replace; sys.path.insert(0,'.')
import tests.core.test_global_accounting_allocation_projection_v1 as T
from src.core.global_settlement_types_v1 import LaneIdV1
from src.core.global_accounting_allocation_projection_v1 import project_allocation_certificate_v1
st=T._backed_state(); f='0x'+'ab'*32
st=replace(st, lane_roots=tuple(replace(l,state_root=f) if l.lane_id is LaneIdV1.PROOF_REWARDS else l for l in st.lane_roots))
print(project_allocation_certificate_v1(st, T._root_of(st)).code.value, '|', T._no_certificate_binds(st))"
#   -> PROJECTION_REGISTERED_EMPTY_ROOT_DRIFT | RECEIPT_WITNESS_REQUIRED
```

The refusal is still **sound** — every certificate over that state is refused, by `RECEIPT_WITNESS_REQUIRED`
with empty slots and by `REGISTERED_EMPTY_ROOT_DRIFT` once a witness is supplied — so no state is refused
that the checker would accept. What is false is the ordering claim, and `_no_certificate_binds`'s "the code
EVERY certificate receives", which is the sentence that justifies the gate. The two fixture states do not
enable a receipt-backed lane, so the tests do not see it.

The claim is not confined to a docstring: S41 also puts it in the top-level packet. O-008 nonclaim 5 now
ends "...refused before the rows are read and **in the checker's own order**", so the falsified ordering
statement is pinned by sha256 alongside the P1's three clauses.

**Minimal fix.** "in the checker's own order **among these two**, so once the lane's witness obligation is
discharged the projection's code is the checker's"; in `_no_certificate_binds`, "a code returned here under
empty witness slots is a code no arrangement of rows can avoid"; and drop "and in the checker's own order"
from O-008 nonclaim 5.

---

## 4. P3 findings, and a verdict on every P40 P3

### New / carried P3s

**P3-1 — the two-certificate exhibition runs four of the seven checks its own sentence names.**
`tests/core/…_projection_v1.py:846-850` runs `_check_exactly_once`, `_check_entitlement_rows`,
`_check_external_obligations`, `_check_lane_aggregates`; the claim in six places is "passes every row,
**partition** and aggregate check", and the partition check is `_check_reserve_rows`. The claim is true —
I ran all seven on both candidates and all seven pass — so this is a test that under-checks its own claim,
not a false claim. **Fix:** add the three missing checks; it is one line.

**P3-2 — two of the six ledger-gated packets are still not pinned by the packet that claims the gate**
(opus2 P40 P3-3, unchanged). `hygiene_selection` pins seven packets;
`THV1-20260901-global-accounting-allocation-certificate-v23` and
`THV1-20260902-test-hygiene-lineage-ordering-v5` are not among them. This now matters more than at P40: the
certificate packet is the one carrying the new Rust mechanical row, i.e. the repair for opus2's
most-weighted P2, and no `packet_sha256` in the O-008 packet binds its row content.

**P3-3 — a test helper's docstring describes the withdrawn pin-based path guard as if it shipped.**
`tests/test_check_o008_formal_cycle_v1.py:1063-1069`: *"The mutation path must be one the formal-cycle packet
pins, because the grader now refuses a mutation applied to a file this packet does not bind (Opus P40 P2-1)."*
The grader does no such thing — `_grade_ledger` accepts 24 rows whose path is
`src/core/definitely_not_a_real_file.py` (§2 C6(b)) — and its own docstring says so. This is the residue of
the abandoned first version the commit message honestly describes; the residue was left in the test.

**P3-4 — "the generator now drops a repeat before writing" names a mechanism that is not in the diff**
(opus2 P40 P3-4, repeated in a new form). S41 changes no tool that writes THV1 packets, and nothing refuses a
duplicate mechanical row outside the six gated packets: `check_test_hygiene_v1.py --json` is green over 231
packets, three of which (`thv1-mutation-ledger-v3`, `-v4`, `test-hygiene-lineage-ordering-v4`) still declare
repeated triples. The *enforcement* that shipped is `_grade_ledger`'s distinctness rule, which is real and
which I confirmed; the generator sentence is not. **Fix:** say the gate refuses repeats at replay time for
the six gated packets, and that the packet validator does not.

**P3-5 — `THV1-…-certificate-v23`'s `claim_scope` now repeats three sentences verbatim** (opus2 P40 P3-5,
worse: one repeat at v22, three at v23), including *"Earlier: v20 re-pin (C9c-1): the certificate module is
unchanged…"* and *"The asset-lane projection joins the pinned surface."* The prepend-and-carry construction
is still un-deduplicated.

**P3-6 — carried open, three at once.** (a) The check-order docstring
(`…projection_v1.py:508-516`) was edited by this candidate to add "(1b) the two state-level gates" and still
does not name the producer-capability gate that runs between (2) and (3) (opus2 P40 P3-2 — touched, not
fixed). (b) `_derive_rows` still takes `state.lane_roots[0]` (`:105`) rather than the enabled lane the entry
point uses (Opus P40 P3-4 — not mentioned). (c) `test_reject_codes_are_closed_and_ordered` (`:522`) still
regexes the whole source text; **7 of the 16 codes now appear on no line containing `assert`**, satisfying
the scan only through `_ROW_CASES` tuples and the `_UNRECONCILABLE_ROW_CODES` literal, so a code named only
in a set literal would pass (opus2 P40 P3-6 — weaker than at P40, when the family was 13).

**P3-7 — the module docstring's claim 2 now enumerates two inclusions and still states no exception**, while
the exception opus2 P40 P2-7 found is real and reproduces at S41 (§2 C9). `…projection_v1.py:36-49` says
"Where NO certificate over the state can be accepted, the projection refuses… That includes the structural
case: … It also includes the two gates that are not about allocation at all: …". Adding a second "includes"
clause to a universal that has a known counterexample reads as an exhaustive account. The candidate states
the gap honestly in the S41 commit message, which is the right instinct and the wrong place: the commit
message is not pinned and is not what a reader of the module or the packet sees. **Fix:** one sentence in
claim 2 — "a witnessed lane's controlled and entitlement rows must also equal the ones the committed lane
root's receipt admitted; the projection cannot check that and will derive a certificate the witness check
refuses" — and the same sentence in THV1 nonclaim 2 or 6.

### Verdict on every P40 P3

| P40 finding | verdict |
|---|---|
| Opus P3-1 — docstring's two-kind split omits 3 of 13 codes | **CLOSED in code** — `ALLOCATION_PROJECTION_REFUSAL_KINDS_V1` + `test_the_three_refusal_kinds_partition_the_family`, which also scans the docstring |
| Opus P3-2 — opus2 P39 P2-5 open in the packet | **CLOSED in code** — `_state_level_refusals_v1` refuses both shapes; O-008 nonclaim 5 now names the two codes |
| Opus P3-3 — "disjoint" is about codes, not states | **CLOSED in prose, pinned by a test** — the family is now stated as a partition of the sixteen codes; no "disjoint" claim about states survives |
| Opus P3-4 — `_derive_rows` reads `lane_roots[0]` | **OPEN**, not mentioned (P3-6b) |
| opus2 P3-1 — taxonomy omits 3 of 13 codes | **CLOSED in code** (same repair) |
| opus2 P3-2 — check order omits the producer gate | **OPEN**, and the docstring was edited without fixing it (P3-6a) |
| opus2 P3-3 — 2 of 6 gated packets unpinned | **OPEN** (P3-2) |
| opus2 P3-4 — generator mechanism claim | **OPEN**, restated in a new form (P3-4) |
| opus2 P3-5 — `claim_scope` repeats a sentence | **OPEN and worse** — 3 repeats (P3-5) |
| opus2 P3-6 — reject-code scan is weaker than its docstring | **OPEN and weaker** (P3-6c) |

Two were answered in prose rather than in code (Opus P3-3, which is acceptable because a test pins it; and
opus2 P3-4, which is not, because the prose describes a mechanism that does not exist).

### INFO

**INFO-1 — the six ledger replay commands are not safe to run concurrently from two checkouts, and this is
not disclosed.** `docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.json` `proof_replay.commands` declares each
ledger run as `thv1_mutation_ledger_v1.py --packet <id> --rev HEAD --python <PYTHON>` with `cwd "."` and
`env_names []`. No `--workdir`, so the staging root is `$TMPDIR/thv1-ledger` and defaults to the shared
`/tmp/thv1-ledger`; `run_ledger_v1` deletes and recreates `<root>/<packet>` at start, and two checkouts
replaying the same packet id will delete each other's in-flight row directories. It is **fail-closed** rather
than silently wrong: a row whose tree vanishes mid-run makes pytest exit 4 (collection error), and
`mutant_verdict_v1` returns `KILLED` only on the pytest tests-failed exit, so a collision produces
`UNVIABLE`/errors and `EXECUTED_FAIL`, never a false `KILLED`. The hazard is pre-existing (the ledger
commands arrived at C9c-3) and this candidate only renames the packets, which is why it is INFO and not a
finding. **Suggested:** add `--workdir` to the six declared commands, or name `TMPDIR` in `env_names` and say
in the packet that the replay is not concurrency-safe.

---

## 5. Reproduction scripts

All probes ran inside the worktree with `PYTHONDONTWRITEBYTECODE=1`; the only edits were the four mutation
spot-checks (three Python, one Rust) and the helper-raise falsification, each restored from a byte copy taken first
(`git status --short` empty afterwards, `current_source_drift []`).

```python
# P2-3: a determined state refused as UNDETERMINED
import sys; from dataclasses import replace; sys.path.insert(0, ".")
import tests.core.test_global_accounting_allocation_projection_v1 as T
from src.core import global_accounting_allocation_certificate_v1 as cert
from tools import render_global_accounting_allocation_certificate_v1_golden as renderer
st = T._backed_state((), custody=(("pool-a", "USD", "vault", 10),),
                     liabilities=(("alice", "USD", "vault", 10),),
                     outbox=((renderer._root(9_001), "dest-1", renderer._root(9_002),
                              renderer._root(9_003), "PENDING"),))
print(T._derive_rows(st))          # -> PROJECTION_EXTERNAL_RESIDUAL_AMBIGUOUS
base = cert.build_registered_empty_certificate_v1(st); lane = st.lane_roots[0]; pend = st.outbox[0]
frag = replace(base.ordered_lane_fragments[0], enabled=lane.enabled, lane_state_root=lane.state_root,
    binding_root=lane.state_root,
    producer_kind=cert.LANE_ALLOCATION_PRODUCER_REGISTRY_V1[lane.lane_id][0],
    controlled_locations=(cert.ControlledLocationRowV1("USD", "pool-a", "vault", 10),),
    claimant_entitlements=(cert.ClaimantEntitlementRowV1("USD", "alice", "vault", 10),),
    pending_external_obligations=(cert.PendingExternalObligationRowV1(
        effect_id=pend.effect_id, asset="USD", amount_atoms=0, destination_id=pend.destination_id,
        commitment_root=pend.payload_hash, control_domain="vault", source_principal="pool-a"),))
c = renderer._certificate_with_fragments(base, (frag, *base.ordered_lane_fragments[1:]))
for fn, args in ((cert._check_exactly_once, (c,)), (cert._check_entitlement_rows, (c, st)),
                 (cert._check_reserve_rows, (c, st)), (cert._check_external_obligations, (c, st)),
                 (cert._check_terminal_bindings, (c, st)), (cert._check_lane_aggregates, (c, st)),
                 (cert._check_terminal_totals, (c,))):
    fn(*args)                       # all seven pass: the certificate is unique and row-checked
```

```python
# C1: how much the added terminal rows are worth (4 of 8 cases would return "ACCEPTED" without them)
# C3: which of the twelve row cases reach their own code through project_allocation_certificate_v1
# C9: opus2 P40 P2-7 at S41 -- one atom added to _witnessed(with_rows=True) still DERIVES
```

---

## 6. Worktree hygiene

`/tmp/zenodex-formal-core-opus-c9c4` is at P41 with `git status --short` empty at the end, and the checker
reports `current_source_drift []`. Every temporary edit (three projection mutants, one Rust mutant, one test
mutant) was restored from a byte copy taken before the edit. The two symlinks I added
(`external/mathlib4`, `lean-mathlib/.lake/packages/mathlib`) plus `external/ESSO` and the eight mathlib
package links are gitignored. `/tmp/zenodex-opus-c9c4-cargo` was deleted. The author's worktree, the
canonical checkout, the other reviewer's worktree and the author's scratchpad were not read or written.

---

## 7. Bottom line

This is the largest and best-executed candidate of the C9c series at the code level, and I verified every
substantive repair independently rather than by reading the commit message. The evidence standard is
genuinely executed — the helper is called, it builds the terminal rows, and four of the eight cases would
have passed against a candidate without them. The Rust guard is now killed by deleting it. The headline guard
and all three new codes have mechanical rows that kill by hand. The ledger grader refuses all three shapes
both P40 reviews got through, with six tests, and the distinctness rule caught two of the author's own
packets — the response was to deduplicate and lower the gate numbers, which is the right response and which
the arithmetic in the commit message states exactly. The new state-level gate is a real design addition: it
closes the P40 primary reviewer's second falsification, closes a P39 finding that two reviews had left open,
and I checked it refuses nothing the checker would have accepted. Pins, node ids, the ceiling, the 97 ledger
kills and every replayable gate reproduce here.

What stops this from being an ACCEPT is the same thing that stopped the last three. The two sentences both
P40 P1s were about — "two accepted certificates … the checker would take either" and "unreachable through
the public entry point" — survive **verbatim** in the packets this candidate cut, and a third false clause
sits in the O-008 nonclaim the author edited in the same commit, five and seven lines above the edit. All ten nonclaims
of the projection packet are byte-identical to the previous cut. The candidate's own new tests refute all
three. That is not a wording quibble: the packet is the artifact under review, its nonclaims are the
campaign's durable claim record, and they are pinned by sha256.

Below that, three smaller claims are stated larger or otherwise than what shipped: the stated limitation on
the evidence standard gives a false reason (P2-1); the defensive branch's "cannot be reached through the row
harness" is refuted by a zero-atom entitlement (P2-2); and the state-level gate's "names the code the checker
would raise first" is refuted by a two-line state (P2-6). One genuinely new taxonomy defect: a determined
state is refused with an UNDETERMINED code (P2-3). And the mechanical-row discipline this candidate enforces
on the projection is not applied to the tooling it added (P2-5), while the new `--lib` killer form does not
bind a row to the file it names (P2-4).

The P1 is a five-line text fix and a packet re-cut. Nothing in the design is wrong.

**Grade B. Authority NONE. `formal_core_complete` false. The claim ceiling must not move on this candidate.**
