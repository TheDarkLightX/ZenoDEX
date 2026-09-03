# ZenoDEX Formal Functional Core Closure — C9c-2 second review

| | |
|---|---|
| Subject commit | `ab8c8ed55b4c3322605d8e2b75f7bc5f922a2cad` ("fix: refuse the states a certificate cannot reconcile, and bind the field nothing read") |
| Artifact | `2928191bbb9856341a42ef50cc73d9b6495b0d6a` (P39), packet sha256 `f1bf72e6ef1dc968eb3e38c96837fc7e8e25930c89d955ff7019944fcb365911` |
| Worktree | `/tmp/zenodex-formal-core-opus2-c9c2` (detached, HEAD == P39, `git status --short` empty before and after) |
| Reviewer | second independent reviewer, fresh-context Opus 5 |
| Date | 2026-09-03 |
| **Grade** | **B-** — 1 P1, 5 P2, 3 P3 |

## Independence caveat (stated as required)

The campaign's second reviewer is normally a fresh-context Fable 5.1 session. Fable is out of usage
credits until 2026-09-06, so this second review is a fresh-context **Opus 5** session running in
parallel with the primary Opus 5 reviewer (worktree `/tmp/zenodex-formal-core-opus-c9c2`). I share a
model family with the primary reviewer and therefore **correlate** with it. I share no transcript,
worktree or notes with it or with the author; I did not read its worktree, its report, the author's
scratchpad, or any other reviewer's worktree. Where a finding below coincides with one I could not
have seen, treat it as convergence, not confirmation.

---

## 1. Replays (all executed here, exact commands and results)

`PY="/home/trevormoc/Downloads/Autonomous Tau DEX/.venv/bin/python"`, `PYTHONDONTWRITEBYTECODE=1`,
`CARGO_TARGET_DIR=/tmp/zenodex-opus2-c9c2-cargo CARGO_INCREMENTAL=0`. Every Lean-bearing command ran
under `flock -w 7200 /tmp/zenodex-lean.lock`; the primary reviewer held the lock for ~25 min and my
run serialised behind it as designed (no SIGBUS, no `pkill`, no pgrep detector).

| Command | Result |
|---|---|
| `check_o008_formal_cycle_v1.py --root $PWD --packet-commit 2928191bb` | exit 0; `ok true`, `packet_admitted true`, `current_source_drift []`, `proof_replay NOT_RUN`; stdout sha256 `85c48342eadf5a07d6f69c0ee084ca6351bb9f400ddf2c9e1f18041150226380` |
| same `--replay --esso-python /usr/bin/python3 --esso-pythonpath …/ESSO` (flock) | exit 0; `EXECUTED_PASS`, **34 runs**, every `exit_code 0`; stdout sha256 `a6a1d4b085c92d4dfc06be32a3139952cf60a518c7124d525c8518eede3b5e1b` |
| `build_o008_formal_cycle_v1.py --root $PWD --subject-commit ab8c8ed55 --created-date 2026-09-03 --check --replay …` (flock) | exit 0; `{"drift":[],"mode":"check","ok":true,"subject_commit":"ab8c8ed55…"}`; `git status --short` empty afterwards (the packet regenerates byte-identically) |
| `cargo fmt --all -- --check` / `clippy --locked --all-targets -D warnings` / `cargo test --locked` in `zk/global_settlement_abi_v1` | exit 0 / 0 / 0 |
| pytest (9 suites incl. `test_lean_asset_transfer_refinement_v1` excluded to its own flock run, `test_zusd_liquidation_partition` excluded as instructed) | **633 passed** in 275 s |
| `tests/core/test_global_accounting_allocation_projection_v1.py` alone | **50 passed** (matches `python_allocation_projection_gate`) |
| both Lean gates serially under the lock (`test_lean_asset_transfer_refinement_v1.py` + `test_lean_global_accounting_allocation_certificate_v1.py`) | **46 passed** (40 + 6) |
| `check_test_hygiene_v1.py --json` | exit 0 |
| `--base-ref 64d17a2f2` (parent of S39) | exit 0 |
| `--base-ref 42ccb6624` | exit 0 |
| `--base-ref fd409ba6f7da8f0ec3e0220a04b7406d69a8cb85` (campaign base) | exit 0 |

**Pins.** All **56** `source_pins` re-hashed against the worktree: 0 drift (the prompt's "57" is off by
one; 56 pins, 56 distinct roles). All **53** `hygiene_selection` entries: `pin_sha256`, `packet_sha256`
and `packet_git_blob` all verify (0 bad). `claim_ceiling`, `completion_scope`, `nonclaims` and
`v1_information_loss` are **byte-identical** to the P38 packet; the artifact adds exactly
`ledger_projection_rows`, `ledger_tool_rows` and the pin `tools/thv1_mutation_ledger_v1.py`.
`migration/production/publication/release/settlement/value_movement/verifier authority = NONE`,
`formal_core_complete false`, `value_movement_gates_closed 0`.

**Mutation ledger, run independently on all four packets carrying mechanical rows** (not just the two
the packet gates):

```
THV1-20260903-global-accounting-allocation-projection-v2       19 mechanical / 19 killed / 0 survived / 0 errors  exit 0
THV1-20260903-thv1-mutation-ledger-v3                          19 / 19 / 0 / 0                                    exit 0
THV1-20260903-global-settlement-exact-ownership-mechanical-v2  21 / 21 / 0 / 0                                    exit 0
THV1-20260903-o008-asset-transfer-receipt-admission-mechanical-v2  31 / 31 / 0 / 0 (+2 narrative)                 exit 0
```

90 declared killers, 90 kills. Nothing is hidden behind the ungated packets.

---

## 2. Verdict on each claim C9c-2 makes

### (a) "The unread field is bound" (opus2 P38 P1-1) — **PARTIAL**

The reported forgery is closed. `_check_external_obligations`
(`src/core/global_accounting_allocation_certificate_v1.py:888-918`) now reads `row.source_principal`,
and its Rust twin mirrors it (`zk/global_settlement_abi_v1/src/global_accounting_allocation_certificate.rs:1081-1094`).

**Class hunt across every row type — otherwise clean.** Every field hashed into `fragment_root`
(and hence `allocation_root`), `field_ownership_root` or `terminal_binding_root` is now read by some
check: `ControlledLocationRowV1` all four by `_check_lane_aggregates:978-991`;
`ClaimantEntitlementRowV1` by `derive_canonical_allocation_rows_v1:671-693` + `_check_entitlement_rows`;
`UnencumberedReserveRowV1` by `_check_reserve_rows:873-886`; `PendingExternalObligationRowV1` all seven
(`effect_id`/`destination_id`/`commitment_root` :896-903, `asset`/`amount_atoms`/`control_domain` by
`_check_exactly_once:845-861`, `source_principal` by the new guard); `TerminalBindingRowV1` all eight
(:919-955). Fragment scalars all read by `_check_lane_bindings:775-833`. `reserve_interpretation` is
read by no check but is a one-member enum, so it cannot vary. **No second unread field found.**

Residual: **P2-1** (the binding is existential, not functional) and **P2-2** (the repair is undeclared
and, in Rust, killed by nothing).

### (b) "The projection refuses what it cannot reconcile" — **NOT CLOSED**

The four new codes are real, reachable and tested; all ten codes have a test; both checked u128 folds
have one; 50 tests pass and all 19 mechanical rows kill. But a **fifth unreconcilable shape — in fact
three whole row families — is still derived**: **P1-1**. And the newly-introduced UNDETERMINED /
UNRECONCILABLE partition is falsified by one of its own codes: **P2-3**. Two further shapes
(`BLOCKED_LANE_PRODUCER_MISSING`, `REGISTERED_EMPTY_ROOT_DRIFT`) are derived rather than refused;
disclosed in the test file, not in the two places that carry the claim: **P2-5**.

### (c) "The vacuity is addressed, not papered over" — **CLOSED**

The row-bearing evidence is genuine, checked here in-process: `_witnessed(with_rows=True)` mints a
witness whose fragment carries `ControlledLocationRowV1("USD","custodian","vault",100)` and
`ClaimantEntitlementRowV1("USD","custodian","vault",100)` (non-empty), the state's `custody` and
`liabilities` tables match it row for row, the full checker returns `AllocationCertificateAcceptedV1`
and `outcome.lane_fragment_roots[0] == fragment.fragment_root`. The fixture-partition claim is scoped
to the twenty-nine golden states in the module docstring (`tests/core/test_global_accounting_allocation_projection_v1.py:3-10`),
the test docstring (:65-73) and the packet claim scope. The partition itself replays: 20 accept / 7
projection refusal / 2 state-level, summing to 29.

Caveat rolled into P1-1: the *general* claim is still stated unscoped in
`docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.json` nonclaim #4 and in the projection module docstring.

### (d) "The ledger is enforced" — **CLOSED**, with **P2-4** on its scope

Both replay commands re-run here: `ledger_projection_rows` and `ledger_tool_rows`, exit 0, 19 killed /
0 survived / 0 errors each, matching the packet's `comparable` block exactly.

*Adversarially: can a report satisfy `_grade_ledger` while a row did nothing?* Not "nothing": the
executor requires the killer to **pass** on an unmutated control copy and **fail** on the mutant
(`mutant_verdict_v1`), the mutated path must be among the packet's source pins, the killer must be a
pinned node, and the path partition forbids a row mutating its own killer — so a no-op replacement
reports SURVIVED and the ledger exits 1. What *can* still pass is a row whose **description does not
describe the mutation that ran**: `_grade_ledger` (`tools/o008_formal_cycle_admission_v1.py:4063-4086`)
reads only `killed/survived/errors/mechanical`. See **P3-3**.

### (e) "A verdict names its mutation" (Opus P38 P2-6) — **PARTIAL**

`RowOutcomeV1.mutation` now records path, needle and replacement digests and the needle's first line
(`tools/thv1_mutation_ledger_v1.py:471-479`), and the pytest control gained the cargo path's
"something ran" guard (`control_error_v1`, `pytest_passed_v1:230-240`). This makes a mismatch
**visible after the fact** — which is what the finding asked for — but not detectable: the record is
derived from the same row it describes, and no gate reads it. **P3-3.**

### (f) "Six previously undeclared guards now have tests and mechanical rows" — **CLOSED**

All nineteen rows of `THV1-20260903-global-accounting-allocation-projection-v2` name a real guard and
all nineteen kill (re-run here). Enumerating the projection's guards against the rows leaves none
undeclared: `BINDING_ROOT_MISSING`(0)/`UNEXPECTED`(5), `TERMINAL_DOMAIN_AMBIGUOUS` both sites (1,14),
`EXTERNAL_RESIDUAL_AMBIGUOUS` all three sites (2,12,13), `NO_LANE_FOR_ROWS` both sites (3,15),
`MULTIPLE_ENABLED_LANES`(4), type boundary(6), family closure(7), binding-root identity(8),
`TERMINAL_EXCEEDS_ENTITLEMENT`(9), `TERMINAL_WITHOUT_ENTITLEMENT`(10), `NEGATIVE_RESIDUAL`(11), both
folds(16,17), witness rows(18). The "row ordering is defensive" note is justified: `_ordered_rows`
(`…certificate_v1.py:356-368`) already refuses a non-canonical tuple.

The guard left undeclared is not in the projection — it is the **certificate module's own new guard**:
**P2-2**.

### (g) Dates and the cutover rule — **PARTIAL**

The narrowing preserves the intent rather than hollowing it out: `_carried_rows_v1`
(`tools/check_test_hygiene_v1.py:209-221`) only forgives a `(description, killer)` pair that already
appears in a packet of the **same lineage** with a strictly earlier `(date, version)`, so a new
lineage still cannot introduce a string-only row, and the "a new row copying an old row's text exactly
reads as carried" residual is written into the function docstring and the lineage packet's claim scope.
I verified the rule bites where it should: `check_test_hygiene_v1` is green against all four base refs,
and the mutant `carried = frozenset()` is a declared, executed, killed row.

Falsified sub-claim: **P3-1** (one of the ten packets is still back-dated).

### (h) The packet — **CLOSED on mechanics**

34 commands, all `EXECUTED_PASS`; 56/56 source pins and 53/53 hygiene pins verify; claim ceiling and
nonclaims byte-identical to P38; authority NONE. The three nonclaims the brief names (no Rust twin for
the projection; the fixture partition is not a general property; a refusal does not mean the state is
invalid) are present — in the **THV1 projection packet**, not in the top-level packet, whose nonclaim
#4 still states the general property that P1-1 falsifies.

---

## 3. Findings

### P1-1 — The projection still derives a certificate the checker must reject, for three entire row families; the repair fixed the arithmetic sub-case and left the structural one, masked by the same gate the author identified

`src/core/global_accounting_lane_producers_v1.py:352-360` — the one registered receipt-backed producer
constructs its fragment with `controlled_locations` and `claimant_entitlements` **only**; it emits no
reserves, no pending external obligations and no terminal bindings. An accepted certificate's enabled
fragment must **equal** a minted witness's fragment (`RECEIPT_WITNESS_FRAGMENT_DRIFT`,
`…certificate_v1.py:808-810`) and no row may sit on a disabled lane (`DISABLED_LANE_NOT_EMPTY`, :819-821).
Therefore **no state carrying a reserve row, a PENDING outbox entry, or an OPEN terminal obligation
admits any accepted certificate at all** — regardless of arithmetic. The projection derives one for a
large class of those states.

Reproduction (executed, `/tmp/opus2c9c2-probe3.py`, using the suite's own real admitted witness):

```
witness, state, certificate, slots = _witnessed(with_rows=True)
check(certificate, state, slots)                       -> AllocationCertificateAcceptedV1
witness.fragment: reserves=0 external=0 terminals=0
state2 = replace(state, terminal_obligations=(TerminalObligationV1(
             "terminal-1", ASSET_TRANSFER, "custodian", "USD", 100, OPEN),))   # within its entitlement
project_allocation_certificate_v1(state2, ((ASSET_TRANSFER, lane_root),))
                                                       -> certificate with 1 terminal row (NOT a refusal)
check(projected, state2, EMPTY_LANE_WITNESS_SLOTS_V1)  -> RECEIPT_WITNESS_REQUIRED
check(projected, state2, slots)  # the REAL minted witness
                                                       -> RECEIPT_WITNESS_FRAGMENT_DRIFT
check(witness-matching certificate, state2, slots)     -> TERMINAL_BINDING_DRIFT
```

The same holds for reserves and for pending external rows (`/tmp/opus2c9c2-probe1.py`, probes A and B);
the candidate's own `test_one_pending_obligation_takes_the_residual_and_the_checker_accepts_the_rows`
(:273-296) ends at `RECEIPT_WITNESS_REQUIRED` for exactly this reason.

This falsifies, verbatim and unscoped, three surviving claims:

* `docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.json` nonclaim #4 (byte-identical to P38's): *"…the C9c-1
  projection, which refuses with a closed code **wherever V1 state does not determine it**…"*;
* `tests/evidence/test_hygiene/THV1-20260903-global-accounting-allocation-projection-v2.json`
  `claim_scope`: *"REFUSES with a closed code **wherever V1 state does not determine a certificate the
  checker can accept**"*;
* `src/core/global_accounting_allocation_projection_v1.py:15-17`, module docstring item 2: *"where no
  certificate over the state can be accepted, it refuses rather than deriving one the checker must
  reject"*.

The commit message calls the previous cut FALSE and names `RECEIPT_WITNESS_REQUIRED` as the mask that
hid it. The mask is still in place, and the sub-case it now hides is structural rather than arithmetic,
so it cannot be reached by adding another counting guard.

**Minimal fix (either).** (a) Refuse in `project_allocation_certificate_v1` when the owning lane's
registered producer cannot emit a family the state populates — a new UNRECONCILABLE code, e.g.
`PROJECTION_NO_PRODUCER_FOR_ROW_FAMILY`, raised when `state.reserves`, the PENDING outbox, or the OPEN
terminal set is non-empty on an enabled receipt-backed lane; add the mechanical row and the test.
(b) Or narrow all three claim texts to "…the row, aggregate and derived-root checks", and declare the
witness-fragment gate as the residual in the top-level packet nonclaim as well as in the test file.
(a) is preferable: (b) leaves the projection deriving objects nothing can back.

### P2-1 — The new `source_principal` binding is existential, so one state still admits two row-check-passing certificates with different `allocation_root`s

`src/core/global_accounting_allocation_certificate_v1.py:893-905` (and the Rust twin at
`…certificate.rs:1081-1094`) require only that *some* controlled location of the same fragment matches
`(asset, controlling_principal, control_domain)`. When two custody rows share one `(asset,
control_domain)` cell with different principals — a shape `GlobalEconomicStateV1` accepts, since its
row key is `(asset, owner, custody_domain)` — the row's `source_principal` is still free.

Reproduction (executed, `/tmp/opus2c9c2-probe1.py` probe C, at the same check level as P38 P1-1's):

```
controlled = {(USD, pool-a, spot-pool, 6), (USD, pool-b, spot-pool, 4)}, one PENDING outbox entry
source_principal = "pool-a": _check_exactly_once + _check_external_obligations + _check_derived_roots -> PASS
source_principal = "pool-b": same three checks                                                        -> PASS
allocation_root 0x498bb3c9417984c6…  vs  0x748691befc8e4d16…    (2 distinct roots, one state)
```

`_check_terminal_bindings:940-951` has the identical existential shape for `controlling_principal`.
Severity below P1 because the projection refuses such states (`principals != 1`, projection :243-249
and :323-329) and because, by P1-1, no external row can appear in an accepted certificate at all — but
the campaign's determination claim at the **checker** level remains false, which is what P38 P1-1 said.

**Minimal fix.** Make the binding functional: require the named principal's controlled total over that
cell to cover the row's atoms, or reject when more than one principal controls the cell (mirroring the
projection's own rule). Add the mechanical row in both languages.

### P2-2 — The packet that pins the changed certificate module states the module is unchanged, declares no mutation for the new guard, and the Rust half of the guard is killed by nothing

`tests/evidence/test_hygiene/THV1-20260901-global-accounting-allocation-certificate-v21.json` was added
by S39 (`git log --diff-filter=A`) with `created_date 2026-09-03`, and its source pins for **both**
`src/core/global_accounting_allocation_certificate_v1.py` and
`zk/global_settlement_abi_v1/src/global_accounting_allocation_certificate.rs` moved to the new bytes.
Yet:

* its `claim_scope` opens *"v20 re-pin (C9c-1): **the certificate module is unchanged**; …"* — v20's
  sentence verbatim, with no text describing the P1-1 repair;
* its 69 mutation rows are **byte-identical to v20's** — zero new rows (verified by set difference
  against every earlier packet of the lineage);
* `nonclaims`, `invariant_ids`, `failure_modes`, `aaa`, `reject_is_noop`, `boundary_dimensions` are all
  identical to v20's.

Consequence, verified mechanically: neutralising the Rust guard (`…certificate.rs:1081-1094` replaced
with `let _ = fragment;`) in a `git archive HEAD` copy and running
`cargo test --offline --locked` gives **30 test binaries, 30 "ok", 0 failed** — the Rust half of the
headline repair is exercised by no test and named by no row. The Python half is killed only by the
assertion added at `tests/core/test_global_accounting_allocation_certificate_v1_golden.py:184`, which
no mutation row names either. This is precisely the class the candidate closed for the projection
("six guards had no declared mutation and survived mutation").

**Minimal fix.** Cut v22 with a claim scope that says what changed, and two mechanical rows: Python
needle = the `controlled = any(...)` block at :893-905, Rust needle = the `let controlled = …` block at
:1081-1094; add a Rust unit test asserting `ExternalObligationBindingDrift` with detail ending
`source binding`, so the twin has a killer.

### P2-3 — `PROJECTION_EXTERNAL_RESIDUAL_AMBIGUOUS` falsifies the UNDETERMINED / UNRECONCILABLE partition it was introduced to state

`src/core/global_accounting_allocation_projection_v1.py:88-93` and the projection packet's claim scope
both declare the AMBIGUOUS codes to mean *"more than one accepted certificate exists"*. Reproductions
(`/tmp/opus2c9c2-probe2.py`), all with one enabled ASSET_TRANSFER lane and its binding root supplied:

```
D1  custody 10, no liabilities/reserves/outbox
    -> EXTERNAL_RESIDUAL_AMBIGUOUS "unassigned controlled atoms with no pending obligation"
       but NO accepted certificate exists (nothing can absorb the residual): UNRECONCILABLE
D2  custody EUR 5 + USD 10, one PENDING outbox entry
    -> EXTERNAL_RESIDUAL_AMBIGUOUS "1 pending rows for 2 residual cells"
       but NO accepted certificate exists (one row cannot carry two cells): UNRECONCILABLE
D3  custody USD 10, liabilities USD 10, one PENDING outbox entry
    -> EXTERNAL_RESIDUAL_AMBIGUOUS "1 pending rows for 0 residual cells"
       but EXACTLY ONE accepted shape exists: a zero-atom external row (verified: all six row,
       aggregate and derived-root checks PASS on it). The state is DETERMINED and is refused.
```

So a single code covers undetermined, unreconcilable and determined states — the distinction the
candidate exists to draw.

**Minimal fix.** Split the branches: route "no pending obligation with open cells" and "fewer pending
rows than open cells" to an unreconcilable code; and either derive the zero-atom row for D3 or record
the deliberate over-refusal in the docstring and the claim scope.

### P2-4 — "the ledger runs over the packets carrying mechanical rows" covers two of the five

`tools/o008_formal_cycle_admission_v1.py:95-98` — `LEDGER_GATED_PACKETS_V1` names
`global-accounting-allocation-projection-v2` (19) and `thv1-mutation-ledger-v3` (19): **38 rows**.
This same commit adds three further packets with mechanical rows that no gate executes:
`global-settlement-exact-ownership-mechanical-v2` (21), `o008-asset-transfer-receipt-admission-mechanical-v2`
(31), `test-hygiene-lineage-ordering-v3` (1). Repo-wide, `check_test_hygiene_v1.py --json` reports
`mechanical 183`, `mechanical_current 149`. The claim in
`THV1-20260903-thv1-mutation-ledger-v3.json` — *"two replay commands run it over **the packets carrying
mechanical rows**"* — and the commit message's *"ninety-two mechanical rows existed and no gate ran any
of them"* read as if the gap were closed; 53 of the 91 current rows remain ungated.

I ran the three ungated packets myself: 21/21 and 31/31 killed, exit 0 (and lineage-ordering-v3's single
row is executed by its own killer). So nothing is failing — the claim is simply broader than the gate.

**Minimal fix.** Add the three command ids to `LEDGER_GATED_PACKETS_V1` with their pinned counts, or
change the claim to "two of the packets carrying mechanical rows".

### P2-5 — Two state-level shapes are derived, not refused; disclosed in the test file, unscoped in both places that carry the claim

`tests/core/test_global_accounting_allocation_projection_v1.py:52-58` names them honestly
(`_STATE_LEVEL_REFUSALS`: `BLOCKED_LANE_PRODUCER_MISSING`, `REGISTERED_EMPTY_ROOT_DRIFT`) and the
partition test carves them out. Verified (`/tmp/opus2c9c2-probe2.py` D4): a state with
`SECOND_ENABLED` (SPOT_LIQUIDITY, `NO_PRODUCER`) projects to a certificate and the full checker rejects
it `BLOCKED_LANE_PRODUCER_MISSING`. Neither the module docstring, nor the packet `claim_scope`, nor the
top-level packet nonclaim #4 carries the carve-out — all three state the property without exception.

**Minimal fix.** Add the exception sentence to the module docstring and both claim texts (or fold into
the P1-1 fix, which subsumes it).

### P3-1 — One of the ten packets still carries a back-dated `created_date`

`tests/evidence/test_hygiene/THV1-20260901-o008-formal-cycle-admission-v35.json` was added by
`ab8c8ed55` (dated 2026-09-03) with `created_date "2026-09-02"`, inherited from v34; the other nine new
packets are stamped 2026-09-03. This is the exact opus2 P38 P2-1 shape the candidate says the generator
now closes, and with evidence-id date 2026-09-01 plus `created_date` 2026-09-02 it takes the declared
back-dating exemption in full (`MECHANICAL_MUTATION_ROWS_FROM = "20260903"`), skipping the carried-row
test for its 105 string-only rows.

Not load-bearing: all 105 rows are present verbatim in v34, so an honest stamp would change no outcome
(verified by set difference). But the claim "the generator now stamps the authoring date" is false for
the largest packet in the set and the use is recorded nowhere.

**Minimal fix.** Stamp v35's `created_date` 2026-09-03 (its rows all pass the carried test), or record
the exception in the lineage packet's claim scope.

### P3-2 — A test named for an acceptance asserts only the masking gate

`tests/core/test_global_accounting_allocation_projection_v1.py:273-296`,
`test_one_pending_obligation_takes_the_residual_and_the_checker_accepts_the_rows`: the docstring claims
"the projected external row satisfies the checker's outbox binding and the exactly-once partition", but
the only checker call asserts `outcome.code is RECEIPT_WITNESS_REQUIRED`. Neither
`_check_external_obligations` nor `_check_exactly_once` is called, so the stated property is untested,
and the test name asserts an acceptance that does not happen. This is the masking pattern the candidate
identifies as the cause of the previous false claim, reproduced inside the repair's own suite.

**Minimal fix.** Call `cert._check_external_obligations(projected, state)` and
`cert._check_exactly_once(projected)` directly and rename the test to what it proves.

### P3-3 — `_grade_ledger` never reads the mutation record added for P2-6

`tools/o008_formal_cycle_admission_v1.py:4063-4086` reads only `killed`, `survived`, `errors` and
`mechanical`. The per-row `mutation` block is also a faithful echo of the row's own declared mutant
(`tools/thv1_mutation_ledger_v1.py:471-479` hashes `mutant.needle` / `mutant.replacement`), so it can
never disagree with the row it describes — it documents what ran, it does not verify that what ran is
what the description says. A row whose free-text `description` misnames its needle still grades KILLED.

**Minimal fix.** Have `_grade_ledger` recompute `needle_sha256` from the pinned packet's row and compare,
so a report cannot be reconciled to a different packet.

---

## 4. Convergence note

I have not read the primary reviewer's report or worktree. Findings P2-1 and P2-3 concern shapes the
brief explicitly asked both reviewers to hunt, so overlap there should be read as convergence between
two same-family sessions, not as independent confirmation. P1-1 (the row families no producer can
emit), P2-2 (the untested Rust half and the "module is unchanged" claim scope) and P3-1 (v35's date)
came from my own class hunt and are the parts of this review I would weight most.

## 5. What is genuinely closed

The vacuity finding is closed with real evidence, not narrowed prose. The mutation ledger is executed
and the execution reproduces exactly (90/90 kills across four packets, run here). Every one of the ten
projection codes is reachable and tested; the six previously undeclared projection guards now have rows
and all of them kill. The unread-field class is closed across every row type but for the existential
weakening in P2-1. All 56 source pins, all 53 hygiene pins, the claim ceiling and the authority stance
verify unchanged. Grade **B-**: the mechanical work is real and reproducible, but the claim the
candidate exists to repair is still false where it is stated, and the headline repair itself ships
undeclared and, in Rust, untested.
