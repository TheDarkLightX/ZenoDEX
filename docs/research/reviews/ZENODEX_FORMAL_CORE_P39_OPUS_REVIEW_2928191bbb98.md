# ZenoDEX Formal Functional Core Closure — Independent Review of C9c-2 (P39)

| field | value |
|---|---|
| subject | S39 = `ab8c8ed55b4c3322605d8e2b75f7bc5f922a2cad` ("fix: refuse the states a certificate cannot reconcile, and bind the field nothing read") |
| artifact | P39 = `2928191bbb9856341a42ef50cc73d9b6495b0d6a` (packet sha256 `f1bf72e6ef1dc968eb3e38c96837fc7e8e25930c89d955ff7019944fcb365911`, verified) |
| worktree | `/tmp/zenodex-formal-core-opus-c9c2` (detached, HEAD = P39, `git status --short` empty before and after) |
| reviewer | fresh-context **Opus 5**, primary reviewer |
| date | 2026-09-03 |
| verdict | **B** — 1 P1, 4 P2, 6 P3, 3 INFO. ACCEPT is advisory; authority stays NONE; the claim ceiling did not move. |

---

## 1. Replays (executed in this worktree; every Lean-bearing command under `flock -w 7200 /tmp/zenodex-lean.lock`)

| command | result |
|---|---|
| `check_o008_formal_cycle_v1.py --root $PWD --packet-commit 2928191bb` | exit 0; `ok true`, `packet_admitted true`, `current_source_drift []`, `proof_replay NOT_RUN` |
| same `--replay --esso-python /usr/bin/python3 --esso-pythonpath …/ESSO` | exit 0; **`EXECUTED_PASS`, 34 runs** (the review prompt says 31; the packet declares 34 commands and 34 ran). Result sha256 `100c2d64a4e82df5b3256e452676b8c346cc4221a87e27ef166457dc179af9b4` |
| `build_o008_formal_cycle_v1.py … --check --replay --output-json/-md` | exit 0; `git status --short` empty after; packet sha256 unchanged |
| `ledger_projection_rows` (inside the replay) | `killed 19, mechanical 19, survived 0, errors 0`, exit 0 |
| `ledger_tool_rows` (inside the replay) | `killed 19, mechanical 19, survived 0, errors 0`, exit 0 |
| `python_allocation_projection_gate` | `passed 50` |
| Python suites, one run: totality, abi resource bounds, abi, `test_check_o008_formal_cycle_v1`, canonical manifest, projection, mutation ledger, test hygiene | **589 passed** in 276s |
| `check_test_hygiene_v1.py --json` | exit 0; `mutation_rows {legacy 5267, mechanical 183, mechanical_current 149, narrative 4}` |
| `--base-ref 64d17a2f2` / `42ccb6624` / `fd409ba6f7da8f0ec3e0220a04b7406d69a8cb85` | exit 0 each (the campaign base is green) |
| `cargo fmt --all -- --check` in `zk/global_settlement_abi_v1` | exit 0 |
| `cargo clippy --locked --all-targets -- -D warnings` | exit 0 |
| `cargo test --locked` | exit 0; 54 `test result: ok` summaries, **534 passed**, 0 failed |
| `tests/formal/test_lean_asset_transfer_refinement_v1.py` (under the lock) | exit 0; **40 passed** |
| `tests/formal/test_lean_global_claimant_custody_relation_v1.py` (under the lock) | exit 0; **6 passed** |
| `tests/formal/test_lean_global_accounting_allocation_certificate_v1.py` (under the lock) | exit 0; **6 passed** |

`tests/core/test_zusd_liquidation_partition.py` excluded as instructed.

**Pin audit.** All **134** `source_pins` + `test_pins` across the ten named THV1 packets are byte-exact at P39;
all **809** pinned pytest node ids resolve to a real `def` (0 orphans). The O-008 packet carries **56**
`source_pins` with 56 distinct roles (the prompt says 57), all byte-exact, and 34 replay commands. The two
ledger-gated packets are pinned by blob id (`b85fff8c…`, `b09bd431…` — both verified with `git hash-object`).
`claim_ceiling` and `nonclaims` are **byte-identical to P38**; `authority` NONE on every axis;
`formal_core_complete false`; `o008_status OPEN_EXACT_ALL_12_RECONCILIATION_MISSING`.

---

## 2. One verdict per claim

### C1. The unread field is bound (opus2 P38 P1-1) — **CLOSED**

The reviewer's forgery, re-run verbatim: state = lane 0 enabled, custody `(pool-a, USD, spot-pool, 10)`,
liabilities `(alice, USD, spot-pool, 4)`, one PENDING outbox entry. The projection derives a certificate whose
row/aggregate/derived-root passes PASS; replacing `source_principal` with `attacker-not-in-custody` and
recomputing the three roots now **rejects** `EXTERNAL_OBLIGATION_BINDING_DRIFT: … source binding`
(`src/core/global_accounting_allocation_certificate_v1.py:900-916`, Rust twin
`zk/global_settlement_abi_v1/src/global_accounting_allocation_certificate.rs:1081-1094`).

**Same-class hunt — clean.** I audited every field of every row type against the checker:
`ControlledLocationRowV1` (all four via `_check_lane_aggregates:978-991`), `ClaimantEntitlementRowV1`
(all four via `_check_entitlement_rows:863-871`), `UnencumberedReserveRowV1` (all four including
`reserve_principal` via `_check_reserve_rows:873-886`), `PendingExternalObligationRowV1`
(`effect_id`/`destination_id`/`commitment_root` at `:888-899`, `asset`/`control_domain`/`amount_atoms`
through the `_check_exactly_once` fold at `:845-861`, `source_principal` now at `:900-916`),
`TerminalBindingRowV1` (all eight at `:919-976`), and the fragment header
(`module_release_id`/`enabled`/`lane_state_root` at `:784-790`, `producer_kind` at `:792`,
`binding_root` at `:831`, `chain_context` at `:765`). **No field is hashed into a derived root and read
by no check.** Two residuals, both INFO-2/INFO-3 below rather than findings.

Two defects attach to *how the repair shipped*, not to the repair: **P2-1** and **P2-2**.

### C2. The projection refuses what it cannot reconcile — **PARTIAL**: it refuses (verified over 4000 states), but the declared UNDETERMINED/UNRECONCILABLE separation is false (P1-1)

All ten codes are reachable and each has an asserting test (verified by reading every assertion, not by
trusting `test_reject_codes_are_closed_and_ordered`, which does not check reachability — P3-4). Both
checked u128 folds are covered (`:483-512`). The four new codes fire where the commit says they do.

**Positive result — the mechanism is sound.** I swept 4000 pseudorandom one-lane states (two principals, two
assets, two domains, 0-2 custody rows, 0-2 liability rows, 0-1 reserve row, 0-2 PENDING outbox entries, 0-2
OPEN terminals; seed 7, probe at `/tmp/opus-c9c2-sweep.py`): **107 derived, 3792 refused, 0 defects** — no
projected certificate ever failed a row, aggregate or derived-root check. So there is no fifth unreconcilable
shape the projection *derives*. The defect is in the labelling, not the derivation.

But the separation the candidate declares — "UNDETERMINED means V1 state leaves more than one certificate
open … UNRECONCILABLE means no certificate over this state can be accepted at all"
(`global_accounting_allocation_projection_v1.py:86-89`, repeated in the packet's `claim_scope`) — is
**false**. `PROJECTION_EXTERNAL_RESIDUAL_AMBIGUOUS` is the code returned for at least four shapes in which
**zero** acceptable certificates exist. This is the fifth unreconcilable shape the prompt asked me to hunt
for: it is not *derived*, it is *mislabelled as undetermined*. See P1-1.

### C3. The vacuity is addressed, not papered over — **CLOSED**

The scoping is real and consistent: the module docstring
(`tests/core/test_global_accounting_allocation_projection_v1.py:1-21`), the test docstring
(`:64-73`) and the packet `claim_scope` all say the partition is a statement about the twenty-nine golden
states and that the general form was false. I found **no place where a scoped claim is stated unscoped**;
the O-008 packet's projection nonclaim is a statement about refusal behaviour, not about the partition.

The row-bearing evidence is genuine, verified by construction rather than by the test's assertions:
`_witnessed(with_rows=True)` yields `fragment.controlled_locations =
(ControlledLocationRowV1('USD','custodian','vault',100),)` and one matching entitlement row, with
`state.custody` and `state.liabilities` equal to them, and `binding_root != lane_state_root` so the
witness's contribution is real. Thin in one respect — P3-5.

### C4. The ledger is enforced — **PARTIAL**

Both commands re-run by me inside the checker replay: 19 mechanical, 19 killed, 0 survived, 0 errors, each.

**Adversarial reading of `_grade_ledger` (`tools/o008_formal_cycle_admission_v1.py:4063-4087`).** Can a
report satisfy it while a row did nothing? Not while the pinned tool produces the report, and the reason
is structural rather than in the grader:
`_execute_mechanical_row` (`tools/thv1_mutation_ledger_v1.py:436-500`) applies **the row's own** `row.mutant`;
`apply_mutant_v1` refuses unless the needle occurs exactly once (`VERDICT_NEEDLE_COUNT` → counted as an
error, which the grader rejects); the control must exit 0 **and** now report ≥1 passed pytest test
(`control_error_v1:208-227`, the new guard); a no-op mutation leaves the file unchanged so the killer passes
→ `SURVIVED`; and a mutation that breaks the file gives pytest exit 2 → `UNVIABLE`, not `KILLED`
(`mutant_verdict_v1:242-253` requires exit code exactly 1). All 19 killers in each packet are **specific
node ids**, not file paths, so "some other test in the selection failed" cannot mask a survivor.

The grader itself, however, reads only four aggregate integers and never inspects the per-row records —
P3-2 — and two modules it depends on for row classification and mutant text are unpinned — P3-3. And the
packet's own statement of what the gate covers is broader than the gate — P2-4.

### C5. A verdict names its mutation (Opus P38 P2-6) — **CLOSED for its stated purpose**

Each row now records `{path, needle_sha256, replacement_sha256, needle_first_line}`
(`thv1_mutation_ledger_v1.py:471-480`), which is enough for a reader to tie a `KILLED` verdict to the packet
row that claims it by recomputing the digests. Since the applied mutant is `row.mutant` by construction, a
mismatch cannot arise from the pinned tool at all; the field closes the *auditability* gap the finding named.
It is not a gate: nothing compares the report's `mutation` to the packet (P3-2). The pytest control guard is
real and I confirmed the cargo path already had the equivalent.

### C6. Six previously undeclared guards — **CLOSED for the projection; one NEW undeclared guard**

All six are present with tests and executed mechanical rows (rows 11-18 of the projection packet, all KILLED).
The type boundary including the duplicate-lane `ValueError` is covered (`:295-311`). The row-ordering row is
honestly recorded as defensive and the test proves `GlobalEconomicStateV1` refuses a non-canonical obligation
tuple (`:469-481`). **But this candidate introduces a guard with the same defect it was repairing**: the
source-binding branch has a Python negative test and **no** mutation row, and in Rust **no test at all**
(P2-2, P3-1).

### C7. Dates and the cutover rule — **PARTIAL** (P2-3)

The narrowing does **not** hollow out the intent. I verified the rule still has teeth: appending one novel
string-only row to `THV1-20260903-global-accounting-allocation-projection-v2.json` and re-running
`check_test_hygiene_v1.py --base-ref 64d17a2f2` fails with
`string-only mutation rows are refused from 20260903`. The carried-forward key is a strict
`(description, killer)` match against a *strictly earlier* packet of the same lineage, so a genuinely new row
cannot be smuggled in without duplicating an existing row verbatim (which asserts nothing new). The residual
is honestly declared in the function docstring.

What is not closed is the *stamping* half of the fix — P2-3.

### C8. The packet — **CLOSED**

34 replay commands, 56 pins/56 roles, all byte-exact; the four claimed nonclaims are present verbatim in
`THV1-20260903-global-accounting-allocation-projection-v2.json`; authority NONE; `formal_core_complete false`;
ceiling and nonclaims byte-identical to P38. One stale nonclaim — P3-6.

---

## 3. Findings

### P1-1 — The declared UNDETERMINED/UNRECONCILABLE separation is false: `PROJECTION_EXTERNAL_RESIDUAL_AMBIGUOUS` is returned for states in which **no** acceptable certificate exists

`src/core/global_accounting_allocation_projection_v1.py:86-89` (the enum docstring),
`:227-232` (the `if not pending:` branch),
`tests/core/test_global_accounting_allocation_projection_v1.py:417-424` (which *pins* the wrong
classification), and the `claim_scope` of
`tests/evidence/test_hygiene/THV1-20260903-global-accounting-allocation-projection-v2.json`.

This is the candidate's headline repair claim. It fails on at least four shapes, all reproduced:

| state (one enabled lane) | returned code |
|---|---|
| custody 10, liabilities 4, no reserves, **no outbox** | `PROJECTION_EXTERNAL_RESIDUAL_AMBIGUOUS` |
| custody 4, liabilities 10, **no outbox** | `PROJECTION_EXTERNAL_RESIDUAL_AMBIGUOUS` |
| custody `(pool-a,USD,spot-pool,10)`, liabilities 10, reserves `(protocol,EUR,vault,5)` | `PROJECTION_EXTERNAL_RESIDUAL_AMBIGUOUS` |
| custody `(pool-a,USD,spot-pool,10)`, liabilities 10 + `(bob,EUR,vault,2)` | `PROJECTION_EXTERNAL_RESIDUAL_AMBIGUOUS` |

The same sweep quantifies it: **1174 of the 3792 refusals (31%)** carry the detail
`"unassigned controlled atoms with no pending obligation"`, and every one of those is a state where no
certificate can be accepted, reported under the code the docstring reserves for states that admit *more than
one*. A further 2303 carry `"N pending rows for M residual cells"`, which mixes both kinds.

Every one of the four shapes above is UNRECONCILABLE, not undetermined. Proof for row 1, executed: the checker's state
bindings leave exactly one admissible fragment — `controlled` must equal `state.custody`
(`_check_lane_aggregates`), `claimant_entitlements` must equal `state.liabilities`
(`_check_entitlement_rows`), `unencumbered_reserves` must equal `state.reserves` = `()`
(`_check_reserve_rows`), and the external effect-id set must equal the PENDING outbox = `∅`
(`_check_external_obligations`). Building that one fragment and running `_check_exactly_once` gives
`SOURCE_ATOM_NOT_ASSIGNED_EXACTLY_ONCE`. **Zero certificates over this state can be accepted.**

Row 2 is worse than a mislabel: the candidate *added* `PROJECTION_NEGATIVE_RESIDUAL` for exactly the
condition "entitlements and reserves exceed custody", but the guard sits **after** the `if not pending:`
early return, so the code fires only when a PENDING outbox entry happens to exist. With no outbox entry the
same economic condition gets the AMBIGUOUS code and the detail string
`"unassigned controlled atoms with no pending obligation"` — which describes an unreconcilable state while
carrying an undetermined code.

Reproduction (self-contained, ~40 lines; the probe I ran is at `/tmp/opus-c9c2-hunt.py`):

```
spec = renderer._spec(lanes_enabled=renderer.ONE_ENABLED,
                      custody=[("pool-a","USD","spot-pool",10)],
                      liabilities=[("alice","USD","spot-pool",4)])
project_allocation_certificate_v1(renderer.build_state_v1(spec),
                                  ((LaneIdV1.ASSET_TRANSFER, root),))
# -> PROJECTION_EXTERNAL_RESIDUAL_AMBIGUOUS "unassigned controlled atoms with no pending obligation"
```

Severity: no runtime consumer, and the projection still refuses (fail-closed), so nothing bad is derived.
But this is precisely the class the previous candidate was marked down for — a pinned headline claim that a
three-line probe falsifies — and it is now pinned in an evidence packet, an enum docstring **and** a test.

Minimal fix (either):
(a) move the negativity test above the early return and give the positive-residual-with-no-outbox case its own
unreconcilable code, e.g. in `_external_rows_v1`:
```python
negative = sorted(k for k, v in open_cells.items() if v < 0)
if negative:
    _fail(RejectCode.PROJECTION_NEGATIVE_RESIDUAL, f"...{asset_domain(negative[0])}")
if not pending:
    if open_cells:
        _fail(RejectCode.PROJECTION_UNASSIGNED_ATOMS, "controlled atoms no row can carry")
    return ()
```
(b) if the family is to stay at ten codes, delete the two-kind claim from `:86-89`, from the packet
`claim_scope`, and from the test docstring at `:417-419`, and state instead that `..._AMBIGUOUS` covers both
kinds where the residual is involved. (a) is preferable: it makes the code family mean what it says.

### P2-1 — The certificate packet says its subject is unchanged in the cut that changed it, and no mutation row declares the new guard

`tests/evidence/test_hygiene/THV1-20260901-global-accounting-allocation-certificate-v21.json`,
`claim_scope[0:80]` = `"v20 re-pin (C9c-1): the certificate module is unchanged; …"`.

S39 changed both certificate modules, and the v21 packet's own pins record it:
`src/core/global_accounting_allocation_certificate_v1.py` `2db66e20…` → `e27b05cf…`,
`zk/…/global_accounting_allocation_certificate.rs` `369949c0…` → `e80681e2…`. The v21 `claim_scope` was
produced by prepending nothing and appending `"Earlier: <v20 text>"`, so the packet now opens by asserting
the module is unchanged. Its 69 mutation rows contain no row for the source-binding guard in either
language (`grep` for `source_principal` / `source binding` across all ten packets returns nothing).

Reproduction: `python3 -c "import json;d=json.load(open('tests/evidence/test_hygiene/THV1-20260901-global-accounting-allocation-certificate-v21.json'));print(d['claim_scope'][:90])"`
against `git show ab8c8ed55 --stat -- src/core/global_accounting_allocation_certificate_v1.py`.

Minimal fix: cut v22 whose `claim_scope` opens with the C9c-2 change ("binds the pending external row's
source principal to a controlled location of its own fragment; Opus P38 P1-1") and carries a mechanical row
for the guard in each language.

### P2-2 — The Rust half of the P1-1 repair has no test and is unreachable from the golden corpus

`zk/global_settlement_abi_v1/src/global_accounting_allocation_certificate.rs:1081-1094`.

The only in-crate test touching pending external rows, `distinct_effect_ids_across_lanes_collect`
(`:1453-1462`), builds fragments with `"controlled_locations": []` and calls `pending_external_rows`, not
`check_external_obligations`, so it never reaches the new branch. The golden corpus cannot reach it either:
the three fixture vectors that carry pending external rows
(`pins_roots_of_a_fully_classified_synthetic_fragment`, `rejects_disabled_lane_with_rows`,
`rejects_later_lane_root_drift_before_earlier_lane_rows`) all reject earlier at `DISABLED_LANE_NOT_EMPTY` or
`LANE_STATE_ROOT_DRIFT`, and the fixture pin `tests/data/global_accounting_allocation_certificate_v1_golden.json`
(`9af6991e…`) is **unchanged** from v20. Python has a negative assertion
(`tests/core/test_global_accounting_allocation_certificate_v1_golden.py`, the `unbacked` case asserting
`detail.endswith("source binding")`); Rust has none, so the Python/Rust parity convention this cycle enforces
elsewhere is not met for the one branch the P1 repair introduced.

Reproduction: `grep -n "source binding" zk/global_settlement_abi_v1/src/*.rs zk/global_settlement_abi_v1/tests/*.rs`
→ only the production site; then the fixture scan above.

Minimal fix: add a `#[test]` beside `duplicate_effect_id_across_lanes_is_rejected` that builds a fragment with
a `controlled_locations` row for `(USD, pool-a, spot-pool)` and a pending row whose `source_principal` is
`pool-b`, asserting `ExternalObligationBindingDrift` with a detail ending `source binding`.

### P2-3 — One of the ten packets still back-dates `created_date`, and that field is exactly what disarms the added-packet rule for it

`tests/evidence/test_hygiene/THV1-20260901-o008-formal-cycle-admission-v35.json`, `created_date` =
`2026-09-02`, added by S39 whose author and commit dates are both `2026-09-03`. Nine of the ten packets this
commit adds stamp `2026-09-03`; this one does not, which contradicts the commit's own statement that "the
generator now stamps the authoring date" — the opus2 P38 P2-1 repair.

The date is load-bearing, verified by experiment (worktree restored after each run, `git status --short`
empty):

| `created_date` in the shipped file | one novel string-only row appended | `check_test_hygiene_v1.py --base-ref 64d17a2f2` |
|---|---|---|
| `2026-09-02` (as shipped) | yes | **exit 0** — packet fully exempt, no check runs |
| `2026-09-03` (honest) | yes | exit 1 — `added evidence packet … declares string-only mutation rows` |

Because `evidence_id[5:13]` = `20260901` < `MECHANICAL_MUTATION_ROWS_FROM` = `20260903` **and**
`_created_date_v1` = `20260902` < the cutover, `_reject_added_legacy_packets`
(`tools/check_test_hygiene_v1.py:255-262`) `continue`s before the carried-row narrowing runs at all. With the
packet's actual rows both dates pass (I checked), so no false claim is currently admitted — but the guard is
switched off for a packet this commit adds, in exactly the way the candidate says it fixed.

Minimal fix: set `created_date` to `2026-09-03` in that packet (the rows are all carried, so the narrowed
rule admits it), and add a hygiene test asserting that every packet added in a commit stamps a
`created_date` not earlier than the commit's author date — or, if that is out of reach, restate the residual
to say which packets currently rely on it.

### P2-4 — The ledger packet claims the gate runs "the packets carrying mechanical rows"; it runs two of five, covering 38 of 91

`tests/evidence/test_hygiene/THV1-20260903-thv1-mutation-ledger-v3.json`, `claim_scope`:
*"the ledger is now EXECUTED BY THE PACKET (two replay commands run it over **the packets carrying
mechanical rows** …), where before ninety-two mechanical rows were gated by nothing"*, and
`LEDGER_GATED_PACKETS_V1` at `tools/o008_formal_cycle_admission_v1.py:95-98`, which names exactly two.

Five current packets carry mechanical rows: `…-allocation-projection-v2` (19, **gated**),
`…-thv1-mutation-ledger-v3` (19, **gated**), `…-global-settlement-exact-ownership-mechanical-v2` (21,
**not gated**), `…-o008-asset-transfer-receipt-admission-mechanical-v2` (31, **not gated**) and
`…-test-hygiene-lineage-ordering-v3` (1, **not gated**) — 91 rows, of which the gate executes 38. The two
largest un-gated packets are **added by this same commit**, so the P38 P2-5 condition ("mechanical rows that
no gate runs") persists for 53 of them, at a smaller scale, while the packet's claim reads as if it were
closed. None of the packet's four nonclaims covers it: they disclaim *undeclared* mutants and *code no row
names*, not *declared rows no gate runs*.

Reproduction (executed): counting mechanical rows across the evidence directory gives the table above, and
running the ledger by hand on one of the un-gated packets shows the rows are honest — the gap is coverage
and claim, not a hidden survivor:

```
python3 tools/thv1_mutation_ledger_v1.py \
  --packet THV1-20260903-global-settlement-exact-ownership-mechanical-v2 --rev 2928191bb
-> {'mechanical': 21, 'killed': 21, 'survived': 0, 'errors': 0}
```

Minimal fix: extend `LEDGER_GATED_PACKETS_V1` with the three remaining packets and their counts (21, 31, 1),
or narrow the `claim_scope` to "the two packets this cycle's candidate authors" and state the residual count.

### P3-1 — No mutation row for the source-binding guard in either language
The certificate lineage carries 69 rows, 0 mechanical, and none names the guard. Every other new guard in
this candidate got a mechanical row. Fix: add one to the v22 packet of P2-1.

### P3-2 — `_grade_ledger` validates four aggregate integers and never inspects a row
`tools/o008_formal_cycle_admission_v1.py:4063-4087`. The `mutation` record the candidate just added
(P38 P2-6) is read by nothing in the gate; the only assertion on it is a unit test over a synthetic packet
(`tests/test_thv1_mutation_ledger_v1.py:358-367`). Fix: have `_grade_ledger` also require every reported row
to carry a non-null `mutation` whose `path` is one of the packet's `source_pins`, and that `verdict` be
`KILLED` for each — a five-line addition that makes the gate check what the report says rather than what it
totals.

### P3-3 — The newly enforced gate's parsing dependencies are unpinned
`tools/thv1_mutation_ledger_v1.py:63,68` imports from `tools/test_hygiene_evidence_v1.py` and
`tools/test_hygiene_model_v1.py`; neither appears in the O-008 packet's `source_pins` or
`hygiene_selection` (`grep -c test_hygiene_evidence_v1 docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.json` → 0).
Those modules decide which rows are mechanical and what text a mutant replaces. The pinned kill count bounds
the damage; the trust base is still larger than the pins. Fix: pin both.

### P3-4 — A test docstring claims a property its body does not check
`tests/core/test_global_accounting_allocation_projection_v1.py:314-317`:
"every code is reachable by a test in this module"; the body asserts only that the tuple equals the enum
order and that two lengths are 10 and 12. The claim happens to be true (I checked all ten by reading the
assertions), but the test does not establish it. Fix: assert the set of codes appearing in this module's
`assert … .code is` sites, or drop the sentence.

### P3-5 — The row-bearing witness exercises one row shape
`_witnessed(with_rows=True)` carries exactly one custody row and one entitlement row, with
`claimant == controlling_principal == "custodian"`, and no reserve, external or terminal rows. The
byte-for-byte claim is no longer vacuous, but "the witness contributes its binding root and its header, not
its rows" is now tested against a single, degenerate row shape. Fix: state the shape in the test docstring,
or admit a witness with two custody rows and a distinct claimant.

### P3-6 — The O-008 packet's projection nonclaim is stale
`docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.md:223` (and the JSON) is byte-identical to P38's and still
enumerates only the two AMBIGUOUS shapes as the cases where the projection refuses. It is not false, but it
does not mention the four codes this candidate added or the two-kind distinction it claims to have drawn.
Fix: extend the nonclaim, or note that the family is enumerated in the THV1 packet.

---

## 4. INFO

**INFO-1 — Prompt/artifact drift.** The checker replay reports **34** runs, not 31; the packet carries
**56** source pins, not 57. Both match the packet's own declarations, so this is an error in the review
brief, not in the candidate.

**INFO-2 — Residual under-determination in the checker, co-extensive with a declared refusal.** When two
principals control one `(asset, control_domain)` cell, the new binding still admits either as
`source_principal`, so two certificates with different `allocation_root`s both pass the row/aggregate/root
passes. Verified: custody `(pool-a,USD,spot-pool,6)` + `(pool-b,USD,spot-pool,4)`, liabilities `()`, one
PENDING entry — hand-built certificates naming `pool-a` and `pool-b` both PASS with different roots. The
projection refuses exactly this state (`PROJECTION_EXTERNAL_RESIDUAL_AMBIGUOUS`, "2 principals control
USD:spot-pool"), so the checker's remaining freedom is confined to states the projection already declines
to derive. Not a finding, but the fix note in opus2's P38 P1-1 — "(a) … makes the projection's guess the only
admissible value" — is true only for single-principal cells and should be recorded as such.

**INFO-3 — opus2 P38 INFO-2 is unchanged.** `derive_canonical_allocation_rows_v1(fragments)` is still called
outside the `except _Reject` boundary in `project_allocation_certificate_v1`
(`global_accounting_allocation_projection_v1.py:448`), so its `OverflowError` would escape as an exception
rather than a refusal. Unreachable, because entitlement keys are unique per state and only one lane may be
enabled.

---

## 5. Lean gate block

All three gates ran serially under `flock -w 7200 /tmp/zenodex-lean.lock` after waiting out
`/tmp/zenodex-formal-core-opus2-c9c2`'s hold on it, and all three are green (40 / 6 / 6 passed, exit 0 each).
Independently, **all seven Lean-bearing commands** — `lean_version`, `lean_direct_check`,
`lean_axioms_probe`, `lean_binding_gate`, `lean_certificate_direct_check`, `lean_certificate_axioms_probe`,
`lean_certificate_binding_gate` — ran to `EXECUTED_PASS` inside the 34-command checker replay in this
worktree and again inside the builder's `--check --replay`, so the Lean evidence is executed three times over.
No SIGBUS, no concurrent-`lean` interference; no pgrep detector was used.

Rust: `cargo fmt --all -- --check`, `cargo clippy --locked --all-targets -- -D warnings` and
`cargo test --locked` all exit 0 in `zk/global_settlement_abi_v1` (54 `test result: ok` summaries, 534
passed, 0 failed). `CARGO_TARGET_DIR=/tmp/zenodex-opus-c9c2-cargo` was used and deleted afterwards.

**Worktree hygiene.** `/tmp/zenodex-formal-core-opus-c9c2` is at P39 with `git status --short` empty at the
end of the review; the three temporary edits made for the P2-3 and C7 experiments were each restored and
verified clean. The author's worktree, the canonical checkout and the other reviewers' worktrees were not
written to, and the author's scratchpad was not read.

## 6. Bottom line

The two P38 P1s are substantively repaired: the forgery is closed with a real binding in both languages, the
ledger is genuinely enforced (I re-ran both commands: 19/19/0/0), the vacuity is genuinely removed with a
row-bearing witness whose receipt proved custody, all ten reject codes have asserting tests, and the pin and
node-id audit is spotless across 134 pins and 809 node ids. The added-packet narrowing keeps its teeth, and
the un-gated mechanical rows I spot-checked by hand are honest (21/21 killed).

Against that: the candidate's own headline — the UNDETERMINED/UNRECONCILABLE separation it exists to draw —
is falsified by a three-line probe and is pinned in a packet, a docstring and a test (P1-1); the guard that
closes the other P1 ships untested in Rust (P2-2) inside a packet that says the module is unchanged (P2-1);
one of the ten packets still back-dates the field that disables the rule the candidate says it repaired
(P2-3); and the ledger packet says the gate covers "the packets carrying mechanical rows" when it covers
two of five (P2-4). Four of the five are the same failure mode as the review they answer: the repair landed
in the code and the claim was written for a larger repair than the one that shipped.

**Grade: B.** Advisory ACCEPT is withheld until P1-1 is closed. Authority stays NONE; the claim ceiling must
not move.
