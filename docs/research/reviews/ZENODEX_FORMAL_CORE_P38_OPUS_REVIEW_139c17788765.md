# Opus C9c-1 review (P38)

| field | value |
|---|---|
| subject | `2e18422919c8cd896c67553645778b46e38e34e5` (S38) |
| source range reviewed | `1f5b1cb81..2e1842291` (5 commits; 4 unreviewed, from a separate agent) |
| artifact | `139c1778876564ff0ec22d13a18e0b7669ee5601` (P38), artifact-only child of S38 |
| packet sha256 | `61eeab4dcc21701b15f2b673589ab28ee5205bfb21f733e18d20cd34b7c220fa` (verified) |
| worktree | `/tmp/zenodex-formal-core-opus-c9c1` (detached, clean, HEAD = P38) |
| reviewer | Opus 5 (independent; ACCEPT is advisory, authority stays NONE) |
| date | 2026-09-03 |
| grade | **B+** — 0 P1, 6 P2, 7 P3, 2 INFO |

## 1. Replays (all commands run under `flock -w 7200 /tmp/zenodex-lean.lock` where Lean-bearing)

| # | command | result |
|---|---|---|
| R1 | `check_o008_formal_cycle_v1.py --root . --packet-commit 139c1778` | exit 0; `ok true`, `packet_admitted true`, `current_source_drift []`, `proof_replay NOT_RUN` |
| R2 | same `--replay --esso-python /usr/bin/python3 --esso-pythonpath …/ESSO` | exit 0; `proof_replay.status = EXECUTED_PASS`, **32 runs**, 0 non-pass, `errors []` |
| R3 | `build_o008_formal_cycle_v1.py --subject-commit 2e184229 --created-date 2026-09-03 --check --replay …` | exit 0; `{"drift":[],"mode":"check","ok":true}`; `git status --short` empty afterwards (artifact reproduces byte-identically) |
| R4 | `cargo fmt --all -- --check` (zk/global_settlement_abi_v1) | exit 0 |
| R5 | `cargo clippy --locked --all-targets -- -D warnings` | exit 0 |
| R6 | `cargo test --locked` | exit 0; all suites ok incl. 3 compile-fail doctests |
| R7 | pytest: `tests/core/test_global_accounting_allocation_projection_v1.py`, `tests/core/test_transition_resource_bound_totality_v1.py`, `tests/core/test_global_settlement_abi_v1_resource_bounds.py`, `tests/core/test_global_settlement_abi_v1.py`, `tests/test_check_o008_formal_cycle_v1.py`, `tests/test_check_global_settlement_canonical_manifest_v1.py`, `tests/test_check_test_hygiene_v1.py`, `tests/test_thv1_mutation_ledger_v1.py` | **579 passed** in 303 s |
| R8 | `check_test_hygiene_v1.py --json` | exit 0; `mutation_rows {legacy: 5043, mechanical: 92, mechanical_current: 90, narrative: 2}` |
| R9 | `--base-ref 8942d6bd2 --json` | exit 0; 5 critical paths |
| R10 | `--base-ref 42ccb6624 --json` | exit 0; 38 critical paths |
| R11 | `--base-ref fd409ba6f7da8f0ec3e0220a04b7406d69a8cb85 --json` (campaign base) | exit 0; 68 critical paths |
| R12 | `thv1_mutation_ledger_v1.py --packet …-allocation-projection-v1` | exit 0; **mechanical=9 killed=9 survived=0 errors=0** |
| R13 | `thv1_mutation_ledger_v1.py --packet …-thv1-mutation-ledger-v2` | exit 0; **mechanical=16 killed=16 survived=0 errors=0** |
| R14 | `thv1_mutation_ledger_v1.py --packet …-global-settlement-exact-ownership-mechanical-v1` (unreviewed range) | exit 0; mechanical=21 **killed=21** survived=0 errors=0 |
| R15 | `thv1_mutation_ledger_v1.py --packet …-o008-asset-transfer-receipt-admission-mechanical-v1` (unreviewed range) | exit 0; mechanical=31 **killed=31** narrative=2 survived=0 errors=0 |
| R15b | `thv1_mutation_ledger_v1.py --packet …-thv1-mutation-ledger-v1` (superseded by v2) | **exit 1**; mechanical=15 killed=13 survived=0 **errors=2 (PIN_DRIFT)** — see P2-5 |
| R16 | `pytest tests/formal/test_lean_asset_transfer_refinement_v1.py` (under the lock) | exit 0; **40 passed** |
| R17 | `pytest tests/formal/test_lean_global_accounting_allocation_certificate_v1.py tests/formal/test_lean_global_claimant_custody_relation_v1.py` (under the lock) | exit 0; **12 passed** |

Packet identity, write set and pins verified independently: P38 changes only
`docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.{json,md}`; `subject_commit = 2e184229…`,
`subject_parent = 8942d6bd2…`, `packet_commit_parent = 2e184229…`; all 55 source pins and the
projection packet's 3 pins match HEAD bytes; the packet's 40 pinned node ids equal the 40 tests
pytest collects from `tests/core/test_global_accounting_allocation_projection_v1.py`
(`python_allocation_projection_gate` expects 40 passed — correct).

Note: the reviewer prompt says the `--replay` run reports 31 runs; I observe **32**, matching the
32 declared `REPLAY_COMMANDS_V1`. Not a defect, but the prompt's figure is stale.

## 2. Verdicts on the declared claims

### C1. "The certificate is DERIVED, not assembled" — **CLOSED**

`src/core/global_accounting_allocation_projection_v1.py:305-411` inverts the checker's
expectations exactly as documented: controlled ← `state.custody`, entitlements ←
`state.liabilities`, reserves ← `state.reserves`, external ← PENDING outbox residual, terminals ←
OPEN obligations. Verified empirically:

* purity/no aliasing/determinism: `canonical_global_bytes_v1(state)` and `state.state_root`
  unchanged across a projection; two projections byte-identical; no row object of
  `fragment.controlled_locations` is an object of `state.custody`; the caller's
  `lane_binding_roots` tuple is unchanged. Inputs are frozen slots dataclasses over immutable
  tuples, so mutation is impossible by construction.
* exact typing at the boundary (`type(...) is not`, not `isinstance`) at :306-315 and :129-145.
* reject-is-a-value: `AllocationProjectionRejectedV1` carries the unchanged pre-state root
  (:94-113); the `_Reject` exception never escapes (`except _Reject` at :390).

Check order vs docstring: matches for steps (0)-(2); see **P3-1** for the enum's ordering claim.

### C2. "The fixture partition is the headline result" — **PARTIAL**

The counts are pinned by a test that really calls the checker
(`test_the_fixture_partition_of_states_is_pinned`, test file :86-114: the `accept` bucket is
incremented only after `assert isinstance(outcome, AllocationCertificateAcceptedV1)`), and I
reproduce `{accept: 20, projection_refusal: 7, state_level: 2}` = 29. The earlier defect the
mutation ledger caught is genuinely repaired.

But the claim's force is much smaller than its prose, and its general form is false — see
**P2-1** and **P2-2**.

### C3. "What the witness adds" — **PARTIAL**

`test_witnessed_certificate_is_the_projection_plus_one_receipt_root` does establish, for the one
registered receipt-backed lane, that the projection given only the receipt root reproduces the
witnessed certificate byte-for-byte, that the checker accepts it in the witnessed slot, and that
without the root the projection refuses `PROJECTION_BINDING_ROOT_MISSING` rather than
substituting the lane root. All three replay. The limit is **P2-2**: the witness fragment used is
empty.

### C4. "Two ambiguities refused, not guessed" — **CLOSED (both reachable), with a third shape found**

Both are reachable and I reproduced them independently
(`PROJECTION_TERMINAL_DOMAIN_AMBIGUOUS` with `2 entitlement domains`;
`PROJECTION_EXTERNAL_RESIDUAL_AMBIGUOUS` with `2 pending rows for 1 residual cells`). I did not
find a shape the projection *guesses*: every under-determined shape I could construct is refused
(two controlling principals for a terminal; two principals over a residual cell; negative
residual; a terminal naming a foreign lane). What I did find is that four of those refusals are
**untested** (**P2-3**) and that the code family conflates "undetermined" with "unreconcilable"
(**P3-2**, **P3-3**).

### C5. The mechanical mutation ledger (the four unreviewed commits) — **CLOSED as a tool, PARTIAL as a gate**

Re-run by me: I executed **every mechanical row in the repository** — all 92 that
`check_test_hygiene_v1.py` counts, across all five mechanical packets (projection 9/9, ledger-v2
16/16, exact-ownership-mechanical-v1 21/21, asset-transfer-receipt-admission-mechanical-v1 31/31
plus 2 NARRATIVE, ledger-v1 13/15). Totals: **90 KILLED, 0 SURVIVED, 0 UNVIABLE, 0 CONTROL_FAILED,
2 PIN_DRIFT** (both in the superseded ledger-v1, which pins `tools/check_test_hygiene_v1.py` at
`2c8eb956f210…` while HEAD is `398157a05df2…`). Every declared killer that can run, kills. Adversarial judgement:

* **CONTROL_FAILED does what it claims** for the failure direction: `control_error_v1`
  (:200-214) rejects a timed-out or non-zero control run, and for cargo additionally requires a
  green summary with ≥1 passed test. `mutant_verdict_v1` (:216-236) is correctly strict: pytest
  exit 1 only is KILLED; exit 0 is SURVIVED; anything else (collection error, compile error) is
  UNVIABLE. I confirmed this by feeding a mutant that raises at import: verdict UNVIABLE, exit 4,
  ledger exit 1. Good.
* **Archive isolation is real**: `git archive <rev>` into a fresh per-row directory created with
  `exist_ok=False`, pins re-checked against the copy before mutating, worktree never read for
  sources and never written; `python -m pytest` from the copy puts the copy at `sys.path[0]`.
  Control and mutant runs share one environment, so environment leakage is common-mode and cannot
  manufacture a kill (see INFO-1).
* **A row CAN be declared so it appears killed without the mutation mattering** — see **P2-6**,
  with a reproduction.
* Date rule: a row cut from `20260903` must be mechanical or narrative
  (`_validate_mutations`, `tools/test_hygiene_evidence_v1.py:355-361`, gated on
  `legacy_allowed = evidence_id[5:13] < "20260903"`). Correct, and `<` makes a packet dated
  exactly at the cutover non-exempt.

### C6. The added-packet rule and its residual — **CLOSED, residual honestly declared**

`_reject_added_legacy_packets` (`tools/check_test_hygiene_v1.py:213-244`). Evasion hunt:

* renames are closed: `collect_git_changed_paths` uses `--find-renames` and `_parse_git_name_status`
  normalizes a rename to D+A, and `_reject_packet_rewrites` (:300-307) raises on any non-`A`
  status under the evidence prefix. Verified by reading; the D half is fatal.
* absent/unparseable/non-string/non-8-digit `created_date` → `"99999999"` → not exempt. Correct,
  and `_created_date_v1`'s docstring says so.
* a hyphenated evidence-id date (e.g. `THV1-2026-09-03-…`) passes the id-date half of the test by
  ASCII ordering (`'-' < '0'`), but the `created_date` half still refuses it. The conjunction is
  what saves this; worth knowing it is load-bearing.
* the declared residual (back-date **both** fields) is real and correctly stated.
* one soft spot: if an ADDED evidence path is not among the loaded packets, `rows_by_name.get(name, ())`
  makes the `require` vacuously true. Not exploitable for coverage (an unloaded file is not a
  packet a rule can select), so INFO only.

The residual is not hypothetical: **130 packets** are reported ADDED against the campaign base
`fd409ba6f`, and four of the six packets under review — `o008-formal-cycle-admission-v34` (105
legacy rows), `global-accounting-allocation-certificate-v20` (69), `claimant-backing-guard-golden-v27`
(13), `global-settlement-v1-canonical-exact-admission-v8` (7) — are added on 2026-09-03 and exempt
because their lineage id-date is 20260901/20260902. Mitigating and worth stating plainly: I diffed
each against its predecessor and **the mutation lists are byte-identical** (v19→v20, v33→v34,
v26→v27, v7→v8), so these re-cuts introduce **no new unexecuted mutation claims**; v34 is a pin
refresh that adds `src/core/global_accounting_allocation_projection_v1.py` as a pinned path.

### C7. Packet, pins, nonclaims, claim ceiling — **CLOSED except the Rust-twin gap**

Claim ceiling unmoved: `formal_core_complete false`, `o008_status OPEN_EXACT_ALL_12_RECONCILIATION_MISSING`,
every authority `NONE`. The new nonclaim (index 4 of `NONCLAIMS_V1`) accurately says the projection
has no consumer, verifies no receipt, and leaves multi-lane ownership undecided. It does **not**
declare the missing Rust twin — **P2-4**.

---

## P2 findings

### P2-1 — the row-defect claim is false in its general form; the projection can express a row defect

`src/core/global_accounting_allocation_projection_v1.py:239-302` (`_terminal_rows_v1`, lines 239-302) derives a
terminal row's domain and principal but never bounds the **sum** of OPEN terminal amounts against
the entitlement, which is exactly what the checker's `_check_terminal_totals`
(`global_accounting_allocation_certificate_v1.py:942-961`) requires. The packet's `claim_scope`
says "it never yields a row, aggregate or derived-root defect, so the twenty certificate-forgery
vectors of the fixture are shapes a derived certificate cannot express" — the second clause reads
as a property of derivation, and it is not one.

Reproduction (exact, no witness needed to see the defect; the full checker masks it at
`RECEIPT_WITNESS_REQUIRED`, position 4 of `CHECK_ORDER_V1`, before the row checks at 6-13):

```python
ONE = [False]*12; ONE[0] = True
state = renderer.build_state_v1(renderer._spec(lanes_enabled=ONE,
    custody=[("pool-a","USD","spot-pool",6)],
    liabilities=[("alice","USD","spot-pool",3)],
    reserves=[("res-a","USD","spot-pool",3)]))
state = replace(state, terminal_obligations=(
    TerminalObligationV1("terminal-1", LaneIdV1.ASSET_TRANSFER, "alice", "USD", 2, OPEN),
    TerminalObligationV1("terminal-2", LaneIdV1.ASSET_TRANSFER, "alice", "USD", 2, OPEN)))
p = project_allocation_certificate_v1(state, ((LaneIdV1.ASSET_TRANSFER, state.lane_roots[0].state_root),))
# p is a certificate carrying both rows; then:
cert._check_terminal_bindings(p, state)
#   -> TERMINAL_BINDING_DRIFT "ASSET_TRANSFER terminal total USD:alice:spot-pool"
# every other row/aggregate/root check PASSES on the same certificate
```

`GlobalEconomicStateV1.__post_init__` orders terminal obligations by `obligation_id` only and
places no bound on their totals, so this state is well-formed.

Minimal fix: either (a) fold the OPEN terminal amounts per `(asset, claimant, domain)` in
`_terminal_rows_v1` and refuse with a new closed code when the total exceeds the entitlement
(making it a state-level unreconcilability, matching the two existing state-level gates), or
(b) restate `claim_scope` and the test docstring as a fixture-scoped observation and drop the
"shapes a derived certificate cannot express" generalisation. (b) is the honest one-line change;
(a) is the one that makes the sentence true.

### P2-2 — the accepted bucket is vacuous for the very checks the claim is about, and so is the witness claim

Census over the 29 fixture states (`renderer.VECTORS_V1`): **22 have every economic table empty**;
the other 7 have exactly one row in exactly one table, and 5 of those land in the
`projection_refusal` bucket. `test_accepted_fixture_vectors_are_reproduced_byte_for_byte`
(test file :118-136) asserts every accepted projection equals
`cert.build_registered_empty_certificate_v1(state)`. So **all 20 members of the accepted bucket
carry zero rows in all twelve fragments**, and `_check_exactly_once`, `_check_entitlement_rows`,
`_check_reserve_rows`, `_check_external_obligations`, `_check_terminal_bindings`,
`_check_lane_aggregates` are satisfied over empty inputs. The sentence "the twenty
certificate-forgery vectors are shapes a derived certificate cannot express" is carried entirely
by the empty certificate.

The same limit hits C3, harder than the prompt's phrasing suggests: `_witnessed()`
(`tests/core/test_global_accounting_allocation_certificate_v1_golden.py:345-374`) builds its state
from `renderer._spec(lanes_enabled=ONE_ENABLED)` with default (empty) tables, and I measured
`witness.fragment.is_empty is True` — 0 controlled, 0 entitlements, 0 reserves, 0 external, 0
terminal rows. The claim "the sealed witness contributes its binding root and its header, **not its
rows**" is therefore proved on a witness that **has no rows**. It is true but empty.

Compounding this: with the current `LANE_ALLOCATION_PRODUCER_REGISTRY_V1`, the only way to reach
the checker's row checks with a non-empty certificate is a minted `VerifiedLaneAllocationFragmentV1`
for ASSET_TRANSFER whose fragment equals the projected fragment; every non-empty projection in the
test file is checked with `EMPTY_LANE_WITNESS_SLOTS_V1` and therefore stops at
`RECEIPT_WITNESS_REQUIRED` (test file :225-243 and :262-278 assert exactly that). **No test in this
candidate ever runs the checker's row checks against a non-empty derived certificate.**

Minimal fix: state this in the packet nonclaims verbatim ("every certificate the checker accepts
in the fixture is the registered-empty one; the witness whose rows are shown to be redundant is
itself empty; no non-empty derived certificate has been checked end-to-end"), and, when a
non-empty admission fixture becomes available, add one vector with non-empty custody/liabilities
that reaches `_check_exactly_once` through a real witness.

### P2-3 — six surviving mutants in undeclared guards of the same 412-line module

The packet declares 9 mechanical rows and all 9 kill. I applied six further mutants to the same
module in a `git archive HEAD` copy and ran the whole pinned test file
(`pytest -q tests/core/test_global_accounting_allocation_projection_v1.py`): **all six survive,
40 passed each time.**

| # | site | mutant | reachable guard (verified) |
|---|---|---|---|
| M1 | `:285` `_terminal_rows_v1` | `if len(principals) != 1:` → `< 1:` | `t1: 2 principals` |
| M2 | `:220` `_external_rows_v1` | `if len(principals) != 1:` → `< 1:` | `2 principals control USD:spot-pool` |
| M3 | `:212` `_external_rows_v1` | `if amount < 0:` → `if False:` | `negative residual for USD:spot-pool` |
| M4 | `:260` `_terminal_rows_v1` | `if terminal.lane_id is not lane_id:` → `if False:` | `terminal t1 names SPOT_LIQUIDITY` |
| M5 | `:200` `_external_rows_v1` | `if open_cells:` → `if False:` | reached via liabilities > custody |
| M6 | `:302` | `sorted(rows, key=…obligation_id)` → `reversed(rows)` | terminal row order unpinned |

M1 and M2 matter most: under them the projection silently takes `principals[0]` — precisely the
*guessing* the module docstring says it refuses ("unique only when … one principal controls it;
anything else is refused rather than guessed"). The declared failure mode "a projection guesses a
terminal row's control domain when the state names two candidates" is covered only on the domain
half; the principal half is untested. M4 means `PROJECTION_NO_LANE_FOR_ROWS`'s second site is dead
to the suite, although `test_reject_codes_are_closed_and_ordered`'s docstring asserts "every code
is reachable by a test in this module" (true per code, not per site).

Minimal fix: six regressions, one per row above, each a two-line state built with
`_one_enabled_state`; then declare them as six further mechanical rows so the ledger executes them.

### P2-4 — no Rust twin of the projection, and the packet does not declare the gap

Every other Python surface in this cycle carries a Rust twin pin role
(`admission_rust_twin`, `producers_rust`, `rust_compiled_projection_gate`, …). The projection is
pinned only as `allocation_projection` / `allocation_projection_replay`
(`tools/o008_formal_cycle_admission_v1.py:89-90, 190-191, 251-252`). Neither the packet's five
nonclaims nor `NONCLAIMS_V1[4]` says a Rust twin does not exist; a reader who knows the cycle's
convention will assume one does. Minimal fix: one nonclaim sentence — "There is no Rust twin of
the allocation projection; the derivation exists in Python only and no differential test compares
it to a Rust implementation."

### P2-5 — nothing in the replay set or the battery executes the mutation ledger

The 32 `REPLAY_COMMANDS_V1` contain no `thv1_mutation_ledger_v1.py` invocation (I enumerated them;
`grep -n thv1_mutation_ledger docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.{json,md}` is empty).
`tools/formal_core_battery_v1.sh` adds `tests/test_thv1_mutation_ledger_v1.py` — the ledger's own
**unit tests**, not a ledger run. So the campaign now has 92 mechanical rows of which **zero are
executed by any gate**; the "mechanical rows are executed" property holds only because a human or
agent runs the tool by hand (as I did for all 92 in this review).

There is a real obstacle worth recording rather than hand-waving, and I confirmed it by running it:
the ledger has no notion of a superseded packet, and `THV1-20260903-thv1-mutation-ledger-v1`
(superseded by v2) pins `tools/check_test_hygiene_v1.py` at `2c8eb956f210…` while HEAD is
`398157a05df2…`, so it returns **exit 1 with 2 PIN_DRIFT rows** — a naive "run every packet" gate is
red on day one. This is exactly the `mechanical: 92` vs `mechanical_current: 90` gap the checker
already reports, which is the right place to scope the gate from. Minimal fix: add a replay command that
runs the ledger for the packets whose pins are current (or for the packets the run's
`hygiene_selection` selected), with an expected `killed == mechanical`.

### P2-6 — the ledger proves the killer is sensitive to the edit, never that the edit is the property named

`_parse_mutant` (`tools/test_hygiene_evidence_v1.py:285-294`) constrains a mutant to: a pinned
source path, a non-empty needle, and `replacement != needle`. Nothing relates the mutant to the
row's `description`. Reproduction, on this exact worktree:

```bash
# packet identical to the committed one except for a single row:
#   description: "the terminal controlling-principal uniqueness check is load-bearing: ..."
#   mutant: src/core/global_accounting_allocation_projection_v1.py
#           "    state_root = state.state_root" -> "    state_root = state.profile_root"
python tools/thv1_mutation_ledger_v1.py --repo . \
  --packet THV1-20260903-global-accounting-allocation-projection-v1 \
  --packet-file <doctored>/THV1-20260903-global-accounting-allocation-projection-v1.json
# -> {"killed": 1, "survived": 0, "errors": 0, "mechanical": 1}, verdict KILLED, exit 0
```

The mutant has nothing to do with terminal principals. Two structural reasons the report cannot be
audited after the fact: (a) `REPORT_KEYS_V1` records `description`, `killer`, `mutant_sha256`
(a digest of the whole mutated file) — never the needle or replacement, so a reader cannot check
description↔mutant correspondence from the report; (b) `--packet-file` and `--filter` are logged to
stderr only and leave **no trace in the JSON**, so a green report is indistinguishable from one
produced against a doctored or partial packet.

The tool's own docstring claim — "so a packet cannot claim a killer that does not kill" — is
precise and true. The campaign's framing around it should not be read as "the declared property is
the one tested". Minimal fix: put `needle_sha256`, `replacement_sha256`, `packet_sha256`, and
`filters` into the report; add one sentence to the ledger nonclaims: "the ledger does not check
that a mutant is the weakening its description names; that correspondence is a review obligation."

## P3 findings

* **P3-1 — the reject enum's declared order is falsified.**
  `AllocationProjectionRejectCodeV1`'s docstring (`global_accounting_allocation_projection_v1.py:78`) says "Closed projection rejects, in the
  order the projection checks them", but `PROJECTION_NO_LANE_FOR_ROWS` (declared 4th) is checked at
  **two** sites, the second (`_terminal_rows_v1:260`) *after* `PROJECTION_EXTERNAL_RESIDUAL_AMBIGUOUS`
  (declared 5th). Repro: one enabled lane, custody `("pool-a","USD","spot-pool",10)`, two PENDING
  outbox rows, and one OPEN terminal naming `SPOT_LIQUIDITY` → the projection reports
  `PROJECTION_EXTERNAL_RESIDUAL_AMBIGUOUS "2 pending rows for 1 residual cells"`, not the
  earlier-declared code. Fix: either hoist the foreign-lane check above `_external_rows_v1`, or
  amend the docstring to "declaration order; `NO_LANE_FOR_ROWS` is checked at two points".
* **P3-2 — `PROJECTION_EXTERNAL_RESIDUAL_AMBIGUOUS` conflates *undetermined* with *unreconcilable*,
  and one detail string is factually wrong.** With `custody = 3` and `liabilities = 5` over the same
  cell the residual is `-2` and the projection refuses with detail
  `"unassigned controlled atoms with no pending obligation"` — the atoms are over-assigned, not
  unassigned, and nothing is ambiguous: no certificate reconciles that state. The module docstring
  presents this family as "WHERE THE STATE DETERMINES NOTHING". Fix: a separate closed code (e.g.
  `PROJECTION_RESIDUAL_NEGATIVE`) or at minimum a correct detail string.
* **P3-3 — `PROJECTION_TERMINAL_DOMAIN_AMBIGUOUS` fires with `0 entitlement domains`.** A terminal
  whose claimant holds no entitlement at all is refused as "ambiguous". Same conflation as P3-2;
  same one-line fix.
* **P3-4 — the contract doc's mutant schema is wrong.** `docs/testing/TEST_HYGIENE_CONTRACT_V1.md`
  (added by `e512cdb12`) documents `"mutant": {"path", "needle", "replacement"}`, but `8942d6bd2`
  changed the schema to `_MUTANT_FIELDS = {"path", "needle_lines", "replacement_lines"}`
  (`tools/test_hygiene_evidence_v1.py:64`) and `exact_fields` refuses anything else. A packet author
  following the doc gets a schema refusal. The doc is not pinned by any packet, so nothing caught it.
* **P3-5 — the contract doc misstates the added-packet rule.** It says "an added packet may not
  carry them whatever date its name claims". An added packet *may*, when both its name date and its
  `created_date` precede the cutover — and 130 packets added since the campaign base do exactly
  that, including four of the six under review. Fix: mirror the checker docstring, residual included.
* **P3-6 — the pytest control path lacks the cargo path's "at least one test ran" guard.**
  `control_error_v1` requires `sum(passed) >= 1` for cargo but accepts any pytest exit 0, so an
  all-skipped killer qualifies as a control. It cannot manufacture a KILLED (the mutant run would
  exit 0 → SURVIVED), so severity is low, but the asymmetry is unstated. Fix: parse the pytest
  summary and require ≥1 passed, as cargo already does.
* **P3-7 — a declared failure mode with no evidence.** The projection packet lists
  "a projection mutates or aliases the caller's state" among its `failure_modes` and asserts it in
  `reject_is_noop.reason`, but no mutation row and no test pins it. I verified the property holds
  (§C1); it is nonetheless an unpinned claim in a packet whose other four failure modes each have a
  killer. Fix: one regression asserting `canonical_global_bytes_v1(state)` is unchanged across a
  projection and a refusal, plus a mechanical row for it.

## INFO

* **INFO-1 — the ledger does not sanitize the caller's environment.** `run_environment_v1`
  (`:327-335`) copies `os.environ` and sets only `PYTHONDONTWRITEBYTECODE`, `LANG`, `LC_ALL`,
  `CARGO_INCREMENTAL`, `CARGO_TARGET_DIR`. `PYTHONPATH`, `PYTEST_ADDOPTS`, `PYTHONSTARTUP` pass
  through. Because the control and mutant runs share one environment, any effect is common-mode and
  cannot produce a false KILLED, and `python -m pytest` puts the copy at `sys.path[0]` ahead of
  `PYTHONPATH`. So this is a hygiene note, not a defect: the "archive isolation" is isolation of
  *files*, not of *environment*.
* **INFO-2 — an ADDED evidence path that is not a loaded packet passes `_reject_added_legacy_packets`
  vacuously** (`rows_by_name.get(name, ())`). Not exploitable for coverage, since an unloaded file
  cannot be selected by any rule; worth an explicit `require(name in rows_by_name)`.

## What I could not falsify

* No state I could construct makes the projection **guess** an under-determined value: the two
  declared ambiguities plus the two-principal, negative-residual and foreign-lane shapes are all
  refused with closed codes (all four verified reachable). The gap is coverage (P2-3), not soundness.
* No pin, node id, sha, or claim-ceiling drift: 55 source pins clean, 3 projection-packet pins
  clean, 40 node ids = 40 collected tests, packet sha256 as declared, `formal_core_complete false`
  and every authority `NONE`.
* The four unreviewed commits do not weaken any existing gate: the hygiene checker is green in
  static mode and against all three bases including the campaign base, and the loader change makes
  the schema *stricter* from the cutover, not looser.

## Verdict

**B+ — ACCEPT WITH CHANGES (advisory).** The engineering is careful and everything replays: the
projection is pure, exact-typed and reject-is-a-value; the partition test now checks the bucket it
counts; the ledger is a real, correctly fail-closed tool whose CONTROL/UNVIABLE handling I could
not break, and 46 declared mechanical rows kill when I run them myself. The grade sits at B+ rather
than A- because the two headline properties are materially weaker than their prose — the row-defect
claim is false in the general form the `claim_scope` states (P2-1) and vacuous in the fixture form
(P2-2, including a witness with no rows) — and because six independently-weakenable guards in the
same module are untested (P2-3). None of this moves the claim ceiling: authority stays NONE,
`formal_core_complete` stays false, and the projection has no consumer.

Required before this reads as A-: P2-1 (fix or restate), P2-2 (nonclaim the emptiness in the
packet), P2-3 (six regressions + six mechanical rows), P2-4 (one nonclaim sentence). P2-5 and P2-6
are campaign-level and can be scheduled.
