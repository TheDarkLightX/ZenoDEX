# Opus 5 independent review — P13 `ca20a72fc92e3ec59a72045d68afd16ef31b0f0e`

Advisory only. This review grants no authority of any kind.

Subject worktree: `/tmp/zenodex-formal-core-review-p-ca20a72fc` (read-only, detached, never modified).
Branch: `codex/formal-core-fable-20260901`. Reviewer: Opus 5. Date: 2026-09-01.

## 0. Chain topology (and one correction to the brief)

```
ca20a72fc (P13, packet-only)  tree bbd21314…  parent 11f879fdb
11f879fdb (S13, C4d)          tree a1b27eb99  parent 0b3dc9b82
0b3dc9b82 (R10, Opus P10 receipt)             parent d5e4d1d44
d5e4d1d44 (P12)                               parent 00269d602
00269d602 (S12, C4c)                          parent f83cf5a9a
f83cf5a9a (P11)                               parent 6e5f4be57
6e5f4be57 (S11, C4b)                          parent b47077ea2 (P10)
```

**The brief's `S13 = 4af399a5f8cd73a1cc9edafdf73b95bdf4dc2a7d` is stale.** That commit exists but is
**not an ancestor of P13**: it is a superseded sibling with the same parent (`0b3dc9b82`), same message
and same author date, differing from the real S13 only in

```
tools/o008_formal_cycle_admission_v1.py:981
-CERTIFICATE_PYTHON_GATE_EXPECTED_PASSED_V1: Final = 32
+CERTIFICATE_PYTHON_GATE_EXPECTED_PASSED_V1: Final = 33
```

plus the corresponding hygiene ledger line. The real S13 is `11f879fdb65a80fdf82fdb5b7e459bb1bcd81069`,
which is what the packet pins (`subject_commit`, `subject_tree = a1b27eb99…`, `packet_commit_parent`).
No artifact defect; the brief's hash is wrong, and every command below used the real S13.

P13 is genuinely packet-only: `git diff 11f879fdb ca20a72fc` touches exactly
`docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.{json,md}`.

## 1. Verification record

| # | Command | Result |
|---|---|---|
| 1 | `check_o008_formal_cycle_v1.py --root $PWD` | exit 0, `ok:true`, `packet_admitted:true`, `proof_replay: NOT_RUN`, `current_applicable:true`, `current_source_drift:[]`, `errors:[]` |
| 2 | same `--replay --python $PY --esso-python /usr/bin/python3 --esso-pythonpath …/ESSO` | exit 0, `EXECUTED_PASS`, **26 runs**, every run exit 0 (3m16s) |
| 3 | `build_o008_formal_cycle_v1.py --root $PWD --subject-commit 11f879fdb --created-date 2026-09-01 --check --replay …` | exit 0, `{"mode":"check","ok":true,"drift":[]}` — packet reproduces byte-identically from the tree |
| 4 | pytest `test_check_o008_formal_cycle_v1.py`, `test_o008_v1_projection_runtime_gate.py`, `test_global_claimant_backing_guard_v1_golden.py`, `test_global_accounting_allocation_certificate_v1_golden.py`, `test_check_global_settlement_canonical_manifest_v1.py` | **447 passed**, exit 0 (189s) |
| 5 | pytest `tests/formal/test_lean_global_claimant_custody_relation_v1.py` (serial) | 6 passed, exit 0 |
| 6 | pytest `tests/formal/test_lean_global_accounting_allocation_certificate_v1.py` (serial, last) | 6 passed, exit 0 — matches packet `binding_gate_expected_passed: 6` |
| 7 | `cargo test --offline --locked --test global_accounting_allocation_certificate_golden` | ok, **3 passed** (= `CERTIFICATE_RUST_GATE_EXPECTED_PASSED_V1`) |
| 8 | `cargo test --offline --locked --lib -- global_accounting_allocation_certificate::tests::` | ok, **2 passed** (= `CERTIFICATE_RUST_UNIT_GATE_EXPECTED_PASSED_V1`) |
| 9 | `cargo clippy --offline --locked --all-targets -- -D warnings` | exit 0, clean |
| 10 | `lake env lean -DwarningAsError=true Proofs/GlobalAccountingAllocationCertificateV1.lean` | exit 0, no output, 3.8s (run serially; no 135/139) |
| 11 | `#print axioms` probe of **all 16** theorems | exit 0; only `propext`, `Quot.sound`, `Classical.choice`. No `sorryAx`, no `Lean.ofReduceBool` (so no `native_decide`). Matches `allowed_axioms` |
| 12 | `check_test_hygiene_v1.py --base-ref 11f879fdb --json` | exit 0, `ok:true`, `changed_path_count:2`, `critical_path_count:0` (correct for a packet-only child) |
| 13 | `ruff check` on the four tools modules + certificate module | All checks passed |
| 14 | `mypy --strict` on the same five | Success: no issues found in 5 source files |
| 15 | Hand-recomputed **all 38** `source_pins` sha256 against the tree | 38/38 match, 0 mismatches, 0 missing. Includes admission core, both Lean files, both ESSO models, `state.rs`, `bounded_vec.rs`, the Rust gate, and the certificate fixture |
| 16 | Independent `ESSO validate` of the certificate model | `ir_hash = sha256:d4b31fee…232b` — matches packet exactly; source sha256 `07caf718…a5a8` matches |

**User decisions all hold.** `claim_ceiling`: every authority (`migration`, `production`, `publication`,
`release`, `settlement`, `value_movement`, `verifier`) is `NONE`; `formal_core_complete: false`;
`o008_status: OPEN_EXACT_ALL_12_RECONCILIATION_MISSING`; `value_movement_gates_closed: 0/12`;
`whole_value_movement_safe: false`. Reserves are claimant-free
(`ReserveInterpretationV1.NAMED_UNENCUMBERED_NO_CLAIMANT`, sole member). Control-domain vocabulary is
used throughout and the V1 wire names are byte-stable (golden replay + manifest source-closure digest
both green). **O-008A is unattested** (0 occurrences in the packet) and **no UP-xx is fixture-selected**
(0 occurrences; the UP-xx labels appear only as `blocked_on` strings in the producer registry, which is
the correct place).

---

## 2. Scope A — C4b, the bounded Lean model (S11)

### Grade: **A−** — ACCEPT, with the P2-1 repair required before the model is used to underwrite a receipt-backed lane.

`lean-mathlib/Proofs/GlobalAccountingAllocationCertificateV1.lean` (415 lines). Three lanes, two
domains, two claimants over `Nat`.

**Structural checks pass.** No double quote anywhere in the raw file (0 occurrences); no `#` command;
no CR, no BOM; no `«` identifiers; `--` occurs only inside `/-- … -/` doc comments. `Proofs.lean`
declares the import. Namespace opens/closes match. `definitional_theorems: []` is correct — I found no
theorem proved by projection out of its own hypothesis.

**Per-theorem quality (repo gates applied).**

*Not a tautology.* `certificate_implies_normativePartition` (:123) is genuinely derived: `Tables`
(:69-75) carries `custody, liability, reserves, external, openTerminal` and **no partition field**, so
the conclusion `custody = Σ liability + reserves + external` is obtained by summing the three lane
partitions and rewriting through the row/aggregate equalities under `omega`. The packet's claim
"Derived, not assumed: `Tables` carries no partition field" is true.

*Substantive (5).* `certificate_implies_normativePartition`, `certificate_implies_terminalCovered`
(:148, real three-lane sum-of-bounds reasoning), `noReceiptBacked_forces_allDisabled` (:174),
`noReceiptBacked_implies_zeroTables` (:188, multi-step), and `lanePartition_premise_is_necessary`
(:405). The last is the highest-value result in the file: a genuine **independence** proof that the
gate + terminal bound + row equality + aggregate equality do **not** imply the normative partition,
witnessed by `unassignedCertificate`/`unassignedTables` where `custody d0 = 7` but
`3+2+0+1 = 6`. That is a real negative result, not padding.

*Thin (2).* `certificate_implies_sameDomainBacked` (:140) and
`certificate_noReserve_noExternal_implies_exactCustody` (:163) are each one `omega` from
`certificate_implies_normativePartition` and would fail a strict 5-second test as standalone theorems.
I do **not** count this against the grade: both are named protocol bridges (R1 of the claimant-backing
guard; the exact current-profile equality of `GlobalClaimantCustodyRelationV1`), so exposing them as
top-level statements is justified. The packet's `substantive_theorem_count: 7 / theorem_count: 16` is
therefore defensible, and reporting both numbers is exactly what the repo rules require. A stricter
reading is 5 substantive + 2 named corollaries + 9 witnesses.

*Non-vacuity is real, twice.* `registeredEmpty_nonvacuous` (:243) is the empty witness, but
`mixed_nonvacuous` (:310) carries actual content — entitlements 3/2/4, reserve 1, external 1, terminal
2 — so the derived theorems are demonstrably not consequences of emptiness. Four refutations
(`unassignedAtom_fails_partition`, `reserve_cannot_cover_claimant`, `enabledWithoutProducer_fails_gate`,
`terminalOverEntitlement_fails_bound`) show each conjunct is load-bearing.
`reserve_cannot_cover_claimant` (:355) is well-constructed: it asserts the *other* conjuncts still hold
(partition and aggregate) while row equality fails, which is what makes it evidence for
`NAMED_UNENCUMBERED_NO_CLAIMANT` rather than a generic failure.

**Correspondence to `CHECK_ORDER_V1`.** `ProducerGate` ↔ `BLOCKED_LANE_PRODUCER_MISSING` +
`DISABLED_LANE_NOT_EMPTY`; `LanePartition` ↔ `SOURCE_ATOM_NOT_ASSIGNED_EXACTLY_ONCE`; `RowsEqual` ↔
`ENTITLEMENT_ROWS_DRIFT` / `RESERVE_ROWS_DRIFT` / `EXTERNAL_OBLIGATION_BINDING_DRIFT` /
`TERMINAL_BINDING_DRIFT`; `AggregateEqual` ↔ `LANE_AGGREGATE_DRIFT`. All correct **except**
`TerminalBound` — see P2-1.

### P2-1 — `TerminalBound` is an aggregate bound; the running check is per-row (MOUNTED)

`lean-mathlib/Proofs/GlobalAccountingAllocationCertificateV1.lean:91-93`

```lean
/-- Every open terminal claim is backed by an entitlement of the same claimant and
domain that is at least as large (`TERMINAL_BINDING_DRIFT`). -/
def TerminalBound (f : LaneFragment) : Prop :=
  ∀ c d, f.terminal c d ≤ f.entitlement c d
```

`f.terminal : Claimant → Domain → Nat` is one number per cell, so this is the **aggregate** bound. The
running check it names is per-row:

`src/core/global_accounting_allocation_certificate_v1.py` (`_check_terminal_bindings`)

```python
entitled = any(
    entitlement.asset == row.asset
    and entitlement.claimant == row.claimant
    and entitlement.control_domain == row.control_domain
    and entitlement.amount_atoms >= row.amount_atoms
    for entitlement in fragment.claimant_entitlements
)
```

Each terminal row is compared against *some single* entitlement row. Nothing sums the rows. Mounted
counterexample — one entitlement of 3 and two OPEN terminal obligations of 2 each for
(alice, USD, spot-pool):

```
exactly-once: PASS
entitlement rows: PASS
>>> RUNTIME _check_terminal_bindings ACCEPTED: aggregate open terminal 2+2=4 > entitlement 3
```

The model's `TerminalBound` is violated by that state; the running check accepts it.

**Consequence.** `certificate_implies_terminalCovered` — documented as "R2 of the claimant-backing
guard" — is a property of the model, not of the running certificate checker. A reader of the file would
conclude that certificate acceptance implies R2. It does not.

**Severity capped to P2, not P1**, for two independent reasons:
1. *Unreachable in the current profile.* The whole-checker path rejects the vector before reaching the
   terminal check: `all lanes disabled → DISABLED_LANE_NOT_EMPTY`; `lane0 enabled →
   BLOCKED_LANE_PRODUCER_MISSING`. No lane is receipt-backed, so no certificate carrying rows is
   accepted today.
2. *The system does enforce an aggregate bound elsewhere.*
   `src/core/global_economic_state_effect_refinement_v1.py:414` folds open terminals by claimant
   (`_fold_backing_totals_v1`) and rejects `OPEN_TERMINAL_EXCEEDS_CLAIMANT_ENTITLEMENTS`. Note that
   guard folds on `(asset, claimant)` — **not** on control domain — so it is still weaker than the
   model's per-`(claimant, domain)` conclusion.

**Required repair.** Either (a) change the docstring to state that `TerminalBound` models the
`OPEN_TERMINAL_EXCEEDS_CLAIMANT_ENTITLEMENTS` fold of the backing guard rather than
`TERMINAL_BINDING_DRIFT`, and add to the module header that the model collapses multiple rows per
`(claimant, domain)` cell into one amount so its terminal bound is strictly stronger than the
certificate's per-row check; or (b) strengthen `_check_terminal_bindings` to fold terminal rows per
`(claimant, asset, control_domain)` before comparing. (b) is the smaller long-run obligation and is what
makes the Lean conclusion true of the code.

### P3-1 — headline of `noReceiptBacked_implies_zeroTables` is broader than its conclusion

`:184-191`. The docstring says the current profile "accepts only the registered-empty certificate"; the
conclusion only states that every table is zero. The stronger fact (`∀ l, FragmentEmpty (cert l) ∧
(cert l).enabled = false`) *is* derived inside the proof but is not exposed. Either expose it in the
statement or trim the headline to the colon clause.

Reproduce (all Scope A):
```
cd /tmp/zenodex-formal-core-review-p-ca20a72fc/lean-mathlib
lake env lean -DwarningAsError=true Proofs/GlobalAccountingAllocationCertificateV1.lean
cd .. && PYTHONPATH=$PWD .venv/bin/python -m pytest -q tests/formal/test_lean_global_accounting_allocation_certificate_v1.py
```

---

## 3. Scope B — C4c, the bounded ESSO model (S12)

### Grade: **B** — REVISE. The model is sound; the mutant-attribution *claim* is not supported.

`src/kernels/dex/global_accounting_allocation_certificate_v1.yaml` (2100 lines). Two lanes, one domain,
two claimants, ≤ 8 atoms per cell, 7 actions, 8 invariants.

**What holds.**
- `ir_hash` re-derived independently: `sha256:d4b31feeb6c9a618fa50e45391e9b1b8ffd88e2c5163a59a5317912b0bfb232b`, exact match. Source sha256 matches. `fingerprint` is correctly labelled `DETERMINISM_WITNESS_NOT_MODEL_BINDING` while `ir_hash` is `MODEL_BINDING_REPLAY_VERIFIED` — the right way round.
- **Observable surface binds every state var**: 28 state vars, `observables.state_vars` is the identical list in the identical order; 0 state vars unobservable, 0 phantom observables. The gate additionally proves the binding is load-bearing by truncating the observable list and showing `ir_hash` changes.
- 8 queries (`init_implies_inv` + 7 `inductive_*`) VERIFIED under z3 4.15.4 + cvc5 1.1.2, determinism 2 trials, solvers agreed, 0 inconclusive.
- Invariant expressions correspond to the Lean predicates one-for-one. `inv_producer_gate` is
  `(enabled ⇒ receipt_backed) ∧ (¬enabled ⇒ all-rows-zero)` per lane — exactly Lean's `ProducerGate`.
- **No vacuity from unreachable actions.** `inv_accept_requires_lane_binding` is `g_decision ≠ GENESIS ⇒ (g_lane_root_bound ∧ g_header_bound)`, and every one of the 7 actions moves `g_decision` off `GENESIS`, so the antecedent is reachable. Three mutants produce clean unique counterexamples, which is direct evidence the action space is live.
- **Model notes are true and unusually honest.** I verified each pinned phrase: "No lane producer is receipt-backed in the running code"; "enable_lane models the future receipt-backed producers, not a present capability"; and — importantly — "The Boolean parameters of every action are adversarial abstract premises established by an opaque verifier; a caller-provided true Boolean would not be authority." That last sentence pre-empts the obvious objection that `enable_lane`'s guard simply requires the caller to pass `receipt_backed = true`.
- Both runtime links genuinely exercise the running checker (`cert._check_entitlement_rows` →
  `ENTITLEMENT_ROWS_DRIFT`; full `check_…` → `BLOCKED_LANE_PRODUCER_MISSING` with
  `pre_state_root == post_state_root`, i.e. reject-is-no-op, plus a positive accept).

### P2-2 — "eight named mutants each attributed to one invariant" is false for 5 of 8 (MOUNTED)

Packet `completion_scope[10]` and the gate docstring both say each mutant is "attributed to one
invariant". The gate's attribution step only shows the named invariant is **sufficient** to catch the
mutant; it never shows it is the **only** one. I re-ran every mutant against all 8 single-invariant
projections (`--solvers z3,cvc5 --determinism-trials 2 --timeout-ms 10000`):

| mutant | attributed | invariants that FAIL | unique? |
|---|---|---|---|
| `enable_without_receipt` | `inv_producer_gate` | 1 | **yes** |
| `disable_with_rows` | `inv_producer_gate` | 1 | **yes** |
| `accept_without_lane_binding` | `inv_accept_requires_lane_binding` | 1 | **yes** |
| `unassigned_atom` | `inv_lane_partition_exact` | 2 | no (+`inv_lane_rows_equal_tables`) |
| `external_table_not_summed` | `inv_lane_rows_equal_tables` | 2 | no (+`inv_normative_partition`) |
| `reserve_masks_entitlement` | `inv_lane_rows_equal_tables` | **7** | no |
| `terminal_over_entitlement` | `inv_terminal_bound_by_entitlement` | **7** | no |
| `custody_double_count` | `inv_lane_aggregate_equals_custody` | **8** | no |

For the three worst cases the counterexample is **not an invariant violation at all** — it is a declared
type-range violation. `custody_double_count` projected onto `inv_producer_gate` returns a z3 model with

```
custody = 7, p_amount = 1, custody_post = 9      # custody : int min 0 max 8
enabled_l0 = True, receipt_backed_l0 = True, enabled_l0_post = True, receipt_backed_l0_post = True
enabled_l1 = False, (all l1 rows) = 0
```

Both pre- and post-state satisfy `inv_producer_gate`; the only thing wrong is `custody_post = 9 > 8`.
Same shape for `terminal_over_entitlement` projected onto `inv_producer_gate`: `term_bob_l1_post = 9`.
So for those mutants the gate's attribution assertion would pass for *any* of the eight invariants and
carries **no** information about which invariant catches which disaster.

**Required repair.** Either (a) have the attribution step assert that the returned counterexample model
actually falsifies the attributed invariant (evaluate the invariant expression on the `_post` valuation),
or (b) keep the mutants inside the declared ranges so a range violation cannot mask the semantic one, or
(c) weaken the packet sentence to "each mutant is caught by its attributed invariant" and drop the
uniqueness reading. (a) is the one that actually buys the evidence the sentence promises.

### P3-2 — two invariants have no mutant, by construction

`inv_normative_partition` and `inv_same_domain_backed` are the derived conclusions, and the meta notes
say so ("are proved as inductive consequences"). No mutant is attributed to either, so the harness gives
no evidence they are load-bearing *checks* — correct, since they are claims, not checks. Worth one
sentence in the packet so a reader does not expect 8 mutants ↔ 8 invariants.

### P3-3 — the same aggregate-vs-per-row gap as P2-1

`inv_terminal_bound_by_entitlement` is `term_alice_l0 <= ent_alice_l0` etc. — aggregate per cell, same
divergence from `_check_terminal_bindings` documented in P2-1. Same repair.

Reproduce:
```
cd /tmp/zenodex-formal-core-review-p-ca20a72fc
PYTHONPATH=/home/trevormoc/Downloads/ESSO /usr/bin/python3 -m ESSO validate \
  src/kernels/dex/global_accounting_allocation_certificate_v1.yaml
# then project the custody_double_count mutant onto each invariant and verify-multi each
```

---

## 4. Scope C — C4d, the repair of my P10 receipt (S13)

### Grade: **B−** — REVISE. Five of the seven repairs are solid; the two lexical-closure repairs do not close what they claim.

### What is correctly repaired

**P1-B2 — exact-byte pins. CLOSED, and closed hard.** `RUST_STATE_FILE_SHA256_V1`,
`RUST_GATE_SHA256_V1`, `BOUNDED_VEC_FILE_SHA256_V1` are compared with a hard
`_reject("RUST_STATE_FILE_DRIFT", …, "whole file differs from the pinned bytes")`
(`tools/o008_formal_cycle_admission_v1.py:2986`), not a soft drift note. The interaction with
`current_applicable` is sound: `current_applicable = packet_admitted and not current_source_drift`
(:3555), and `check_o008_formal_cycle_v1.py:58-62` **refuses replay** with
`REPLAY_REFUSED_WORKTREE_DRIFT` when it is false. A pin failure therefore cannot be papered over by a
green replay. All 38 `source_pins` recomputed clean.

**P2-A1 — duplicate `effect_id`. CLOSED, both languages, with tests.** Python now builds `pending`
with an explicit membership guard instead of a dict comprehension that silently kept the last row
(`_check_external_obligations`, `_fail(EXTERNAL_OBLIGATION_BINDING_DRIFT, f"duplicate {row.effect_id}")`).
Rust mirrors it in `pending_external_rows` (`global_accounting_allocation_certificate.rs:897`) and also
guards duplicate terminal `obligation_id` (:950). Python already had the terminal guard, so parity holds
on both. Tests: `tests/core/…_golden.py:148 test_duplicate_effect_id_across_lanes_is_rejected` asserting
detail `"duplicate 0x" + "ab"*32`, and `…certificate.rs:1242
duplicate_effect_id_across_lanes_is_rejected` — the latter replayed by `rust_certificate_unit_gate`
(2 passed, run #8 above).

**P2-A2 — check-major precedence. CLOSED.** `_check_lane_bindings` is now four sequential loops over the
same `pairs` tuple (state root → producer kind → blocked producer → disabled-lane rows), which is
literally the enum order `LANE_STATE_ROOT_DRIFT, PRODUCER_KIND_DRIFT, BLOCKED_LANE_PRODUCER_MISSING,
DISABLED_LANE_NOT_EMPTY`. The new vector
`rejects_later_lane_root_drift_before_earlier_lane_rows` exists in the renderer, the golden fixture and
the hygiene ledger, and expects `LANE_STATE_ROOT_DRIFT`. The reject-code docstring now states the
realised precedence *and* the `ALLOCATION_TOTAL_OVERFLOW` exception explicitly.

*Answering the brief's question directly:* **no, the realised precedence is not literally the enum
order, and the code says so.** `ALLOCATION_TOTAL_OVERFLOW` sits 7th in the enum but fires from whichever
checked fold overflows first — the exactly-once fold (realised 5th), the reserve fold (10th), or the
custody fold (13th). That is disclosed in the enum docstring. **P3-4:** `CHECK_ORDER_V1` still lists
`checked_u128_arithmetic_and_canonical_order` as the 11th check with no such caveat at that site; a
reader of the tuple alone would get the wrong precedence. Add the caveat to the tuple's neighbourhood.

**P2-A3 — `AllocationClassV1` removed. CLOSED.** Gone from the module body and from `__all__`, and
removed from `GLOBAL_SETTLEMENT_CANONICAL_ENUM_TYPES_V1`. Count verified by AST: **33** enum types, and
`tests/test_check_global_settlement_canonical_manifest_v1.py:32` pins `enum_type_count == 33`.

**P3-A4/A5 — `certificate_fixture_surface_v1` total. CLOSED.** Every nested access is type-checked
before use (`isinstance` on the fixture, `reject_messages`, `check_order`, `producer_registry` and its
values, `vectors`, each vector, each `expected_outcome`, `certificate`, `ordered_lane_fragments` and
each fragment), so a hostile fixture yields `CERTIFICATE_FIXTURE_DRIFT` rather than an untyped
exception. `CERTIFICATE_FIXTURE_ACCEPTED_V1 = 3` and every accepted vector is checked to be
registered-empty over disabled lanes.

### P1-1 — `_statement_binding_nodes` does not see "every module-level binding form" (MOUNTED, 8 bypasses)

`tools/o008_formal_cycle_admission_v1.py:1797-1815`. The function handles `FunctionDef`,
`AsyncFunctionDef`, `ClassDef`, `Global`, `Import`, `ImportFrom`, `Assign`, `AnnAssign`, `AugAssign`,
`For`, `AsyncFor`, `With`, `AsyncWith` — and returns `[]` for everything else, including a bare
`ast.Expr`. `python_dynamic_binding_scan_v1` then only iterates `module.body` for the hook names, so any
binding that is not one of those statement forms is invisible.

Baseline (correctly refused): `def __getattr__(n): …` and `__getattr__ = lambda n: …`.

Bypasses, all `MISSED`:

```
walrus expr __getattr__          (__getattr__ := (lambda n: 1))
walrus in call arg               print((__getattr__ := (lambda n: 1)))
global inside function + call    def _i():\n  global __getattr__\n  __getattr__ = …\n_i()
class body rebind                class _C:\n  def __getattr__(self, n): …
comprehension walrus             [y for _ in [0] if (__getattr__ := …)]
try/except binding               except ValueError as __getattr__:
match-case capture               match 1:\n  case __getattr__:
walrus __dir__                   (__dir__ := (lambda : []))
```

The first and third are not theoretical — both install a real PEP 562 module hook:

```
walrus  module __getattr__ installed: True -> SECRET = pwned
global  module __getattr__ installed: True -> SECRET = pwned
```

And the hardening the canonical-manifest dispatcher is *forced* to use does not help:

```
ModuleType.__getattribute__ honours module __getattr__: pwned
```

PEP 562 is implemented inside `module.__getattribute__`, so requiring
`ModuleType.__getattribute__` / `object.__getattribute__` / `type.__getattribute__`
(`tools/check_global_settlement_canonical_manifest_v1.py:276-279`) defends against a *class-level*
`__getattribute__` override but not against a module-level `__getattr__`.

**Why it matters here specifically.** The scan runs on the three pinned Python paths including
`CERTIFICATE_PYTHON_PATH_V1` (:2943). Its stated job is "reject dynamic name binding that an AST scan of
definitions cannot see through" — i.e. to make the AST-extracted facts (enum members, `CHECK_ORDER_V1`,
class shapes) equal the runtime facts. A module `__getattr__` can only *serve names the module dict
lacks*, so it cannot override an existing symbol — but that is exactly enough to undo **P2-A3**: a
walrus-bound hook can re-serve `AllocationClassV1` at runtime while every AST closure, and the
`enum_type_count == 33` assertion, still report it removed.

**Severity P1** because the repair's own claim ("every module-level binding form of
`__getattr__`/`__dir__`") is false with a one-line bypass, not because authority is escalated — every
authority in this packet is `NONE`. Mitigating: `check_global_settlement_canonical_manifest_v1.py`
already discloses the residual in its `nonclaims` ("Python process and loaded-module namespace integrity
remain trusted premises"); the admission core makes no such disclosure.

**Required repair.** Replace the statement-form allowlist with a walk that treats *any* `ast.Name` in a
`Store`/`Del` context anywhere in the module (plus `ast.Global`/`ast.Nonlocal` name lists and
`ast.ExceptHandler.name` and `ast.MatchAs.name`) as a binding of that name, i.e.
`for node in ast.walk(module): if _binds_name(node, hook)`. That is strictly simpler than the current
per-statement dispatch and closes all eight vectors at once.

### P2-3 — `lean_literal_closure_v1` is not a closure: `«…--…»` hides arbitrary commands (MOUNTED)

`tools/o008_formal_cycle_admission_v1.py:1588-1601` and
`tools/scan_lean_proof_placeholders_v1.py:70` (`strip_lean_noncode`).

The stripper treats `--` as opening a line comment unconditionally. Lean 4 does not: inside a `«…»`
identifier, `--` is an ordinary identifier character. So everything after `«a--»` on that line is
**invisible to every stripped-code closure while Lean elaborates it**:

```
src = "namespace A\ndef «a--» : Nat := 0 set_option debug.skipKernelTC true\ntheorem t1 : True := trivial\nend A\n"
  MISSED  lean_literal_closure_v1
  MISSED  lean_command_closure_v1
  definition surface seen by checker:
    namespace A def «a theorem t1 : True end A
$ lake env lean -DwarningAsError=true SetOptProbe.lean   →  EXIT=0
```

The escalation works: a hidden `macro_rules` redefines a token used in a pinned statement, so the
statement *text* is unchanged while its *meaning* is not.

```lean
namespace A
def «a--» : Nat := 0 macro_rules | `($x ≤ $y) => `($x = $x ∨ $y = $y)
theorem certificate_implies_sameDomainBacked : (3 : Nat) ≤ 2 := Or.inl rfl
end A
```
```
$ lake env lean -DwarningAsError=true MacroProbe2.lean   →  EXIT=0
```

The packet sentence `lean_evidence.statement_binding` — "the file contains no string or char literal
(no double quote) and **no # command** and **may use no notation, macro, syntax, instance, attribute,
scope, or open command**" — is therefore false as a *closure claim*. Both halves are evadable by the
same one-token trick.

**Why this is P2 and not P1.** The binding does not actually rest on the lexical closures. To be a
command the carrier must sit at column 0, and a column-0 carrier changes
`lean_definition_surface_v1`'s output, hence `definition_surface_sha256`
(`db6e720f8cca8d62525889c6e529e383a1e2f42297c982b422728d70e0e6594d`) — which I confirmed is embedded in
`tools/o008_formal_cycle_admission_v1.py`, not merely in the packet. So exploitation additionally
requires an admission-core edit that a reviewer sees. I checked the obvious way around that, putting the
carrier inside an elided proof region where the surface is deliberately blind:

```
clean and attack files produced IDENTICAL surface and IDENTICAL statement hashes:
  surface: namespace A theorem t1 : True theorem t2 : True end A
  stmt hashes: ['6dd041b911d4', '6dd041b911d4']
```

— but Lean rejects it (`error: unknown tactic`, EXIT=1), because a command is not a tactic. **The
current artifact is clean**: the pinned Lean file contains zero `«` and its only `--` occurrences are
inside `/-- … -/` doc comments.

**Required repair.** Make `strip_lean_noncode` skip `«…»` spans (they are lexically closed and cannot
contain a comment), or — simpler and fail-closed — add `«` to the forbidden raw-byte set alongside `"`
in `lean_literal_closure_v1`, since no pinned proof file needs French-quoted identifiers. Until then,
weaken the packet's `statement_binding` sentence to say the binding rests on
`definition_surface_sha256`, with the lexical closures as defence in depth.

### P3-5 — the `#` regex under-approximates Lean whitespace (defence in depth only)

`lean_literal_closure_v1` searches `^[ \t]*#`. Every other character Lean accepts before a command
evades it:

```
  refused plain #exit at col0 / indented #exit
  MISSED  CR then #exit, FF then #exit, VT then #exit, U+2028 then #exit, CR-only line then #exit
```

All five are nevertheless caught by Lean itself under the direct check:
`\r` → `error: isolated carriage returns are not allowed`; FF/VT/U+2028 → `error: expected token`; all
EXIT=1. `#exit` also always emits at least a warning, which `-DwarningAsError=true` promotes. So this is
sound today but only because of an undocumented premise about Lean's lexer. Either widen the character
class or record the premise explicitly.

### Re-mount of the original P10 vehicles

I reconstructed my P10 vehicles from the receipt (my `/tmp/opus-p10-*` copies were gone) and re-ran them
against the P13 checker with full attacker re-pinning. **P1-B1's stated attack (a `"` inside a char
literal or line comment opening a phantom string) is genuinely dead**: with zero `"` in the raw bytes the
stripper's `in_string` state is unreachable, and the check runs on raw bytes before any stripping and
first in `_project_lean_subject` (:2695). **P1-B2 is dead** (hard reject, see above). **P2-A1, P2-A2,
P2-A3, P3-A4, P3-A5 are dead.** **P2-B3 is not dead** (P1-1). The P1-B1 *class* — a lexical
disagreement between the stripper and Lean — is not dead; it moved from `"` to `«` (P2-3).

---

## 5. Grades

| Candidate | Scope | Grade | Verdict |
|---|---|---|---|
| **C4b** (S11 `6e5f4be57`) | bounded Lean model | **A−** | ACCEPT — fix P2-1 before the model underwrites a receipt-backed lane |
| **C4c** (S12 `00269d602`) | bounded ESSO model | **B** | REVISE — P2-2 attribution claim |
| **C4d** (S13 `11f879fdb`) | P10 receipt repair | **B−** | REVISE — P1-1, P2-3 |
| **P13** (`ca20a72fc`) | packet re-freeze | — | Faithful. Reproduces byte-identically (`drift: []`); all 38 pins clean; every gate green |

## 6. Findings index

| ID | Sev | Where | One line |
|---|---|---|---|
| P1-1 | P1 | `o008_formal_cycle_admission_v1.py:1797` | `_statement_binding_nodes` misses 8 module-level binding forms incl. walrus and function-`global`; both install a real module `__getattr__` |
| P2-1 | P2 | `GlobalAccountingAllocationCertificateV1.lean:91` | `TerminalBound` is aggregate; `_check_terminal_bindings` is per-row — runtime accepts 2+2 > 3 |
| P2-2 | P2 | `test_esso_…_certificate_v1.py` + packet `completion_scope[10]` | 5 of 8 mutants break 2–8 invariants; 3 fail on type-range, not the attributed invariant |
| P2-3 | P2 | `scan_lean_proof_placeholders_v1.py:70`, `admission:1588` | `«a--»` hides `set_option`/`macro_rules` from every closure; hidden `macro_rules` makes `(3:Nat) ≤ 2` compile EXIT=0 |
| P3-1 | P3 | `…Certificate V1.lean:184` | `noReceiptBacked_implies_zeroTables` headline broader than conclusion |
| P3-2 | P3 | packet `esso_evidence.certificate_model` | 2 of 8 invariants have no mutant (they are conclusions) — say so |
| P3-3 | P3 | ESSO `inv_terminal_bound_by_entitlement` | same aggregate/per-row gap as P2-1 |
| P3-4 | P3 | `global_accounting_allocation_certificate_v1.py:754` | `CHECK_ORDER_V1` lists u128 arithmetic 11th without the overflow caveat |
| P3-5 | P3 | `admission:1600` | `^[ \t]*#` misses CR/FF/VT/U+2028; Lean catches all of them — undocumented premise |

## 7. Nonclaims

- I did not review the RISC0 guest, Tau, mounting, the ZenoLedger admission path, or anything outside the three named scopes.
- I did not attempt to construct a kernel-level unsoundness through `debug.skipKernelTC`; I established only that the option can be set invisibly to the closures.
- I did not exercise P1-1 end-to-end through a rebuilt packet; I established the bypass, the semantics of the installed hook, and that `ModuleType.__getattribute__` honours it.
- The three ESSO mutant range-violation findings are from z3's returned model; I did not re-derive them with cvc5 independently (both solvers agreed on sat in every run).
- Grades are per-candidate engineering judgement under the repository's own Lean quality gates. I grant no authority and this review does not close O-008.

## 8. Residual risks

1. **The Lean/ESSO models are both stronger than the code on the terminal bound.** Today this is
   unreachable (no receipt-backed producer). It becomes live with the first receipt-backed lane, which is
   precisely when these models will be cited. Fix before, not after.
2. **Statement binding rests on one hash, not on the closures.** `definition_surface_sha256` is doing all
   the work; the lexical closures around it are bypassable (P2-3). That is a thinner margin than the
   packet describes.
3. **The AST/runtime equality premise is open** (P1-1). Every AST-derived fact in the admission core —
   enum sets, `CHECK_ORDER_V1`, class shapes — is only as good as the guarantee that the imported module
   has no hidden `__getattr__`.
4. The mutant harness (P2-2) currently over-reports attribution strength; anyone reading the packet would
   over-trust the model's per-invariant necessity evidence.
