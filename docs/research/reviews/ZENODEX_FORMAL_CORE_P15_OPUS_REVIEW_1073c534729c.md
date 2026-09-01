# Opus independent review of record — C5 (S14/P14) and C6 (S15/P15)

ZenoDEX formal functional core closure campaign, branch `codex/formal-core-fable-20260901`.
Reviewed in the clean detached worktree `/tmp/zenodex-formal-core-review-p-1073c5347` (HEAD
`1073c534729c1d6574cba837c8922d15b83f3632`, `git status --porcelain` empty at start and at end).
No file in the worktree was edited. All mutation experiments were done on in-memory copies or on
copies written under the scratchpad.

**Grades: C5 = B+, C6 = C+.**
**Findings: 2 x P1, 2 x P2, 3 x P3.**

---

## 1. Envelope verification (duty 1) — PASS

| Check | C5 | C6 |
|---|---|---|
| `git rev-list --count S..P` | 1 | 1 |
| P is a single-parent child of S | `ab182bd78^` = `7551c52a2` | `1073c5347^` = `c55e51d4b` |
| P touches only the two packet files | `M docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.{json,md}` | same |
| packet `subject_commit` == S | — | `c55e51d4b7f71611942451b6fb96d3fc6e2334fb` = S15 |
| packet schema | v10 | `zenodex/o008-formal-cycle-evidence/v11` |

Chain: `ca20a72fc` (P13 receipt) -> `7551c52a2` (S14) -> `ab182bd78` (P14) -> `22c368026` (P13
review receipt) -> `c55e51d4b` (S15) -> `1073c5347` (P15).

**Admission checker at HEAD** (`tools/check_o008_formal_cycle_v1.py --root .`): `rc=0`,
`ok=true`, `packet_admitted=true`, `errors=[]`, `head_commit == packet_commit == 1073c5347`,
`subject_commit == c55e51d4b`, `proof_replay.status = NOT_RUN`, stderr empty.

**Projection round-trip under full replay.** `tools/build_o008_formal_cycle_v1.py --check --replay`
with the project venv, `/usr/bin/python3` as the ESSO interpreter and
`PYTHONPATH=/home/trevormoc/Downloads/ESSO`:

```
{"drift":[],"mode":"check","ok":true,"subject_commit":"c55e51d4b7f71611942451b6fb96d3fc6e2334fb"}
```

stderr empty; worktree still clean afterwards (the replay sandboxes `CARGO_TARGET_DIR`, `CARGO_HOME`,
`HOME` and `TMPDIR`). All 28 recorded proof commands executed and the rebuilt projection — including
the `EXECUTED` author record — is byte-identical to the committed packet. This is the strongest form
of duty 1 and it passes.

Independently re-run gates (outside the builder), both matching the packet's expectations exactly:

* `tests/formal/test_esso_global_accounting_allocation_certificate_v1.py` — **24 passed** in 41.8 s
  (packet: `esso_certificate_gate` expects 24).
* `tests/formal/test_esso_global_claimant_custody_certificate_v1.py` — **20 passed** in 20.0 s
  (packet: `esso_gate` expects 20).
* `lake env lean -DwarningAsError=true Proofs/GlobalClaimantCustodyRelationV1.lean` — rc 0,
  0 bytes stdout, 0 bytes stderr (packet: `lean_direct_check`).

---

## 2. P1 findings

### P1-1 — A mid-line `#` command in an elided proof region defeats the whole Lean closure stack and executes arbitrary IO during replay

**Location.** `tools/o008_formal_cycle_admission_v1.py:1648`

```python
hash_command = re.search(r"^\s*#", _lean_code(text, path), re.MULTILINE)
```

**What C6 changed.** P13 P3-5 asked for any Unicode whitespace to be allowed before `#`; C6 widened
`^[ \t]*#` to `^\s*#`. That half is genuinely closed (`\f#eval`, `  #exit` are both
rejected — pinned by new cases at `tests/test_check_o008_formal_cycle_v1.py:371-372`). What C6 did
not change is the **line anchoring**: `^` in `re.MULTILINE` only matches at the string start and
after `\n`, so the rule only sees a `#` command whose line contains nothing but whitespace before it.
Lean accepts a command anywhere a command may begin, including after a term on the same line.

**Why nothing else catches it.** Put the command on an **indented** line inside a theorem's elided
proof region, after the proof text:

* `lean_definition_surface_v1` (`:1668`) elides from the statement end to the next column-zero line,
  so the payload is not in the definition-surface hash — the very hash the C6 claim sentence now
  names as "carrying the binding".
* `_LEAN_INDENTED_DECL_RE` (`:1045`) lists `@\[|def|theorem|lemma|structure|inductive|namespace|end|import`
  and does not include `#`.
* `lean_command_closure_v1` (`:1655`) matches whole words against `_LEAN_FORBIDDEN_WORDS_V1`; `#eval`
  contributes only the bare word `eval`, which is not in the set.
* No `"` and no `«`/`»` are needed, so `LEAN_DOUBLE_QUOTE_FORBIDDEN` and the new
  `LEAN_GUILLEMET_FORBIDDEN` (`:1644`) never fire.

**Concrete exploit, on the real pinned file.** Injecting into
`lean-mathlib/Proofs/GlobalClaimantCustodyRelationV1.lean` after the elided proof line `  Iff.rfl`
of `necessaryRelation_independent_of_reserves`:

```lean
  Iff.rfl #eval (IO.FS.writeFile (String.ofList ['<path>']) (String.ofList ['o','k']) : IO Unit)
```

(no double quote, no guillemet — the path and payload are built with `String.ofList` over char
literals, which the closure permits; `String.mk` would emit a deprecation warning, `String.ofList`
is silent).

Every static admission check passes on the mutated bytes:

```
literal_closure    PASS
command_closure    PASS
namespace_check    PASS
placeholder_scan   PASS
theorem_inventory  PASS
surface hash       UNCHANGED (== LEAN_DEFINITION_SURFACE_SHA256_V1)
statement hashes   25 theorems, drift=[]
```

And the real replay gate passes:

```
$ cd lean-mathlib && lake env lean -DwarningAsError=true <mutated file>
MUTATED rc=0  stdout=0B  stderr=0B
$ cat LEAN_GATE_PWNED.txt
ok
```

`rc=0` with empty stdout and stderr is *exactly* `lean_direct_check`'s recorded expectation
("exit 0; empty stdout and stderr"). The baseline pristine file gives the identical observable
(`rc=0, 0B, 0B`), so the gate cannot distinguish them.

Reproduced on the **second** pinned Lean file
`lean-mathlib/Proofs/GlobalAccountingAllocationCertificateV1.lean` (payload appended to the elided
line `    exact nomatch this` at line 185): literal/command/placeholder/inventory all PASS, surface
hash UNCHANGED, all statement hashes match. The gap is systemic across the Lean closure stack, not
specific to one file.

**Escalation — this forges every later gate.** `lean_direct_check` is replay command **#2 of 28**.
The worktree is verified equal to S exactly once, *before* replay, and never re-verified after:

* builder: `tools/build_o008_formal_cycle_v1.py:63` `_require_worktree_equals_subject(...)` then
  `:74` `observations = shell.run_proof_replay_v1(root, environment)`.
* checker: `tools/check_o008_formal_cycle_v1.py:96` `read_current_source_state_v1(...)` then `:99`
  `replay, extra = (_replay(...) if args.replay else ...)`.

So arbitrary IO executed by command #2 can rewrite any source, test, or fixture the remaining 26
commands replay, and neither the builder nor the admission checker re-reads the worktree afterwards.
A packet whose entire value is that its pins bind can therefore record 28 green gates that ran
against bytes the pins do not describe.

**Claims falsified.** `lean_evidence.statement_binding` in the packet (constant
`LEAN_STATEMENT_BINDING_V1`, `tools/o008_formal_cycle_admission_v1.py:600-607`) states the file
"contains no double quote or guillemet, **no # command**, and no notation, macro, syntax, instance,
attribute, scope, or open command; each elided region is indented proof text with no declaration, so
only how a theorem is proved is left to replay". Both the "no # command" clause and the "only how a
theorem is proved is left to replay" clause are false: an elided region may also contain a command
that runs arbitrary IO.

**Note on `#exit`.** The truncation variant (`  Iff.rfl #exit`) is equally invisible to every static
check but *is* caught, incidentally, by `-DwarningAsError=true` (Lean emits "using 'exit' to
interrupt Lean" as a warning; rc becomes 1). `#eval` has no such warning and is the live vehicle.

**Fix direction.** Ban `#` on the stripped code without line anchoring (`re.search(r"#", code)`),
or add `#` to `_LEAN_INDENTED_DECL_RE` and reject any command token inside an elided region; and
add a post-replay worktree re-verification in both the builder and the checker.

---

### P1-2 — A module hook bound by a `def`/`class` nested in any module-level compound statement is not caught

**Location.** `tools/o008_formal_cycle_admission_v1.py:1876-1882` (`python_dynamic_binding_scan_v1`)
and `:1845-1861` (`_binds_hook_name`).

```python
for node in ast.walk(module):                       # :1876  — covers Name/alias/Global/Nonlocal/ExceptHandler/Match*
    for hook in _PYTHON_MODULE_HOOKS_V1:
        if _binds_hook_name(node, hook): _reject(...)
for statement in module.body:                       # :1880  — def/class arm, TOP LEVEL ONLY
    if isinstance(statement, ast.FunctionDef | ast.AsyncFunctionDef | ast.ClassDef) and statement.name in _PYTHON_MODULE_HOOKS_V1:
        _reject(...)
```

`_binds_hook_name` returns `False` for `FunctionDef`, `AsyncFunctionDef` and `ClassDef` (by design —
the comment says class-body methods stay allowed), and the compensating def/class arm iterates only
`module.body`. A `def __getattr__` inside an `if`/`try`/`for`/`while`/`with`/`match` at module level
executes in module scope and installs a working module hook, and is seen by neither loop.

**Surviving vehicles** (all confirmed to pass `python_dynamic_binding_scan_v1`; the five vehicles
C6 pinned are all correctly rejected):

```
F_def_inside_if          PASSES     J_class_inside_if        PASSES
G_def_inside_try         PASSES     K_async_def_inside_if    PASSES
H_def_inside_for         PASSES     L_def_inside_while       PASSES
I_def_inside_with        PASSES     M_def_inside_match       PASSES
O_dir_def_inside_if      PASSES     P_decorated_def_in_if    PASSES
N_star_import            PASSES
```

**Confirmed on a real pinned surface.** Appending
`\n\nif True:\n    def __getattr__(name: str) -> object:\n        return int\n` to
`src/core/global_accounting_allocation_certificate_v1.py` (= `CERTIFICATE_PYTHON_PATH_V1`) passes the
scan, while the top-level form C6 pinned is rejected:

```
pristine                                          : PASS
+ nested `def __getattr__` inside `if True:`      : PASS   <== BYPASS
+ top-level `def __getattr__` (the pinned vehicle): REJECT PYTHON_DYNAMIC_BINDING_FORBIDDEN
```

**Runtime effect** (the property the scan exists to guarantee — "an AST scan of definitions can see
through this module"):

```
statically-visible CHECK_ORDER_V1 : ('a', 'b')
dynamically fabricated name       : ('EXFIL_REJECT_CODES_V1',)
from-import of an undefined name  : ('EXFIL_ANY_NAME_AT_ALL',)
AST-visible module bindings       : ['CHECK_ORDER_V1']
```

Any name a consumer imports from a pinned module can be supplied by code the AST scan never sees.

**Second vehicle:** `from m import *` where `m` sets `__all__ = ["__getattr__"]` also passes
(`ImportFrom` is only checked against `_PYTHON_FORBIDDEN_MODULES_V1`); demonstrated fabricating
`victim2.NOT_DEFINED_ANYWHERE`.

**This is a re-break of the finding C6 was chartered to close.** C6's own new test
`module_dir_nested_import_alias` (`tests/test_check_o008_formal_cycle_v1.py:798`) is
`if True:\n    import os as __dir__` — so nesting *was* contemplated, but only for the alias/Name
forms that `ast.walk` already covers. The def/class arm was left at `module.body`.

**Fix direction.** Walk for def/class too, and exclude only definitions whose immediate parent is a
`ClassDef` body (a parent map, or a recursive descent that skips class bodies), rather than keying on
`module.body` membership. Also decide explicitly about `from x import *`.

---

## 3. P2 findings

### P2-1 — `binding_root` is unconstrained: the checker accepts registered-empty fragments outside the producers' image (C5)

**Locations.** `src/core/global_accounting_allocation_certificate_v1.py:360` (field), `:375`
(shape-only `_require_root(..., allow_zero=True)`), `:864` (the producer path sets
`binding_root=lane_root.state_root`); no comparison of `fragment.binding_root` against anything
exists anywhere in `check_global_accounting_allocation_certificate_v1`
(`grep -n binding_root` returns only the field, its shape check, `to_canonical`, the constructor,
and the unrelated certificate-level `terminal_binding_root`).

**Duty-3 answer, precisely.** Through `produce_registered_empty_fragment_v1` a caller *cannot* obtain
a registered-empty fragment at a root other than the pinned empty state root: the precedence is
`LANE_NOT_REGISTERED_EMPTY -> LANE_ENABLED -> REGISTERED_EMPTY_ROOT_DRIFT`, the last comparing
`lane_root.state_root != empty_root`, and the emitted fragment sets both `lane_state_root` and
`binding_root` to that verified root. The taxonomy is closed (3 codes), total over
`LaneStateRootV1` (a non-`LaneStateRootV1` input raises `TypeError` at the type boundary), and
reject-is-no-op by construction (pure function over an immutable input; the rejection echoes the
committed root unchanged). The two pinned roots are the real empty typed states
(`ExternalCustodyDisabledStateV1().state_root`, `ProofRewardsPolicyBlockedStateV1().state_root`) and
`REGISTERED_EMPTY_PRODUCER_LANES_V1` resolves to exactly `['PROOF_REWARDS', 'EXTERNAL_CUSTODY']`,
matching packet claim [12].

**But the checker does not require fragments to be producer outputs.** Counterexample, on the
accepted registered-empty certificate over the all-lanes-disabled state:

```
baseline registered-empty certificate: AllocationCertificateAcceptedV1
(a) forged lane_state_root  -> AllocationCertificateRejectedV1 LANE_STATE_ROOT_DRIFT  EXTERNAL_CUSTODY
(b) forged binding_root     -> AllocationCertificateAcceptedV1        <== accepted
    fragment.binding_root = 0xdededededededededededededededededededededededededededededededede
(c) zero binding_root       -> AllocationCertificateAcceptedV1        <== accepted
```

(derived roots recomputed via the renderer's `_certificate_with_fragments`, so the certificate is
self-consistent). The field named for binding binds nothing; the producer is not the unique source of
accepted registered-empty fragments.

**Scope honesty.** No packet sentence is falsified by this. `required_checks` does not list a
binding-root check, the bounded Lean `LaneFragment` has no `binding_root` field, and
`implementation.registered_empty_producers.binding` speaks only of the *committed lane root*, which
is enforced. It is scored P2 because it is an unvalidated root-shaped field on the single new
authority-shaped surface C5 introduces, and it is exactly the field that would carry the receipt
binding once a receipt-backed producer exists.

**Confirmed non-issue nearby (checked, sound).** `_check_terminal_totals` builds `entitled` with a
dict comprehension (`:759-761`) that would silently keep only the last row on a duplicate
`(asset, claimant, control_domain)` key, while `claimed` uses the summing `_fold`. This is safe
because `_ordered_rows` (`:341`) enforces `keys == tuple(sorted(set(keys)))` on
`claimant_entitlements`, so duplicate keys are unrepresentable. Rust's `.collect()` into a
`BTreeMap` has the same last-wins shape and the same guarantee.

### P2-2 — Python/Rust reject-detail divergence on `ALLOCATION_TOTAL_OVERFLOW`, including at the fold C6 just added

**Locations.** Python `_fold` has a default label `"fold"`
(`src/core/global_accounting_allocation_certificate_v1.py:646`) and four of five call sites take it:
`:660` (controlled), `:682` (reserves), `:756` (terminal totals — **new in C6**), `:768` (custody);
only `:661` passes `f"{lane} assignments"`. Rust labels every site distinctly:
`zk/global_settlement_abi_v1/src/global_accounting_allocation_certificate.rs:801`
(`"{lane} controlled"`), `:896` (`"reserves"`), `:1064` (`"terminal totals"`), `:1115` (`"custody"`).

**Counterexample.** Two terminal rows of `u128::MAX` for the same `(USD, alice, spot-pool)` against a
matching entitlement:

```
PYTHON  code   = ALLOCATION_TOTAL_OVERFLOW
PYTHON  detail = 'fold'
RUST    detail = 'terminal totals'   (src line 1064)
```

and at the pre-existing controlled-locations site:

```
PYTHON code=ALLOCATION_TOTAL_OVERFLOW detail='fold'   RUST label='{lane} controlled'
```

**Why the fixture does not catch it.** The shared golden test asserts detail parity per vector
(`tests/core/test_global_accounting_allocation_certificate_v1_golden.py:87`,
`assert outcome.detail == vector["expected_outcome"]["detail"]`), but **0 of the 27 recorded vectors
produce `ALLOCATION_TOTAL_OVERFLOW`** — the code has a registered entry in `reject_messages` and no
vector. So the one cross-language binding that would detect this never exercises the path.

**Why it is C6's.** Three of the four divergent sites pre-date C6; the terminal-totals site is new in
C6, and C6 simultaneously added the CHECK_ORDER_V1 caveat
(`src/core/global_accounting_allocation_certificate_v1.py:789-790`, the P3-4 repair) which
*documents* overflow as firing "inside the first checked fold that overflows (positions 5, 7, 9, 10)".
I verified those positions are exactly right — but the repair drew the claim tighter around a
behaviour whose detail is not language-parity-bound and has no vector.

**Fix direction.** Give the Python `_fold` call sites the same labels as Rust (and drop the default),
and add four `ALLOCATION_TOTAL_OVERFLOW` vectors to the shared fixture, one per fold.

---

## 4. P3 findings

### P3-1 — Packet claim [9] undercounts the golden vectors and nothing binds the number

`tools/o008_formal_cycle_admission_v1.py:274` — "both replay one rendered golden vector of
**twenty-five** state/certificate pairs". The fixture holds **27**
(`tests/data/global_accounting_allocation_certificate_v1_golden.json`, `len(vectors) == 27`).
History: 26 at C4d `ca20a72fc`, 27 at C5 `7551c52a2` and C6 `c55e51d4b`, with the sentence unchanged
throughout. No check binds the count (the string appears once, in prose). It is an undercount, so it
does not overstate coverage, but it is a factually wrong unbound number in a claim sentence.

### P3-2 — Rust producer swallows a real error and remaps it to a different reject code

`zk/global_settlement_abi_v1/src/global_accounting_lane_producers.rs:74-78`

```rust
let empty_root = registered_empty_lane_root_v1(lane_root.lane_id)
    .ok()
    .flatten();
```

An `Err` from `state_root()` is discarded and becomes `None`, which then reports
`LANE_NOT_REGISTERED_EMPTY` for a lane that *is* registered empty. Python has no analogous path (the
roots are module constants computed at import, so a failure is an import-time error, not a reject).
Fail-closed in outcome — it still rejects — but it is a swallowed error on a CBC path and a latent
Python/Rust reject-code divergence. The certificate checker's own use of the same helper
(`global_accounting_allocation_certificate.rs:748-753`) does map the error to a distinct
`RegisteredEmptyRootDrift` with a "empty lane state root unavailable" detail, which Python also
cannot produce.

### P3-3 — The new pre-state check in the ESSO counterexample evaluator is fail-open on omitted variables

`tests/formal/test_esso_global_accounting_allocation_certificate_v1.py`,
`_assert_counterexample_falsifies`: the post-state assertion is correctly fail-closed
(`assert _evaluate(...) is False`, so a missing variable yields `None` and the test fails), but the
pre-state assertion is `assert _evaluate(...) is not False`, which `None` satisfies. A solver model
that omits a variable would silently make the "counterexample does not start from an
invariant-violating state" check vacuous for that invariant. Measured on the live runs this is not
currently exercised (see §5), so it is a hardening remark, not a live defect.

---

## 5. What C6 does close — verified, not taken on trust

**P2-2 (in-domain ESSO mutants + three-valued counterexample evaluation) — closed, and it is
substantive.** I re-ran all eight mutants under z3 and cvc5 and evaluated every invariant on both
solvers' models myself:

```
state_vars declared: 28; invariants: 8
reserve_masks_entitlement    inv_lane_rows_equal_tables        | z3:vars=61 post=False pre T/N/F=8/0/0 | cvc5:vars=61 post=False pre T/N/F=8/0/0
unassigned_atom              inv_lane_partition_exact          | z3:vars=60 post=False pre T/N/F=8/0/0 | cvc5:vars=60 post=False pre T/N/F=8/0/0
enable_without_receipt       inv_producer_gate                 | z3:vars=60 post=False pre T/N/F=8/0/0 | cvc5:vars=60 post=False pre T/N/F=8/0/0
terminal_over_entitlement    inv_terminal_bound_by_entitlement | z3:vars=61 post=False pre T/N/F=8/0/0 | cvc5:vars=61 post=False pre T/N/F=8/0/0
custody_double_count         inv_lane_aggregate_equals_custody | z3:vars=61 post=False pre T/N/F=8/0/0 | cvc5:vars=61 post=False pre T/N/F=8/0/0
disable_with_rows            inv_producer_gate                 | z3:vars=59 post=False pre T/N/F=8/0/0 | cvc5:vars=59 post=False pre T/N/F=8/0/0
external_table_not_summed    inv_lane_rows_equal_tables        | z3:vars=60 post=False pre T/N/F=8/0/0 | cvc5:vars=60 post=False pre T/N/F=8/0/0
accept_without_lane_binding  inv_accept_requires_lane_binding  | z3:vars=61 post=False pre T/N/F=8/0/0 | cvc5:vars=61 post=False pre T/N/F=8/0/0

TOTALS: {'post_False': 16, 'post_None': 0, 'pre_None': 0, 'pre_True': 128, 'pre_False': 0}
```

Every one of the 16 (8 mutants x 2 solvers) attributed invariants is **definitely false** on its post
state — no reliance on the three-valued `None` escape. All 128 pre-state evaluations are **definitely
true** — no spurious counterexample starts from an invariant-violating state, and P3-3's fail-open
branch is never taken. The three-valued evaluator itself is sound in the "definitely False"
direction (`and` returns `False` only on a definitely-false conjunct, `or` only when all args are
definitely false, `=>`/`not`/`ite` propagate `None` correctly, and the arithmetic and comparison
operators short-circuit to `None` on any `None` argument before evaluating); an unsupported operator
raises `AssertionError`, and a parse miss makes the post assertion fail. The hardcoded `_in_domain`
bound of `8` is correct: all 21 int state vars in the model declare `min=0, max=8` (the other 7 are
bool/enum), and the evaluator independently re-checks `declared["min"] <= value <= declared["max"]`.
The attribution run reduces the model to the single attributed invariant, and
`test_derived_invariants_carry_no_mutant` pins that `inv_normative_partition` and
`inv_same_domain_backed` carry no mutant. **No mutant fails duty 2's test.**

**P2-1 / P3-3 (aggregate terminal fold) — closed.** Differential over 584 configurations (2 claimants
x entitlements in {0,1,2,3} x {0,2} x 0/1/2 terminal rows with amounts in {0,1,2,3}), comparing
`_check_terminal_bindings` (which now calls `_check_terminal_totals`) against the bounded cell model
`forall c: sum(terminal rows for c) <= entitlement[c]`:

```
configs: 584
checker ACCEPT & model REJECT (UNSOUND): 0
checker REJECT & model ACCEPT (stricter): TERMINAL_BINDING_DRIFT only
```

**Zero terminal-row multisets that the aggregate fold accepts while the bounded model rejects.** The
"stricter" direction is not a fold divergence: it is the separate obligation-id-set check against the
state's open terminals (the golden vector `rejects_open_terminal_without_binding_row`,
detail `obligation_id set`), which my harness's registered-empty base state necessarily triggers.
The Lean `TerminalBound` docstring is now accurate and explicitly discloses that the model keeps one
amount per cell while the runtime folds rows.

**P2-3 (guillemet ban) — closed.** `«` and `»` are banned on raw bytes at `:1644`, before any
stripping, so the `«a--»` identifier-that-opens-a-comment vehicle is dead. `«»` is Lean 4's only
identifier-quoting syntax, so the ban is complete for that vehicle. Pinned by two new cases and one
certificate-file case.

**P3-1 (zeroTables docstring) — closed.** The new docstring enumerates exactly the five equalities
the theorem concludes (custody, reserves, external, every liability, every open terminal) and
correctly attributes the disabled-flag half to `noReceiptBacked_forces_allDisabled` rather than
claiming it.

**P3-4 (CHECK_ORDER_V1 overflow caveat) — closed and accurate.** I verified the five Python fold call
sites map to check-order positions 5 (`_check_exactly_once`, two folds), 7 (`_check_reserve_rows`),
9 (`_check_terminal_bindings`), 10 (`_check_lane_aggregates`) — exactly the "positions 5, 7, 9, 10"
the comment states.

**C5's root-binding pass is load-bearing.** `rejects_registered_empty_lane_with_foreign_root` is a
recorded vector producing `REGISTERED_EMPTY_ROOT_DRIFT` / detail `PROOF_REWARDS`, and the fixture
declares the mutation killers "accept a registered-empty lane at a foreign root" and "accept the
registered-empty certificate over a non-empty state". The new check is not shadowed by the earlier
`LANE_STATE_ROOT_DRIFT` comparison: that one compares the fragment against `state.lane_roots`, while
the new one compares against the pinned constant, so it adds value precisely when the *state* claims
a registered-empty lane at a foreign root.

---

## 6. Nonclaims and authority ceiling (duty 5)

**Intact.** `claim_ceiling`: `migration_authority`, `production_authority`, `publication_authority`,
`release_authority`, `settlement_authority`, `value_movement_authority`, `verifier_authority` all
`NONE`; `formal_core_complete = false`; `whole_value_movement_safe = false`;
`o008_status = OPEN_EXACT_ALL_12_RECONCILIATION_MISSING`;
`value_movement_gates_closed = 0` of `12`;
`supported_claim = O008_RELATION_NECESSARY_CHECKS_AND_INFORMATION_LOSS_PROVED`. The 11 nonclaims
correctly disclaim O-008 completion, refinement to any running execution, cryptographic binding,
mounting, the fingerprint-vs-ir_hash distinction, the unpinned Rust modules, the author record being
an observation only, and all authority.

**Overclaiming sentences found:**

1. `lean_evidence.statement_binding` — "the file contains no double quote or guillemet, **no # command**"
   and "each elided region is indented proof text with no declaration, so only how a theorem is proved
   is left to replay". Both false; see P1-1. The C6 rewrite that added "(the definition-surface hash
   carries the binding; the lexical closures are defence in depth)" is an honest improvement in
   framing, but it does not rescue this sentence, because the surface hash is blind to exactly the
   region the payload occupies.
2. `completion_scope[9]` — "twenty-five state/certificate pairs" vs 27. See P3-1.
3. Not an overclaim, but worth stating: `completion_scope[12]`'s "the certificate checker rejects a
   registered-empty lane committed at any other root" is true of `lane_state_root` and silent about
   `binding_root`; see P2-1.

Everything else I sampled in `completion_scope` and `required_sidecar` is supported by what I
executed, and `esso_evidence` / `lean_evidence` gate counts (24, 20, 6, 6) and the recorded solver
versions match the fresh runs.

---

## 7. Grades

### C5 (S14 `7551c52a2`, P14 `ab182bd78`) — **B+**

Envelope clean; producers are pure, total over their input type, with a closed three-code taxonomy in
declared precedence, reject-is-no-op by construction, Python and Rust twins that agree, exhaustive
registry coverage matching claim [12], real empty typed state roots, a recorded golden vector, and a
declared mutation killer. Duty 3's specific question answers cleanly in the negative: the producer
cannot emit a registered-empty fragment at a non-pinned root. Held below A by P2-1 — the one new
authority-shaped surface leaves its principal root-shaped field (`binding_root`) entirely
unvalidated, so the checker accepts fragments no producer could emit — and by P3-2's swallowed error
in the Rust twin.

### C6 (S15 `c55e51d4b`, P15 `1073c5347`) — **C+**

C6 exists solely to close the P13 findings. Scorecard: **5 of 7 closed, 2 open.**

| P13 finding | Verdict |
|---|---|
| P1-1 module hook binding walk | **OPEN** — fresh bypass, see P1-2 |
| P2-1 / P3-3 aggregate terminal fold | CLOSED, verified over 584 configs |
| P2-2 in-domain ESSO mutants + three-valued CEX evaluation | CLOSED, verified 16/16 and 128/128 |
| P2-3 guillemet raw-byte ban | CLOSED |
| P3-5 Unicode-whitespace `#` rule + claim sentence | **PARTIALLY OPEN** — whitespace half closed, line anchoring left, claim sentence now asserts the stronger false property; see P1-1 |
| P3-1 zeroTables docstring | CLOSED |
| P3-4 CHECK_ORDER_V1 overflow caveat | CLOSED and accurate |

The ESSO counterexample work is the best thing in this candidate and would carry an A on its own: it
is a genuine three-valued semantics over the model, in-domain by construction *and* by independent
assertion, with the attribution model reduced to a single invariant and the derived invariants pinned
mutant-free. The terminal fold repair is likewise correct and now honestly documented on the Lean
side.

Against that, the two closure classes C6 was specifically chartered to seal both remain open, each
with a vehicle at least as natural as the one it was given. The hook walk misses the most ordinary
way anyone writes a conditional module hook (`if TYPE_CHECKING:` / `if sys.version_info >= ...:` /
`try: ... except ImportError:` around a `def`), and C6's own test set shows nesting was on the
author's mind for the alias form. The `#` rule was widened along the axis I named and left anchored
along the axis that matters, while the accompanying claim sentence was strengthened to assert the
property the checker does not enforce — and that gap is not cosmetic: it is a demonstrated,
end-to-end, zero-output arbitrary-code-execution path through a pinned evidence file, positioned two
commands into a 28-command replay that is never re-verified against the worktree afterwards.

C+ rather than lower because the envelope, the full `--check --replay` byte-identical round-trip, and
five of seven repairs are exemplary and independently verified here. Not higher because a packet
whose whole value proposition is that its pins bind must not admit a pinned file that can rewrite
what the rest of the replay reads.

**Not promotable.** Recommend a C7 that (a) walks def/class for the hook names with a class-body
exclusion by parent rather than by `module.body` membership, and decides `from x import *`;
(b) un-anchors the `#` ban on stripped code and adds `#` to the indented-declaration rule; (c) adds a
post-replay worktree re-verification to both `build_o008_formal_cycle_v1.py` and
`check_o008_formal_cycle_v1.py`; (d) corrects `LEAN_STATEMENT_BINDING_V1` and the "twenty-five"
count; and, for C5's surface, (e) binds `binding_root` (for registered-empty lanes, to the pinned
empty root) and labels the Python fold sites to match Rust with overflow vectors in the shared
fixture.

---

## Appendix — commands run

```
git rev-list --count 7551c52a2..ab182bd78            -> 1
git rev-list --count c55e51d4b..1073c5347            -> 1
git diff --name-status <S> <P>  (both)               -> only the two packet files
tools/check_o008_formal_cycle_v1.py --root .          -> rc 0, ok true, packet_admitted true
tools/build_o008_formal_cycle_v1.py --check           -> CHECK_MODE_MISMATCH (expected: needs --replay)
tools/build_o008_formal_cycle_v1.py --check --replay   -> {"drift":[],"ok":true}
pytest tests/formal/test_esso_global_accounting_allocation_certificate_v1.py -> 24 passed
pytest tests/formal/test_esso_global_claimant_custody_certificate_v1.py     -> 20 passed
lake env lean -DwarningAsError=true Proofs/GlobalClaimantCustodyRelationV1.lean -> rc 0, 0B/0B
lake env lean -DwarningAsError=true <mutated copy>    -> rc 0, 0B/0B, wrote LEAN_GATE_PWNED.txt
```

Artifacts under
`/tmp/claude-1000/-home-trevormoc-Downloads-Autonomous-Tau-DEX/37cec583-0c57-4fc0-844c-9f17c86c9adf/scratchpad/opus_p15/`:
`builder_replay.json`, `admission.json`, `gate_esso_cert.log`, `gate_esso_custody.log`,
`gate_clean.{out,err}`, `gate_mut.{out,err}`, `LEAN_GATE_PWNED.txt`,
`mutated_GlobalClaimantCustodyRelationV1.lean`, `mutated_cert.lean`, `leanprobe/`, `hookdemo/`.
