# Opus review receipt: candidates C4a and C1''''' at P = b47077ea2fc25c94a32364bd195d558761fbc22b

Reviewer: Opus 5 (`Agent(model: "opus")`, read-only, detached worktree `/tmp/zenodex-formal-core-review-p-b47077ea2`; adversarial copies under `/tmp/opus-p10-*`, deleted by the reviewer).
Date: 2026-09-01. Subject: P10 = b47077ea2fc25c94a32364bd195d558761fbc22b (tree 5ec6fbfe58be4033ed98604a91deaff18534dda8), S10 = e11f42ad29290fda9f10dd515dc2eb596598dbcf; C4a source S9 = b3a816a7b4c963e523e99eaa1705589f1a82f207; parent R9 = bfec733aa996b593968fa173b45f5fa17067b415.
Verdict: C4a Grade A-, ACCEPT (P2-A1 duplicate external effect ids, P2-A2 lane-major precedence, P2-A3 dead AllocationClassV1, P3-A4/A5 fixture surface totality); C1''''' Grade C+, REVISE (P1-B1 char-literal/comment phantom string blinds the Lean stripper, P1-B2 whitespace-normalised whole-file pins collide across // comments, P2-B3 assignment forms of module __getattr__). Disposition: every finding is repaired by candidate C4d (the next source commit after this receipt, cut on top of C4b/C4c = d5e4d1d447f097438eff984ae305c41528886868). The grade is advisory and grants no authority.

Verbatim report follows (sha256 of the reviewer's file: 72f854e182bc60df2fc8b86658e1c7799184e3c654cce6afda5b7345cda0750e).

---

# Opus 5 independent review — P10 `b47077ea2fc25c94a32364bd195d558761fbc22b`

Subject: packet-only child of S10 `e11f42ad29290fda9f10dd515dc2eb596598dbcf`, branch
`codex/formal-core-fable-20260901`, reviewed read-only at
`/tmp/zenodex-formal-core-review-p-b47077ea2`. Two candidates reviewed together:
**C4a** (S9 `b3a816a7b`, GlobalAccountingAllocationCertificateV1 sidecar checker) and
**C1'''''** (S10 `e11f42ad2`, repair of the Opus C1'''' receipt).

**Advisory only. This review grants no authority of any kind.**

| Candidate | Grade | Disposition |
|---|---|---|
| **C4a** — allocation certificate checker | **A-** | **ACCEPT** (3 × P2, 2 × P3; no reachable correctness defect, no parity divergence) |
| **C1'''''** — C1'''' repair | **C+** | **REVISE** (2 × P1 fully mounted; both falsify claim sentences the packet asserts) |

---

## 1. Verification record

Chain topology verified: `git rev-list --parents -n 1 HEAD` gives exactly one parent
(`e11f42ad2…`); `git diff --stat e11f42ad2 b47077ea2` touches exactly the two packet paths
(`docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.{json,md}`). Worktree clean at start and end.

| # | Command | Result |
|---|---|---|
| 1 | `check_o008_formal_cycle_v1.py --root $PWD` | exit 0, `ok:true`, `packet_admitted:true`, `proof_replay.status = NOT_RUN` |
| 2 | same `--replay --python … --esso-python /usr/bin/python3 --esso-pythonpath …` | exit 0, `EXECUTED_PASS`, **19 runs** (counted) |
| 3 | `build_o008_formal_cycle_v1.py --subject-commit e11f42ad2… --created-date 2026-09-01 --check --replay …` | exit 0, `{"drift":[],"mode":"check","ok":true}` |
| 4 | pytest, 7 files | **443 collected**; 330 / 6 / 20 / 13 / 35 / 31 / 8 — every expected count met |
| 5 | `cargo test --offline --locked --test global_accounting_allocation_certificate_golden` | exit 0, **3 passed** |
| 6 | `cargo clippy --offline --locked --all-targets -- -D warnings` | exit 0, clean |
| 7 | `check_test_hygiene_v1.py --base-ref e11f42ad2… --json` | exit 0, `ok:true` |
| 8 | `ruff check` (5 modules) | `All checks passed!` |
| 9 | `mypy --strict` (5 modules) | `Success: no issues found in 5 source files` |
| 10 | `check_global_settlement_canonical_manifest_v1.py --repo-root $PWD --json` | exit 0, `ok:true` |

**Note on run 4.** My first pytest invocation reported 13 failures in
`tests/formal/test_esso_global_claimant_custody_certificate_v1.py`. This was **my harness
error**, not a defect: I omitted `PYTHONPATH=…/ESSO ZENO_ESSO_PYTHON=/usr/bin/python3`.
Rerun with the env: **20 passed**. The failure mode is a `RuntimeError` ("ESSO is
unavailable; set ZENO_ESSO_PYTHON…"), i.e. the suite **fails closed** rather than
silently skipping — correct behaviour, and worth crediting.

### Hand-recomputed pins (all match)

| Pin | Recomputed | Verdict |
|---|---|---|
| `executing_tools` `check_o008_formal_cycle_v1.py` | `7055bfbf9a78…f2b65e88` | match |
| `executing_tools` `o008_formal_cycle_admission_v1.py` | `c600f64b9fc6…73b82900c` | match |
| `executing_tools` `o008_formal_cycle_shell_v1.py` | `3963ef02c643…44435682d1a` | match |
| `executing_tools` `scan_lean_proof_placeholders_v1.py` | `44a7c6714295…745f58239fc4` | match |
| `RUST_STATE_FILE_NORMALIZED_SHA256_V1` | `55c89650deb9f423a5be9759127f12f5404560fba885cc294b983377399c3337` | match |
| `LEAN_DEFINITION_SURFACE_SHA256_V1` | `cd1e010a3f82e1595c4cefa7fc7354bc8d972e77c669ed026d177bb8cf275b11` | match |
| certificate fixture sha256 | `51986e67a6ee656f6465c2693e9d67e93da0bd3e1cd851e9e7a7470086a8cb3d` | match, and **byte-identical to the renderer output**, deterministic over two runs, `--check` exit 0 |
| manifest checker constants | 102 serializers / 34 enums / `hash_global_v1`=219 / 93 call files / 94 closure files / closure `f7de2f69…` | **exact for the tree** |

### User decisions — all hold

`migration/production/publication/release/settlement/value_movement/verifier authority =
NONE`; `formal_core_complete = false`; `o008_status =
OPEN_EXACT_ALL_12_RECONCILIATION_MISSING`; `value_movement_gates_closed = 0/12`;
`whole_value_movement_safe = false`. Reserves are the claimant-free term
(`ReserveInterpretationV1.NAMED_UNENCUMBERED_NO_CLAIMANT`, sole member). Control-domain
vocabulary is used in the sidecar (`control_domain`, `controlling_principal`,
`claimant_entitlement`, `unencumbered_reserve`, `pending_external_obligation`) while V1
wire names stay byte-stable: `git diff --stat 7896065ef e11f42ad2 --
src/core/global_settlement_types_v1.py zk/…/src/state.rs` is **empty**, and
`EconomicAmountV1` still carries `owner`/`custody_domain`. No `UP-xx` string appears
anywhere in the packet (`grep -o "UP-[0-9]*"` → no output), so no UP policy value is
fixture-selected. O-008A is not attested in this packet.

### Deferral honoured

Lean/ESSO models **of the certificate** are deferred to C4b. I did not grade their
absence, and I found no claim in the module, the fixture, the tests or the packet that
implies they exist. `required_sidecar.implementation` carries only `check_order`,
`reject_codes`, `producer_registry`, `golden`, `status`, `mounted:false` — no formal-model
claim.

---

## 2. Candidate C4a — GlobalAccountingAllocationCertificateV1 (grade **A-**, ACCEPT)

### 2.1 What I confirmed

**CBC-core discipline.** `check_global_accounting_allocation_certificate_v1` is a total
pure transition. Exact-type guards on both arguments; `pre_state_root` captured before any
check; every reject path returns `AllocationCertificateRejectedV1` whose `__post_init__`
*raises* unless `post_state_root == pre_state_root`, so reject-is-no-op is enforced by the
type, not by convention. No floats, no `hash()`, no `assert`, no I/O, no clock. Every fold
is checked (`_fold` / `derive_canonical_allocation_rows_v1` both bound at
`MAX_ATOMS_U128_V1`); Rust uses `checked_add(…).ok_or(AllocationTotalOverflow)`. Every row
list is canonically ordered *and* unique by construction — Python
`keys != tuple(sorted(set(keys)))` and Rust `windows(2).any(|p| !(a.key() < b.key()))` are
equivalent strict-sorted-unique tests. `MAX_FRAGMENT_ROWS_V1 = 4096` on both sides.
**I could not find an unchecked arithmetic path, or an overflow not reported as
`ALLOCATION_TOTAL_OVERFLOW`.**

**Python/Rust parity — no divergence found.** Mechanical diff of the producer registry
(12 rows, lane × kind × blocked-on) and of the code/message tables (14 rows):
**byte-identical**. `LaneIdV1` Python `.value` equals the Rust variant name equals its
`Debug` rendering, so every lane-bearing `detail` string agrees; likewise
`LaneProducerKindV1` (`#[allow(non_camel_case_types)]` SCREAMING_SNAKE variants).
Beyond the fixture's 25 vectors I constructed **11 adversarial (state, certificate) pairs**
in Python, serialised them canonically, and replayed them through the Rust twin in a
scratch crate: u128-max rows, duplicate `effect_id` across lanes, the accepted baseline,
an enabled lane, an OPEN terminal with no binding row, header `writer_epoch` drift, a
forged allocation root, a lane-order swap, producer-kind drift, reserves-without-rows, and
a two-fault precedence probe. **11/11 agreed exactly on outcome, code, `detail`, and
`pre_state_root == post_state_root`.**

The Rust golden harness is strong: it decodes each vector, re-encodes and hashes it
(binding the Rust decoder to the Python renderer), asserts the canonical JSON round-trip,
asserts all four derived roots, and on reject asserts **code, `detail`, message,
`pre == post`, and `pre == expected_state_root`**. The Python harness rebuilds state and
certificate from the renderer spec rather than decoding the fixture, so the two directions
close the loop.

**Registry.** Exhaustive over `LaneIdV1` (asserted in both test suites and by the fixture
surface check), **no `RECEIPT_BACKED` lane** (asserted in Rust:
`assert_ne!(kind, LaneProducerKindV1::RECEIPT_BACKED)`), and every `blocked_on` string
names unresolved obligations without selecting a value.

**Mutation killers — I executed all 17, not the required five.** I loaded source-mutated
copies of the checker while rebinding all classes/constants to the pristine objects (so
exact-type guards and enum identity cannot cause a spurious kill), and ran the named
vector through each mutant. Result: **17/17 genuinely killed** (15 flip to ACCEPT, 2 flip
to a different reject code, which the golden's exact-code assertion still catches), and
**17/17 declared polarities match the baseline outcome**. Harness:
`/tmp/opus-p10-mut/kill.py`.

**Fixture and accepted vectors.** 25 vectors; 12 of the 14 reject codes are covered. The
two uncovered codes are `ALLOCATION_TOTAL_OVERFLOW` and
`SOURCE_ATOM_NOT_ASSIGNED_EXACTLY_ONCE` — and I verified these are **unreachable by
construction in the current profile**: `_check_lane_bindings` rejects every non-empty
fragment (enabled → `BLOCKED_LANE_PRODUCER_MISSING`, disabled → `DISABLED_LANE_NOT_EMPTY`)
before any fold that could overflow or any exactly-once comparison. So the fixture's
coverage is complete for what is reachable. The three ACCEPT vectors are registered-empty
over all-lanes-disabled states, and the renderer's own docstring is honest about the rest:
"Vectors with non-empty fragments are still recorded: they pin the cross-language roots of
every row type even though the checker rejects them" — and the `derived` block does pin
those roots on both sides, so those vectors do real work.

**`required_sidecar.implementation` is a true projection**, not a restatement:
`_project_certificate` parses the real `CHECK_ORDER_V1` and
`AllocationCertificateRejectCodeV1` out of the module source
(`python_sequence_constant_v1` / `python_enum_members_v1`) and compares them against
`("header_binding", *SIDECAR_CHECKS_V1, "derived_roots")` — i.e. against the packet's own
`required_checks` — then runs `python_dynamic_binding_scan_v1` and
`certificate_fixture_surface_v1` over the decoded fixture.

**Packet wording is true.** The nonclaim ("no receipt-backed lane producer and is not
mounted; the only certificate it accepts today is the registered-empty certificate over a
state with every lane disabled, so no exact all-twelve-lane reconciliation exists") and
the completion-scope sentence both match exactly what I measured.

### 2.2 Findings

#### P2-A1 — `_check_external_obligations` is duplicate-blind; the "exactly once" property is not enforced across lanes for the pending-external term

`src/core/global_accounting_allocation_certificate_v1.py:674-686` builds
`pending = {row.effect_id: row for fragment … for row in …}`, a dict comprehension that
**silently collapses a repeated `effect_id`**. Rust is the same shape
(`zk/…/global_accounting_allocation_certificate.rs:878`, `BTreeMap … .collect()`).
The sibling `_check_terminal_bindings` (`:694`, Rust `:924`) has an explicit duplicate
guard and rejects with `TERMINAL_BINDING_DRIFT: duplicate <id>`. The asymmetry is the bug.

`OutboxStateV1` carries no `asset` and no `amount_atoms`, so the pending-external term is
the one term whose amounts the V1 outbox cannot contradict — precisely where duplicated
atoms can hide.

**Mounted evidence.** Not reachable today (any non-empty fragment rejects at check 3/4),
so I probed the property under a hypothetical profile, changing *only* two registry values
in place (classes and canonical identity untouched):

```
state has ONE registered PENDING outbox row 0xabab…
ASSET_TRANSFER claims 7 atoms and SPOT_LIQUIDITY claims 9 atoms against that SAME effect id
distinct effect ids in the certificate: 1 / rows: 2
  duplicate effect_id across lanes   -> ACCEPT
  CONTROL: duplicate obligation_id   -> REJECT:TERMINAL_BINDING_DRIFT:duplicate t1
```

**Required repair.** Reject a repeated `effect_id` across fragments with
`EXTERNAL_OBLIGATION_BINDING_DRIFT`, detail `duplicate <effect_id>`, mirroring the
terminal-binding guard, in both implementations, with a fixture vector. **Must land before
C4b makes any lane `RECEIPT_BACKED`** — at that point this becomes reachable.

#### P2-A2 — the declared reject precedence is not the precedence the checker realises

`AllocationCertificateRejectCodeV1`'s docstring is "Closed reject codes in check precedence
(first failing check wins)". Two ways that is false:

1. `_check_lane_bindings` (`:610-624`) iterates **lane-major**, running four checks per
   lane, so a lower-ranked code on an earlier lane beats a higher-ranked code on a later
   lane. Reachable today — I built the witness: lane 0 disabled-with-rows
   (`DISABLED_LANE_NOT_EMPTY`, declared rank 6) plus lane 1 with a forged
   `lane_state_root` (`LANE_STATE_ROOT_DRIFT`, declared rank 3) yields
   **`DISABLED_LANE_NOT_EMPTY`**. Each fault alone yields its own code, so both are live.
   **Rust agrees exactly** (`REJECT code=DISABLED_LANE_NOT_EMPTY detail=ASSET_TRANSFER
   pre==post=true`) — this is a shared specification defect, *not* a parity divergence.
2. `ALLOCATION_TOTAL_OVERFLOW` sits at enum rank 7 but at `CHECK_ORDER_V1` position 11,
   and actually fires inside whichever fold overflows first (run position 4, 6 or 9). The
   `check_…` docstring acknowledges this; the enum docstring does not.

CLAUDE.md makes reject precedence part of the contract, so the declared order should be
made true or the docstring narrowed. **Repair:** state the realised precedence
("first failing *check*, and within `_check_lane_bindings` first failing *lane*"), or
hoist the four lane checks into four separate passes so the enum order is literal.

#### P2-A3 — `AllocationClassV1` is dead surface, and it is pinned into the canonical manifest

`AllocationClassV1` (`:70-78`) is defined, exported in `__all__` (`:855`), and registered
in `GLOBAL_SETTLEMENT_CANONICAL_ENUM_TYPES_V1` (`src/core/global_settlement_canonical_manifest_v1.py:128`).
It is **never constructed, compared, serialised, or referenced** by any check, the
renderer, the fixture, the tests, or the Rust twin (`grep -rn AllocationClassV1` over the
tree returns exactly those three definitional lines; the Rust module has zero
occurrences). Worse, its five members do not match the three-term normative partition —
`UNENCUMBERED_CONTROLLED_LOCATION` and `TERMINAL_OBLIGATION` name classes the partition
does not contain — while its docstring claims "Exactly-once classification of a controlled
source atom". So it is dead code that also misdescribes the implemented partition, and it
inflates `EXPECTED_ENUM_COUNT_V1` (34) and the pinned closure hash, making speculative
surface look load-bearing to the next reviewer.

**Repair:** delete the enum, its `__all__` entry and its manifest registration; re-pin
`EXPECTED_ENUM_COUNT_V1 = 33` and `EXPECTED_SOURCE_CLOSURE_SHA256_V1`. If C4b genuinely
needs it, add it in C4b.

#### P3-A4 — `certificate_fixture_surface_v1` is not total over decoded JSON

`tools/o008_formal_cycle_admission_v1.py:2493-2532` guards the top-level shapes but not the
nested ones. Six hostile fixtures raise an untyped `AttributeError` instead of a typed
`CERTIFICATE_FIXTURE_DRIFT`:

```
registry entry is a plain string           -> AttributeError: 'str' object has no attribute 'get'
registry entry is a list                   -> AttributeError
accepted vector certificate is a list      -> AttributeError
accepted vector certificate is a string    -> AttributeError
ordered_lane_fragments holds a string      -> AttributeError
expected_outcome is a list                 -> AttributeError
```

Still fail-closed (nonzero exit), but not a stable code, and inconsistent with the module's
own discipline — the sibling `_hygiene_pins` guards with
`isinstance(rows, list) and all(isinstance(row, dict) …)`.

#### P3-A5 — the registered-empty flag is vacuous when no vector is ACCEPT

The same function returns `"accepted_vectors_are_registered_empty_over_disabled_lanes": True`
unconditionally, and its loop is vacuous if no vector has `status == "ACCEPT"`; a vector
that is not a dict is silently skipped rather than rejected. I confirmed both:
flipping every ACCEPT to REJECT, and replacing a vector with a string, both return `True`.
Mitigated — the packet pins the three accepted vector names, so the drift is caught by the
packet byte-comparison — hence P3 rather than P2. **Repair:** assert
`len(accepted) == 3` (or ≥ 1) and reject a non-dict vector.

---

## 3. Candidate C1''''' — repair of the Opus C1'''' receipt (grade **C+**, REVISE)

### 3.1 Per-finding disposition

| C1'''' finding | Repair at P10 | Disposition |
|---|---|---|
| **P1-1** `RUST_MACRO_REDEFINED` + whole-file `state.rs` pin | `rust_lexical_closure_v1` rejects a second `macro_rules!` of the same name; only the pinned bounded-vec macro may emit a `fn`; `RUST_STATE_FILE_NORMALIZED_SHA256_V1` | **CLOSED** |
| **P1-2** Lean command closure + elided-region tightening | `_LEAN_FORBIDDEN_WORDS_V1`, `_LEAN_OPEN_COMMAND_RE`, `_LEAN_ITEM_START_RE` / `_LEAN_INDENTED_DECL_RE` on the region | **OPEN** — see P1-B1 |
| **P2-1** `static_closure` / `statement_binding` sentences | rewritten | **OPEN** — the new sentence is falsified by P1-B1 |
| **P2-2** golden-v6 precedence rows | 12 new parametrized smuggling cases + a `| open` / `.open` non-regression test | **CLOSED** (good tests; they cover the *visible* case only) |
| **P3-3** module-level `__getattr__` | rejects `def`/`async def` `__getattr__`/`__dir__` | **PARTIAL** — see P2-B3 |

**P1-1 remount.** My exact C1'''' vehicle (`/tmp/opus-c1qprime-work/state.rs.mutated`: a
second `macro_rules! bounded_state_vec_deserializer_v1` whose body calls a hostile
`evil_widen_rows_v1` that strips a `zz_shadow` key before decoding, defeating
`deny_unknown_fields`) is now rejected at the **first** stage:

```
pristine state.rs (control)  : rust_lexical_closure_v1 PASS, import closure PASS, whole-file pin PASS
C1'''' P1-1 vehicle          : rust_lexical_closure_v1 REJECT
                               AdmissionRejectV1: RUST_MACRO_REDEFINED at …/state.rs: bounded_state_vec_deserializer_v1
```

I could not reconstruct a surviving Rust variant: a differently-named `fn`-emitting macro
is caught by the new `\bfn\b` test; a `$body:item` passthrough is caught because `named is
None`; nested invocations are caught by `RUST_MACRO_NESTED_INVOCATION`; and `state.rs` has
**zero** comment→code adjacencies, so the collision below does not apply to it.

### 3.2 P1-B1 — the Lean command closure **and** `LEAN_DEFINITION_SURFACE_SHA256_V1` are both bypassable; arbitrary commands can be injected invisibly

**Root cause.** `strip_lean_noncode`
(`tools/scan_lean_proof_placeholders_v1.py:70-141`) treats `"` as a string delimiter even
when it is the *content of a Lean `Char` literal*. Its docstring says char literals are
"deliberately not treated as quoting" — but the consequence was not followed through: `'"'`
opens a phantom string the stripper never closes until the next `"`, and a `"` inside a
`--` line comment closes it (comments are not processed while `in_string`). Everything
between is blanked to spaces. Because `lean_definition_surface_v1` ends with
`" ".join(…split())`, blanked text contributes **nothing** to the surface hash; and because
blanked lines are all spaces, they are invisible to `_LEAN_COLUMN_ZERO_RE`,
`_LEAN_INDENTED_DECL_RE`, `_LEAN_DECL_RE`, `_LEAN_WORD_RE` and `_LEAN_OPEN_COMMAND_RE` too.

**Fully mounted attack** on the real pinned file
`lean-mathlib/Proofs/GlobalClaimantCustodyRelationV1.lean` (+168 bytes). Opener is a silent
`have` tactic inside a proof (elided region), closer is a quote inside a line comment:

```lean
  intro injective
  have _dq : Char := '"'                                     -- opens the phantom string
  exact terminalProjection_domainErasure_witness.1
    (injective terminalProjection_domainErasure_witness.2)
axiom opusEvilAxiom : False
instance opusEvilInstance : Inhabited Nat := ⟨0⟩
-- close the phantom string with a quote inside a line comment: "
```

Every gate passes:

```
scan_lean_proof_placeholders(axioms)     PASS   <- its explicit axiom rule does not fire
lean_namespace_check_v1                  PASS
lean_command_closure_v1                  PASS   <- the entire C1''''' P1-2 repair
lean_theorem_inventory_v1 == pinned      PASS
lean_definition_surface_v1 == pinned     PASS   <- cd1e010a… byte-identical
```

And it survives replay:

```
lake env lean -DwarningAsError=true Hostile3.lean
  exit=0  stdout=0B  stderr=0B          <- lean_direct_check requires exactly this
lean_axioms_probe (25 #print axioms)
  pristine 20d5fe6f0c5d…d79548  hostile 20d5fe6f0c5d…d79548  -> byte-identical
```

(`20d5fe6f…` is the same `stdout_sha256` the P10 replay recorded for `lean_axioms_probe`.)

**Why this matters.** `_LEAN_FORBIDDEN_WORDS_V1` exists, per its own comment, to stop
"commands that can rebind what a later statement's tokens mean, add instances, or open
scopes". An injected `instance` changes elaboration of a pinned statement without adding
any axiom, so the axioms probe is structurally blind to it. Both P1-2 and the surface hash
fail together, which is what makes this P1 rather than P2.

**This falsifies a claim sentence the packet asserts** (`LEAN_STATEMENT_BINDING_V1`, the
C1''''' P2-1 rewrite): "…the file may use no notation, macro, syntax, instance, attribute,
scope, or open command, and each elided region is indented proof text with no declaration,
so only how a theorem is proved is left to replay." At P10 the file *can* carry an
`instance` and an `axiom`, and an elided region *can* contain column-zero declarations.

**Evidence boundary (stated honestly).** I demonstrated arbitrary command injection
invisible to every static gate, the compile gate and the axioms probe. I did **not**
construct a specific semantic weakening of a named pinned theorem via the injected
instance; that is a further step this file's particular statements may or may not admit.

**Required repair (any one closes it; I recommend 1 + 3):**
1. Teach `strip_lean_noncode` about `Char` literals: when not already in a string or
   comment, a `'` that is **not** preceded by an identifier character and is followed by
   (an escape or one character) and then `'` is a char literal — blank it as a unit. This
   also removes the `--`-comment-closes-a-string interaction, which only arises from a
   phantom open.
2. Reject any `"` that is not part of a same-line balanced string in the pinned Lean file.
3. **Add a raw-bytes sha256 pin of the Lean proof file to the admission core**, alongside
   the surface hash. The surface hash exists so proof edits do not churn the pin; a raw
   pin would end that convenience, so instead pin the sha256 of `strip_lean_noncode`'s
   *input length and character-class histogram*, or simply also pin
   `sha256(_lean_code(text))` — any injection that blanks itself changes neither, so
   prefer (1) as the real fix and treat (3) as defence in depth.

### 3.3 P1-B2 — the whole-file `_normalized` pins are collision-prone; I built a compiling, passing, weakened `v1_projection_gate.rs`

`_normalized(text) = " ".join(text.split())`
(`tools/o008_formal_cycle_admission_v1.py:1969`) backs three whole-file pins
(`RUST_STATE_FILE_NORMALIZED_SHA256_V1`, `BOUNDED_VEC_FILE_NORMALIZED_SHA256_V1`,
`RUST_GATE_NORMALIZED_SHA256_V1`) and two template comparisons. It **erases the newline
that terminates a `//` line comment**, so any code on the line(s) after a line comment can
be folded *into* that comment — deleting it from the compiled program while the normalized
hash is unchanged.

`state.rs` and `bounded_vec.rs` have **zero** comment→code adjacencies today, so they are
not currently exploitable. `zk/global_settlement_abi_v1/tests/v1_projection_gate.rs` has
**three**, and I exploited the one at L151→L152:

```
pristine normalized sha256 : 38db418dee30744ae1e9cbf242ad07dd8dd7b7c32c93ebe6d6ba80334cdcfa51
hostile  normalized sha256 : 38db418dee30744ae1e9cbf242ad07dd8dd7b7c32c93ebe6d6ba80334cdcfa51
constant RUST_GATE_NORMALIZED_SHA256_V1 : 38db418dee…cdcfa51      <- both match
raw bytes differ : True (8422 vs 8398)
rust_lexical_closure_v1 on the hostile file : PASS (does not notice)
```

The hostile file folds the three `xorshift64*` mixing statements into the preceding
comment, so the seeded property test's `state` is never mixed and every "unknown key" it
generates derives from the unmixed seed. It **compiles and passes**:

```
v1_projection_gate_pristine : 7 passed    (RUST_GATE_EXPECTED_PASSED_V1 = 7)
v1_projection_gate_hostile  : 7 passed
```

**This falsifies the rationale comment at `:625-627`** — "plus the named tests and tables,
so a gate cannot keep its names and lose its assertions." The gate keeps its names, keeps
its pass count, keeps its pinned hash, and loses three statements.

**Required repair.** Preserve line structure in the normalization — collapse only
intra-line whitespace runs:
`"\n".join(" ".join(line.split()) for line in text.splitlines())`. That still tolerates
indentation and formatting churn (the reason `_normalized` exists) while making
comment-folding impossible. Re-pin all three constants and the two templates. A secondary,
lower-severity collision remains regardless: whitespace *inside string literals* is also
collapsed, so two files whose literals differ only in internal whitespace hash equal — in
these files that reaches only diagnostic labels, but the line-preserving fix does not
address it, and a comment-stripping-then-hashing variant would be stronger still.

**Common root cause.** P1-B1 and P1-B2 are the same class: *a normalization or stripping
function used as a security boundary is not injective on the property it is meant to
protect.* Whatever repairs land, both should be accompanied by a mounted-survivor test in
`tests/test_check_o008_formal_cycle_v1.py`, the way the C1''''' P2-2 rows were.

### 3.4 P2-B3 — the module-level `__getattr__` closure covers only the `def` form

`python_dynamic_binding_scan_v1` (`:1461-1470`) rejects module-level
`def`/`async def` named `__getattr__` or `__dir__`. PEP 562 resolves the hook by *name
lookup in the module namespace*, however it got there, so the assignment forms are live:

```
module-level __getattr__                  REJECT PYTHON_DYNAMIC_BINDING_FORBIDDEN
module-level __dir__                      REJECT PYTHON_DYNAMIC_BINDING_FORBIDDEN
async module-level __getattr__            REJECT PYTHON_DYNAMIC_BINDING_FORBIDDEN
class-level __getattr__ (should pass)     PASS   <- correct
__getattr__ = lambda n: 1                 PASS   <- BYPASS
def _g(n): ...  ; __getattr__ = _g        PASS   <- BYPASS
```

`PYTHON_GATE_AST_SHA256_V1` backstops only `PYTHON_GATE_PATH_V1`. The other two scan
targets — `PYTHON_TYPES_PATH_V1` (`:2483`) and `CERTIFICATE_PYTHON_PATH_V1` (`:2546`) —
have **no** tool-side AST or whole-file pin, so the bypass is unmitigated for them.

**Repair.** Also reject module-level `ast.Assign` / `ast.AnnAssign` / `ast.AugAssign`
whose target name is `__getattr__` or `__dir__`; or extend AST pinning to the two
unpinned files.

### 3.5 What is genuinely good in C1'''''

The 12 new parametrized cases in
`test_lean_commands_smuggled_into_proof_regions_are_rejected` are real mounted survivors
with correct expected codes and details (`notation`, `macro_rules`, `open`, `partial`,
`instance`, `export`, `local`, `deriving instance`, unknown column-zero item, indented
`def`, indented `end` → `LEAN_NAMESPACE_DRIFT`, `#eval` → `LEAN_DEFINITION_SURFACE_DRIFT`),
and each `LEAN_COMMAND_FORBIDDEN` case additionally asserts that the surface hash alone
would *not* have caught it. `test_lean_constructor_and_field_named_open_are_not_commands`
is a well-judged non-regression test: the `TerminalStatus.open` constructor and `.open`
field survive because only the command form is banned. Two mounted survivors from my
C1'''' review are pinned as Rust cases. `hygiene_lineage_key_v1` orders by numeric `-vN`
so `v10` outranks `v9` — the lineage-naming trap is correctly handled.

---

## 4. Nonclaims of this review

- I did not verify the ESSO or Lean **content** beyond what the prescribed commands
  execute; I re-ran them and compared hashes, I did not re-derive the theorems.
- I did not construct a semantic weakening of a named pinned theorem via P1-B1's injected
  instance (see the evidence boundary in §3.2).
- P2-A1 is demonstrated under a hypothetical registry profile; it is **not** reachable at
  P10.
- I did not audit `canonical.rs`, `release.rs`, or the lane modules — the packet's own
  nonclaim already scopes them out.
- I ran no Kani, no Tau, and no RISC0.
- Grades are advisory. I grant no authority.

## 5. Residual risks

1. C4a's post-`_check_lane_bindings` logic (checks 4-10) is **entirely unexercised for
   accept** in the current profile. It is pinned, parity-tested on reject paths, and
   root-pinned on non-empty fragments — but the first lane to become `RECEIPT_BACKED` will
   activate ~60% of the checker at once. P2-A1 and P2-A2 both live in that region.
2. The `detail` strings on the two unreachable codes are **not** at parity and will bite
   when they become reachable: on an `_check_exactly_once` controlled-fold overflow Python
   emits the default label `"fold"` while Rust emits `"<LANE> controlled"`; on an
   entitlement-fold overflow Python emits `str(OverflowError)` =
   `"allocation certificate total overflows"` while Rust emits
   `"canonical allocation rows"`. Fix these together with P2-A1.
3. `_LEAN_COLUMN_ZERO_RE` exempts lines starting with `|`, so column-zero `|` content is
   elided and unscanned by `_LEAN_INDENTED_DECL_RE`. The global word closure currently
   covers it; if that closure is ever narrowed, this reopens.
4. Rust `check_lane_bindings` uses a non-strict `zip` where Python uses `zip(strict=True)`.
   It is safe **only** because `state.state_root()` calls `validate()` (which enforces
   exactly 12 canonical lane roots) before `run()`. I verified this; it is a transitive
   invariant, not a local one, and would break silently if `state_root()` were ever
   memoised or the pre-root moved.
5. The disk was ~97% full throughout; all my builds used
   `CARGO_TARGET_DIR=/tmp/opus-p10-cargo-target`, now deleted.

## 6. Process disclosure

While setting up the Lean compile I ran a command that wrote
`lean-mathlib/Proofs/OpusP10Hostile.lean` into the review worktree; the same command
removed it immediately. I then confirmed `git status --porcelain` is **empty** and the file
is absent. No commit, no push, no other write occurred; all subsequent Lean work ran from
`/tmp/opus-p10-mut` using a `LEAN_PATH` captured via `lake env printenv`. I am reporting
this rather than omitting it.
