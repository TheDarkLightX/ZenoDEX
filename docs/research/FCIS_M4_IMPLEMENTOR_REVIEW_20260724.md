# FCIS M4 Implementor Review

**Received implementation head:** `1887f7ca059a5261d929586b22a5db48d39c4b5c`

**Intermediate repair head:** `8bb0f2885cae4d99b604de84f4d72d8fae10c6ea`

**Pre-checker repair head:** `9e732524d3c8fc6a05472793d22761915e0a92b8`

**Reviewed source head:** `a6e20097d74641784402fb2af5a9939beaf11a9d`

**Milestone:** M4 exact authoritative consumers

**Production mount:** no

**Independent exact-head verdict:** GO for M4 stack progression; no production mount

## Executive result

The received implementation was a no-go. It aimed at exact authoritative
consumers, while several leaves admitted a value and continued reading or
reconstructing a separate value graph. Its tests established useful behavioral
properties without enforcing the specified construction mechanism.

The intermediate repair fixed the visible raw-read and support-root versioning
problems. Independent review then found three remaining blockers:

1. nonce, settlement, and support consumers repeatedly re-admitted or
   reconstructed command values instead of sharing one admitted graph;
2. the structural checker could miss a raw companion passed transitively beside
   an admitted value;
3. support-root v5 evidence was derived from evaluated post-state instead of
   the exact admitted pre-state.

The repaired source head closes all three in source and executable evidence.
The evaluator performs one command admission and forwards the same object
identities to restricted private already-admitted sinks. The checker validates
the complete call shapes, forbids raw companions, restricts imports of those
private sinks, and rejects post-state support-root derivation. Runtime identity
evidence confirms that nonce, settlement, fee, and support consumers share the
same admitted command graph.

The first review of `9e732524` remained a no-go because the checker still
accepted raw aliases and reflective private-sink capture. The final checker
repair requires every authoritative sink result to be assigned exactly once,
permits raw command loads only in the one admission call, and rejects direct,
computed, module-dictionary, `vars`, dynamic-import, `sys.modules`, and module-
object acquisition of private authority modules. Independent retesting rejected
all 11 bounded variants.

M4 remains unmounted. M5 must complete support-root v5 coverage and migration,
the three-way decision, the root-bound commit bundle, the expected-root shell
commit port, and Python/Rust refinement evidence before any authority switch.

## Frozen decisions applied

1. The closed typed combinator is the sole authority admission mechanism.
2. The evaluator admits each authoritative command graph once.
3. Downstream private sinks consume the already-admitted graph without
   re-admission, reconstruction, or raw companion parameters.
4. Public leaf wrappers remain independently safe and admit their own untrusted
   inputs before delegating to a private sink.
5. Private already-admitted sinks are restricted capabilities. Only their
   defining modules and the exact evaluator may import them.
6. A malformed canonical command rejects at `COMMAND_ADMISSION` with a stable
   code and path.
7. Mounted support-root v4 semantics and bytes remain unchanged.
8. Support-root v5 is an unmounted projected pre-state commitment.
9. Generic recursive freezing, `copy.deepcopy`, mutable-base inheritance,
   mutation seals, and hand-written parallel validation are forbidden.

## Findings and repairs

### M4-R1: multiple admitted command graphs

**Severity:** blocking

**Status at received and intermediate heads:** open

**Status at repaired head:** source-fixed and tested

Repeated admission can return equal values while breaking the stronger
authority law:

```text
admit(command_schema, raw) = AdmitOk(exact)
------------------------------------------------------
all authoritative consumers receive that same exact graph
```

The repaired evaluator imports and calls private admitted sinks at
`src/core/fcis_step_evaluator.py:60`, `:81`, `:90`, `:370`, `:426`, and `:608`.
The public wrappers remain independently safe in
`src/core/nonce_batch_transition.py:97` and
`src/core/settlement_strong_validator.py:892`; their private sinks begin at
lines 147 and 931 respectively. The support-root private sink begins at
`src/state/support_root.py:770`.

The runtime witness at `tests/core/test_fcis_step_evaluator.py:208` records
object identities and requires one settlement identity for settlement and fee
calculation and one intent-tuple identity for nonce, settlement, and support.

### M4-R2: transitive raw-companion checker escape

**Severity:** blocking

**Status at intermediate head:** open

**Status at repaired head:** source-fixed and mutation-tested

A helper could accept both `exact_settlement` and `raw_settlement`, then consume
the raw value below the direct evaluator call. Direct-name checks did not prove
transitive provenance.

The checker now validates exact helper parameters and keyword call shapes. The
mutation at
`tests/tools/test_check_fcis_authority_snapshot_contract.py:309` adds a raw
companion to the fee sink and must fail with `EXACT_CONSUMER_DATAFLOW`.

Private admitted sinks are listed in the capability allowlist at
`tools/check_fcis_authority_snapshot_contract.py:235`. Unauthorized-import
mutations begin at
`tests/tools/test_check_fcis_authority_snapshot_contract.py:1049` and must fail
with `PRIVATE_AUTHORITY_IMPORT`.

### M4-R3: support-root v5 used the post-state

**Severity:** blocking

**Status at intermediate head:** open

**Status at repaired head:** source-fixed and regression-tested

The support root commits the projected pre-state required to validate a
transition. The repaired `_candidate_evidence_v1` receives `pre_state` at
`src/core/fcis_step_evaluator.py:580` and calls the admitted support sink with
that value at line 608. The post-state retains its separately named state root.

The v5 fixture is now:

```text
0xd73a8a0148d5d861c46477fe5cc90f35f98f5d262b5210e8ff840ea3e2357280
```

Mounted v4 remains:

```text
0x66c43d933bdf3105ea34adb2adf9fc43745b18fd70693998eda71e44d213dbcf
```

No v4/v5 equivalence is claimed.

### M4-R4: public support wrapper briefly became coercive

**Severity:** high regression found during repair

**Status at repaired head:** fixed

Moving projection behind the private support sink briefly let the public
committed wrapper coerce a plain mapping through snapshot admission. The
focused semantic suite caught the change. The public wrapper now requires exact
`OwnedMapV1`, re-admits independently, and delegates to the private sink. This
preserves public exact-type rejection while allowing the evaluator to avoid a
second admission.

## Grades

| Surface | Received head | Intermediate head | Repaired source head | Reason |
| --- | --- | --- | --- | --- |
| Frozen-design fidelity | D | C | A- / pass | One admitted graph and restricted sinks now encode the specified mechanism. |
| Authority isolation | D | C- | A- / pass | Raw aliases, ignored results, second admission, reflection, and unauthorized imports are gated. |
| Determinism and versioning | C | B | A | v4 is stable; v5 is explicit and uses exact pre-state. |
| Counterexample quality | C | B- | A- | Identity, raw-companion, post-state, and private-import witnesses cover the discovered failures. |
| Structural enforcement | D | C | B+ | The checker closes the known escapes; its size and line-pinned compatibility allowlist remain maintenance debt. |
| Production readiness | F | F | F | M4 is intentionally unmounted and M5 obligations remain open. |
| Overall M4 checkpoint | D / no-go | C- / no-go | A- / pass for stack progression | Independent review closed all three M4 blockers; mounting remains blocked. |

The received implementation did useful exploratory work, but it failed the
authority mechanism contract. Passing behavioral tests cannot raise that grade.

## Evidence at repaired source head

- Focused exact-consumer and integration suite: `196 passed`, one warning.
- Structural checker suite: `180 passed`, one warning.
- Structural profiles:
  - `state-substrate`: `ok=true`, zero violations;
  - `authority-graph`: `ok=true`, zero violations;
  - `exact-replay`: `ok=true`, zero violations, 35 declared compatibility
    findings;
  - `exact-consumers`: `ok=true`, zero violations, 50 declared compatibility
    findings.
- Packet checker: `ok=true`, 39 requirements, 103 declared tests, 103 bound
  tests, 34 audit findings.
- Ruff: passed on changed Python files.
- Mypy: no issues in 25 configured source files.
- Critical quality gate:
  - acceptance TCB: `553 passed`;
  - critical suite: `790 passed`;
  - support-root branch coverage: `82.5%`, floor `80%`.
- Production-boundary checker: `ok=true`.
- Permissionless assurance: critical lane `READY`; six formal/release lanes
  unavailable.
- Security scan: zero high findings; four medium inherited broad catches.
- Independent drift review: all three M4 blockers closed; 11 raw-provenance
  and private-capability variants rejected with `EXACT_CONSUMER_DATAFLOW` or
  `PRIVATE_AUTHORITY_IMPORT`.

## Remaining M5 blockers

1. Define complete v5 support and absence semantics for every mounted spot
   intent and every read, write, context, fee, nonce, LP-duration, and recipient
   dependency.
2. Bind v5 to its schema, verifier, adapter, proof guest, golden vectors,
   migration, replay, and Python/Rust parity evidence, or leave it unmounted.
3. Implement one immutable exhaustive `Accept | Reject | CommittedFailure`
   decision.
4. Implement one root-bound commit bundle containing state patch,
   authoritative plan, receipt, replay updates, and outbox records.
5. Demonstrate expected-pre-root compare-and-swap, crash behavior, and
   idempotent outbox delivery at the actual datastore boundary.
6. Keep the authority switch blocked until the final-mount structural profile
   and all checkpoint reviews pass.

## Implementor lessons

1. Treat construction mechanism and object provenance as security properties.
2. Test identity and complete dataflow when one admitted graph is required;
   equality tests cannot establish that law.
3. Keep public wrappers safe for direct callers and provide narrowly scoped
   private sinks for already-admitted values.
4. Make private authority helpers checker-enforced capabilities in Python.
5. Mutation-test the structural checker against a transitive raw companion,
   second admission, wrong transition side, and unauthorized import.
6. Use distinct actors, recipients, and pre/post values in counterexamples.
7. Stop before mounting when a commitment profile lacks complete migration and
   cross-language evidence.

## Progression rule

The reviewed source head may be used as the M5 ancestor. The M5 implementor
must follow
`docs/research/prompts/FCIS_M5_ATOMIC_MOUNT_REVIEWED_HANDOFF_20260724.md`.
If a support-root, atomic-commit, or refinement prerequisite remains open, the
required outcome is `M5_BLOCKED_NO_AUTHORITY_SWITCH`.
