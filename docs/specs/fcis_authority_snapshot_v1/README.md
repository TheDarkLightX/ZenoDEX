# FCIS Authority Snapshot V1

Status: **normative repair packet; unresolved design decisions and production claim blocked**

This folder is the authoritative implementation packet for repairing the
committed-state work in PR #477 and the authenticated-command/effect work in
PR #478. It exists because the earlier implementation drifted from the agreed
design while chat context was compacted and the branches were reconstructed.

The packet is pinned to the reviewed local heads:

```text
PR #477: fc2f9150c1eacfdb7f6e4272f2a8efbd5fdafe85
PR #478: 6dbb9b36237d982515777caae04a296d0ebac040
```

The implementation agent must read `ERRATA.md` first. Where it conflicts
with an older clause, the errata controls. Continue in this order:

1. `ERRATA.md` records normative corrections discovered after assembly.
2. `DECISIONS.md` records the selected design and its rationale.
3. `AUDIT_FINDINGS.md` identifies the known defects at the pinned heads.
4. `COMBINATOR_CONTRACT.md` defines the only allowed admission machinery.
5. `PR477_STATE_SCHEMA.md` defines the committed-state source and output
   language.
6. `PR478_AUTHORITY_EFFECT_SCHEMA.md` defines the command, settlement, effect,
   and JSON language.
7. `DESIGN_PATTERN_AUDIT.md` records the pattern, rationale, guarantees,
   non-guarantees, and audit bindings for each repair.
8. `IMPLEMENTATION_RUNBOOK.md` gives the exact implementation sequence.
9. `TEST_MATRIX.md` defines mandatory negative and parity evidence.
10. `CONTEXT_DRIFT_PROTOCOL.md` defines mandatory re-entry and review checks.
11. `IMPLEMENTATION_AGENT_PROMPT.md` is the prompt to give the implementation
   agent.
12. `requirements.json` is the machine-readable requirement ledger.

The normative continuation files are
`ASSURANCE_FACTORIZATION_ADDENDUM.md` and
`TEST_MATRIX_PR477_PR478.md`. Use `REVIEW_CHECKLIST.md` for independent final
acceptance. These files are part of the packet even though they were recovered
after the initial numbered list was written.

## Scope

This packet repairs two representation boundaries:

```text
mutable domain builders
  -> exact, closed admission
  -> owned committed state                         PR #477

mutable/parser-owned command and settlement data
  -> exact, closed admission
  -> owned authenticated command and effect plan  PR #478
```

It does not claim to complete the entire ZenoDEX assurance program. Economic
lifecycle repairs, consensus-derived time, cross-language refinement, atomic
database commitment, idempotent outbox delivery, persistent collections, and a
Rust ownership boundary remain separately gated work.

## Required outcome

For each accepted value `x` and resulting owned value `o`:

```text
admit(schema, x) = Accept(o)

implies

  x belongs to the schema's closed source language
  o belongs to the schema's closed owned language
  every value reachable from o is owned and data-only
  later mutation of x cannot alter o
  no caller-defined copy, conversion, comparison, hash, or iteration hook
    is used to admit x
  canonical_bytes(o) and behavior(o) remain stable
```

For every rejected value:

```text
admit(schema, x) = Reject(code, path)

implies

  no candidate state, command, effect, receipt, nonce, or outbox value escapes
  code and path are deterministic under the declared error precedence
```

## Hard stop

The implementation is not review-ready while any authoritative path contains
one of these mechanisms:

```text
copy.deepcopy or copy.copy
pickle or caller-controlled copy protocols
an Any -> Any freeze/thaw helper
reflective dataclass or enum admission
broad isinstance admission for a declared authority type
generic Mapping, Sequence, Iterable, set, or frozenset admission
mutable-base inheritance for a committed value
constructor bypass with object.__new__
unbounded recursive authority traversal
an unregistered record, enum, event, intent kind, or perps market variant
```

## Claim vocabulary

Passing this packet may support the narrow claims:

- `implemented`: the specified owned boundaries exist;
- `tested`: the named counterexamples and parity tests pass;
- `refinement checked`: only if the specified runtime/canonical differential
  evidence also passes at the exact head.

It cannot support `production ready`, `bug free`, or an unqualified
`transitively immutable` claim. The CPython trusted-computing-base assumptions
and all residual blockers must remain explicit.
