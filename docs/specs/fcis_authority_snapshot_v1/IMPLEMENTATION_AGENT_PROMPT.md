# Copy-Paste Prompts for the Implementation Agent

Use Prompt A first. Do not send Prompt B until the reviewed final #477 head is
known. Replace angle-bracket placeholders with exact values.

## Prompt A: repair PR #477

```text
You are implementing a normative security repair packet in ZenoDEX. You are an
implementer, not the design authority. Work only on PR #477's committed-state
ownership boundary.

Repository: TheDarkLightX/ZenoDEX
PR: #477
Reviewed starting head: fc2f9150c1eacfdb7f6e4272f2a8efbd5fdafe85
Expected base: <INSERT EXACT BASE SHA>
Production release claim: BLOCKED

Before editing:

1. Work in a clean clone/worktree and read every applicable AGENTS.md.
2. Read ERRATA.md first, then every file under
   docs/specs/fcis_authority_snapshot_v1, including both TEST_MATRIX files,
   DESIGN_PATTERN_AUDIT.md, and ASSURANCE_FACTORIZATION_ADDENDUM.md.
3. Run CONTEXT_DRIFT_PROTOCOL.md. Return the source and packet checkpoint.
4. Confirm local HEAD, GitHub head, base, merge base, and clean status.
5. Run the style-map, trust-surface, red-flag, and design-metrics tools listed
   in IMPLEMENTATION_RUNBOOK.md.
6. Run and record the current focused-test baseline.

Implement only the `FCIS-477-*`, shared combinator, owned-collection, static
checker, and PR #477 parity requirements in requirements.json.

Non-negotiable design:

- Legacy source admission is one-way: `LegacySource -> CommittedValue`.
- Leaf authority transitions accept exact committed values and return a new
  exact committed value, effects, and receipt or a typed rejection. Aggregate
  DEX transitions use `Accept | Reject | CommittedFailure`; only `Reject` is a
  no-op.
- Committed values use composition and exact committed-type APIs. They never inherit
  dict, list, BalanceTable, LPTable, Intent, Settlement, or another mutable
  domain class.
- Authority admission is a total, bounded, closed tagged combinator algebra.
- The mounted four-argument admission facade owns one declarative registry and
  exhaustive resolver set. Callers never supply registry or callable behavior.
- Every scalar, enum, record, field, collection, optional value, and perps
  variant has an explicit schema and exact source type.
- bool is rejected for every integer field.
- Unknown records, variants, fields, and schema tags fail closed.
- Rejection code, path, and precedence are stable.
- All accepted children are owned data. Canonical bytes are defined by the
  existing versioned encoder, not object layout.
- Build all field candidates before publishing a DexState.
- Do not expose `to_scratch_*`, accept a mutable builder in the functional
  core, or re-admit a mutable post-transition builder.
- A private builtin work buffer is allowed only inside one pure function, must
  not escape, and requires differential parity with a return-new reference.

Forbidden:

- Any -> Any freeze/thaw helper;
- copy.copy, copy.deepcopy, pickle, or caller copy protocols;
- broad Mapping, Sequence, Iterable, set, or frozenset admission;
- reflective arbitrary dataclass or Enum admission;
- callable fields in schema or registry records, or a caller-selected profile;
- broad isinstance for a declared authority source;
- mutable-base inheritance;
- structural read protocols at authority-core entry points;
- public committed-to-mutable conversion;
- legacy mutable domain construction inside the admission resolver;
- object.__new__ constructor bypass;
- unbounded recursion;
- trusting an already-owned-looking value without full validation;
- normalization/coercion at the committed boundary;
- changing economics, ordering, rounding, authorization, codecs, roots, or
  rejection semantics to ease migration;
- self-modifying CI, base64 patch payloads, force-push before local evidence,
  or starting PR #478.

Execution order:

1. Add every mandatory failing witness for shared combinators, owned
   collections, and PR #477. Prove the pinned implementation fails them.
2. Implement snapshot_combinators.py and its stable result/error algebra.
3. Implement OwnedEnumV1 and OwnedMapV1 by composition with read-only exact
   methods. Exact Python Enum members are source values only; copy tag/member
   ordinals.
4. Implement exact table/pool schemas and one-way legacy-source admission.
5. Implement explicit vault, Oracle, fee, and complete perps variant schemas.
6. After the registry is complete, implement `state_admission_profile.py` as
   the only mounted binding of the private registry-aware interpreter.
   Mutation-test its exact four-argument facade and repository-wide call-site
   allowlist.
7. Wire DexState atomically.
8. Migrate authority readers to exact committed types and mutators to pure
   return-new transition functions.
9. Prove canonical bytes, state/support roots, and valid mounted behavior match
   the pinned baseline on a full fixture.
10. Implement the AST contract checker and mutation-kill every rule.
11. Run all narrow and broad gates from the runbook.
12. Stop. Do not begin #478.

If the repository contradicts the packet, stop and return a design question
with exact file, symbol, field, existing invariant/bound, minimal witness, and
which requirement cannot be satisfied. Do not guess a bound or silently add a
compatibility case.

Return exactly:

Exact head:
Base head:
Spec packet SHA-256:
Changed files:
Requirement IDs implemented:
Requirement IDs still open:
Counterexamples observed failing before repair:
Exact commands and results:
Canonical/root parity artifacts and hashes:
GitHub checks at exact head:
Known unrelated failures:
Nonclaims:
Design questions or deviations: none | listed with IDs
```

## Prompt B: repair PR #478 after #477 review

```text
You are implementing the second normative ZenoDEX authority-boundary
repair. Work only on PR #478 after rebasing it onto the reviewed final #477
head.

Repository: TheDarkLightX/ZenoDEX
PR: #478
Old reviewed head with known defects: 6dbb9b36237d982515777caae04a296d0ebac040
Required final #477 parent head: <INSERT REVIEWED #477 SHA>
Production release claim: BLOCKED

Before editing:

1. Use a clean clone/worktree and read all applicable AGENTS.md files.
2. Read ERRATA.md first, then every file under
   docs/specs/fcis_authority_snapshot_v1.
3. Run CONTEXT_DRIFT_PROTOCOL.md and return the checkpoint.
4. Rebase/rebuild #478 on the exact reviewed #477 head.
5. Prove no old deep_freeze/deep_thaw/deepcopy or mutable Frozen* subtype
   survives.
6. Rerun the complete #477 focused suite and contract checker before adding
   #478 code.

Implement only the `FCIS-478-*`, PR #478 parity, and inherited shared
requirements in requirements.json.

Preserve these distinct authority phases:

RawBytes -> CanonicalBytes -> ParsedCommand -> AuthenticatedCommand
         -> AuthorizedCommand -> EvaluatedCandidate -> CommittedReceipt

An OwnedIntent proves stable owned data. It is not itself evidence of
authentication or authorization. Later functions accept only the exact phase
type they require.

Required ownership design:

- preserve the existing strict raw-byte decoder and its canonical command
  identity; parser replacement is outside this PR;
- owned JSON uses the closed shared combinator algebra;
- common and kind-specific intent fields have one registry used by parser,
  snapshot, runtime, and drift checker;
- OwnedIntentV1 is distinct from mutable Intent and owns nested data;
- signed envelopes bind exact canonical bytes of the owned intent;
- admitted batches are bounded tuples;
- owned settlements/fills/deltas are distinct exact records with no seal/cache
  fields in their protocol schema;
- accepted state, effects, receipt, roots, nonce updates, and future outbox
  data derive from one owned evaluated candidate;
- current generic event payload compatibility is bounded owned JSON and keeps
  EVENT-TYPING-001 explicitly open.

All forbidden mechanisms and stop conditions from Prompt A remain in force.
Do not claim atomic datastore commit, cross-language refinement, typed events,
footprint soundness, parallel equivalence, economic terminal closure, or
production readiness from this PR.

Execution order:

1. Add and demonstrate every required pre-repair #478 witness.
2. Implement bounded owned JSON and preserve existing canonical boundary
   parity.
3. Centralize the intent schema and add drift tests.
4. Implement OwnedIntentV1, signed-message binding, tuple batches, and exact
   phase consumers.
5. Implement owned settlement/fill/delta records and explicit conversions.
6. Implement exact owned effects from the same evaluated candidate.
7. Prove signing bytes, settlement/effect bytes and hashes, nonce behavior,
   mounted execution, and rejection parity.
8. Run all #477 and #478 focused suites, contract checker, mounted consumers,
   critical gate, and production-boundary status.
9. Stop and return the exact handoff below.

Return exactly:

Exact head:
Parent #477 head:
Base head:
Spec packet SHA-256:
Changed files:
Requirement IDs implemented:
Requirement IDs still open:
Counterexamples observed failing before repair:
Exact commands and results:
Canonical/signature/effect parity artifacts and hashes:
GitHub checks at exact head:
Known unrelated failures:
Nonclaims:
Design questions or deviations: none | listed with IDs
```

## Prompt C: independent final review

```text
Perform a read-only security and context-drift review of the exact candidate
head. Read all files in docs/specs/fcis_authority_snapshot_v1, requirements.json,
the complete diff, and mounted callers/consumers. Do not edit code. Do not rely
on the PR title, body, or implementer's conclusions.

For every active requirement, report:

Requirement ID
source section
positive requirement
forbidden mechanism
exact code binding
SATISFIED | VIOLATED | UNVERIFIED
minimal counterexample or structural proof
evidence command/artifact
claim impact

Independently search for accepted-language expansion, caller behavior during
admission, mutable-base/reinitialization paths, cycles and missing bounds,
registry drift, lost authority phases, noncanonical encodings, unstable
rejection precedence, stale ancestry/evidence, same-candidate divergence, and
tests that cover examples rather than the full declared language. Pin every
conclusion to the exact source SHA and keep production readiness blocked unless
the wider assurance profile is separately closed.
```
