# ZenoDEX Architecture Tournament V1

Status: research-only, unselected, unfrozen, no production authority.

## Result

The current architecture has sound authority allocation and useful typed V1
donors. Its compositional contract is incomplete. The initial tournament names
`TYPED_SETTLEMENT_MICROKERNEL_V2` as the research leader and returns
`selected_candidate_id = null`.

The nominated shape is:

```text
versioned pure economic modules
  -> typed module proposals and kernel intents
  -> one deterministic settlement fold
  -> centrally derived complete value delta
  -> global invariant check
  -> one expected-head ZenoLedger publication
  -> committed external outbox delivery
```

ZenoLedger remains the sole durable economic writer. Domain modules own the
semantics of namespaced lifecycle state and cannot persist balances, issue or
burn assets, consume nullifiers, or emit external effects directly. Tau and a
native fallback implement one policy-verifier port. Their disagreement rejects.
Direct and ZRPF execution identify the same transition core.

## Candidate comparison

| Candidate | Derived design gates | Minimum advisory metric | Weighted advisory metric | Status |
|---|---:|---:|---:|---|
| Global monolith V2 | 13/13 | 350/1000 | 679/1000 | Research eligible; broad change blast radius |
| Event microservices V2 | 6/13 | 300/1000 | 614/1000 | Structurally ineligible |
| Actor saga V2 | 6/13 | 250/1000 | 556/1000 | Structurally ineligible |
| Typed settlement microkernel V2 | 13/13 | 700/1000 | 872/1000 | Research leader; unproved and unselected |

Event-driven services and sagas fail because irreversible economic transitions
cannot safely depend on partial commits or compensating actions. The global
monolith preserves atomicity with a larger proof, migration, and change surface.
The microkernel preserves one atomic writer while isolating economic modules
behind closed proposal and intent types.

## Selection mechanism

The source-bound artifact is
`docs/research/PRODUCTION_READINESS_ARCHITECTURE_TOURNAMENT_V1.json`. The checker
derives structural gate results from each candidate rather than trusting its
claimed statuses:

```bash
python3 tools/check_production_readiness_architecture_tournament_v1.py --json
```

The current research ranking is:

```text
1. reject every candidate with a derived structural violation
2. reject every candidate with an open blocker counterexample
3. maximize its weakest metric
4. maximize its weighted metric
5. break an exact tie by canonical candidate ID
```

This ranking can nominate a prototype. Selection requires every hard gate and
scenario to carry the checker-declared independent evidence grade, every metric
to be measured, and every counterexample to have verified closure. Missing,
`UNKNOWN`, timeout, disagreement, advisory score, or self-asserted status yields
`NO_SELECTION`.

## Current hard gates

- one ZenoLedger durable writer;
- one semantic owner per state domain;
- four closed typed port roles;
- acyclic component dependencies;
- canonical module and command order;
- central delta derivation and one expected-head commit;
- exact reject-no-commit;
- verifier-only construction of opaque admissions;
- Tau/native mismatch rejection;
- release coexistence, object pinning, drain, verification, and retirement;
- replay scope including creating release and writer epoch;
- one mounted ZenoLedger submission capability;
- identical direct and ZRPF core identity.

The artifact also includes ten stateful disaster scenarios and fourteen named
structural mutants. The tests alter candidate structure while retaining its
claimed pass status; the checker must detect every mismatch.

## Open composition obligations

The tournament does not yet establish `ComposableV2(P)`. The next revision must
add machine-checked closure for:

1. exactly one governed route or proved-disabled no-writer row for every one of
   the 33 commands;
2. typed `ModuleDescriptorV2`, `PortContractV2`, `RouteSpecV2`,
   `ModuleOutcomeV2`, and `KernelIntentV2` definitions;
3. producer-guarantee implication of consumer assumptions, with Z3 and CVC5
   agreement and no `UNKNOWN`;
4. authenticated evidence and verifier-registry resolution, including
   accept-all-verifier and self-attested-evidence mutants;
5. total migration classification against an exact source-object inventory;
6. occurrence identities that bind deployment, profile, release, route,
   context, pre-root, and writer epoch;
7. complete effect consumption, external-effect ancestry, and build-derived
   no-bypass inventory;
8. direct, RISC0, formal, and Python-oracle equality over the complete
   observable outcome.

V1 release lifecycle, canonical roots, governed image and journal bindings, and
opaque verified-witness patterns are useful donors. V1 remains research-only,
single-release-per-lane in important paths, and incomplete for whole-economy
composition.

## Claim boundary

The checker provides deterministic source binding, structural derivation,
integer ranking, and mutation evidence for its declared model. It does not prove
runtime behavior, economic correctness, migration completeness, verifier
soundness, mounted authority, or production readiness. Subagent reviews supply
candidates and attacks; they have zero selection and settlement authority.
