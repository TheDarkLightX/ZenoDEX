---
name: zeno-test-architect
description: Design obligation-first, independent-oracle tests for ZenoDEX, ZRM, ZenoLedger, and ZRPF. Use when adding or reviewing tests, choosing AAA, BVA/BVE, BDD, property, model, metamorphic, differential, combinatorial, fuzz, mutation, concurrency, crash, or formal techniques, or closing an assurance gap.
---

# Zeno Test Architect

## Authority

Design the smallest test strategy that closes one falsifiable semantic
obligation. Read `docs/testing/TEST_QUALITY_CONTRACT_V2.md` and use
`docs/testing/templates/test_obligation_v2.yaml`.

The V2 checker establishes schema and execution linkage. Independent tools and
review decide semantic adequacy.

## Workflow

1. Write one dominant claim before test code.
2. Name concrete faults: omitted binding, stale authority, wrong precedence,
   incomplete set, arithmetic error, noncanonical parse, rejection side effect,
   replay violation, race/crash history, or proof/ledger mismatch.
3. Record RIPR:

   ```text
   Reach      input or history reaches the risky operation
   Infect     the defect changes semantic state or result
   Propagate  the difference reaches a stable observation
   Reveal     an independent oracle rejects or differs
   ```

4. Ask whether a stronger type removes the fault class. Route cardinality,
   ordering, ownership, lifecycle, and derived-identity problems to
   `zeno-semantic-compressor`.
5. Choose the smallest technique:

   ```text
   one concrete behavior          focused example with clear AAA structure
   edge partition                 BVA/BVE and equivalence classes
   multi-condition guard          decision table and exact precedence
   small finite domain            exhaustive enumeration
   large value/history domain     property or state machine with shrinking
   known relation between runs    metamorphic
   independent implementation     differential
   configuration interaction      constrained t-way combinations
   structured hostile input       structure-aware fuzzing
   suite adequacy                 mutation testing
   concurrency                    linearizability histories
   persistence                    bounded crash exploration
   universal invariant            proof/model checking and executable bridge
   ```

6. Use BDD for externally meaningful business and lifecycle scenarios.
7. Prefer exact typed errors and no-effect state equality, reviewed fixed
   vectors, independent references, solver/theorem agreement, metamorphic
   relations, and explicit state models.
8. Bind the obligation to an executed mutant or minimized counterexample.
9. Parameterize repeated examples when they share one oracle. Preserve distinct
   authority boundaries, independent oracles, fixed vectors, and smallest
   witnesses.

## Required output

- linked V1 and V2 evidence packets;
- fault list and RIPR account;
- technique choice and rejected alternatives;
- oracle grade and independent source;
- minimal test inventory and executable falsifier;
- commands, outcomes, and nonclaims.

## Prohibitions

- Do not optimize for test count or coverage percentage.
- Do not add ritual AAA comments.
- Do not assert literal runner output such as `7 passed`.
- Do not use broad error assertions when a stable typed error exists.
- Do not claim proof from randomized testing.
