---
name: zeno-mutation-hardener
description: Run survivor-driven mutation hardening for Zeno authority code. Use when authority code changes, coverage is high but adequacy is uncertain, a mutation campaign has survivors, an agent proposes tests without a defect target, or a suite needs a test-by-mutant kill matrix.
---

# Zeno Mutation Hardener

## Authority

Use executable mutants to improve fault discrimination. Read
`docs/testing/TEST_QUALITY_CONTRACT_V2.md` and use
`docs/testing/templates/mutation_campaign_v1.yaml`.

Mutation is adequacy evidence, not proof. Never silently exclude a survivor.

## Mutation hierarchy

1. Extreme mutations replace a body, predicate, return, or transition with a
   default, constant, error, success, or no-op. They find pseudo-tested code.
2. Language-native mutations change boundaries, booleans, arithmetic,
   statements, match arms, and checked operations.
3. Zeno semantic mutants each change one authority coordinate:
   - omit a commitment field;
   - trust a caller-supplied identity;
   - remove freshness, release, or policy checks;
   - swap reject precedence;
   - accept a duplicate resource, receipt, or child;
   - drop a conservation term or reverse rounding;
   - reapply effects on retry;
   - skip exact journal or manifest equality;
   - update replay state before atomic value commit;
   - map one lane, profile, or release to another.

## Workflow

1. Read the obligation and authority boundary.
2. Generate or select one-coordinate mutants.
3. Prove the unmutated baseline passes.
4. Execute every mutant under deterministic commands.
5. Classify it as `killed`, `survived`, `equivalent`, `unviable`,
   `out_of_scope`, or `unresolved`.
6. For survivors, identify the missing RIPR stage.
7. Ask `zeno-test-architect` for the smallest independent-oracle killer.
8. Rerun baseline and targeted mutants.
9. Emit a test-by-mutant kill matrix.
10. Route duplicate kill vectors to `zeno-suite-distiller`.

Equivalent status requires a semantic or unreachable-state argument, compiler
evidence, bounded exhaustive equivalence, or another reviewer-readable proof.
Difficulty is not equivalence.

Prefer one property that kills a fault family over one test per mutant. Keep
stable catastrophic mutants as named controls.

## Promotion rule

No unresolved viable critical mutant may be silently promoted. Record any
temporary survivor with its threat, blocker, owner, and explicit nonclaim.
