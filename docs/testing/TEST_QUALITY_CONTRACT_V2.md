# ZenoDEX Test Quality Contract V2

Status: `IMPLEMENTED_OVERLAY_GATE`. Repository-host branch protection still
requires live owner verification.

This contract adds obligation quality to Test Hygiene Contract V1. V1 owns
critical-path classification, source and test hashes, exact pytest nodes, and
append-only execution evidence. V2 requires the selected V1 packet to carry a
falsifiable semantic obligation, RIPR propagation account, independent oracle,
representation review, and executable falsifier.

It does not establish correctness, proof soundness, production readiness, or
complete M6 workflow coverage.

## Authority boundary

```text
AgentOrSkillProposal
  -> AppendOnlyV1ExecutableEvidence
  -> AppendOnlyV2SemanticObligation
  -> DiffAwareDeterministicChecker
  -> ExactPinnedTests
  -> RequiredRepositoryCheck
  -> HumanOwnerReview
```

`AGENTS.md` and skills guide behavior. They cannot establish compliance. The
V2 checker independently obtains changed paths through V1, requires one unique
V2 packet for every selected V1 packet, and runs the exact V1-pinned nodes.

The checker proves structural closure and execution linkage. A model can still
write misleading prose or a weak test. Mutation execution, independent models,
formal tools, code review, CODEOWNERS, and branch protection remain necessary
for semantic trust.

## Promotion unit

The promotion unit is one semantic obligation. Each packet defines:

1. claim and exact promotion scope;
2. authority surface and tier;
3. concrete one-coordinate failure model;
4. Reach, Infect, Propagate, and Reveal;
5. representation/degrees-of-freedom review;
6. smallest suitable test technique;
7. independent oracle and exact reject/no-effect observation;
8. executed mutation, counterexample, or history linked to a pinned test;
9. minimal test inventory and retained witness decision;
10. SLOC/runtime delta and explicit nonclaims.

## Canonical artifacts

- V1 contract: `tools/test_hygiene_contract_v1.json`
- V2 machine contract: `tools/test_quality_contract_v2.json`
- V2 model/parser: `tools/test_quality_model_v2.py`
- V2 checker: `tools/check_test_quality_v2.py`
- V2 diff runner: `tools/run_test_quality_gate_v2.py`
- V2 packets: `tests/evidence/test_quality/TQV2-*.json`
- V2 regressions: `tests/test_check_test_quality_v2.py`
- Focused skills: `agent_skills/zeno-*/SKILL.md`
- Authoring templates: `docs/testing/templates/`

Existing V1 packets remain immutable historical records. V2 applies when a
candidate diff selects a new V1 packet. A V2 packet links to exactly one V1
packet, and duplicate V2 links reject.

## RIPR and oracle policy

Every critical obligation states:

```text
Reach      input or history reaches the risky operation
Infect     the fault creates a different semantic state or result
Propagate  the difference reaches a stable observation boundary
Reveal     an exact independent oracle distinguishes it
```

Input selection techniques such as BVA, BVE, equivalence partitioning, pairwise
coverage, fuzzing, and properties mainly improve Reach. They require a Reveal
account. AAA may clarify a focused test; ritual AAA comments carry no evidence.

Oracle independence is recorded as:

```text
0  process success, no panic, or coverage only
1  same-implementation round trip or self-consistency
2  reviewed fixed vector or explicit decision table
3  independently implemented executable model
4  theorem, independent solver, or cross-tool agreement
```

The current critical-path overlay requires grade 2 or higher. This grade is
descriptive. Human review still checks whether the claimed source is genuinely
independent.

## Technique selection

Choose the smallest technique that closes the obligation:

| Risk shape | Primary technique |
|---|---|
| One concrete behavior | focused example with clear AAA structure |
| Numeric/input edge classes | BVA/BVE and equivalence partitions |
| Multi-condition guards | decision table and exact precedence |
| Small closed domain | exhaustive enumeration |
| Large structured histories | state-machine properties with shrinking |
| Known relation between runs | metamorphic testing |
| Independent implementation/tool | differential testing |
| Configuration interactions | constrained t-way combinations |
| Parser, journal, or manifest | structure-aware fuzzing |
| Suite adequacy | mutation testing |
| Concurrent exact-once behavior | linearizability histories |
| Persistence and recovery | bounded crash exploration |
| Universal invariant | proof/model checking plus executable bridge |

BDD belongs at externally meaningful workflow and lifecycle boundaries.

## Mutation and rejection contracts

Every currently classified critical surface requires an executed mutation
linked to a V1-pinned pytest node. Named hypothetical mutants in prose do not
satisfy the contract.

Curated one-coordinate semantic mutants include omitted commitment fields,
stale release acceptance, wrong reject precedence, duplicate resources,
conservation-term deletion, wrong rounding, replay reapplication, incomplete
recursive child coverage, and proof admission without exact journal equality.

For fail-closed paths, tests normally assert:

```text
exact stable reject class
+ specified precedence
+ no panic or partial descriptor
+ unchanged balances, roots, history, and replay state
+ deterministic replay
```

The packet records an explicit `applied` or `not_applicable` no-effect decision.

## Bloat controls

- Do not assert literal runner test counts.
- Do not wrap a language-native test runner unless its boundary is under test.
- Do not add a test when a stronger type can remove the invalid state.
- Use one authoritative source for closed vocabularies and gate inventories.
- Preserve separately written independent models and fixed compatibility vectors.
- Generate counts, paths, hashes, and inventories from retained results.
- After mutation campaigns, compare kill vectors before consolidating tests.
- Stop when a candidate kills no new mutant, closes no obligation/history, adds
  no independent oracle, retains no smaller witness, and improves no runtime or
  determinism property.

## Commands

```bash
python3 tools/check_test_hygiene_v1.py --json
python3 tools/check_test_quality_v2.py --json
python3 tools/run_test_quality_gate_v2.py --base-ref origin/main --json
pytest -q tests/test_check_test_quality_v2.py tests/test_run_test_quality_gate_v2.py
```

## Promotion and nonclaims

A green V2 gate establishes:

- every selected V1 packet has one closed-schema V2 obligation;
- RIPR, oracle, representation, technique, witness, metrics, and nonclaim fields
  are present and reject placeholders;
- the oracle grade and falsifier kinds meet the path rule;
- every falsifier points to an exact selected V1-pinned node;
- those nodes pass in the candidate checkout;
- existing V2 packets were not edited or deleted.

It does not prove that prose is truthful, the oracle is mathematically valid,
the mutant represents every fault, or the feature is production-ready.
Independent review and stronger evidence retain those authority decisions.
