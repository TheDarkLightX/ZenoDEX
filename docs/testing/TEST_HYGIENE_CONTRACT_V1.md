# ZenoDEX Test Hygiene Contract V1

Status: `IMPLEMENTED_GATE`. A current release still requires live verification
of repository-host branch protection.

This contract controls test-evidence promotion for changed critical paths. It
does not establish correctness, production readiness, proof soundness, or
complete M6 workflow coverage.

## Authority boundary

Agent instructions and skills guide test construction. The deterministic gate
decides whether a change has supplied the minimum reviewable evidence packet.

```text
AgentOutput
  -> VersionedEvidencePacket
  -> DiffAwareChecker
  -> DeclaredTestExecution
  -> RequiredRepositoryCheck
  -> HumanOwnerReview
```

`AGENTS.md`, model system prompts, and skills cannot prove model compliance.
The PR gate computes changed paths from the repository base, independently of
an agent's report. Every matched critical path must have a current hash pin in
an evidence packet. Existing packets are append-only.

The gate remains a critical authority surface. Repository-host settings must
require the `test-hygiene` check and protect `.github/`, `tools/`, `tests/`, and
this contract through CODEOWNERS. An actor able to change the checker, workflow,
ownership policy, and branch settings can bypass this repository-local control.

## Canonical artifacts

- Machine contract: `tools/test_hygiene_contract_v1.json`
- Checker: `tools/check_test_hygiene_v1.py`
- Closed model/parser: `tools/test_hygiene_model_v1.py`
- Evidence parser: `tools/test_hygiene_evidence_v1.py`
- Diff-aware runner: `tools/run_test_hygiene_gate_v1.py`
- Evidence packets: `tests/evidence/test_hygiene/THV1-*.json`
- Checker regressions: `tests/test_check_test_hygiene_v1.py`
- Runner regressions: `tests/test_run_test_hygiene_gate_v1.py`

The JSON contract owns path classification and required evidence families. This
document explains its intent and cannot override the checker.

## Change protocol

For each changed path matched by a critical rule:

1. Name the invariant and concrete failure mode.
2. Retain the minimized counterexample or negative regression.
3. Select boundary dimensions from the normative specification and observed
   behavioral partitions.
4. Add at least one stronger family appropriate to the risk: property,
   metamorphic, differential, stateful, fuzz, mutation, formal, or replay.
5. Record explicit AAA and reject-is-no-op applicability decisions.
6. Pin every covered source and executable pytest file by SHA-256.
7. Name each pytest node. The PR gate executes those nodes using an argv vector
   without shell interpretation.
8. State nonclaims.

Deleting or renaming critical evidence requires a new packet that records the
removed path, reason, and pinned replacements. Existing packet modification or
deletion fails closed.

## AAA policy

AAA is an explicit decision rather than a comment-counting rule.

- Focused unit and regression tests should have one clear arrangement, one
  action under examination, and complete assertions over observable results.
- BDD workflow tests may use Given/When/Then structure.
- Property, stateful, fuzz, differential, and formal tests retain their native
  shape. Their packet records why literal AAA is inapplicable when it would hide
  the governing invariant.
- Critical rejects assert the stable reject reason and unchanged authoritative
  state whenever a state transition is present.

## Boundary evidence policy

Boundary selection starts from the local specification: zero, one atom,
minimum and maximum neighbors, overflow, dust, rounding, epoch transitions,
Oracle freshness, fee and collateral thresholds, empty/singleton/maximum
collections, malformed values, and resource ceilings.

The suite then adds behavioral exploration:

- Structure-preserving one-defect mutations isolate binding failures.
- Lower/equal/upper threshold neighbors test exact reject precedence.
- Pairwise combinations provide a baseline interaction inventory.
- Bounded deeper combinations cover named high-risk dependency paths.
- Stateful archives retain replay, reorder, duplicate, stale, partial-failure,
  cancellation, recovery, and terminal traces.
- Quality-diversity exploration may propose underrepresented behavioral
  boundaries. Every promoted candidate needs deterministic replay and a named
  invariant.

This policy uses Boundary Value Exploration to discover behavioral partitions
when specification subdomains are unclear, following
[Boundary Value Exploration for Software Analysis](https://arxiv.org/abs/2001.06652).
It also adopts the archive-diversity principle from
[SETBVE](https://doi.org/10.1145/3797890) for exploratory generation. Paper
output and LLM-selected edges remain advisory until local deterministic evidence
passes.

## Commands

```bash
python3 tools/check_test_hygiene_v1.py --json
python3 tools/run_test_hygiene_gate_v1.py \
  --changed-file M:src/core/example.py \
  --changed-file A:tests/core/test_example.py
python3 tools/run_test_hygiene_gate_v1.py --base-ref origin/main
```

The static contract check and permanent checker regressions are also part of
`tools/run_critical_quality_gate.sh`.

## Promotion and nonclaims

A green V1 gate establishes only these scoped facts:

- matched changed paths have a structurally valid current evidence packet;
- packet source and test hashes match the checked-out candidate;
- required evidence families and applicability decisions are present;
- named pytest nodes pass;
- existing evidence packets were not edited in the candidate diff.

Human review still checks whether the named invariant, mutant, boundaries,
tests, and nonclaims truthfully describe the change. Stronger proof, replay,
mutation, differential, stateful, release, migration, and no-bypass gates retain
their own authority.
