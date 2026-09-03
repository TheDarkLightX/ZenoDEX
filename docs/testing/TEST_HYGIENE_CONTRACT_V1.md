# ZenoDEX Test Hygiene Contract V1

Status: `IMPLEMENTED_GATE`, pending repository-host branch-protection activation.

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
The PR gate computes the changed paths from the repository base, independently
of an agent's report. Every matched critical path must have a current hash pin
in an evidence packet. Existing packets are append-only.

The gate itself remains a critical authority surface. Repository-host settings
must require the `critical-quality` check and CODEOWNER approval for `.github/`,
`tools/`, `tests/`, and this contract. A writer able to change the checker,
workflow, ownership policy, and branch settings can bypass this repository-local
control.

## Canonical artifacts

- Machine contract: `tools/test_hygiene_contract_v1.json`
- Checker: `tools/check_test_hygiene_v1.py`
- Closed model/parser: `tools/test_hygiene_model_v1.py`
- Evidence parser: `tools/test_hygiene_evidence_v1.py`
- Diff-aware runner: `tools/run_test_hygiene_gate_v1.py`
- Mutation ledger: `tools/thv1_mutation_ledger_v1.py`
- Evidence packets: `tests/evidence/test_hygiene/THV1-*.json`
- Checker regressions: `tests/test_check_test_hygiene_v1.py`
- Runner regressions: `tests/test_run_test_hygiene_gate_v1.py`
- Ledger and row-schema regressions: `tests/test_thv1_mutation_ledger_v1.py`

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
5. Record an explicit AAA and reject-is-no-op applicability decision.
6. Pin every covered source and executable pytest file by SHA-256.
7. Name each pytest node. The PR gate executes those nodes using an argv vector
   without shell interpretation.
8. State nonclaims.

Deleting or renaming critical evidence requires a new packet that records the
removed path, reason, and pinned replacements. Existing packet modification or
deletion fails closed.

## AAA policy

AAA is required as an explicit decision rather than a comment-counting rule.

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
  boundaries. Every promoted candidate needs a deterministic replay and a
  named invariant.

This policy uses Boundary Value Exploration to discover behavioral partitions
when specification subdomains are unclear, following
[Boundary Value Exploration for Software Analysis](https://arxiv.org/abs/2001.06652).
It also adopts the archive-diversity principle from
[SETBVE](https://doi.org/10.1145/3797890) for exploratory generation. Neither
paper output nor an LLM-selected edge authorizes promotion without local
deterministic evidence.

## Mutation rows and the mutation ledger

A packet's `mutations` list names the defects its pinned tests are claimed to
catch. From evidence-id date `20260903` on, every row must take one of two
shapes; the checker refuses any other:

- Mechanical: `{"description", "killed_by", "mutant": {"path", "needle",
  "replacement"}}`. `path` is one of the packet's `source_pins`; `needle` must
  occur exactly once in that file (the checker verifies this while the pin is
  current); `replacement` is the mutated text. `killed_by` is a pinned pytest
  node, or `<pinned crate>/tests/<target>.rs::<filter>` for a cargo test.
- Narrative: `{"description", "killed_by", "narrative": true}`. A defect the
  packet argues about but cannot execute; the description says why. Narrative
  rows are listed and never counted as killed.

Packets dated before the cutover keep their string-only rows as immutable
replay records; the checker reports them as `legacy`, and an added packet may
not carry them whatever date its name claims.

`tools/thv1_mutation_ledger_v1.py --packet <evidence-id>` executes the
mechanical rows: each row gets a fresh `git archive HEAD` copy under
`$TMPDIR/thv1-ledger/`, the pins are checked against the copy, the mutant is
applied, and the killer runs there (`pytest -q -x -p no:cacheprovider` or
`cargo test --offline --locked --test <target> <filter>`). The killer must pass
on an unmutated control copy and fail on the mutated copy; a killer that still
passes marks the row `SURVIVED` and the ledger exits 1. The report is one JSON
object on stdout with rows sorted by description; logs go to stderr.

Nonclaim: the mutation ledger executes declared rows only; it does not measure
mutants nobody declared.

## Commands

Execute a packet's declared mutation rows:

```bash
python3 tools/thv1_mutation_ledger_v1.py --packet THV1-20260903-example-v1
```

Validate the contract and all packet schemas:

```bash
python3 tools/check_test_hygiene_v1.py --json
```

Validate a local candidate set and run its declared tests:

```bash
python3 tools/run_test_hygiene_gate_v1.py \
  --changed-file M:src/core/example.py \
  --changed-file A:tests/core/test_example.py
```

PR CI uses the fetched base branch:

```bash
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
