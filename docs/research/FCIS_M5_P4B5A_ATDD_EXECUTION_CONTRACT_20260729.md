# FCIS M5-P4B5A ATDD execution contract

```text
status: executable support contract v1
contract kind: acceptance and subagent coordination
visibility: repository research and evidence surface
execution authorized: B1B-1 carrier scope only
local commit authority: coordinator only
push, PR mutation, publication, and external messaging authority: false
terminal condition: exact-head B1B-1 review packet ready for independent review
```

**Status:** `B1B1_IMPLEMENTATION_AUTHORIZED_UNMOUNTED`; `B1B2_DESIGN_ONLY`.

**Purpose:** convert the independently approved Revision 3.4 design into
executable acceptance boundaries for humans and subagents. This contract
authorizes no runtime mount, migration, state transition, publication, proof
input, receipt, bundle, or value movement.

## 1. Normative source

The normative design and approval identity is:

```text
Revision 3.4 target:
  a8b9d191b91a3258e3d7857784bbd6067a0463e1

Review packet:
  1665e788a4c4daf43982262c307d0c04b914d89b

Revision 3.4 document SHA-256:
  cae6562b5e0cade2a03827a2a8f591561317b6cf684de4d22d726c25917108c5

Review source-manifest SHA-256:
  46c721c8dcc2082e8ea08e6cfb664e375cab2ff45b2dbf79b570093423017b9a

Verdict:
  APPROVE_B1B1_REVISION_3_4_UNMOUNTED
```

The unchanged carrier field sets, schema identifiers, and root domains are
inherited from:

```text
docs/research/FCIS_M5_P4B5A_B1B_COMMITTED_CONFIGURATION_AUTHORITY_REVISION_3_1_20260729.md
SHA-256:
  a71752f138dc2de165dff78bd526d3ab734d900e6bbf0394832f6cb8b7a33226
inherited sections:
  3. Exact committed authority header
  4. Public bootstrap and migration carriers
```

The open implementation PR with head
`6ff2ad2080526b2e42883d7cc4f30041fa387847` is reusable evidence only. It does
not descend from the approved packet and replaces the approved Revision 3.4
document with a materially different implementation-candidate text. Agents may
inspect individual implementation ideas. They must retain the approved document
and independently port only items inside the approved B1B-1 scope.

## 2. Why ATDD applies

Acceptance Test-Driven Development fixes the externally observable contract
before implementation. Each slice follows:

```text
precondition
  -> verify once before edits

implementation where red_required = true
  -> semantic failing assertion -> minimum implementation -> green -> refactor

implementation where mutation_kill_required = true
  -> acceptance test first -> named semantic mutant fails -> clean code passes

phase_gate or design_obligation
  -> evaluate only at its declared lifecycle boundary
```

ATDD is useful here because the primary risk is authority drift across many
individually plausible values, codecs, tests, and agent handoffs. The acceptance
matrix binds each change to:

```text
Given
When
Then
Invariant
Counterexample
EvidenceCommand
NonClaim
```

Unit, property, boundary, mutation, and parity tests remain necessary inside
each acceptance case.

## 3. Authority boundary

The approval permits only:

```text
FCISAuthorityHeaderV2
DeploymentBootstrapAnchorClaimV2
V1ToV2MigrationManifestV2
closed schemas and field registries
canonical Python/Rust codecs and roots
shared positive and negative vectors
limited structural-checker coverage
```

These are untrusted canonical carriers. They carry no authenticated pin,
currentness, migration authority, state authority, settlement authority, or
publication authority.

The complete forbidden surface is machine-checked in
`ACCEPTANCE_MATRIX.json`. In particular, B1B-1 cannot add a pinned verifier,
migration candidate, committed V2 state, state-bound configuration, transition,
configuration update, receipt, decision, bundle, proof input, publication, or
runtime mount.

The production helper
`src/core/fcis_fee_distribution_configuration_content_validation.py` from the
open implementation PR is outside the exact carrier checkpoint. It is deferred
unless a later reviewed checkpoint explicitly admits it.

## 4. Agent protocol

Every implementation agent must:

1. Work in one clean, isolated worktree rooted at the approved packet plus this
   ATDD contract.
2. Stay inside that worktree. Do not inspect unrelated repositories or other
   temporary directories.
3. Receive exactly one active `ATDD-B1B1-*` ID from the coordinator. Stop when
   no ID is assigned.
4. Read its `case_lifecycle` classification. Run full packet verification only
   for the precondition before edits; do not rerun that mutable-source manifest
   as an implementation regression gate.
5. For a red-required case, preserve a semantic assertion failure. For a
   mutation-required case, preserve the named mutant failure. Do not count
   absence, import failure, unknown commands, or resource exhaustion as red.
6. Make the smallest change for that one ID, run its focused case, then run all
   live or completed recurring B1B-1 gates. Close the ID before selecting the
   next one.
7. Run the contract checker with the one assigned ID. The checker derives the
   complete tracked and untracked Git diff; agents cannot enumerate or omit
   paths. Every changed path must resolve to an owner set containing the active
   ID. The integration gate uses `ATDD-B1B1-009`.
8. Record changed files, exact commands, exit codes, and non-claims.
9. Stop if the change requires any forbidden type, authority source, hidden
   environment variable, runtime import, or mount.
10. Build mutation fixtures from the checker's declared required paths or a
   bounded synthetic tree. Never copy the full repository once per mutant.
   Treat temporary-space exhaustion as an evidence-harness failure.

Do not modify the approved Revision 3.4 document or its approved review packet.

## 5. Phase promotion

```text
B1B-1 implementation complete
  && focused gates green
  && source manifest rebuilt from committed bytes
  && independent exact-head review approves
  -> B1B-1 may be treated as approved implementation evidence
```

```text
current matrix B1B-2 execution_authorized = false

new committed ATDD contract revision
  && exact B1B-1 implementation approval identity
  && exact B1B-2 design approval identity
  && explicit user implementation authority
  -> a later contract may set B1B-2 execution_authorized = true
```

B1B-2 is currently design-only. No agent, reviewer, local test, subagent
consensus, Probity event, or design verdict can edit that phase flag implicitly.

## 6. Exact-head implementation packet

The planned implementation packet path is:

```text
docs/research/prompts/fcis_m5_p4b5a_b1b1_implementation_review_v1/
  README.md
  REVIEW_PROMPT.md
  SOURCE_MANIFEST.sha256
```

Use a two-commit relation:

```text
implementation target H
  -> code, vectors, tests, checkers, workflow, and implementation report

documentation-only packet commit P, exactly one child of H
  -> README, review prompt, and source manifest
```

The deterministic builder must inventory every path changed from approved
packet `1665e788...` through H, add the immutable Revision 3.1 and Revision 3.4
sources, sort paths by raw repository-relative UTF-8 text, hash committed Git
bytes, reject missing or extra entries, and omit only the manifest itself to
avoid a circular self-hash. Packet siblings are hashed from P. Run:

```bash
python3 -m tools.build_fcis_b1b1_implementation_review_packet --check
```

## 7. B1B-2 design packet construction

The B1B-2 design packet uses a second two-commit relation after an independent
exact-head B1B-1 implementation approval exists:

```text
exact independently approved B1B-1 packet commit B
  -> immutable design base and approval identity

documentation-only B1B-2 design target D
  -> design document and bounded design evidence

documentation-only review packet commit Q, exactly one child of D
  -> README, review prompt, and source manifest
```

The builder inventories every committed path changed from B through D. It also
includes the immutable Revision 3.1 and Revision 3.4 authority sources, this
ATDD contract and matrix, and the exact B1B-1 approval sources. Paths are sorted
by raw repository-relative UTF-8 text and hashed from committed Git bytes.
Packet siblings are hashed from Q. The builder rejects missing, extra,
duplicate, uncommitted, or non-descendant entries. The manifest excludes itself
to avoid a circular self-hash. Run:

```bash
python3 -m tools.build_fcis_b1b2_pinned_migration_review_packet --check
```

The packet cannot authorize implementation. Its approval verdict is design-only.

## 8. Probity boundary

Probity may later be piloted as a local development interlock that observes
write and command order. A useful pilot would require a selected acceptance ID,
a red test before production writes, and the focused green command before a
commit attempt.

Probity remains a suggestion and process-enforcement layer:

```text
ProbityAllows
  && RepositoryCheckerAccepts
  && ExecutableEvidencePasses
  -> ProcessSequenceObserved
```

It cannot decide protocol authority or replace the repository matrix, checker,
tests, manifests, independent review, or phase gate. No dependency installation
is authorized by this contract.

## 9. Durable artifacts

```text
docs/research/prompts/fcis_m5_p4b5a_atdd_subagents_v1/
  ACCEPTANCE_MATRIX.json
  B1B1_IMPLEMENTATION_PROMPT.md
  B1B1_REVIEW_PROMPT.md
  B1B2_DESIGN_PROMPT.md
  B1B2_REVIEW_PROMPT.md
  README.md

tools/check_fcis_m5_p4b5a_atdd_contract.py
tools/fcis_m5_p4b5a_atdd_policy.py
tools/fcis_m5_p4b5a_atdd_validation.py
tests/tools/test_check_fcis_m5_p4b5a_atdd_contract.py
```

Run:

```bash
python3 -B tools/check_fcis_m5_p4b5a_atdd_contract.py --assigned-id ATDD-B1B1-009
python3 -m pytest -q tests/tools/test_check_fcis_m5_p4b5a_atdd_contract.py
```

Both commands must work as written from the repository root.
