# B1B-1 ATDD implementation prompt

```text
status: compiled candidate
prompt kind: one-slice implementation
visibility: assigned subagent
compiled from: FCIS M5-P4B5A ATDD execution contract v1
execution authorized: one assigned B1B-1 carrier acceptance ID
local commit authority: false unless the coordinator explicitly grants it
push, PR mutation, publication, and external messaging authority: false
terminal condition: assigned ID closed with an evidence receipt, then stop
```

Required coordinator input:

```text
ASSIGNED_ACCEPTANCE_ID = exactly one ATDD-B1B1-* identifier
```

## Role

Implement exactly the assigned acceptance case. Stop with `ASSIGNMENT_MISSING`
if the coordinator did not supply one ID.

## Exact authority

```text
target commit:
  a8b9d191b91a3258e3d7857784bbd6067a0463e1

packet commit:
  1665e788a4c4daf43982262c307d0c04b914d89b

verdict:
  APPROVE_B1B1_REVISION_3_4_UNMOUNTED
```

The normative design is
`docs/research/FCIS_M5_P4B5A_B1B_COMMITTED_CONFIGURATION_AUTHORITY_REVISION_3_4_20260729.md`.
Do not edit or replace it.

The exact inherited carrier fields, schemas, and root domains are Sections 3
and 4 of:

```text
docs/research/FCIS_M5_P4B5A_B1B_COMMITTED_CONFIGURATION_AUTHORITY_REVISION_3_1_20260729.md
SHA-256:
  a71752f138dc2de165dff78bd526d3ab734d900e6bbf0394832f6cb8b7a33226
```

Do not infer carrier fields from the open PR.

## Workspace boundary

Work only in the assigned clean worktree. Do not inspect unrelated
repositories, home-directory trees, downloads, or other temporary workspaces.
Inspect the open implementation PR only when the coordinator supplies an exact
commit or file path.

## Allowed implementation

```text
FCISAuthorityHeaderV2
DeploymentBootstrapAnchorClaimV2
V1ToV2MigrationManifestV2
closed schemas and field registries
canonical Python codecs and roots
canonical Rust codecs and roots
shared positive and negative vectors
limited structural-checker coverage
```

No runtime mount is permitted.

Do not implement any pinned verifier, migration authority or successor,
committed V2 state, state-bound configuration, configuration update,
transition, receipt, decision, bundle, proof input, publication, or runtime
integration. Do not add
`fcis_fee_distribution_configuration_content_validation.py` in this checkpoint.

## Required loop

Use:

```text
Red -> Green -> Refactor -> Gate
```

For the assigned acceptance ID:

1. Read its complete matrix entry.
2. Read its `case_lifecycle` classification and name the invariant and minimized
   counterexample.
3. Add or select its acceptance test before production code.
4. If `red_required`, preserve a failing semantic assertion. Missing files,
   import errors, unknown commands, and disk exhaustion are invalid red evidence.
5. If `mutation_kill_required`, show the named semantic mutant fails while the
   clean candidate passes.
6. Implement the minimum pure carrier, schema, codec, vector, or checker change
   owned by this ID.
7. Run the focused test and all live or previously completed recurring gates.
   Do not rerun the old 45-file preflight manifest after implementation edits.
8. Review for canonical determinism, exact ownership, closed fields, Boolean
   aliases, U256 bounds, Unicode scalars, digest form, and authority leakage.
9. Close the ID, return an evidence receipt, and stop.

Mutation fixtures must copy only the checker's exact required paths or build a
bounded synthetic tree. Do not use `shutil.copytree` on the repository for each
mutant. A disk-exhausted run is unavailable evidence, even if the intended
assertion would otherwise pass.

## Hidden environment prohibition

Every documented command must work exactly as written from the repository root.
Do not depend on `PYTHONPATH=.`, an interactive shell activation, mutable
environment variables, network access, or unrecorded generated files.

Matrix commands classified as `planned_evidence` are target interfaces. Do not
claim they ran until the owning slice creates them. The two ATDD bootstrap
commands are live now.

Before handoff, run the checker with the literal assigned acceptance ID. For an
`ATDD-B1B1-003` assignment, the exact command is:

```bash
python3 -B tools/check_fcis_m5_p4b5a_atdd_contract.py --assigned-id ATDD-B1B1-003
```

Use the ID supplied by the coordinator. Do not use an environment variable or
wrapper to supply it. The checker automatically derives tracked changes and
ordinary untracked files from `HEAD`; there is no caller-supplied changed-path
list. Every discovered path must be owned by the active ID. An ignored path
matching the evidence ownership registry must already be force-added to Git or
the checker rejects it.

The exact integration command is:

```bash
python3 -B tools/check_fcis_m5_p4b5a_atdd_contract.py --assigned-id ATDD-B1B1-009 --diff-base 1665e788a4c4daf43982262c307d0c04b914d89b
```

## Required final receipt

```text
Assigned acceptance IDs:
Changed files:
Red commands and failures:
Green commands and results:
Cross-language evidence:
Structural evidence:
Invariant impact:
Non-claims:
Commands not run:
Residual risk:
```

Stop and report `SCOPE_BLOCKED` if an assigned case requires any forbidden
surface. Do not widen the scope.
