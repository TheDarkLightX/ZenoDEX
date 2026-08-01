# C07 Exact Migration Review Prompt

You are reviewing the FCIS M6 R03 research packet at an exact local Git
head. Treat the packet as `TESTED / UNMOUNTED` evidence. Do not infer
production authority from any value in it.

## Exact inputs

- Packet: `docs/research/m6_tasks/TASK_C07_MIGRATION_REVIEW_PACKET.json`
- Checker: `experiments/fcis_m6_c07_review_packet_check.py`
- Schema: `docs/research/FCIS_M6_C07_MIGRATION_REVIEW_PACKET_SCHEMA_V1.md`
- Source head recorded in the packet: `476ec022e755ff049c39bf9f08c6606ac87532ca`
- C05 Lean source: `lean-mathlib/Proofs/FCISFeeApportionmentAGQESRGDTraceConjugacy.lean`
- B09 result and index paths recorded in the packet

## Required review sequence

1. Confirm the worktree is clean except for the intended C07 files and record
   `git status --short`.
2. Resolve the packet source head and every lineage commit/tree with local
   Git. Stop on any missing object or tree mismatch.
3. Run:

   ```bash
   python3 -m experiments.fcis_m6_c07_review_packet_check
   python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks C07
   sha256sum --check --strict docs/research/m6_tasks/TASK_C07_SOURCE_MANIFEST.sha256
   ```

4. Run the focused C01-C04/C06 regression suite:

   ```bash
   pytest -q tests/core/test_fcis_m6_profile_ids.py \
     tests/core/test_fcis_entitlement_key_v1.py \
     tests/core/test_fcis_entitlement_migration_v1.py \
     tests/core/test_fcis_entitlement_transport_v1.py \
     tests/core/test_fcis_entitlement_rotation_admission_v1.py
   ```

5. Run the C05 Lean target using the repository’s recorded environment. If
   the local mathlib checkout requires the prior ephemeral `external` link,
   record that setup and removal explicitly.
6. Inspect the packet, checker diff, source manifest, report, and evidence
   JSON for exact identity consistency and conservative nonclaims.

## Acceptance rules

Accept the packet only if:

- the checker prints `C07_REVIEW_PACKET_MATCH`;
- every declared source hash and manifest line matches the current bytes;
- C03 canonical state and manifest recomputation passes;
- C04 exact entry mapping and sign-dual transport passes;
- all listed C05 declaration hashes and the Lean source hash match;
- B09 result and artifact-index hashes, counts, output digests, and parity
  flags match;
- the focused Python tests and Lean target pass;
- the report states exact local commit/tree identities and no remote or
  production promotion.

Reject on any missing, surplus, changed, caller-selected, unauthenticated,
or noncanonical field. Preserve the failing output as a witness before any
repair.

## Explicit prohibition

Do not merge, push, open or modify a remote PR, mount a caller, mount a
datastore, switch authority, deploy, migrate production state, enable value
movement, or treat the research carriers as production authority witnesses.
