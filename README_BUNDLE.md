# FCIS M6 Durable-Retraction Research and Luna Implementation Bundle

This packet contains the reviewed M6 durable-retraction research artifacts, the
repair implementation, executable reference models, bounded-search evidence,
formal artifacts, and the authoritative Luna repair inputs.

Status: connective research evidence, locally verified where recorded, and
unmounted. Nothing in this packet authorizes runtime mounting, authority
switching, value movement, or M6 promotion.

Key entry points:

- `docs/research/FCIS_M6_LUNA_IMPLEMENTATION_TASKBOOK_V1.md`
- `docs/research/FCIS_M6_LUNA_TASK_GRAPH_V1.json`
- `docs/research/FCIS_M6_DURABLE_RETRACTION_BREAKTHROUGH_20260731.md`
- `docs/research/FCIS_M6_R02_COMPLETE_SRGD_THEOREM_20260731.md`
- `src/core/fcis_durable_retraction.py`
- `tests/core/test_fcis_durable_retraction.py`
- `formal/esso/fcis_durable_retraction_v1.yaml`
- `lean-mathlib/Proofs/FCISDurableRetraction.lean`
- `docs/research/FCIS_M6_LUNA_REPAIR_REPORT_20260731.md`
- `docs/research/FCIS_M6_LUNA_SOURCE_MANIFEST_V1.json`
- `docs/research/FCIS_M6_LUNA_CHANGE_INVENTORY_V1.md`
- `docs/research/FCIS_M6_LUNA_TOOLCHAIN_V1.json`
- `docs/research/FCIS_M6_LUNA_NONCLAIMS_V1.md`

The reviewed functional implementation target is the authority-boundary repair
recorded in `docs/research/FCIS_M6_LUNA_REPAIR_REPORT_20260731.md`. The exact-head
delivery target changes only the workflow. It checks the supplied repair-input
SHA-256 ledger, installs the hash-locked Python requirements, verifies the exact
ESSO and mathlib dependency revisions, and validates the final packet.

The canonical archive and its manifest are generated from the declared source
set. The final branch has one workflow-only delivery target followed by one
documentation-only packet child. The workflow regenerates the archive
byte-for-byte, creates `artifacts/fcis-m6-external-delivery-receipt.json` after
the packet commit, and uploads that receipt with the archive. Nothing in this
bundle authorizes runtime mounting, authority switching, value movement, or M6
promotion.
