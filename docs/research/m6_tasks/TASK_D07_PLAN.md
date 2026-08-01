# FCIS M6 Task D07 Plan

TASK_ID: D07
TITLE: Implement RQAG stutter receipts

## Scope

D07 creates a closed StutterReceiptV1 and a fail-closed verifier for the four
initially eligible RQAG observational identities. The receipt records concrete
operation identity, canonical pre/post roots, the common observable root,
pinned checker identity, and a derived verification root.

New commits, acknowledgment publication, and migration are explicit
non-stutter operation kinds and are rejected before receipt construction.

## Required outputs

- src/core/fcis_stutter_receipt.py
- experiments/fcis_m6_d07_stutter_receipt_check.py
- tests/core/test_fcis_m6_d07_stutter_receipt.py
- docs/research/m6_tasks/TASK_D07_STUTTER_RECEIPT_VECTOR.json
- docs/research/FCIS_M6_D07_RQAG_STUTTER_RECEIPT_SCHEMA_V1.md
- this plan, report, evidence, and source manifest

## Fail-closed acceptance

    python3 -m py_compile <all changed D07 Python files>
    python3 -m ruff check <all changed D07 Python files>
    python3 -m ruff format --check <all changed D07 Python files>
    python3 -m mypy --strict <all changed D07 Python files>
    python3 -m pytest -q tests/core/test_fcis_m6_d07_stutter_receipt.py
    python3 experiments/fcis_m6_d07_stutter_receipt_check.py
    python3 -m json.tool docs/research/m6_tasks/TASK_D07_STUTTER_RECEIPT_VECTOR.json

The checker and tests must cover all eligible operation kinds, explicit new
commit/ack/migration rejections, canonical and observable state changes,
wrong-type roots, checker substitution, verification-root substitution, and
direct construction.

## Nonclaims

D07 is tested unmounted RQAG evidence. It does not prove upstream operation
classification, production canonical-state extraction, destination idempotency,
TCG path completeness, durable publication, recovery, migration authority,
proof-context mounting, or value movement.
