"""Independent checker and vector builder for the F04A ack-progress relation."""

from __future__ import annotations

import json
from dataclasses import replace
from pathlib import Path
from typing import cast

from experiments.fcis_m6_f02_history_encoder_check import build_history
from experiments.fcis_m6_f03_reopen_check import build_layout
from src.core.fcis_m6_f02_history_encoder import encode_history, encode_layout_v1
from src.core.fcis_m6_f04_ack_progress import (
    FCIS_M6_F04_ACK_PROGRESS_SCHEMA_V1,
    F04AckProgressCodeV1,
    F04AckProgressRejectV1,
    F04AckProgressStatusV1,
    F04AckProgressSuccessV1,
    check_f04_ack_progress,
)
from src.state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex

ROOT = Path(__file__).resolve().parents[1]
VECTOR_PATH = ROOT / "docs/research/m6_tasks/TASK_F04A_ACK_PROGRESS_V1.json"


def _root(label: str) -> str:
    from src.core.fcis_durable_retraction import tagged_digest

    return f"0x{tagged_digest(f'f04a/{label}')}"


def build_acked_payload() -> bytes:
    return cast(bytes, encode_layout_v1(build_layout()))


def build_pending_payload() -> bytes:
    history = build_history()
    return cast(bytes, encode_layout_v1(encode_history(replace(history, acks=()))))


def _rehash_layout_root(wire: dict[str, object]) -> None:
    value = wire["value"]
    if type(value) is not dict:
        raise AssertionError("F04A layout value is not an object")
    projection = dict(value)
    projection.pop("layout_root", None)
    value["layout_root"] = sha256_hex(
        domain_sep_bytes("zenodex/fcis/m6/f02/layout-root", version=1)
        + canonical_json_bytes(projection)
    )


def build_mutated_ack_payload() -> bytes:
    wire = cast(dict[str, object], json.loads(build_acked_payload().decode("utf-8")))
    value = cast(dict[str, object], wire["value"])
    rows = cast(list[dict[str, object]], value["ack_rows"])
    rows[0]["destination_receipt_root"] = _root("mutated-receipt")
    _rehash_layout_root(wire)
    return cast(bytes, canonical_json_bytes(wire))


def build_history_changed_payload() -> bytes:
    history = build_history()
    empty = replace(history, atoms=(), acks=())
    return cast(bytes, encode_layout_v1(encode_history(empty)))


def run_checks(*, check_vector: bool = True) -> dict[str, object]:
    acked = build_acked_payload()
    pending = build_pending_payload()
    pending_result = check_f04_ack_progress(pending, pending)
    if type(pending_result) is not F04AckProgressSuccessV1:
        raise AssertionError("F04A rejected unchanged pending state")
    if pending_result.status is not F04AckProgressStatusV1.PENDING:
        raise AssertionError("F04A lost pending status")

    completed = check_f04_ack_progress(pending, acked)
    if type(completed) is not F04AckProgressSuccessV1:
        raise AssertionError("F04A rejected an added acknowledgment")
    if completed.status is not F04AckProgressStatusV1.ACKED:
        raise AssertionError("F04A did not expose ACKED status")
    if len(completed.added_ack_effect_ids) != 1:
        raise AssertionError("F04A did not record the added acknowledgment")

    removed = check_f04_ack_progress(acked, pending)
    if type(removed) is not F04AckProgressRejectV1:
        raise AssertionError("F04A accepted acknowledgment deletion")
    if removed.code is not F04AckProgressCodeV1.ACK_REMOVED:
        raise AssertionError("F04A used the wrong deletion rejection")

    mutated = check_f04_ack_progress(acked, build_mutated_ack_payload())
    if type(mutated) is not F04AckProgressRejectV1:
        raise AssertionError("F04A accepted acknowledgment mutation")
    if mutated.code is not F04AckProgressCodeV1.ACK_MUTATED:
        raise AssertionError("F04A used the wrong mutation rejection")

    changed = check_f04_ack_progress(acked, build_history_changed_payload())
    if type(changed) is not F04AckProgressRejectV1:
        raise AssertionError("F04A accepted non-ack history change")
    if changed.code is not F04AckProgressCodeV1.HISTORY_CHANGED:
        raise AssertionError("F04A used the wrong history rejection")

    wrong = check_f04_ack_progress(object(), pending)
    if type(wrong) is not F04AckProgressRejectV1:
        raise AssertionError("F04A accepted an untyped prior payload")
    if wrong.code is not F04AckProgressCodeV1.WRONG_EXACT_TYPE:
        raise AssertionError("F04A used the wrong type rejection")

    payload = {
        "schema": FCIS_M6_F04_ACK_PROGRESS_SCHEMA_V1,
        "prior_acked_layout_root": completed.prior_layout_root,
        "current_acked_layout_root": completed.current_layout_root,
        "pending_status": pending_result.status.value,
        "completed_status": completed.status.value,
        "added_ack_count": len(completed.added_ack_effect_ids),
        "pending_effect_count": len(pending_result.pending_effect_ids),
        "rejections": {
            "ack_removed": removed.code.value,
            "ack_mutated": mutated.code.value,
            "history_changed": changed.code.value,
            "wrong_type": wrong.code.value,
        },
        "all_rejections_typed": True,
        "prior_state_required": True,
        "universal_current_layout_missing_ack_claim": "not_admitted",
    }
    if check_vector:
        expected = json.loads(VECTOR_PATH.read_text(encoding="utf-8"))
        if canonical_json_bytes(payload) != canonical_json_bytes(expected):
            raise SystemExit("FAIL: F04A ack-progress vector is stale")
    return payload


def main() -> None:
    result = run_checks()
    print("F04A_ACK_PROGRESS_CHECKS_PASS", result["completed_status"])


if __name__ == "__main__":
    main()
