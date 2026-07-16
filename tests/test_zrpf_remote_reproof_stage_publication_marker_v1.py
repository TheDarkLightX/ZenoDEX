"""Exact tests for authority-false remote reproof stage publication markers."""

from __future__ import annotations

import copy
from typing import cast

import pytest

from tools import zrpf_remote_reproof_stage_publication_marker_v1 as marker


def _sha(label: str) -> str:
    import hashlib

    return hashlib.sha256(label.encode("ascii")).hexdigest()


def _outputs() -> list[dict[str, object]]:
    return [
        {
            "schema": "zenodex/zrpf_remote_reproof_artifact_record/v2",
            "artifact_id": _sha("receipt-artifact-id"),
            "contract_id": _sha("receipt-contract-id"),
            "role": "v6_l1_receipt",
            "path": "proofs/v6_l1_receipt.json",
            "producer_stage": "v6_l1_receipt",
            "sha256": _sha("receipt-bytes"),
            "size_bytes": 17,
        },
        {
            "schema": "zenodex/zrpf_remote_reproof_artifact_record/v2",
            "artifact_id": _sha("report-artifact-id"),
            "contract_id": _sha("report-contract-id"),
            "role": "v6_l1_report",
            "path": "reports/v6_l1_candidate_report.json",
            "producer_stage": "v6_l1_receipt",
            "sha256": _sha("report-position-distinct-bytes"),
            "size_bytes": 603,
        },
    ]


def _marker() -> dict[str, object]:
    return marker.build_stage_publication_marker_v1(
        handoff_id=_sha("handoff"),
        execution_packet_id=_sha("packet"),
        task_id=_sha("task"),
        stage_id="v6_l1_receipt",
        ordinal=7,
        capture_id=_sha("capture"),
        outputs=_outputs(),
    )


def test_marker_binds_complete_stage_identity_outputs_and_false_authority() -> None:
    document = _marker()

    marker.validate_stage_publication_marker_v1(
        document,
        expected_handoff_id=_sha("handoff"),
        expected_execution_packet_id=_sha("packet"),
        expected_task_id=_sha("task"),
        expected_stage_id="v6_l1_receipt",
        expected_ordinal=7,
        expected_outputs=_outputs(),
    )

    assert document["content_id"] == marker.derive_stage_publication_content_id_v1(document)
    assert document["authority"] == marker.false_authority_v1()
    assert (
        marker.stage_publication_marker_relative_path_v1(7, "v6_l1_receipt")
        == ".zrpf-stage-publications/v1/07-v6_l1_receipt.json"
    )


@pytest.mark.parametrize(
    ("field", "replacement"),
    (
        ("handoff_id", _sha("other-handoff")),
        ("execution_packet_id", _sha("other-packet")),
        ("task_id", _sha("other-task")),
        ("stage_id", "v6_l2_receipt"),
        ("ordinal", 8),
        ("outputs", []),
    ),
)
def test_marker_binding_tamper_rejects(field: str, replacement: object) -> None:
    document = copy.deepcopy(_marker())
    document[field] = replacement
    document["content_id"] = marker.derive_stage_publication_content_id_v1(document)

    with pytest.raises(marker.StagePublicationMarkerError):
        marker.validate_stage_publication_marker_v1(
            document,
            expected_handoff_id=_sha("handoff"),
            expected_execution_packet_id=_sha("packet"),
            expected_task_id=_sha("task"),
            expected_stage_id="v6_l1_receipt",
            expected_ordinal=7,
            expected_outputs=_outputs(),
        )


def test_marker_content_id_binds_capture_identity() -> None:
    document = copy.deepcopy(_marker())
    document["capture_id"] = _sha("other-capture")

    with pytest.raises(marker.StagePublicationMarkerError, match="content ID"):
        marker.validate_stage_publication_marker_v1(
            document,
            expected_handoff_id=_sha("handoff"),
            expected_execution_packet_id=_sha("packet"),
            expected_task_id=_sha("task"),
            expected_stage_id="v6_l1_receipt",
            expected_ordinal=7,
            expected_outputs=_outputs(),
        )


@pytest.mark.parametrize("mutation", ("reverse", "cross_field_substitution"))
def test_recomputed_marker_id_cannot_hide_output_position_or_field_substitution(
    mutation: str,
) -> None:
    document = copy.deepcopy(_marker())
    outputs = cast(list[dict[str, object]], document["outputs"])
    if mutation == "reverse":
        document["outputs"] = list(reversed(outputs))
    else:
        outputs[0]["role"], outputs[1]["role"] = outputs[1]["role"], outputs[0]["role"]
        outputs[0]["sha256"], outputs[1]["sha256"] = (
            outputs[1]["sha256"],
            outputs[0]["sha256"],
        )
    document["content_id"] = marker.derive_stage_publication_content_id_v1(document)

    with pytest.raises(marker.StagePublicationMarkerError, match="outputs mismatch"):
        marker.validate_stage_publication_marker_v1(
            document,
            expected_handoff_id=_sha("handoff"),
            expected_execution_packet_id=_sha("packet"),
            expected_task_id=_sha("task"),
            expected_stage_id="v6_l1_receipt",
            expected_ordinal=7,
            expected_outputs=_outputs(),
        )


def test_marker_missing_or_non_boolean_authority_rejects() -> None:
    missing = copy.deepcopy(_marker())
    del missing["authority"]
    with pytest.raises(marker.StagePublicationMarkerError, match="fields"):
        marker.validate_stage_publication_marker_v1(
            missing,
            expected_handoff_id=_sha("handoff"),
            expected_execution_packet_id=_sha("packet"),
            expected_task_id=_sha("task"),
            expected_stage_id="v6_l1_receipt",
            expected_ordinal=7,
            expected_outputs=_outputs(),
        )

    substituted = copy.deepcopy(_marker())
    authority = dict(cast(dict[str, object], substituted["authority"]))
    authority["production_authority"] = 0
    substituted["authority"] = authority
    substituted["content_id"] = marker.derive_stage_publication_content_id_v1(substituted)
    with pytest.raises(marker.StagePublicationMarkerError, match="Boolean false"):
        marker.validate_stage_publication_marker_v1(
            substituted,
            expected_handoff_id=_sha("handoff"),
            expected_execution_packet_id=_sha("packet"),
            expected_task_id=_sha("task"),
            expected_stage_id="v6_l1_receipt",
            expected_ordinal=7,
            expected_outputs=_outputs(),
        )
