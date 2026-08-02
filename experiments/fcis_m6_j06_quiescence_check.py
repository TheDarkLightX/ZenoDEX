"""Deterministic J06 quiescence checker and adversarial witnesses."""

from __future__ import annotations

import json
import sys
from dataclasses import replace
from pathlib import Path
from typing import cast

_ROOT = Path(__file__).resolve().parents[1]
if str(_ROOT) not in sys.path:
    sys.path.insert(0, str(_ROOT))

from src.core import fcis_durable_retraction as dra  # noqa: E402
from src.core.fcis_m6_j06_quiescence import (  # noqa: E402
    J06_REQUIRED_WRITER_IDS_V1,
    J06AdmissionResultV1,
    J06Error,
    J06QuiescenceGateV1,
    J06RejectCodeV1,
    J06WriterAttemptV1,
    _mint_gate_v1,
    reject_writer_v1,
)
from tools.build_fcis_m6_j06_quiescence import (  # noqa: E402
    DEFAULT_CONFIG_PATH,
    DEFAULT_OUTPUT_PATH,
    build_payload,
)
from tools.check_fcis_m6_j02_writer_matrix import check_writer_matrix  # noqa: E402


def _read_vector() -> dict[str, object]:
    value = json.loads((_ROOT / DEFAULT_OUTPUT_PATH).read_text(encoding="utf-8"))
    if type(value) is not dict:
        raise AssertionError("J06 vector must be an object")
    return cast(dict[str, object], value)


def _gate(payload: dict[str, object]) -> J06QuiescenceGateV1:
    writer_ids = payload.get("covered_writer_ids")
    markers = payload.get("evidence_markers")
    if type(writer_ids) is not list or type(markers) is not list:
        raise AssertionError("J06 vector collections are malformed")
    return _mint_gate_v1(
        manifest_root=cast(str, payload["manifest_root"]),
        entrypoint_inventory_root=cast(str, payload["entrypoint_inventory_root"]),
        phase=dra.MigrationPhaseV1(cast(str, payload["phase"])),
        activation_sequence=cast(int, payload["activation_sequence"]),
        authority_epoch_index=cast(int, payload["authority_epoch_index"]),
        authority_state_root=cast(str, payload["authority_state_root"]),
        legacy_profile_root=cast(str, payload["legacy_profile_root"]),
        target_profile_root=cast(str, payload["target_profile_root"]),
        current_head_root=cast(str, payload["current_head_root"]),
        replay_head_root=cast(str, payload["replay_head_root"]),
        current_snapshot_root=cast(str, payload["current_snapshot_root"]),
        replay_snapshot_root=cast(str, payload["replay_snapshot_root"]),
        replay_evidence_root=cast(str, payload["replay_evidence_root"]),
        covered_writer_ids=tuple(cast(str, item) for item in writer_ids),
        evidence_markers=tuple(cast(str, item) for item in markers),
        quiescence_root=cast(str, payload["quiescence_root"]),
    )


def _attempt(
    gate: J06QuiescenceGateV1,
    publisher_id: str,
    *,
    profile_label: str = "target",
) -> J06WriterAttemptV1:
    return J06WriterAttemptV1(
        publisher_id=publisher_id,
        writer_profile_root=(
            gate.legacy_profile_root if profile_label == "legacy" else gate.target_profile_root
        ),
        authority_epoch_index=gate.authority_epoch_index,
        authority_state_root=gate.authority_state_root,
        expected_head_root=gate.current_head_root,
        commit_id=dra.tagged_digest(f"j06/commit/{publisher_id}/{profile_label}"),
        command_root=dra.tagged_digest(f"j06/command/{publisher_id}/{profile_label}"),
        sequence=gate.activation_sequence,
    )


def _assert_noop(result: J06AdmissionResultV1, gate: J06QuiescenceGateV1) -> None:
    if result.accepted is not False or result.state_unchanged is not True:
        raise AssertionError("J06 produced a non-rejecting or state-changing result")
    if (
        result.pre_head_root != gate.current_head_root
        or result.post_head_root != gate.current_head_root
    ):
        raise AssertionError("J06 changed the current head in a rejection")
    if (
        result.pre_authority_state_root != gate.authority_state_root
        or result.post_authority_state_root != gate.authority_state_root
    ):
        raise AssertionError("J06 changed authority state in a rejection")
    if (
        result.pre_snapshot_root != gate.current_snapshot_root
        or result.post_snapshot_root != gate.current_snapshot_root
    ):
        raise AssertionError("J06 changed durable snapshot state in a rejection")
    if result.gate_root != gate.quiescence_root:
        raise AssertionError("J06 result is not bound to its gate")


def run_checks() -> None:
    baseline = build_payload(_ROOT / DEFAULT_CONFIG_PATH)
    vector = _read_vector()
    if baseline != vector:
        raise AssertionError("J06 vector is not the independently regenerated payload")
    gate = _gate(baseline)
    check_writer_matrix()
    if gate.covered_writer_ids != J06_REQUIRED_WRITER_IDS_V1:
        raise AssertionError("J06 does not cover the exact in-scope K01 writer set")
    if gate.current_head_root != gate.replay_head_root:
        raise AssertionError("J06 accepted unequal replay/current heads")
    if gate.current_snapshot_root != gate.replay_snapshot_root:
        raise AssertionError("J06 accepted unequal replay/current snapshots")

    accepted_attempts = 0
    for publisher_id in gate.covered_writer_ids:
        for profile_label in ("legacy", "target"):
            result = reject_writer_v1(
                gate, _attempt(gate, publisher_id, profile_label=profile_label)
            )
            _assert_noop(result, gate)
            if result.code is not J06RejectCodeV1.QUIESCED_WRITER_REJECTED:
                raise AssertionError(f"quiesced writer was not rejected: {publisher_id}")
            accepted_attempts += int(result.accepted)
    if accepted_attempts != 0:
        raise AssertionError("J06 accepted a writer during final replay comparison")

    unknown = reject_writer_v1(gate, _attempt(gate, "unreviewed_writer"))
    _assert_noop(unknown, gate)
    if unknown.code is J06RejectCodeV1.ENTRYPOINT_NOT_COVERED:
        pass
    else:
        raise AssertionError("J06 admitted an entrypoint outside the K01 bound")

    stale_epoch = replace(
        _attempt(gate, gate.covered_writer_ids[0]),
        authority_epoch_index=gate.authority_epoch_index + 1,
    )
    if reject_writer_v1(gate, stale_epoch).code is not J06RejectCodeV1.AUTHORITY_EPOCH_MISMATCH:
        raise AssertionError("stale authority epoch was not rejected")
    stale_authority = replace(
        _attempt(gate, gate.covered_writer_ids[0]),
        authority_state_root=dra.tagged_digest("j06/foreign-authority"),
    )
    if reject_writer_v1(gate, stale_authority).code is not J06RejectCodeV1.AUTHORITY_ROOT_MISMATCH:
        raise AssertionError("foreign authority root was not rejected")
    stale_head = replace(
        _attempt(gate, gate.covered_writer_ids[0]),
        expected_head_root=dra.tagged_digest("j06/foreign-head"),
    )
    if reject_writer_v1(gate, stale_head).code is not J06RejectCodeV1.HEAD_MISMATCH:
        raise AssertionError("stale head was not rejected")
    wrong_sequence = replace(
        _attempt(gate, gate.covered_writer_ids[0]),
        sequence=gate.activation_sequence + 1,
    )
    if reject_writer_v1(gate, wrong_sequence).code is not J06RejectCodeV1.SEQUENCE_MISMATCH:
        raise AssertionError("wrong activation sequence was not rejected")
    foreign_profile = replace(
        _attempt(gate, gate.covered_writer_ids[0]),
        writer_profile_root=dra.tagged_digest("j06/foreign-profile"),
    )
    if reject_writer_v1(gate, foreign_profile).code is not J06RejectCodeV1.WRITER_PROFILE_MISMATCH:
        raise AssertionError("foreign writer profile was not rejected")

    try:
        replace(gate, replay_head_root=dra.tagged_digest("j06/divergent-replay"))
    except (J06Error, TypeError, ValueError):
        pass
    else:
        raise AssertionError("J06 accepted a replay/current-head divergence")

    result = reject_writer_v1(gate, _attempt(gate, gate.covered_writer_ids[0]))
    try:
        replace(result, accepted=True)
    except (J06Error, TypeError, ValueError):
        pass
    else:
        raise AssertionError("J06 result could be mutated into an accepted outcome")


if __name__ == "__main__":
    run_checks()
    print("J06_QUIESCENCE_MATCH")
