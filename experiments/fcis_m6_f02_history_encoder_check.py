"""Independent checker and canonical vector builder for F02."""

from __future__ import annotations

import json
from collections.abc import Callable
from dataclasses import replace
from pathlib import Path

from experiments.fcis_m6_f01_history_atom_check import build_atom
from src.core.fcis_durable_retraction import MigrationPhaseV1, tagged_digest
from src.core.fcis_m6_f02_history_encoder import (
    FCIS_M6_F02_HISTORY_SCHEMA_V1,
    F02AckRowV1,
    F02AuthorityEpochV1,
    F02AuthorizedHistoryV1,
    F02DurableLayoutV1,
    F02HistoryEncoderError,
    encode_history,
    encode_layout_v1,
)
from src.state.canonical import canonical_json_bytes

ROOT = Path(__file__).resolve().parents[1]
VECTOR_PATH = ROOT / "docs/research/m6_tasks/TASK_F02_HISTORY_ENCODER_V1.json"


def _root(label: str) -> str:
    return f"0x{tagged_digest(f'f02/{label}')}"


def build_history() -> F02AuthorizedHistoryV1:
    atom = build_atom()
    writer = atom.writer_profile_root
    authority_rows = tuple(
        F02AuthorityEpochV1(
            epoch_index=index,
            phase=phase,
            authority_state_root=(
                atom.authority_state_root if index == 3 else _root(f"authority-{index}")
            ),
            allowed_writer_roots=(writer,),
            transition_root=_root(f"transition-{index}"),
        )
        for index, phase in enumerate(
            (
                MigrationPhaseV1.LEGACY,
                MigrationPhaseV1.SHADOW_REPLAY,
                MigrationPhaseV1.DUAL_CHECK,
                MigrationPhaseV1.AUTHORITY_SWITCH,
            )
        )
    )
    record = atom.outbox[0]
    ack = F02AckRowV1(
        effect_id=record.effect_id,
        commit_id=atom.commit_id,
        destination=record.destination,
        payload_root=record.payload_root,
        destination_receipt_root=_root("destination-receipt"),
        adapter_profile_root=record.adapter_profile_root,
        idempotency_root=record.idempotency_root,
        response_root=atom.response_root,
    )
    return F02AuthorizedHistoryV1(
        genesis_state_root=atom.expected_pre_state_root,
        deployment_config_root=atom.deployment_config_root,
        verifier_profile_root=atom.verifier_profile_root,
        authority_epochs=authority_rows,
        atoms=(atom,),
        acks=(ack,),
    )


def _assert_rejects(factory: Callable[[], object], message: str) -> None:
    try:
        mutated = factory()
        if isinstance(mutated, F02DurableLayoutV1):
            mutated.__post_init__()
        else:
            encode_history(mutated)
    except F02HistoryEncoderError:
        return
    raise AssertionError(message)


def run_checks(*, check_vector: bool = True) -> dict[str, object]:
    history = build_history()
    layout = encode_history(history)
    encoded = encode_layout_v1(layout)
    repeated = encode_layout_v1(encode_history(build_history()))
    if encoded != repeated:
        raise AssertionError("F02 encoder is not repeatable")
    if layout.header.history_count != 1:
        raise AssertionError("F02 history count is wrong")
    if layout.header.evidence_count != 8:
        raise AssertionError("F02 evidence count is wrong")
    if layout.header.nullifier_count != 1 or layout.header.outbox_count != 1:
        raise AssertionError("F02 parallel row counts are wrong")
    if layout.header.authority_count != 4 or layout.header.ack_count != 1:
        raise AssertionError("F02 authority or acknowledgment count is wrong")

    _assert_rejects(
        lambda: replace(layout, evidence_rows=layout.evidence_rows[:-1]),
        "F02 accepted a missing evidence row",
    )
    _assert_rejects(
        lambda: replace(layout, header=replace(layout.header, evidence_count=7)),
        "F02 accepted a stale header count",
    )
    _assert_rejects(
        lambda: replace(layout, layout_root=_root("foreign-layout")),
        "F02 accepted a foreign layout root",
    )
    _assert_rejects(
        lambda: replace(layout, evidence_rows=tuple(reversed(layout.evidence_rows))),
        "F02 accepted reordered evidence",
    )
    foreign_authority = replace(
        layout.authority_rows[-1], authority_state_root=_root("foreign-authority")
    )
    _assert_rejects(
        lambda: replace(
            layout,
            authority_rows=(*layout.authority_rows[:-1], foreign_authority),
            header=replace(
                layout.header,
                current_authority_state_root=foreign_authority.authority_state_root,
            ),
        ),
        "F02 accepted an authority row crossed with the atom",
    )
    foreign_record = replace(layout.outbox_rows[0].record, effect_id=_root("foreign-effect"))
    foreign_outbox = replace(layout.outbox_rows[0], record=foreign_record)
    _assert_rejects(
        lambda: replace(layout, outbox_rows=(foreign_outbox,)),
        "F02 accepted an outbox row crossed with the atom",
    )
    try:
        encode_history(object())
    except F02HistoryEncoderError:
        pass
    else:
        raise AssertionError("F02 accepted an untyped source history")

    if check_vector:
        expected = json.loads(VECTOR_PATH.read_text(encoding="utf-8"))
        if canonical_json_bytes(build_payload()) != canonical_json_bytes(expected):
            raise SystemExit("FAIL: F02 history-encoder vector is stale")
    return build_payload()


def build_payload() -> dict[str, object]:
    layout = encode_history(build_history())
    return {
        "schema": FCIS_M6_F02_HISTORY_SCHEMA_V1,
        "layout_schema": "zenodex/fcis/m6/f02/durable-layout/v1",
        "layout_root": layout.layout_root,
        "layout_bytes_utf8": encode_layout_v1(layout).decode("utf-8"),
        "history_rows": len(layout.history_rows),
        "evidence_rows": len(layout.evidence_rows),
        "nullifier_rows": len(layout.nullifier_rows),
        "outbox_rows": len(layout.outbox_rows),
        "authority_rows": len(layout.authority_rows),
        "ack_rows": len(layout.ack_rows),
        "single_materializer": "encode_history",
    }


def main() -> None:
    result = run_checks()
    print("F02_HISTORY_ENCODER_CHECKS_PASS", result["layout_root"])


if __name__ == "__main__":
    main()
