"""Independent checker and vector builder for F03 total reopen."""

from __future__ import annotations

import json
from pathlib import Path
from typing import cast

from experiments.fcis_m6_f02_history_encoder_check import build_history
from src.core.fcis_durable_retraction import tagged_digest
from src.core.fcis_m6_f02_history_encoder import (
    F02DurableLayoutV1,
    encode_history,
    encode_layout_v1,
)
from src.core.fcis_m6_f03_reopen import (
    FCIS_M6_F03_REOPEN_SCHEMA_V1,
    F03ReopenCodeV1,
    F03ReopenRejectV1,
    F03ReopenSuccessV1,
    reopen_layout,
    reopen_layout_bytes,
)
from src.state.canonical import canonical_json_bytes

ROOT = Path(__file__).resolve().parents[1]
VECTOR_PATH = ROOT / "docs/research/m6_tasks/TASK_F03_REOPEN_V1.json"


def _root(label: str) -> str:
    return f"0x{tagged_digest(f'f03/{label}')}"


def build_layout() -> F02DurableLayoutV1:
    return encode_history(build_history())


def _wire(layout: object) -> dict[str, object]:
    encoded = encode_layout_v1(layout)
    return cast(dict[str, object], json.loads(encoded.decode("utf-8")))


def _value(wire: dict[str, object]) -> dict[str, object]:
    raw = wire["value"]
    if type(raw) is not dict:
        raise AssertionError("layout vector value is not a mapping")
    return cast(dict[str, object], raw)


def _rejected(payload: bytes, message: str) -> F03ReopenRejectV1:
    result = reopen_layout_bytes(payload)
    if type(result) is not F03ReopenRejectV1:
        raise AssertionError(message)
    return result


def run_checks(*, check_vector: bool = True) -> dict[str, object]:
    layout = build_layout()
    encoded = encode_layout_v1(layout)
    reopened = reopen_layout(layout)
    if type(reopened) is not F03ReopenSuccessV1:
        raise AssertionError("F03 exact layout reopen failed")
    if reopened.history != build_history():
        raise AssertionError("F03 exact layout history differs")
    wire_reopened = reopen_layout_bytes(encoded)
    if type(wire_reopened) is not F03ReopenSuccessV1:
        raise AssertionError("F03 byte reopen failed")
    if wire_reopened.canonical_layout_bytes != encoded:
        raise AssertionError("F03 canonical bytes differ after reopen")

    missing = _wire(layout)
    cast(list[object], _value(missing)["evidence_rows"]).pop()
    missing_result = _rejected(canonical_json_bytes(missing), "F03 accepted a missing evidence row")

    extra = _wire(layout)
    evidence = cast(list[object], _value(extra)["evidence_rows"])
    evidence.append(evidence[-1])
    extra_result = _rejected(canonical_json_bytes(extra), "F03 accepted a surplus evidence row")

    reordered = _wire(layout)
    reordered_evidence = cast(list[object], _value(reordered)["evidence_rows"])
    reordered_evidence.reverse()
    reordered_result = _rejected(canonical_json_bytes(reordered), "F03 accepted reordered evidence")

    foreign_root = _wire(layout)
    _value(foreign_root)["layout_root"] = _root("foreign-layout")
    foreign_result = _rejected(
        canonical_json_bytes(foreign_root), "F03 accepted a selected-root-only mutation"
    )

    crossed_atom = _wire(layout)
    history_rows = cast(list[dict[str, object]], _value(crossed_atom)["history_rows"])
    atom_bytes = history_rows[0]["atom_bytes_utf8"]
    if type(atom_bytes) is not str:
        raise AssertionError("history atom bytes are not text")
    atom_wire = json.loads(atom_bytes)
    atom_value = cast(dict[str, object], atom_wire["value"])
    atom_value["anf_root"] = _root("foreign-anf")
    history_rows[0]["atom_bytes_utf8"] = canonical_json_bytes(atom_wire).decode("utf-8")
    crossed_result = _rejected(
        canonical_json_bytes(crossed_atom), "F03 accepted a crossed atom projection"
    )

    noncanonical = b" " + encoded
    noncanonical_result = _rejected(noncanonical, "F03 accepted noncanonical layout bytes")
    if noncanonical_result.code is not F03ReopenCodeV1.NONCANONICAL_BYTES:
        raise AssertionError("F03 used the wrong noncanonical rejection code")

    wrong_type = reopen_layout(object())
    if type(wrong_type) is not F03ReopenRejectV1:
        raise AssertionError("F03 accepted an untyped exact-layout input")
    incomplete = object.__new__(type(layout))
    incomplete_result = reopen_layout(incomplete)
    if type(incomplete_result) is not F03ReopenRejectV1:
        raise AssertionError("F03 accepted an incomplete layout object")

    if check_vector:
        expected = json.loads(VECTOR_PATH.read_text(encoding="utf-8"))
        if canonical_json_bytes(build_payload()) != canonical_json_bytes(expected):
            raise SystemExit("FAIL: F03 reopen vector is stale")
    return build_payload(
        rejection_codes=(
            missing_result,
            extra_result,
            reordered_result,
            foreign_result,
            crossed_result,
            noncanonical_result,
            incomplete_result,
        )
    )


def build_payload(
    rejection_codes: tuple[F03ReopenRejectV1, ...] | None = None,
) -> dict[str, object]:
    layout = build_layout()
    if rejection_codes is None:
        rejection_codes = (
            _rejected(
                canonical_json_bytes(
                    {
                        **_wire(layout),
                        "value": {
                            **_value(_wire(layout)),
                            "layout_root": _root("foreign-layout"),
                        },
                    }
                ),
                "vector setup",
            ),
        )
    return {
        "schema": FCIS_M6_F03_REOPEN_SCHEMA_V1,
        "layout_root": layout.layout_root,
        "canonical_layout_bytes_utf8": encode_layout_v1(layout).decode("utf-8"),
        "reopened_history_rows": len(layout.history_rows),
        "reopened_evidence_rows": len(layout.evidence_rows),
        "reopened_nullifier_rows": len(layout.nullifier_rows),
        "reopened_outbox_rows": len(layout.outbox_rows),
        "reopened_authority_rows": len(layout.authority_rows),
        "reopened_ack_rows": len(layout.ack_rows),
        "rejection_codes": [result.code.value for result in rejection_codes],
        "all_rejections_typed": all(
            type(result) is F03ReopenRejectV1 for result in rejection_codes
        ),
    }


def main() -> None:
    result = run_checks()
    print("F03_REOPEN_CHECKS_PASS", result["layout_root"])


if __name__ == "__main__":
    main()
