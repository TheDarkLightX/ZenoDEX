"""Independent F04 whole-layout fixed-point checker and mutation vector."""

from __future__ import annotations

import copy
import json
from pathlib import Path
from typing import cast

from experiments.fcis_m6_f03_reopen_check import build_layout
from src.core.fcis_m6_f02_history_encoder import encode_layout_v1
from src.core.fcis_m6_f04_fixed_point import (
    FCIS_M6_F04_FIXED_POINT_SCHEMA_V1,
    F04FixedPointRejectV1,
    F04FixedPointSuccessV1,
    check_whole_layout_fixed_point,
)
from src.state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex

ROOT = Path(__file__).resolve().parents[1]
VECTOR_PATH = ROOT / "docs/research/m6_tasks/TASK_F04_FIXED_POINT_V1.json"
_LAYOUT_ROOT_DOMAIN = "zenodex/fcis/m6/f02/layout-root"

_COUNT_FIELDS = {
    "authority_rows": "authority_count",
    "history_rows": "history_count",
    "evidence_rows": "evidence_count",
    "nullifier_rows": "nullifier_count",
    "outbox_rows": "outbox_count",
    "ack_rows": "ack_count",
}
_MULTI_ROW_COLLECTIONS = ("authority_rows", "evidence_rows")
_ALL_COLLECTIONS = (
    "authority_rows",
    "history_rows",
    "evidence_rows",
    "nullifier_rows",
    "outbox_rows",
    "ack_rows",
)


def _wire() -> dict[str, object]:
    return cast(dict[str, object], json.loads(encode_layout_v1(build_layout())))


def _value(wire: dict[str, object]) -> dict[str, object]:
    raw = wire["value"]
    if type(raw) is not dict:
        raise AssertionError("layout value is not an exact object")
    return cast(dict[str, object], raw)


def _rehash_layout_root(wire: dict[str, object]) -> None:
    value = _value(wire)
    projection = dict(value)
    projection.pop("layout_root", None)
    value["layout_root"] = sha256_hex(
        domain_sep_bytes(_LAYOUT_ROOT_DOMAIN, version=1) + canonical_json_bytes(projection)
    )


def _mutate_collection(collection: str, operation: str) -> bytes:
    wire = _wire()
    value = _value(wire)
    rows_raw = value[collection]
    if type(rows_raw) is not list or not rows_raw:
        raise AssertionError(f"{collection} is not a nonempty list")
    rows = cast(list[object], rows_raw)

    if operation == "missing":
        rows.pop()
    elif operation == "extra":
        extra = copy.deepcopy(rows[-1])
        if type(extra) is dict and "sequence" in extra:
            extra["sequence"] = len(rows) + 1
        rows.append(extra)
    elif operation == "duplicate":
        rows.append(copy.deepcopy(rows[-1]))
    elif operation == "reordered":
        if len(rows) < 2:
            raise AssertionError(f"{collection} cannot be reordered")
        rows.reverse()
    else:
        raise AssertionError(f"unknown collection operation: {operation}")

    header = value["header"]
    if type(header) is not dict:
        raise AssertionError("layout header is not an exact object")
    header[_COUNT_FIELDS[collection]] = len(rows)
    _rehash_layout_root(wire)
    return cast(bytes, canonical_json_bytes(wire))


def _crossed_collection(collection: str) -> bytes:
    wire = _wire()
    value = _value(wire)
    rows = value[collection]
    if type(rows) is not list or not rows:
        raise AssertionError(f"{collection} is not a nonempty list")

    if collection == "authority_rows":
        authority = cast(list[object], rows)
        authority[0] = copy.deepcopy(authority[1])
    elif collection == "history_rows":
        history = cast(list[object], rows)
        evidence = value["evidence_rows"]
        if type(evidence) is not list:
            raise AssertionError("evidence rows are not a list")
        history[0] = copy.deepcopy(evidence[0])
    elif collection == "evidence_rows":
        evidence = cast(list[dict[str, object]], rows)
        evidence[0]["value_root"] = evidence[1]["value_root"]
    elif collection == "nullifier_rows":
        nullifier = cast(list[dict[str, object]], rows)[0]
        nested = nullifier["nullifier"]
        if type(nested) is not dict:
            raise AssertionError("nullifier body is not an object")
        history_rows_raw = value["history_rows"]
        if type(history_rows_raw) is not list:
            raise AssertionError("history rows are not a list")
        history_rows = cast(list[object], history_rows_raw)
        atom_bytes = history_rows[0]
        if type(atom_bytes) is not dict:
            raise AssertionError("history row is not an object")
        atom_text = atom_bytes["atom_bytes_utf8"]
        if type(atom_text) is not str:
            raise AssertionError("atom bytes are not text")
        atom_wire = json.loads(atom_text)
        atom_value = atom_wire["value"]
        if type(atom_value) is not dict:
            raise AssertionError("atom value is not an object")
        nested["nullifier_root"] = atom_value["anf_root"]
    elif collection == "outbox_rows":
        outbox = cast(list[dict[str, object]], rows)[0]
        record = outbox["record"]
        if type(record) is not dict:
            raise AssertionError("outbox record is not an object")
        history_rows_raw = value["history_rows"]
        if type(history_rows_raw) is not list:
            raise AssertionError("history rows are not a list")
        history_rows = cast(list[object], history_rows_raw)
        atom_row = history_rows[0]
        if type(atom_row) is not dict:
            raise AssertionError("history row is not an object")
        atom_wire = json.loads(cast(str, atom_row["atom_bytes_utf8"]))
        atom_value = atom_wire["value"]
        if type(atom_value) is not dict:
            raise AssertionError("atom value is not an object")
        record["effect_id"] = atom_value["commit_id"]
    elif collection == "ack_rows":
        ack = cast(list[dict[str, object]], rows)[0]
        ack["response_root"] = ack["payload_root"]
    else:
        raise AssertionError(f"unknown collection: {collection}")

    _rehash_layout_root(wire)
    return cast(bytes, canonical_json_bytes(wire))


def build_mutation_payloads() -> dict[str, bytes]:
    payloads: dict[str, bytes] = {}
    for collection in _ALL_COLLECTIONS:
        for operation in ("missing", "extra", "duplicate"):
            payloads[f"{collection}:{operation}"] = _mutate_collection(collection, operation)
        if collection in _MULTI_ROW_COLLECTIONS:
            payloads[f"{collection}:reordered"] = _mutate_collection(collection, "reordered")
        payloads[f"{collection}:crossed"] = _crossed_collection(collection)
    return payloads


def run_checks(*, check_vector: bool = True) -> dict[str, object]:
    layout = build_layout()
    valid = check_whole_layout_fixed_point(encode_layout_v1(layout))
    if type(valid) is not F04FixedPointSuccessV1:
        raise AssertionError("F04 rejected its canonical source layout")
    if valid.layout != layout or valid.canonical_layout_bytes != encode_layout_v1(layout):
        raise AssertionError("F04 success did not preserve the canonical layout")

    rejected: dict[str, str] = {}
    accepted_pending_ack: list[str] = []
    for name, payload in build_mutation_payloads().items():
        result = check_whole_layout_fixed_point(payload)
        if name == "ack_rows:missing":
            if type(result) is not F04FixedPointSuccessV1:
                raise AssertionError("F04 rejected a valid pending-delivery layout")
            accepted_pending_ack.append(name)
        else:
            if type(result) is not F04FixedPointRejectV1:
                raise AssertionError(f"F04 accepted invalid mutation: {name}")
            rejected[name] = result.code.value
    wrong_type = check_whole_layout_fixed_point(object())
    if type(wrong_type) is not F04FixedPointRejectV1:
        raise AssertionError("F04 accepted an untyped payload")
    if check_vector:
        expected = json.loads(VECTOR_PATH.read_text(encoding="utf-8"))
        if canonical_json_bytes(
            build_payload(rejected, accepted_pending_ack)
        ) != canonical_json_bytes(expected):
            raise SystemExit("FAIL: F04 fixed-point vector is stale")
    return build_payload(rejected, accepted_pending_ack)


def build_payload(
    rejected: dict[str, str] | None = None,
    accepted_pending_ack: list[str] | None = None,
) -> dict[str, object]:
    if rejected is None:
        rejected = {}
        for name, payload in build_mutation_payloads().items():
            result = check_whole_layout_fixed_point(payload)
            if name != "ack_rows:missing" and type(result) is F04FixedPointRejectV1:
                rejected[name] = result.code.value
    if accepted_pending_ack is None:
        accepted_pending_ack = ["ack_rows:missing"] if "ack_rows:missing" not in rejected else []
    layout = build_layout()
    return {
        "schema": FCIS_M6_F04_FIXED_POINT_SCHEMA_V1,
        "layout_root": layout.layout_root,
        "canonical_layout_bytes_utf8": encode_layout_v1(layout).decode("utf-8"),
        "mutation_count": len(rejected) + len(accepted_pending_ack),
        "accepted_pending_ack": accepted_pending_ack,
        "all_rejections_typed": True,
        "rejection_codes": rejected,
        "source_gate": "F03 partial reopen plus independent F02 re-materialization",
    }


def main() -> None:
    result = run_checks()
    print("F04_FIXED_POINT_CHECKS_PASS", result["layout_root"])


if __name__ == "__main__":
    main()
