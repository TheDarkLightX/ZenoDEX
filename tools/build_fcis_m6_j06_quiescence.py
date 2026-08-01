"""Build the source-bound FCIS M6 J06 quiescence vector."""

from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any, cast

_ROOT = Path(__file__).resolve().parents[1]
if str(_ROOT) not in sys.path:
    sys.path.insert(0, str(_ROOT))

from src.core import fcis_durable_retraction as dra  # noqa: E402
from src.core.fcis_m6_j06_quiescence import (  # noqa: E402
    FCIS_M6_J06_SCHEMA_V1,
    J06_QUIESCENCE_MARKERS_V1,
    J06_REQUIRED_WRITER_IDS_V1,
    J06Error,
    J06QuiescenceGateV1,
    quiescence_payload_v1,
    quiescence_root_from_body_v1,
)
from src.state.canonical import canonical_json_bytes  # noqa: E402
from tools.build_fcis_m6_k01_entrypoint_inventory import (  # noqa: E402
    DEFAULT_CONFIG_PATH as K01_CONFIG_PATH,
)
from tools.build_fcis_m6_k01_entrypoint_inventory import (  # noqa: E402
    build_payload as build_k01_payload,
)
from tools.check_fcis_m6_j02_writer_matrix import check_writer_matrix  # noqa: E402
from tools.check_fcis_m6_j04_migration_manifest import check_manifest  # noqa: E402

DEFAULT_CONFIG_PATH = Path("config/deploy/fcis_m6_j06_quiescence_v1.json")
DEFAULT_OUTPUT_PATH = Path("docs/research/m6_tasks/TASK_J06_QUIESCENCE_GATE_V1.json")
J06_CONFIG_SCHEMA_V1 = "zenodex/fcis/m6/j06/quiescence-gate-config/v1"
J04_MANIFEST_PATH = Path("docs/research/m6_tasks/TASK_J04_MIGRATION_MANIFEST_V1.json")


class _DuplicateJsonKey(ValueError):
    pass


def _strict_object(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise _DuplicateJsonKey(key)
        result[key] = value
    return result


def _load_json(path: Path) -> dict[str, object]:
    try:
        value = json.loads(
            path.read_text(encoding="utf-8"),
            object_pairs_hook=_strict_object,
        )
    except (OSError, UnicodeError, json.JSONDecodeError, _DuplicateJsonKey) as exc:
        raise J06Error(f"strict JSON load failed for {path}") from exc
    if type(value) is not dict:
        raise J06Error(f"JSON root is not an object: {path}")
    return cast(dict[str, object], value)


def _text(value: object, name: str, *, maximum_bytes: int = 2048) -> str:
    if type(value) is not str or not value:
        raise J06Error(f"{name} must be a nonempty exact string")
    if len(value.encode("utf-8")) > maximum_bytes:
        raise J06Error(f"{name} exceeds its byte bound")
    return value


def _digest(value: object, name: str) -> str:
    checked = _text(value, name, maximum_bytes=64)
    if len(checked) != 64 or any(character not in "0123456789abcdef" for character in checked):
        raise J06Error(f"{name} must be a lowercase SHA-256 digest")
    return checked


def _u32(value: object, name: str, *, positive: bool = False) -> int:
    if type(value) is not int or value < (1 if positive else 0) or value > (1 << 32) - 1:
        raise J06Error(f"{name} is outside its closed u32 bound")
    return value


def _strings(
    value: object, name: str, *, expected: tuple[str, ...] | None = None
) -> tuple[str, ...]:
    if type(value) is not list or not value:
        raise J06Error(f"{name} must be a nonempty list")
    values = tuple(_text(item, f"{name}[{index}]") for index, item in enumerate(value))
    if len(set(values)) != len(values):
        raise J06Error(f"{name} contains duplicates")
    if expected is not None and values != expected:
        raise J06Error(f"{name} does not match the exact expected ordered set")
    return values


def _load_config(path: Path) -> dict[str, object]:
    raw = _load_json(path)
    expected = {
        "schema",
        "profile_id",
        "expected_j04_manifest_root",
        "expected_k01_entrypoint_inventory_root",
        "expected_quiesced_epoch",
        "expected_quiesced_authority_root",
        "activation_sequence",
        "expected_current_head_root",
        "expected_replay_head_root",
        "required_writer_ids",
        "evidence_markers",
        "pinned_quiescence_root",
        "nonclaims",
    }
    if set(raw) != expected:
        raise J06Error("J06 configuration fields are not exact")
    if raw["schema"] != J06_CONFIG_SCHEMA_V1:
        raise J06Error("J06 configuration schema is wrong")
    _text(raw["profile_id"], "profile_id")
    for name in (
        "expected_j04_manifest_root",
        "expected_k01_entrypoint_inventory_root",
        "expected_quiesced_authority_root",
        "expected_current_head_root",
        "expected_replay_head_root",
        "pinned_quiescence_root",
    ):
        _digest(raw[name], name)
    _u32(raw["expected_quiesced_epoch"], "expected_quiesced_epoch")
    _u32(raw["activation_sequence"], "activation_sequence", positive=True)
    _strings(raw["required_writer_ids"], "required_writer_ids", expected=J06_REQUIRED_WRITER_IDS_V1)
    _strings(raw["evidence_markers"], "evidence_markers", expected=J06_QUIESCENCE_MARKERS_V1)
    nonclaims = raw["nonclaims"]
    if (
        type(nonclaims) is not list
        or not nonclaims
        or any(type(item) is not str for item in nonclaims)
    ):
        raise J06Error("nonclaims must be a nonempty string list")
    return raw


def _quiesced_authority() -> dra.AuthorityStateV1:
    check_writer_matrix()
    phases = tuple(dra.MigrationPhaseV1)
    authority = dra.initial_authority_state(
        dra.tagged_digest("j02/legacy-profile"),
        dra.tagged_digest("j02/target-profile"),
    )
    for index, phase in enumerate(phases[1:], start=1):
        authority = dra.advance_authority_state(
            authority,
            phase,
            dra.tagged_digest(f"j02/transport/{index}"),
        )
        if phase is dra.MigrationPhaseV1.QUIESCED:
            return authority
    raise J06Error("J02 trace did not produce QUIESCED")


def _in_scope_writer_ids(k01_payload: dict[str, object]) -> tuple[str, ...]:
    raw_rows = k01_payload.get("entrypoints")
    if type(raw_rows) is not list:
        raise J06Error("K01 entrypoints are not a list")
    values: list[str] = []
    for index, raw_row in enumerate(raw_rows):
        if type(raw_row) is not dict:
            raise J06Error(f"K01 entrypoint row {index} is not an object")
        row = cast(dict[str, Any], raw_row)
        publisher_id = _text(row.get("publisher_id"), f"K01 entrypoints[{index}].publisher_id")
        if row.get("value_moving") is True and row.get("legacy_status") != "outside_m6_scope":
            values.append(publisher_id)
    result = tuple(sorted(set(values), key=lambda item: item.encode("utf-8")))
    if result != J06_REQUIRED_WRITER_IDS_V1:
        raise J06Error("K01 in-scope value-moving writer set differs from the J06 pin")
    return result


def derive_payload(config_path: Path = _ROOT / DEFAULT_CONFIG_PATH) -> dict[str, object]:
    """Derive J06 while checking the J02, J04, and K01 dependency pins."""

    config = _load_config(config_path.resolve())
    manifest_path = _ROOT / J04_MANIFEST_PATH
    check_manifest(manifest_path)
    manifest = _load_json(manifest_path)
    manifest_root = _digest(manifest.get("manifest_root"), "J04 manifest_root")
    if manifest_root != config["expected_j04_manifest_root"]:
        raise J06Error("J04 manifest root differs from the J06 pin")
    activation_sequence = _u32(
        manifest.get("activation_sequence"), "J04 activation_sequence", positive=True
    )
    if activation_sequence != config["activation_sequence"]:
        raise J06Error("J04 activation sequence differs from the J06 pin")
    manifest_markers = _strings(manifest.get("quiescence_evidence"), "J04 quiescence_evidence")
    if not set(J06_QUIESCENCE_MARKERS_V1).issubset(manifest_markers):
        raise J06Error("J04 quiescence evidence omits a required marker")

    k01 = build_k01_payload(_ROOT / K01_CONFIG_PATH)
    inventory_root = _digest(k01.get("entrypoint_inventory_root"), "K01 entrypoint_inventory_root")
    if inventory_root != config["expected_k01_entrypoint_inventory_root"]:
        raise J06Error("K01 inventory root differs from the J06 pin")
    writer_ids = _in_scope_writer_ids(k01)

    authority = _quiesced_authority()
    expected_epoch = _u32(config["expected_quiesced_epoch"], "expected_quiesced_epoch")
    expected_authority_root = _digest(
        config["expected_quiesced_authority_root"],
        "expected_quiesced_authority_root",
    )
    if authority.epoch_index != expected_epoch or authority.root != expected_authority_root:
        raise J06Error("J02 QUIESCED authority differs from the J06 pin")

    current_head_root = _digest(config["expected_current_head_root"], "expected_current_head_root")
    replay_head_root = _digest(config["expected_replay_head_root"], "expected_replay_head_root")
    body = {
        "manifest_root": manifest_root,
        "entrypoint_inventory_root": inventory_root,
        "phase": authority.phase.value,
        "activation_sequence": activation_sequence,
        "authority_epoch_index": authority.epoch_index,
        "authority_state_root": authority.root,
        "current_head_root": current_head_root,
        "replay_head_root": replay_head_root,
        "covered_writer_ids": list(writer_ids),
        "evidence_markers": list(J06_QUIESCENCE_MARKERS_V1),
    }
    gate = J06QuiescenceGateV1(
        manifest_root=manifest_root,
        entrypoint_inventory_root=inventory_root,
        phase=authority.phase,
        activation_sequence=activation_sequence,
        authority_epoch_index=authority.epoch_index,
        authority_state_root=authority.root,
        current_head_root=current_head_root,
        replay_head_root=replay_head_root,
        covered_writer_ids=writer_ids,
        evidence_markers=J06_QUIESCENCE_MARKERS_V1,
        quiescence_root=quiescence_root_from_body_v1(body),
    )
    config_pin = _digest(config["pinned_quiescence_root"], "pinned_quiescence_root")
    return {
        **quiescence_payload_v1(gate),
        "profile_id": _text(config["profile_id"], "profile_id"),
        "pinned_quiescence_root": config_pin,
        "nonclaims": cast(list[str], config["nonclaims"]),
    }


def build_payload(config_path: Path = _ROOT / DEFAULT_CONFIG_PATH) -> dict[str, object]:
    """Derive J06 and require the pinned root after configuration is complete."""

    config = _load_config(config_path.resolve())
    payload = derive_payload(config_path)
    if payload["quiescence_root"] != config["pinned_quiescence_root"]:
        raise J06Error("derived J06 root differs from the pinned root")
    if payload["schema"] != FCIS_M6_J06_SCHEMA_V1:
        raise J06Error("J06 output schema is wrong")
    return payload


def main(argv: list[str] | None = None) -> int:
    args = list(argv or sys.argv[1:])
    config = _ROOT / DEFAULT_CONFIG_PATH
    output = _ROOT / DEFAULT_OUTPUT_PATH
    check = False
    print_derived = False
    index = 0
    while index < len(args):
        token = args[index]
        if token == "--check":
            check = True
        elif token == "--print-derived":
            print_derived = True
        elif token == "--config" and index + 1 < len(args):
            index += 1
            candidate = Path(args[index])
            config = candidate if candidate.is_absolute() else _ROOT / candidate
        elif token == "--output" and index + 1 < len(args):
            index += 1
            candidate = Path(args[index])
            output = candidate if candidate.is_absolute() else _ROOT / candidate
        else:
            raise SystemExit(f"unknown or incomplete argument: {token}")
        index += 1
    payload = derive_payload(config) if print_derived else build_payload(config)
    if print_derived:
        print("J06_DERIVED_QUIESCENCE_ROOT", payload["quiescence_root"])
        return 0
    encoded = canonical_json_bytes(payload) + b"\n"
    if check:
        if output.read_bytes() != encoded:
            raise SystemExit("FAIL: J06 quiescence vector is stale")
    else:
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_bytes(encoded)
    print("J06_QUIESCENCE_MATCH", payload["quiescence_root"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
