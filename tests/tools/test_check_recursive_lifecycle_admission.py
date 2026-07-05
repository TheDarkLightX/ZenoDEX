from __future__ import annotations

import copy
import hashlib
import json
from pathlib import Path
from typing import Any, Callable

import pytest

from tools.check_recursive_lifecycle_admission import (
    HEADER_BOUND_ROOT_FIELDS,
    PACKET_SCHEMA,
    PROOF_PROFILE_RECURSIVE,
    PROOF_TYPE_RECURSIVE,
    ZERO32,
    _asset_delta_root,
    main,
    validate_recursive_lifecycle_admission_packet_v1,
)


def _hex32(label: str) -> str:
    return hashlib.sha256(label.encode("utf-8")).hexdigest()


def _valid_rows(authority_root: str) -> list[dict[str, Any]]:
    return [
        {
            "asset_id": "USDC",
            "debit_atoms": 100,
            "credit_atoms": 100,
            "authorized_mint_atoms": 0,
            "authorized_burn_atoms": 0,
            "authority_root": ZERO32,
        },
        {
            "asset_id": "zUSD",
            "debit_atoms": 0,
            "credit_atoms": 50,
            "authorized_mint_atoms": 50,
            "authorized_burn_atoms": 0,
            "authority_root": authority_root,
        },
    ]


def _valid_packet() -> dict[str, Any]:
    authority_root = _hex32("zUSD mint authority")
    rows = _valid_rows(authority_root)
    root_errors: list[str] = []
    aggregate_asset_delta_root = _asset_delta_root(rows, root_errors)
    assert root_errors == []
    assert aggregate_asset_delta_root is not None

    bound_roots = {field: _hex32(field) for field in HEADER_BOUND_ROOT_FIELDS}
    bound_roots["aggregate_asset_delta_root"] = aggregate_asset_delta_root
    transcript_hash = _hex32("recursive transcript")

    return {
        "schema": PACKET_SCHEMA,
        "proof_requested": True,
        "proof_verified": True,
        "proof_type": PROOF_TYPE_RECURSIVE,
        "proof_profile": PROOF_PROFILE_RECURSIVE,
        "unsupported_lifecycle_absent": True,
        "transcript_binding_hash": transcript_hash,
        "expected_transcript_binding_hash": transcript_hash,
        "allowed_authority_roots": [authority_root],
        "asset_delta_rows": rows,
        "proof_meta": {
            **bound_roots,
            "child_count": 2,
        },
        "header": bound_roots,
    }


def _set_path(packet: dict[str, Any], path: tuple[Any, ...], value: Any) -> None:
    target: Any = packet
    for part in path[:-1]:
        target = target[part]
    target[path[-1]] = value


def _reverse_rows(packet: dict[str, Any]) -> None:
    packet["asset_delta_rows"] = list(reversed(packet["asset_delta_rows"]))


_MUTATORS: dict[str, Callable[[dict[str, Any]], None]] = {
    "proof_not_verified": lambda packet: _set_path(packet, ("proof_verified",), False),
    "unsupported_profile": lambda packet: _set_path(packet, ("proof_profile",), "leaf_epoch_v1"),
    "row_root_drift": lambda packet: _set_path(
        packet,
        ("proof_meta", "aggregate_asset_delta_root"),
        _hex32("wrong aggregate root"),
    ),
    "unbalanced_row": lambda packet: _set_path(packet, ("asset_delta_rows", 1, "credit_atoms"), 49),
    "unauthorized_authority": lambda packet: _set_path(
        packet,
        ("allowed_authority_roots",),
        [_hex32("different authority")],
    ),
    "unexpected_authority": lambda packet: _set_path(
        packet,
        ("asset_delta_rows", 0, "authority_root"),
        _hex32("unexpected authority"),
    ),
    "header_binding_drift": lambda packet: _set_path(
        packet,
        ("header", "post_state_root"),
        _hex32("different post state root"),
    ),
    "transcript_drift": lambda packet: _set_path(
        packet,
        ("expected_transcript_binding_hash",),
        _hex32("different transcript"),
    ),
    "unsorted_rows": _reverse_rows,
    "zero_child_count": lambda packet: _set_path(packet, ("proof_meta", "child_count"), 0),
}


def _mutated_packet(mutate: str) -> dict[str, Any]:
    packet = copy.deepcopy(_valid_packet())
    _MUTATORS[mutate](packet)
    return packet


def test_valid_recursive_lifecycle_packet_accepts_and_exports_tau_inputs() -> None:
    report = validate_recursive_lifecycle_admission_packet_v1(_valid_packet())

    assert report["ok"] is True
    assert report["status"] == "accepted"
    assert report["errors"] == []
    assert report["row_count"] == 2
    assert report["computed_aggregate_asset_delta_root"] == report["expected_aggregate_asset_delta_root"]
    assert report["tau_inputs"] == {
        "proof_requested": True,
        "proof_verified": True,
        "proof_profile_supported": True,
        "leaf_rows_derived": True,
        "asset_delta_root_bound": True,
        "aggregate_rows_balanced": True,
        "authority_roots_allowed": True,
        "unsupported_lifecycle_absent": True,
        "tau_header_binding_ok": True,
        "transcript_binding_ok": True,
    }


@pytest.mark.parametrize(
    ("mutate", "expected_error"),
    [
        ("proof_not_verified", "proof_verified must be true"),
        ("unsupported_profile", "proof profile unsupported"),
        ("row_root_drift", "asset_delta_root binding mismatch"),
        ("unbalanced_row", "aggregate row unbalanced: zUSD"),
        ("unauthorized_authority", "asset authority root not allowed: zUSD"),
        ("unexpected_authority", "asset authority root unexpected: USDC"),
        ("header_binding_drift", "header binding mismatch: post_state_root"),
        ("transcript_drift", "transcript binding mismatch"),
        ("unsorted_rows", "asset_delta_rows must be sorted by unique asset_id"),
        ("zero_child_count", "proof_meta.child_count must be a positive integer"),
    ],
)
def test_recursive_lifecycle_packet_rejects_boundary_mutations(
    mutate: str,
    expected_error: str,
) -> None:
    report = validate_recursive_lifecycle_admission_packet_v1(_mutated_packet(mutate))

    assert report["ok"] is False
    assert report["status"] == "rejected"
    assert expected_error in report["errors"]


def test_recursive_lifecycle_packet_rejects_duplicate_rows() -> None:
    packet = _valid_packet()
    packet["asset_delta_rows"][1]["asset_id"] = packet["asset_delta_rows"][0]["asset_id"]

    report = validate_recursive_lifecycle_admission_packet_v1(packet)

    assert report["ok"] is False
    assert "asset_delta_rows must be sorted by unique asset_id" in report["errors"]


def test_recursive_lifecycle_packet_rejects_u128_overflow() -> None:
    packet = _valid_packet()
    packet["asset_delta_rows"][0]["debit_atoms"] = str(1 << 128)

    report = validate_recursive_lifecycle_admission_packet_v1(packet)

    assert report["ok"] is False
    assert "asset_delta_rows[0].debit_atoms out of u128 range" in report["errors"]


def test_recursive_lifecycle_admission_cli_accepts_valid_packet(tmp_path: Path, capsys: Any) -> None:
    packet_path = tmp_path / "packet.json"
    packet_path.write_text(json.dumps(_valid_packet(), indent=2, sort_keys=True), encoding="utf-8")

    code = main([str(packet_path)])
    out = capsys.readouterr().out
    report = json.loads(out)

    assert code == 0
    assert report["ok"] is True
    assert report["status"] == "accepted"


def test_recursive_lifecycle_admission_cli_rejects_invalid_packet(tmp_path: Path, capsys: Any) -> None:
    packet_path = tmp_path / "packet.json"
    packet_path.write_text(
        json.dumps(_mutated_packet("transcript_drift"), indent=2, sort_keys=True),
        encoding="utf-8",
    )

    code = main([str(packet_path)])
    out = capsys.readouterr().out
    report = json.loads(out)

    assert code == 1
    assert report["ok"] is False
    assert "transcript binding mismatch" in report["errors"]
