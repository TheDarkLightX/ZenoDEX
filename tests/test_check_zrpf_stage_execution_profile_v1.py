from __future__ import annotations

import copy
import hashlib
import json
from pathlib import Path
from typing import Any

import pytest

from tools import check_zrpf_stage_execution_profile_v1 as checker

CPU_PROFILE = "risc0_ipc_cpu_v1"


def _artifact(raw: bytes) -> dict[str, object]:
    return {"sha256": hashlib.sha256(raw).hexdigest(), "size_bytes": len(raw)}


def _position_distinct_bytes(length: int, multiplier: int, offset: int) -> bytes:
    raw = bytes(((ordinal * multiplier + offset) % 251) for ordinal in range(length))
    assert raw != raw[::-1]
    return raw


def _fixture(tmp_path: Path) -> tuple[dict[str, Any], dict[str, Path]]:
    tmp_path.mkdir(parents=True, exist_ok=True)
    raw = {
        "program": b"\x7fELF" + _position_distinct_bytes(599, 73, 19),
        "guest_input": _position_distinct_bytes(947, 41, 7),
        "assumption": _position_distinct_bytes(1223, 37, 23),
        "r0vm": b"\x7fELF" + _position_distinct_bytes(1603, 29, 31),
        "journal": _position_distinct_bytes(431, 17, 11),
    }
    paths: dict[str, Path] = {}
    for role in ("program", "guest_input", "assumption", "r0vm"):
        path = tmp_path / role
        path.write_bytes(raw[role])
        paths[role] = path
    paths["r0vm"].chmod(0o755)
    journal = _artifact(raw["journal"])
    document: dict[str, Any] = {
        "schema": checker.SCHEMA,
        "status": checker.STATUS,
        "profile_record_id": checker.ZERO_SHA256,
        "stage_id": "spot_settlement_v7",
        "proof_profile_id": checker.PROOF_PROFILE,
        "prover_compute_profile_id": CPU_PROFILE,
        "program": {
            "artifact": _artifact(raw["program"]),
            "image_id": "12" * 32,
        },
        "r0vm": _artifact(raw["r0vm"]),
        "guest_input": _artifact(raw["guest_input"]),
        "assumptions": [
            {
                "ordinal": 0,
                "receipt": _artifact(raw["assumption"]),
                "expected_image_id": "23" * 32,
                "journal_sha256": "34" * 32,
                "journal_bytes": 509,
            }
        ],
        "expected_journal": journal,
        "observed_journal": copy.deepcopy(journal),
        "receipt_claim_sha256": "45" * 32,
        "segment_limit_po2": 20,
        "segments": [
            {
                "ordinal": 0,
                "po2": 19,
                "user_cycles": 345_679,
                "padded_cycle_capacity": 1 << 19,
            },
            {
                "ordinal": 1,
                "po2": 20,
                "user_cycles": 456_791,
                "padded_cycle_capacity": 1 << 20,
            },
        ],
        "segment_count": 2,
        "total_user_cycles": 802_470,
        "total_padded_cycle_capacity": (1 << 19) + (1 << 20),
        "exit_system": 0,
        "exit_user": 0,
        "duration_milliseconds": 137,
        "authority": {field: False for field in checker.AUTHORITY_FIELDS},
        "non_claims": list(checker.NON_CLAIMS),
    }
    document["profile_record_id"] = checker._derive_record_id(document)
    paths["profile"] = tmp_path / "profile.json"
    paths["profile"].write_bytes(checker._canonical_bytes(document))
    return document, paths


def _check(paths: dict[str, Path]) -> dict[str, object]:
    return checker.check_profile(
        paths["profile"],
        paths["program"],
        paths["guest_input"],
        [paths["assumption"]],
        paths["r0vm"],
        expected_stage="spot_settlement_v7",
        expected_compute_profile=CPU_PROFILE,
    )


def _rewrite(paths: dict[str, Path], document: dict[str, Any]) -> None:
    document["profile_record_id"] = checker._derive_record_id(document)
    paths["profile"].write_bytes(checker._canonical_bytes(document))


def test_position_distinct_profile_binds_every_acceptance_artifact(tmp_path: Path) -> None:
    document, paths = _fixture(tmp_path)

    assert _check(paths) == document

    paths["program"].write_bytes(paths["program"].read_bytes()[:-1] + b"\xff")
    with pytest.raises(checker.ProfileCheckError, match="program bytes differ"):
        _check(paths)


def test_segment_order_and_totals_remain_active_after_reanchoring(tmp_path: Path) -> None:
    document, paths = _fixture(tmp_path)
    document["segments"].reverse()
    _rewrite(paths, document)

    with pytest.raises(checker.ProfileCheckError, match="segment ordering"):
        _check(paths)


def test_authority_and_compute_profile_substitution_reject(tmp_path: Path) -> None:
    document, paths = _fixture(tmp_path)
    document["authority"]["proof_generated"] = True
    _rewrite(paths, document)
    with pytest.raises(checker.ProfileCheckError, match="authority"):
        _check(paths)

    document, paths = _fixture(tmp_path / "compute")
    with pytest.raises(checker.ProfileCheckError, match="compute profile"):
        checker.check_profile(
            paths["profile"],
            paths["program"],
            paths["guest_input"],
            [paths["assumption"]],
            paths["r0vm"],
            expected_stage="spot_settlement_v7",
            expected_compute_profile=(
                "risc0_ipc_cuda_single_visible_device_build_request_v1"
            ),
        )


def test_integer_boolean_float_integer_and_reordered_fields_reject(tmp_path: Path) -> None:
    document, paths = _fixture(tmp_path)
    document["authority"]["proof_generated"] = 0
    paths["profile"].write_bytes(checker._canonical_bytes(document))
    with pytest.raises(checker.ProfileCheckError, match="authority"):
        _check(paths)

    document, paths = _fixture(tmp_path / "boolean-ordinal")
    document["segments"][0]["ordinal"] = False
    _rewrite(paths, document)
    with pytest.raises(checker.ProfileCheckError, match="segment ordinal"):
        _check(paths)

    document, paths = _fixture(tmp_path / "boolean-exit")
    document["exit_system"] = False
    _rewrite(paths, document)
    with pytest.raises(checker.ProfileCheckError, match="exit system"):
        _check(paths)

    document, paths = _fixture(tmp_path / "float")
    document["duration_milliseconds"] = 1.5
    paths["profile"].write_bytes(
        json.dumps(document, separators=(",", ":")).encode("utf-8")
    )
    with pytest.raises(checker.ProfileCheckError, match="JSON decode"):
        _check(paths)

    document, paths = _fixture(tmp_path / "order")
    reordered = {"status": document["status"], "schema": document["schema"]}
    reordered.update({key: value for key, value in document.items() if key not in reordered})
    reordered["profile_record_id"] = checker._derive_record_id(reordered)
    paths["profile"].write_bytes(checker._canonical_bytes(reordered))
    with pytest.raises(checker.ProfileCheckError, match="field order"):
        _check(paths)
