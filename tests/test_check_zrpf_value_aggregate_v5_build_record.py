from __future__ import annotations

import copy
import hashlib
import json
from pathlib import Path

import pytest

from tools import check_zrpf_value_aggregate_v5_build_record as checker


def test_committed_build_record_is_strictly_accepted() -> None:
    report = checker.check_record()

    assert report == {
        "ok": True,
        "schema": "zenodex/zrpf_value_aggregate_v5_program_build_check/v1",
        "record_sha256": checker.EXPECTED_RECORD_SHA256,
        "level_one_image_id": checker.EXPECTED_L1_IMAGE,
        "level_two_image_id": checker.EXPECTED_L2_IMAGE,
        "artifact_bytes_rechecked": False,
        "proofs_generated": False,
        "production_authority": False,
    }


@pytest.mark.parametrize(
    "raw",
    [
        b'{"schema":"a","schema":"b"}\n',
        b'{"schema":1.0}\n',
        b'{"schema":NaN}\n',
    ],
)
def test_loader_rejects_ambiguous_or_floating_json(tmp_path: Path, raw: bytes) -> None:
    path = tmp_path / "record.json"
    path.write_bytes(raw)

    with pytest.raises(checker.RecordError):
        checker.load_record(path)


def test_loader_rejects_equivalent_noncanonical_bytes(tmp_path: Path) -> None:
    document, _ = checker.load_record(checker.DEFAULT_RECORD)
    path = tmp_path / "record.json"
    path.write_text(json.dumps(document), encoding="utf-8")

    with pytest.raises(checker.RecordError, match="noncanonical"):
        checker.load_record(path)


@pytest.mark.parametrize(
    ("mutation", "message"),
    [
        (
            lambda value: value["claims"].__setitem__("production_authority", True),
            "claims.production_authority must be exactly False",
        ),
        (
            lambda value: value["level_two"].__setitem__(
                "pinned_level_one_image_id", "00" * 32
            ),
            "L2 pinned L1 image mismatch",
        ),
        (
            lambda value: value["level_one"].__setitem__("unreviewed", True),
            "level_one field set mismatch",
        ),
    ],
)
def test_validator_rejects_claim_identity_and_schema_mutations(
    mutation,
    message: str,
) -> None:
    document, _ = checker.load_record(checker.DEFAULT_RECORD)
    changed = copy.deepcopy(document)
    mutation(changed)
    raw = checker.canonical_bytes(changed)

    with pytest.raises(checker.RecordError, match=message):
        checker.validate_record(changed, raw, require_anchor=False)


def test_governed_anchor_rejects_coherent_record_byte_change() -> None:
    document, _ = checker.load_record(checker.DEFAULT_RECORD)
    changed = copy.deepcopy(document)
    changed["recorded_at"] = "2026-07-13"
    raw = checker.canonical_bytes(changed)
    assert hashlib.sha256(raw).hexdigest() != checker.EXPECTED_RECORD_SHA256

    with pytest.raises(checker.RecordError, match="governed anchor"):
        checker.validate_record(changed, raw)
