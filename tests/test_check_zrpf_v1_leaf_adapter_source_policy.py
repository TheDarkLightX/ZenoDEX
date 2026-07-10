from __future__ import annotations

import copy
from pathlib import Path

from tools import check_zrpf_v1_leaf_adapter_source_policy as checker


def _policy() -> dict:
    policy, errors = checker.load_policy()
    assert errors == []
    assert isinstance(policy, dict)
    return policy


def test_default_source_policy_matches_reference_and_rust_constants() -> None:
    report = checker.validate_policy(_policy())

    assert report["ok"] is True
    assert report["facts"] == {
        "source_count": 1,
        "receipt_authority": False,
        "status": "compatibility_mapping_only",
    }


def test_source_policy_rejects_reference_image_substitution() -> None:
    policy = _policy()
    policy["sources"][0]["image_id_words"][0] ^= 1

    report = checker.validate_policy(policy)

    assert report["ok"] is False
    assert "spot image words do not encode image_id" in report["errors"]
    assert "spot image_id_words differs from source reference" in report["errors"]


def test_source_policy_rejects_unknown_fields() -> None:
    policy = _policy()
    policy["sources"][0]["unreviewed_image"] = "00" * 32

    report = checker.validate_policy(policy)

    assert report["ok"] is False
    assert "sources[0] has unknown fields: unreviewed_image" in report["errors"]


def test_source_policy_rejects_receipt_authority_promotion() -> None:
    policy = copy.deepcopy(_policy())
    policy["receipt_authority"] = True

    report = checker.validate_policy(policy)

    assert report["ok"] is False
    assert "pure mapping must deny receipt authority" in report["errors"]


def test_loader_rejects_duplicate_keys(tmp_path: Path) -> None:
    policy = tmp_path / "policy.json"
    policy.write_text('{"schema":"a","schema":"b"}', encoding="utf-8")

    loaded, errors = checker.load_policy(policy)

    assert loaded is None
    assert errors == ["policy JSON rejected: duplicate JSON key: schema"]
