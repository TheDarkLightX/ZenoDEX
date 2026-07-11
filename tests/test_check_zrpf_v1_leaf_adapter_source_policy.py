from __future__ import annotations

import copy
import hashlib
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


def test_source_policy_rejects_historical_anchor_substitution(tmp_path: Path) -> None:
    policy = copy.deepcopy(_policy())
    anchor_path = tmp_path / "config/proof_profiles/zrpf_v1_retained_source_anchor_v1.json"
    anchor_path.parent.mkdir(parents=True)
    source_anchor = checker.REPO_ROOT / policy["source_reference"]["path"]
    anchor = source_anchor.read_text(encoding="utf-8").replace(
        checker.HISTORICAL_REFERENCE_COMMIT,
        "0" * 40,
    )
    anchor_path.write_text(anchor, encoding="utf-8")
    policy["source_reference"]["sha256"] = hashlib.sha256(
        anchor.encode("utf-8")
    ).hexdigest()

    report = checker.validate_policy(policy, repo_root=tmp_path)

    assert report["ok"] is False
    assert "historical source reference identity mismatch" in report["errors"]


def test_loader_rejects_duplicate_keys(tmp_path: Path) -> None:
    policy = tmp_path / "policy.json"
    policy.write_text('{"schema":"a","schema":"b"}', encoding="utf-8")

    loaded, errors = checker.load_policy(policy)

    assert loaded is None
    assert errors == ["policy JSON rejected: duplicate JSON key: schema"]
