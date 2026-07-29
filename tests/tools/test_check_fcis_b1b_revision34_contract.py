from __future__ import annotations

import shutil
from pathlib import Path

from tools.check_fcis_b1b_revision34_contract import (
    REVISION_PATH,
    RUST_PATH,
    check_repository,
)

REPO = Path(__file__).resolve().parents[2]


def _copy(tmp_path: Path) -> Path:
    target = tmp_path / "repo"
    shutil.copytree(REPO, target)
    return target


def _codes(root: Path) -> set[str]:
    return {finding.code for finding in check_repository(root).findings}


def test_revision34_contract_is_green() -> None:
    report = check_repository(REPO)
    assert report.ok, report.findings


def test_deleting_b1a_validation_is_detected(tmp_path: Path) -> None:
    root = _copy(tmp_path)
    path = root / REVISION_PATH
    text = path.read_text(encoding="utf-8").replace(
        "call validate_fee_distribution_configuration_claim_v2",
        "skip semantic validator",
        1,
    )
    path.write_text(text, encoding="utf-8")
    assert "REV34_PIPELINE_MISSING" in _codes(root)


def test_receipt_inside_evaluation_candidate_is_detected(tmp_path: Path) -> None:
    root = _copy(tmp_path)
    path = root / REVISION_PATH
    text = path.read_text(encoding="utf-8").replace(
        "    replay_update,\n    transition_cause,",
        "    replay_update,\n    receipt,\n    transition_cause,",
        1,
    )
    path.write_text(text, encoding="utf-8")
    assert "REV34_RECEIPT_CYCLE" in _codes(root)


def test_downstream_hash_inside_cause_is_detected(tmp_path: Path) -> None:
    root = _copy(tmp_path)
    path = root / REVISION_PATH
    text = path.read_text(encoding="utf-8").replace(
        "    transition_kind,\n)",
        "    transition_kind,\n    decision_hash,\n)",
        1,
    )
    path.write_text(text, encoding="utf-8")
    assert "REV34_CAUSE_DOWNSTREAM_HASH" in _codes(root)


def test_premature_authority_type_is_detected(tmp_path: Path) -> None:
    root = _copy(tmp_path)
    path = root / "src/core/fcis_b1b_authority_values.py"
    path.write_text(
        path.read_text(encoding="utf-8")
        + "\nclass PinnedDeploymentBootstrapVerifierV2:\n    pass\n",
        encoding="utf-8",
    )
    assert "B1B1_PREMATURE_AUTHORITY" in _codes(root)


def test_bare_header_update_function_is_detected(tmp_path: Path) -> None:
    root = _copy(tmp_path)
    path = root / "src/core/fcis_b1b_authority_values.py"
    path.write_text(
        path.read_text(encoding="utf-8")
        + "\ndef update_authority_header_v2(pre_header):\n    return pre_header\n",
        encoding="utf-8",
    )
    assert "B1B1_BARE_HEADER_TRANSITION" in _codes(root)


def test_missing_rust_carrier_is_detected(tmp_path: Path) -> None:
    root = _copy(tmp_path)
    path = root / RUST_PATH
    text = path.read_text(encoding="utf-8").replace(
        "pub struct V1ToV2MigrationManifestV2",
        "struct V1ToV2MigrationManifestV2",
        1,
    )
    path.write_text(text, encoding="utf-8")
    assert "B1B1_RUST_GAP" in _codes(root)
