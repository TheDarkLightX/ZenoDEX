from __future__ import annotations

import json
import shutil
from pathlib import Path

from tools.check_zenocover_lp_loss_cover import (
    DEFAULT_BUNDLE_DIR,
    main,
    validate_zenocover_lp_loss_cover_bundle,
)


def test_zenocover_lp_loss_cover_checker_accepts_checked_in_bundle() -> None:
    report = validate_zenocover_lp_loss_cover_bundle(DEFAULT_BUNDLE_DIR)

    assert report["ok"] is True
    assert report["status"] == "accepted"
    assert report["artifact_upper"] == 80
    assert report["proof_tree_evidence_floor"] == "implemented"
    assert report["settlement"]["holder_delta"] == 30
    assert report["settlement"]["writer_delta"] == -30
    assert report["settlement"]["delta_conservation"] is True
    assert report["settlement"]["writer_posted"] == report["settlement"]["writer_collateral_required"]


def test_zenocover_lp_loss_cover_checker_rejects_expected_hash_mismatch() -> None:
    report = validate_zenocover_lp_loss_cover_bundle(
        DEFAULT_BUNDLE_DIR,
        expected_bundle_hash="sha256:" + ("0" * 64),
    )

    assert report["ok"] is False
    assert report["errors"] == ["expected_bundle_hash_mismatch"]


def test_zenocover_lp_loss_cover_checker_rejects_tampered_replay_input(tmp_path: Path) -> None:
    bundle_dir = tmp_path / "lp_loss_cover_v1"
    shutil.copytree(DEFAULT_BUNDLE_DIR, bundle_dir)
    replay_path = bundle_dir / "replay_input.json"
    replay = json.loads(replay_path.read_text(encoding="utf-8"))
    replay["writer_posted"] = 79
    replay_path.write_text(json.dumps(replay, indent=2, sort_keys=True), encoding="utf-8")

    report = validate_zenocover_lp_loss_cover_bundle(bundle_dir)

    assert report["ok"] is False
    assert report["errors"] == ["replay_input_sha_mismatch"]


def test_zenocover_lp_loss_cover_cli_outputs_report(capsys) -> None:
    code = main(["--bundle-dir", str(DEFAULT_BUNDLE_DIR)])
    out = capsys.readouterr().out
    report = json.loads(out)

    assert code == 0
    assert report["ok"] is True
    assert report["schema"] == "zenodex.zenocover.lp_loss_cover_replay_report.v0"
