from __future__ import annotations

import json
import shutil
from pathlib import Path

from tools.check_zenocover_lp_loss_cover import DEFAULT_BUNDLE_DIR
from tools.check_zenocover_reserve_solvency import (
    MANIFEST_SCHEMA,
    main,
    validate_zenocover_reserve_solvency_v0,
)


def _manifest(**reserve_overrides: object) -> dict[str, object]:
    reserve: dict[str, object] = {
        "asset": "zUSD",
        "balance": 200,
        "existing_locked": 0,
        "min_surplus": 20,
    }
    reserve.update(reserve_overrides)
    return {
        "schema": MANIFEST_SCHEMA,
        "reserve": reserve,
        "positions": [
            {
                "id": "lp-loss-cover-devnet-v1",
                "status": "active",
                "bundle_dir": str(DEFAULT_BUNDLE_DIR),
            }
        ],
    }


def test_zenocover_reserve_solvency_accepts_funded_active_cover() -> None:
    report = validate_zenocover_reserve_solvency_v0(_manifest())

    assert report["ok"] is True
    assert report["facts"]["active_required_collateral"] == 80
    assert report["facts"]["surplus_after_active"] == 120
    assert report["positions"][0]["required_collateral"] == 80


def test_zenocover_reserve_solvency_rejects_insufficient_reserve() -> None:
    report = validate_zenocover_reserve_solvency_v0(_manifest(balance=90))

    assert report["ok"] is False
    assert "reserve balance below active collateral plus min_surplus" in report["errors"]
    assert report["facts"]["surplus_after_active"] == 10


def test_zenocover_reserve_solvency_rejects_duplicate_position_ids() -> None:
    manifest = _manifest()
    manifest["positions"].append(dict(manifest["positions"][0]))  # type: ignore[index, union-attr]

    report = validate_zenocover_reserve_solvency_v0(manifest)

    assert report["ok"] is False
    assert "position id must be unique" in report["positions"][1]["errors"]


def test_zenocover_reserve_solvency_rejects_tampered_bundle(tmp_path: Path) -> None:
    bundle_dir = tmp_path / "lp_loss_cover_v1"
    shutil.copytree(DEFAULT_BUNDLE_DIR, bundle_dir)
    replay_path = bundle_dir / "replay_input.json"
    replay = json.loads(replay_path.read_text(encoding="utf-8"))
    replay["writer_posted"] = 79
    replay_path.write_text(json.dumps(replay, indent=2, sort_keys=True), encoding="utf-8")
    manifest = _manifest()
    manifest["positions"][0]["bundle_dir"] = str(bundle_dir)  # type: ignore[index]

    report = validate_zenocover_reserve_solvency_v0(manifest)

    assert report["ok"] is False
    assert "bundle replay rejected" in report["positions"][0]["errors"]
    assert report["positions"][0]["bundle_errors"] == ["replay_input_sha_mismatch"]


def test_zenocover_reserve_solvency_cli_outputs_report(tmp_path, capsys) -> None:
    manifest_path = tmp_path / "reserve.json"
    manifest_path.write_text(json.dumps(_manifest()), encoding="utf-8")

    code = main([str(manifest_path)])
    out = capsys.readouterr().out
    report = json.loads(out)

    assert code == 0
    assert report["ok"] is True
    assert report["schema"] == "zenodex.zenocover.reserve_solvency_report.v0"
