from __future__ import annotations

import json
from pathlib import Path


def test_public_follower_acceptance_writes_live_common_header_report(
    tmp_path: Path,
    monkeypatch,
) -> None:
    from tools import zenodex_public_follower as follower

    data_dir = tmp_path / "node"
    bundle_root = data_dir / "bundle"

    def fake_join(**kwargs):
        data_dir.mkdir(parents=True, exist_ok=True)
        (data_dir / "public_network_config.json").write_text(
            json.dumps(
                {
                    "schema": "zenodex.zeno_ledger.public_network_config.v0",
                    "network_config_hash": "0x" + "11" * 32,
                    "public_config_url_posture": "session_stable_quick_tunnel",
                }
            ),
            encoding="utf-8",
        )
        (data_dir / "node_join_config.json").write_text(
            json.dumps(
                {
                    "submit_peer_url": "https://seed.example",
                    "min_lp_position_age_seconds": 300,
                    "lp_duration_risk_policy": "zeno-oracle",
                }
            ),
            encoding="utf-8",
        )
        return {
            "ok": True,
            "status": "accepted",
            "network_config_hash": "0x" + "11" * 32,
            "submit_peer_url": "https://seed.example",
            "sync_report": {
                "used_bundle_archive": True,
                "bundle_archive_sha256": "0x" + "44" * 32,
                "downloaded_artifact_count": 341,
                "downloaded_mirror_count": 11,
            },
        }

    monkeypatch.setattr(follower, "join_public_node_from_network_config_url_v0", fake_join)

    def fake_pull_live(**kwargs):
        assert kwargs["min_lp_position_age_seconds"] == 300
        assert kwargs["lp_duration_risk_policy"] is not None
        return {"ok": True, "status": "accepted", "pulled_count": 3}

    monkeypatch.setattr(follower, "pull_live_from_peer_v0", fake_pull_live)
    monkeypatch.setattr(
        follower,
        "check_peer_status_v0",
        lambda **kwargs: {
            "ok": True,
            "status": "accepted",
            "local_tip": {"live": True, "height": 8, "header_hash": "0x22", "app_hash": "0x33"},
            "peers": [
                {
                    "ok": True,
                    "status": "accepted",
                    "common_header_match": True,
                    "height_relation": "same_height",
                    "peer_tip": {"live": True, "height": 8, "header_hash": "0x22", "app_hash": "0x33"},
                }
            ],
        },
    )

    report = follower.join_and_accept_public_follower(
        config_url="https://seed.example/public_network_config.json",
        node_id="follower-a",
        data_dir=data_dir,
        bundle_root=bundle_root,
        host="127.0.0.1",
        port=8788,
        poll_seconds=5,
        pull_live=True,
        require_live=True,
        report_path=None,
    )

    assert report["ok"] is True
    assert report["common_header_match"] is True
    assert report["live_observed"] is True
    assert report["pulled_count"] == 3
    report_path = Path(report["report_path"])
    assert report_path.is_file()
    saved = json.loads(report_path.read_text(encoding="utf-8"))
    assert saved["schema"] == follower.PUBLIC_FOLLOWER_ACCEPTANCE_SCHEMA
    assert saved["peer_url"] == "https://seed.example"
    assert saved["min_lp_position_age_seconds"] == 300
    assert saved["lp_duration_risk_policy"] == "zeno-oracle"
    assert saved["bundle_sync"]["used_bundle_archive"] is True
    assert saved["bundle_sync"]["bundle_archive_sha256"] == "0x" + "44" * 32


def test_public_follower_rejects_invalid_join_config_follow_policy(tmp_path: Path) -> None:
    from tools import zenodex_public_follower as follower

    data_dir = tmp_path / "node"
    data_dir.mkdir(parents=True)
    (data_dir / "node_join_config.json").write_text(
        json.dumps(
            {
                "submit_peer_url": "https://seed.example",
                "min_lp_position_age_seconds": -1,
                "lp_duration_risk_policy": "zeno-oracle",
            }
        ),
        encoding="utf-8",
    )

    try:
        follower._join_config_follow_policy(data_dir)
    except ValueError as exc:
        assert "min_lp_position_age_seconds" in str(exc)
    else:  # pragma: no cover - assertion failure path
        raise AssertionError("invalid min LP age was accepted")


def test_public_follower_rejects_without_live_tip(tmp_path: Path, monkeypatch) -> None:
    from tools import zenodex_public_follower as follower

    data_dir = tmp_path / "node"
    bundle_root = data_dir / "bundle"

    def fake_join(**kwargs):
        data_dir.mkdir(parents=True, exist_ok=True)
        (data_dir / "node_join_config.json").write_text(
            json.dumps({"submit_peer_url": "https://seed.example"}),
            encoding="utf-8",
        )
        return {"ok": True, "status": "accepted", "network_config_hash": "0x" + "11" * 32}

    monkeypatch.setattr(follower, "join_public_node_from_network_config_url_v0", fake_join)
    monkeypatch.setattr(follower, "pull_live_from_peer_v0", lambda **kwargs: {"ok": True, "pulled_count": 0})
    monkeypatch.setattr(
        follower,
        "check_peer_status_v0",
        lambda **kwargs: {
            "ok": True,
            "local_tip": {"live": False, "height": 5, "header_hash": "0x22", "app_hash": "0x33"},
            "peers": [
                {
                    "common_header_match": True,
                    "peer_tip": {"live": False, "height": 5, "header_hash": "0x22", "app_hash": "0x33"},
                }
            ],
        },
    )

    report = follower.join_and_accept_public_follower(
        config_url="https://seed.example/public_network_config.json",
        node_id="follower-a",
        data_dir=data_dir,
        bundle_root=bundle_root,
        host="127.0.0.1",
        port=8788,
        poll_seconds=5,
        pull_live=True,
        require_live=True,
        report_path=None,
    )

    assert report["ok"] is False
    assert "live_tip_not_observed" in report["errors"]
