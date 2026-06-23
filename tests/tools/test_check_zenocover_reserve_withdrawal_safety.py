from __future__ import annotations

import copy
import json

from tools.check_zenocover_reserve_withdrawal_safety import (
    MANIFEST_SCHEMA,
    main,
    validate_reserve_withdrawal_safety_v0,
)


def _manifest() -> dict[str, object]:
    return {
        "schema": MANIFEST_SCHEMA,
        "pool": {
            "reserve_asset": "zUSD",
            "reserve_balance": 1_000,
            "active_liability": 600,
            "pending_claim_window_liability": 100,
            "min_surplus": 50,
        },
        "withdrawal_requests": [
            {
                "id": "safe-withdrawal",
                "amount": 200,
                "cooldown_complete": True,
                "claim_window_closed": False,
                "expected_accepted": True,
                "expected_post_reserve": 800,
            }
        ],
    }


def test_reserve_withdrawal_accepts_safe_withdrawal_before_claim_window_closed() -> None:
    report = validate_reserve_withdrawal_safety_v0(_manifest())

    assert report["ok"] is True
    assert report["pool"]["facts"]["initial_liability_floor"] == 750
    assert report["withdrawal_requests"]["items"][0]["facts"]["liability_floor"] == 750
    assert report["withdrawal_requests"]["items"][0]["facts"]["accepted"] is True
    assert report["attack_query_sweep"]["ok"] is True


def test_reserve_withdrawal_rejects_underfunding_before_claim_window_closed() -> None:
    manifest = copy.deepcopy(_manifest())
    manifest["withdrawal_requests"][0]["amount"] = 251  # type: ignore[index]
    manifest["withdrawal_requests"][0]["expected_accepted"] = True  # type: ignore[index]
    manifest["withdrawal_requests"][0]["expected_post_reserve"] = 749  # type: ignore[index]

    report = validate_reserve_withdrawal_safety_v0(manifest)

    assert report["ok"] is False
    row = report["withdrawal_requests"]["items"][0]
    assert row["facts"]["accepted"] is False
    assert "expected_accepted mismatch" in row["errors"]
    assert "expected_post_reserve mismatch" in row["errors"]


def test_reserve_withdrawal_rejects_missing_cooldown() -> None:
    manifest = copy.deepcopy(_manifest())
    manifest["withdrawal_requests"][0]["cooldown_complete"] = False  # type: ignore[index]
    manifest["withdrawal_requests"][0]["expected_accepted"] = True  # type: ignore[index]

    report = validate_reserve_withdrawal_safety_v0(manifest)

    assert report["ok"] is False
    row = report["withdrawal_requests"]["items"][0]
    assert row["facts"]["accepted"] is False
    assert "expected_accepted mismatch" in row["errors"]


def test_reserve_withdrawal_releases_pending_floor_after_claim_window_closed() -> None:
    manifest = copy.deepcopy(_manifest())
    manifest["withdrawal_requests"][0]["amount"] = 300  # type: ignore[index]
    manifest["withdrawal_requests"][0]["claim_window_closed"] = True  # type: ignore[index]
    manifest["withdrawal_requests"][0]["expected_post_reserve"] = 700  # type: ignore[index]

    report = validate_reserve_withdrawal_safety_v0(manifest)

    assert report["ok"] is True
    row = report["withdrawal_requests"]["items"][0]
    assert row["facts"]["liability_floor"] == 650
    assert row["facts"]["accepted"] is True


def test_reserve_withdrawal_rejects_sequential_overdraw() -> None:
    manifest = copy.deepcopy(_manifest())
    second = {
        "id": "second-withdrawal",
        "amount": 60,
        "cooldown_complete": True,
        "claim_window_closed": False,
        "expected_accepted": True,
        "expected_post_reserve": 740,
    }
    manifest["withdrawal_requests"].append(second)  # type: ignore[union-attr]

    report = validate_reserve_withdrawal_safety_v0(manifest)

    assert report["ok"] is False
    row = report["withdrawal_requests"]["items"][1]
    assert row["facts"]["accepted"] is False
    assert "expected_accepted mismatch" in row["errors"]


def test_reserve_withdrawal_rejects_initial_underfunded_pool() -> None:
    manifest = copy.deepcopy(_manifest())
    manifest["pool"]["reserve_balance"] = 700  # type: ignore[index]

    report = validate_reserve_withdrawal_safety_v0(manifest)

    assert report["ok"] is False
    assert "reserve_balance below active and pending liability floor" in report["pool"]["errors"]


def test_reserve_withdrawal_cli_outputs_report(tmp_path, capsys) -> None:
    manifest_path = tmp_path / "withdrawal.json"
    manifest_path.write_text(json.dumps(_manifest()), encoding="utf-8")

    code = main([str(manifest_path)])
    out = capsys.readouterr().out
    report = json.loads(out)

    assert code == 0
    assert report["ok"] is True
    assert report["schema"] == "zenodex.zenocover.reserve_withdrawal_safety_report.v0"
