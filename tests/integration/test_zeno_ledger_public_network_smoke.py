from __future__ import annotations

import json

from tools.zeno_ledger_public_network_smoke import main, run_public_network_smoke_v0


def test_public_network_smoke_covers_live_dex_intent_set(tmp_path) -> None:
    report = run_public_network_smoke_v0(
        out_dir=tmp_path / "public-network-smoke",
        network_id="zeno-ledger-public-testnet-smoke-test",
        chain_id="zeno-ledger-public-testnet-smoke-test",
    )

    assert report["ok"] is True
    assert report["live_dex_all_accepted"] is True
    assert report["covered_live_dex_intent_kinds"] == [
        "CREATE_POOL",
        "ADD_LIQUIDITY",
        "REMOVE_LIQUIDITY",
        "SWAP_EXACT_IN",
        "SWAP_EXACT_OUT",
    ]
    assert report["swap_exact_out_height"] > report["swap_height"]
    assert report["node_b_pulled_count"] >= 7


def test_public_network_smoke_cli_writes_report(tmp_path) -> None:
    report_out = tmp_path / "report.json"

    rc = main(
        [
            "--out-dir",
            str(tmp_path / "public-network-smoke-cli"),
            "--network-id",
            "zeno-ledger-public-testnet-smoke-cli",
            "--chain-id",
            "zeno-ledger-public-testnet-smoke-cli",
            "--report-out",
            str(report_out),
        ]
    )

    assert rc == 0
    report = json.loads(report_out.read_text(encoding="utf-8"))
    assert report["ok"] is True
    assert report["live_dex_all_accepted"] is True
    assert "SWAP_EXACT_OUT" in report["covered_live_dex_intent_kinds"]
