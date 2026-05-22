from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from tools.zenodex_campaign5_disaster_class_corpus import build_corpus

ROOT = Path(__file__).resolve().parents[1]


def test_campaign5_disaster_class_corpus_closes_scoped_classes() -> None:
    receipt = build_corpus()

    assert receipt["schema"] == "zenodex.campaign5.disaster_class_corpus.v1"
    assert receipt["status"] == "accepted"
    assert receipt["named_disaster_class_count"] == 3
    assert receipt["closed_class_count"] == 3
    assert receipt["failed_class_count"] == 0

    cases = {case["class_id"]: case for case in receipt["cases"]}
    assert set(cases) == {
        "adl_sybil_bankruptcy_closure",
        "twal_yield_vampire_closure",
        "exact_out_ring_topology_closure",
    }

    adl = cases["adl_sybil_bankruptcy_closure"]["observed"]
    assert adl["standard_profit"] == adl["standard_insurance_draw"] == 1_000
    assert adl["adl_profit"] == 0
    assert adl["adl_treasury_draw"] == 0

    twal = cases["twal_yield_vampire_closure"]["observed"]
    assert twal["snapshot_reward"] == 9_900
    assert twal["twal_reward"] == 900
    assert twal["reward_reduction_bps"] == 9_090

    routing = cases["exact_out_ring_topology_closure"]["observed"]
    assert routing["same_asset_route_rejected"] is True
    assert routing["cross_asset_route_found"] is True
    assert routing["quote_call_count"] <= routing["quote_call_bound"]
    assert routing["bounded_hops"] is True
    assert routing["acyclic_paths"] is True


def test_campaign5_disaster_class_corpus_cli_writes_receipt(tmp_path: Path) -> None:
    output = tmp_path / "campaign5-disaster-corpus.json"
    proc = subprocess.run(
        [
            sys.executable,
            "tools/zenodex_campaign5_disaster_class_corpus.py",
            "--format",
            "json",
            "--output",
            str(output),
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
        timeout=20,
    )

    assert proc.returncode == 0
    stdout_receipt = json.loads(proc.stdout)
    file_receipt = json.loads(output.read_text(encoding="utf-8"))
    assert stdout_receipt == file_receipt
    assert file_receipt["status"] == "accepted"
