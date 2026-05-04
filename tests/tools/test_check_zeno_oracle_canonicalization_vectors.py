from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
CHECKER = ROOT / "tools" / "check_zeno_oracle_canonicalization_vectors.py"
VECTORS = ROOT / "docs" / "zeno_oracle" / "canonicalization_vectors_v1.json"


def test_zeno_oracle_canonicalization_vectors_check() -> None:
    proc = subprocess.run(
        [sys.executable, str(CHECKER), "--json"],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    data = json.loads(proc.stdout)

    assert proc.returncode == 0, proc.stderr
    assert data["ok"] is True
    assert data["vector_count"] >= 19

    vectors = json.loads(VECTORS.read_text(encoding="utf-8"))["vectors"]
    vector_ids = {vector["id"] for vector in vectors}
    assert {
        "report_signing_payload_price_e8_v1",
        "signed_report_id_price_e8_v1",
        "aggregate_median_distinct_sources_v1",
        "accepted_read_o3_zusd_v1",
        "dispute_open_report_timestamp_v1",
        "typed_oracle_authorization_zusd_mint_v1",
        "oracle_authorization_bundle_terminal_graph_v1",
        "query_policy_equity_settlement_v1",
        "source_registry_root_registered_sources_v1",
        "reporter_state_at_submit_commitment_v1",
        "source_state_at_submit_commitment_v1",
        "query_policy_registered_independent_agrs_zdex_v1",
        "reward_ledger_entry_v1",
        "slash_settlement_v1",
        "reward_ledger_entry_emitted_receipt_v1",
        "slash_settlement_emitted_receipt_v1",
    }.issubset(vector_ids)


def test_zeno_oracle_canonicalization_vectors_reject_tamper(tmp_path: Path) -> None:
    tampered = json.loads(VECTORS.read_text(encoding="utf-8"))
    tampered["vectors"][0]["payload"]["value_e8"] += 1
    tampered_path = tmp_path / "vectors.json"
    tampered_path.write_text(json.dumps(tampered, sort_keys=True, indent=2), encoding="utf-8")

    proc = subprocess.run(
        [sys.executable, str(CHECKER), "--json", str(tampered_path)],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    data = json.loads(proc.stdout)

    assert proc.returncode == 2
    assert data["ok"] is False
    assert any("oracle_value_agrs_zdex_v1" in error for error in data["errors"])
