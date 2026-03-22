from __future__ import annotations

import json
import subprocess
from pathlib import Path


def test_pokayoke_audit_tool_runs_and_emits_report(tmp_path: Path) -> None:
    out_dir = tmp_path / "pokayoke_audit_out"
    proc = subprocess.run(
        ["python3", "tools/pokayoke/pokayoke_audit.py", "--repo-root", ".", "--out-dir", str(out_dir)],
        text=True,
        capture_output=True,
        check=False,
    )
    assert proc.returncode == 0, proc.stderr
    report = out_dir / "report.json"
    assert report.exists()
    obj = json.loads(report.read_text(encoding="utf-8"))
    assert obj.get("schema") == "zenodex/pokayoke_audit_report/v1"
    assert isinstance(obj.get("opportunities"), list)
    rows = {row["failure_id"]: row for row in obj["opportunities"]}
    assert rows["swap_mev_conflict_unacknowledged"]["coverage_status"] in {"covered", "partial"}
    assert "liquidity_add_imbalanced_amounts" not in rows
    assert "liquidity_remove_near_total" not in rows
    for row in obj["opportunities"]:
        status = row["coverage_status"]
        assert status in {"covered", "partial", "signal_only", "uncovered"}
        if row["signal_present"] and row["interlock_present"]:
            assert status == "covered"
        elif row["interlock_present"]:
            assert status == "partial"
        elif row["signal_present"]:
            assert status == "signal_only"
        else:
            assert status == "uncovered"
