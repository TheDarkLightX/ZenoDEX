from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from src.fire.pathing_v1 import fire_stdlib_objects_dir

REPO_ROOT = Path(__file__).resolve().parents[2]
CHECK_CLI = REPO_ROOT / "tools" / "check_fire_fmos_spec.py"
SPEC_DIR = fire_stdlib_objects_dir()


def test_check_fire_fmos_spec_cli_accepts_burn_spec() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(CHECK_CLI),
            str(SPEC_DIR / "burn_boost_call_v1.json"),
            "--pretty",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["schema"] == "zenodex/fire-fmos-spec-check-report/v1"
    assert report["ok"] is True
    assert report["object_id"] == "burn_boost_call_v1"
    assert report["term_fields"][0] == {
        "name": "n_notional",
        "unit": "Amount[zUSD]",
        "minimum": 0,
        "maximum": 1000,
    }
    assert report["source_bounds"] == []
    assert report["imports"] == ["burn_final"]
    assert report["outputs"] == ["settlement_payoff"]


def test_check_fire_fmos_spec_cli_accepts_burn_index_interface_spec() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(CHECK_CLI),
            str(SPEC_DIR / "burn_index_v1.json"),
            "--pretty",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["object_id"] == "burn_index_v1"
    assert report["imports"] == []
    assert report["outputs"] == ["burn_final"]


def test_check_fire_fmos_spec_cli_rejects_bad_expression_ref(tmp_path: Path) -> None:
    bad_spec = json.loads((SPEC_DIR / "burn_boost_call_v1.json").read_text(encoding="utf-8"))
    bad_spec["expression"] = {"kind": "exact_param", "name": "missing_term"}
    bad_path = tmp_path / "bad_fire_spec.json"
    bad_path.write_text(json.dumps(bad_spec, indent=2, sort_keys=True), encoding="utf-8")

    proc = subprocess.run(
        [
            sys.executable,
            str(CHECK_CLI),
            str(bad_path),
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 1
    assert "unknown_exact_params:missing_term" in proc.stderr


def test_check_fire_fmos_spec_cli_rejects_inverted_term_bounds(tmp_path: Path) -> None:
    bad_spec = json.loads((SPEC_DIR / "burn_boost_call_v1.json").read_text(encoding="utf-8"))
    bad_spec["term_fields"][0]["minimum"] = 9
    bad_spec["term_fields"][0]["maximum"] = 3
    bad_path = tmp_path / "bad_term_bounds.json"
    bad_path.write_text(json.dumps(bad_spec, indent=2, sort_keys=True), encoding="utf-8")

    proc = subprocess.run(
        [
            sys.executable,
            str(CHECK_CLI),
            str(bad_path),
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 1
    assert "term field n_notional has inverted bounds" in proc.stderr
