from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
FIXTURE = REPO / "tests" / "fixtures" / "fcis_fee_apportionment_v2_golden.json"
BUILDER = REPO / "tools" / "build_fcis_fee_apportionment_v2_golden.py"


def test_shared_python_rust_fixture_is_source_current() -> None:
    completed = subprocess.run(
        [sys.executable, str(BUILDER), "--check"],
        cwd=REPO,
        capture_output=True,
        text=True,
        check=False,
    )

    assert completed.returncode == 0, completed.stdout + completed.stderr


def test_shared_fixture_covers_accept_reject_and_u256_maximum() -> None:
    document = json.loads(FIXTURE.read_text(encoding="utf-8"))
    cases = document["cases"]

    assert document["kernel"] == "SUPPORT_RESPECTING_GREEDY_DEFICIT_V1"
    assert len(cases) == 12
    assert any(case["expected"]["accept"] for case in cases)
    assert any(not case["expected"]["accept"] for case in cases)
    u256 = next(case for case in cases if case["id"] == "u256_maximum")
    assert u256["input"]["contributions"][0]["amount"] == (1 << 256) - 1
