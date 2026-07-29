from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
FIXTURE = REPO / "tests" / "fixtures" / "fcis_b1b_authority_v2_golden.json"
BUILDER = REPO / "tools" / "build_fcis_b1b_authority_v2_golden.py"


def test_shared_b1b_fixture_is_source_current() -> None:
    completed = subprocess.run(
        [sys.executable, str(BUILDER), "--check"],
        cwd=REPO,
        capture_output=True,
        text=True,
        check=False,
    )
    assert completed.returncode == 0, completed.stdout + completed.stderr


def test_fixture_covers_unicode_u256_roots_and_carrier_only_constants() -> None:
    document = json.loads(FIXTURE.read_text(encoding="utf-8"))
    cases = document["cases"]
    assert len(cases) == 5
    assert any("α" in case["canonical_utf8"] for case in cases)
    maximum = next(case for case in cases if case["id"] == "authority_header_u256_maximum")
    assert maximum["value"]["sequence"] == (1 << 256) - 1
    rooted = [case for case in cases if "root" in case]
    assert len(rooted) == 3
    assert all(case["root"].startswith("0x") and len(case["root"]) == 66 for case in rooted)
    carrier_only = next(
        case for case in cases if case["id"] == "structurally_exact_wrong_fixed_constants"
    )
    assert carrier_only["semantic_status"] == "carrier_only_not_migration_authority"
    assert carrier_only["value"]["source_snapshot_version"] == 3
