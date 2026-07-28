from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
FIXTURE = REPO / "tests" / "fixtures" / "fcis_fee_distribution_configuration_v2_golden.json"
BUILDER = REPO / "tools" / "build_fcis_fee_distribution_configuration_v2_golden.py"


def test_shared_configuration_fixture_is_source_current() -> None:
    completed = subprocess.run(
        [sys.executable, str(BUILDER), "--check"],
        cwd=REPO,
        capture_output=True,
        text=True,
        check=False,
    )

    assert completed.returncode == 0, completed.stdout + completed.stderr


def test_fixture_covers_roots_versions_unicode_and_u256() -> None:
    document = json.loads(FIXTURE.read_text(encoding="utf-8"))
    cases = document["cases"]

    assert len(cases) == 7
    assert sum(bool(case["expected"]["accept"]) for case in cases) == 3
    assert any("α" in json.dumps(case, ensure_ascii=False) for case in cases)
    maximum = next(case for case in cases if case["id"] == "valid_u256_maximum")
    assert maximum["input"]["body"]["activation_sequence"] == (1 << 256) - 1
    attacker = next(
        case for case in cases if case["id"] == "self_consistent_attacker_configuration"
    )
    assert attacker["expected"]["accept"] is True
    assert attacker["input"]["body"]["policy"]["buyback_destination"] == "mallory"
    assert "validated-configuration-claim/v2" in attacker["expected"]["validated_claim_utf8"]
    assert "authenticated-configuration" not in attacker["expected"]["validated_claim_utf8"]
    reject_codes = {case["expected"]["code"] for case in cases if not case["expected"]["accept"]}
    assert reject_codes == {
        "algorithm_version_mismatch",
        "accepted_language_version_mismatch",
        "policy_root_mismatch",
        "configuration_root_mismatch",
    }
