from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

import pytest

from src.core.fcis_b1b_authority_values import (
    FCISAuthorityHeaderV2,
    V1ToV2MigrationManifestV2,
)

REPO = Path(__file__).resolve().parents[2]
FIXTURE = REPO / "tests" / "fixtures" / "fcis_b1b_authority_v2_golden.json"
BUILDER_MODULE = "tools.build_fcis_b1b_authority_v2_golden"


def test_shared_b1b_fixture_is_source_current() -> None:
    clean_environment = dict(os.environ)
    clean_environment.pop("PYTHONPATH", None)
    completed = subprocess.run(
        [sys.executable, "-m", BUILDER_MODULE, "--check"],
        cwd=REPO,
        env=clean_environment,
        capture_output=True,
        text=True,
        check=False,
    )
    assert completed.returncode == 0, completed.stdout + completed.stderr


def test_fixture_covers_unicode_u256_roots_and_carrier_only_constants() -> None:
    document = json.loads(FIXTURE.read_text(encoding="utf-8"))
    assert document["version"] == 2
    maximum_u256 = (1 << 256) - 1
    assert document["u256_boundaries"] == [
        0,
        1,
        maximum_u256 - 1,
        maximum_u256,
    ]
    cases = document["cases"]
    assert len(cases) == 5
    assert any("α" in case["canonical_utf8"] for case in cases)
    maximum = next(case for case in cases if case["id"] == "authority_header_u256_maximum")
    assert maximum["value"]["sequence"] == maximum_u256
    rooted = [case for case in cases if "root" in case]
    assert len(rooted) == 3
    assert all(case["root"].startswith("0x") and len(case["root"]) == 66 for case in rooted)
    carrier_only = next(
        case for case in cases if case["id"] == "structurally_exact_wrong_fixed_constants"
    )
    assert carrier_only["semantic_status"] == "carrier_only_not_migration_authority"
    assert carrier_only["value"]["source_snapshot_version"] == 3


def _manifest_with_version(version: object) -> V1ToV2MigrationManifestV2:
    zero = "0x" + ("0" * 64)
    one = "0x" + ("0" * 63) + "1"
    return V1ToV2MigrationManifestV2(
        "deployment",
        zero,
        "domain",
        one,
        0,
        version,  # type: ignore[arg-type]
        0,
        4,
        5,
    )


def test_shared_negative_vectors_reject_with_exact_code() -> None:
    document = json.loads(FIXTURE.read_text(encoding="utf-8"))
    seen: set[str] = set()
    zero = "0x" + ("0" * 64)
    for case in document["negative_cases"]:
        seen.add(case["id"])
        assert case["expected_code"] == "invalid_value"
        assert "python" in case["languages"]
        kind = case["kind"]
        value = case["value"]
        with pytest.raises((TypeError, ValueError)):
            if kind == "identifier":
                FCISAuthorityHeaderV2(value, 0, zero)
            elif kind == "digest":
                FCISAuthorityHeaderV2("deployment", 0, value)
            elif kind == "u256":
                FCISAuthorityHeaderV2("deployment", value, zero)
            elif kind == "positive_u256":
                _manifest_with_version(value)
            else:
                raise AssertionError(f"unknown negative-vector kind: {kind}")

    assert seen == {
        "identifier_empty",
        "identifier_character_and_utf8_overflow",
        "digest_uppercase",
        "digest_malformed_length",
        "u256_boolean_alias",
        "u256_negative",
        "u256_overflow",
        "positive_u256_zero",
    }
