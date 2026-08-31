from __future__ import annotations

import hashlib
import json
from pathlib import Path

FROZEN_V1_GOLDEN_SHA256 = (
    "9e2b233076a0724635dffb3d7f06f1cb26b7b4ac3c79b3ae4f02420e5877c9e4"
)


def _golden_path() -> Path:
    return Path(__file__).parents[1] / "data" / "global_settlement_abi_v1_golden.json"


def test_v1_golden_fixture_bytes_remain_frozen() -> None:
    golden_bytes = _golden_path().read_bytes()

    assert hashlib.sha256(golden_bytes).hexdigest() == FROZEN_V1_GOLDEN_SHA256


def test_v1_journals_do_not_admit_v2_oracle_plan_fields() -> None:
    fixture = json.loads(_golden_path().read_text(encoding="utf-8"))
    vectors = fixture["vectors"]

    for vector_name in ("module_journal", "lane_journal", "route_journal"):
        journal = vectors[vector_name]["canonical"]
        assert journal["schema"] == "zenodex/global-settlement-abi/v1"
        assert "oracle_occurrence_plan_root" not in journal
