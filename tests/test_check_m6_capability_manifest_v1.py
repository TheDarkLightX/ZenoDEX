from __future__ import annotations

import json
from copy import deepcopy
from pathlib import Path

from src.core.global_economic_capability_profile_binding_v1 import (
    M6_CAPABILITY_MANIFEST_ROOT_V1,
)
from tools.check_m6_capability_manifest_v1 import (
    DEFAULT_MANIFEST,
    REPO_ROOT,
    check_m6_capability_manifest_v1,
)


def _manifest() -> dict[str, object]:
    return json.loads((REPO_ROOT / DEFAULT_MANIFEST).read_text(encoding="utf-8"))


def _write(tmp_path: Path, value: dict[str, object]) -> Path:
    path = tmp_path / "manifest.json"
    path.write_text(json.dumps(value), encoding="utf-8")
    return path


def test_manifest_closes_all_lane_names_without_promoting_authority() -> None:
    report = check_m6_capability_manifest_v1()

    assert report == {
        "schema": "zenodex/m6-capability-manifest-check/v1",
        "ok": True,
        "lane_count": 12,
        "open_capability_count": 103,
        "manifest_root": M6_CAPABILITY_MANIFEST_ROOT_V1,
        "manifest_complete": False,
        "release_eligible": False,
        "production_authority": "NONE",
        "findings": [],
    }


def test_subset_profile_cannot_erase_farms_or_buy_and_burn(tmp_path: Path) -> None:
    mutated = deepcopy(_manifest())
    mutated["lanes"] = [  # type: ignore[index]
        lane
        for lane in mutated["lanes"]  # type: ignore[index]
        if lane["lane_id"] != "FARM_INCENTIVES"
    ]
    tokenomics = next(
        lane
        for lane in mutated["lanes"]  # type: ignore[index]
        if lane["lane_id"] == "ZDEX_TOKENOMICS"
    )
    tokenomics["capabilities"].remove("atomic_purchase_and_burn")

    report = check_m6_capability_manifest_v1(manifest_path=_write(tmp_path, mutated))

    assert report["ok"] is False
    assert "lane IDs must exactly match GlobalSettlementABI V1 order" in report["findings"]
    assert any("atomic_purchase_and_burn" in finding for finding in report["findings"])


def test_metadata_cannot_promote_an_unresolved_manifest(tmp_path: Path) -> None:
    mutated = deepcopy(_manifest())
    mutated["manifest_complete"] = True
    mutated["release_eligible"] = True
    mutated["lanes"][0]["disposition"] = "ACTIVE"  # type: ignore[index]

    report = check_m6_capability_manifest_v1(manifest_path=_write(tmp_path, mutated))

    assert report["ok"] is False
    assert (
        "manifest_complete must remain false while capabilities are unresolved"
        in report["findings"]
    )
    assert (
        "release_eligible must remain false while capabilities are unresolved"
        in report["findings"]
    )
    assert "lane disposition drift: ASSET_TRANSFER" in report["findings"]


def test_autonomous_governance_cannot_gain_publication_authority(tmp_path: Path) -> None:
    mutated = deepcopy(_manifest())
    exclusion = next(
        row
        for row in mutated["explicit_exclusions"]  # type: ignore[index]
        if row["capability"] == "autonomous_governance_publication_authority"
    )
    exclusion["disposition"] = "ALLOWED"

    report = check_m6_capability_manifest_v1(manifest_path=_write(tmp_path, mutated))

    assert report["ok"] is False
    assert "explicit exclusion semantics drift" in report["findings"]
