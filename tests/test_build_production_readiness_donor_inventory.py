from __future__ import annotations

import json
from pathlib import Path

from tools import build_production_readiness_donor_inventory as donor_builder

REPO_ROOT = Path(__file__).resolve().parents[1]


def test_committed_donor_inventory_replays_the_frozen_ref_snapshot() -> None:
    expected = json.loads(donor_builder.DEFAULT_OUTPUT.read_text(encoding="utf-8"))

    observed = donor_builder.build_inventory(REPO_ROOT, donor_builder.DEFAULT_BASE_COMMIT)

    assert observed == expected
    assert observed["counts"]["imports"] == 0
    assert observed["counts"]["DESCENDANT_UNVERIFIED"] == 0


def test_check_mode_rejects_inventory_drift(
    tmp_path: Path,
    monkeypatch,
) -> None:
    inventory = {
        "counts": {"unique_candidates": 1, "imports": 0},
        "status": "FROZEN_UNREVIEWED",
    }
    output = tmp_path / "donors.json"
    output.write_text("{}\n", encoding="utf-8")
    monkeypatch.setattr(donor_builder, "build_inventory", lambda _repo, _base: inventory)

    exit_code = donor_builder.main(
        [
            "--repo-root",
            str(REPO_ROOT),
            "--output",
            str(output),
            "--check",
        ]
    )

    assert exit_code == 1


def test_write_mode_uses_canonical_sorted_json(
    tmp_path: Path,
    monkeypatch,
) -> None:
    inventory = {
        "schema": donor_builder.SCHEMA,
        "counts": {"unique_candidates": 0, "imports": 0},
        "z_field": 1,
        "a_field": 2,
    }
    output = tmp_path / "donors.json"
    monkeypatch.setattr(donor_builder, "build_inventory", lambda _repo, _base: inventory)

    exit_code = donor_builder.main(
        [
            "--repo-root",
            str(REPO_ROOT),
            "--output",
            str(output),
        ]
    )

    assert exit_code == 0
    assert output.read_text(encoding="utf-8") == donor_builder._encoded(inventory)
