from __future__ import annotations

import hashlib
import json
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
RESULT = ROOT / "docs/research/FCIS_M6_FORMAL_SUITE_BOUNDED_RESULT_V1.json"
MATRIX = ROOT / "docs/research/FCIS_M6_FORMAL_RUNTIME_REFINEMENT_MATRIX_V1.json"
MANIFEST = ROOT / "docs/research/FCIS_M6_FORMAL_SUITE_SOURCE_MANIFEST.sha256"


def test_committed_bounded_result_is_a_fresh_canonical_replay() -> None:
    completed = subprocess.run(
        [
            sys.executable,
            "tools/check_fcis_m6_formal_specs.py",
            "--check",
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
        timeout=90,
    )
    assert completed.returncode == 0, completed.stdout + completed.stderr


def test_tau_continuity_lane_is_reachable_and_fail_closed() -> None:
    result = json.loads(RESULT.read_text(encoding="utf-8"))
    model = result["models"]["fcis_m6_zenoledger_tau_continuity_v1"]
    action_counts = model["action_counts"]

    assert action_counts["commit_with_tau_unavailable"] > 0
    assert action_counts["commit_with_tau_censoring"] > 0
    assert action_counts["commit_during_tau_rejoin"] > 0
    assert action_counts["anchor_authenticated_checkpoint"] > 0
    assert action_counts["tau_rewrite_ledger_head"] == 0
    assert all(
        kills > 0
        for kills in result["invariant_mutant_coverage"][
            "fcis_m6_zenoledger_tau_continuity_v1"
        ].values()
    )


def test_runtime_projection_obligations_remain_explicitly_unimplemented() -> None:
    matrix = json.loads(MATRIX.read_text(encoding="utf-8"))
    projection_contract = matrix["projection_contract"]
    used = {projection for entry in matrix["entries"] for projection in entry["runtime_projection"]}

    assert projection_contract["status"] == "DECLARED_ONLY_NO_RUNTIME_IMPLEMENTATION"
    assert projection_contract["registered_ids"] == sorted(used)
    assert all(entry["runtime_status"] == "SPEC_ONLY_UNMOUNTED" for entry in matrix["entries"])


def test_matrix_rejects_an_unregistered_projection(tmp_path: Path) -> None:
    shutil.copytree(ROOT / "formal/esso", tmp_path / "formal/esso")
    (tmp_path / "docs/research").mkdir(parents=True)
    shutil.copy2(RESULT, tmp_path / RESULT.relative_to(ROOT))
    shutil.copy2(MATRIX, tmp_path / MATRIX.relative_to(ROOT))
    (tmp_path / "features").mkdir()
    shutil.copy2(
        ROOT / "features/fcis_m6_formal_runtime_refinement.feature",
        tmp_path / "features/fcis_m6_formal_runtime_refinement.feature",
    )

    mutated_path = tmp_path / MATRIX.relative_to(ROOT)
    mutated = json.loads(mutated_path.read_text(encoding="utf-8"))
    mutated["entries"][0]["runtime_projection"].append("project_bogus_v1")
    mutated_path.write_text(json.dumps(mutated), encoding="utf-8")

    completed = subprocess.run(
        [
            sys.executable,
            str(ROOT / "tools/check_fcis_m6_formal_runtime_matrix.py"),
            "--root",
            str(tmp_path),
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
        timeout=30,
    )
    report = json.loads(completed.stdout)
    assert completed.returncode == 1
    assert report["verdict"] == "FORMAL_RUNTIME_MATRIX_MISMATCH"
    assert "runtime projection registry differs from matrix use" in report["errors"]


def test_source_manifest_matches_exact_bytes() -> None:
    for line in MANIFEST.read_text(encoding="utf-8").splitlines():
        expected, relative = line.split("  ", maxsplit=1)
        actual = hashlib.sha256((ROOT / relative).read_bytes()).hexdigest()
        assert actual == expected, relative
