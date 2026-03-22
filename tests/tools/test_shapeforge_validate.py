from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
VALIDATOR = ROOT / "tools" / "shapeforge_validate.py"
WORLD_MODEL = ROOT / "docs" / "zenodex" / "shapeforge_promoted" / "zenodex_world_model.seed.json"
NEGATIVE_KNOWLEDGE = (
    ROOT / "docs" / "zenodex" / "shapeforge_promoted" / "zenodex_negative_knowledge.seed.json"
)
TARGET_SHAPES = (
    ROOT / "docs" / "zenodex" / "shapeforge_promoted" / "zenodex_target_shapes.seed.json"
)


def test_zenodex_world_model_validates() -> None:
    result = subprocess.run(
        [sys.executable, str(VALIDATOR), str(WORLD_MODEL)],
        cwd=str(ROOT),
        capture_output=True,
        text=True,
        check=False,
    )
    assert result.returncode == 0, result.stderr
    assert result.stdout.strip() == f"OK {WORLD_MODEL}"


def test_zenodex_negative_knowledge_validates() -> None:
    result = subprocess.run(
        [sys.executable, str(VALIDATOR), str(NEGATIVE_KNOWLEDGE)],
        cwd=str(ROOT),
        capture_output=True,
        text=True,
        check=False,
    )
    assert result.returncode == 0, result.stderr
    assert result.stdout.strip() == f"OK {NEGATIVE_KNOWLEDGE}"


def test_zenodex_target_shapes_validate() -> None:
    result = subprocess.run(
        [sys.executable, str(VALIDATOR), str(TARGET_SHAPES)],
        cwd=str(ROOT),
        capture_output=True,
        text=True,
        check=False,
    )
    assert result.returncode == 0, result.stderr
    assert result.stdout.strip() == f"OK {TARGET_SHAPES}"


def test_world_model_rejects_unknown_evidence_class(tmp_path: Path) -> None:
    world_model = json.loads(WORLD_MODEL.read_text(encoding="utf-8"))
    world_model["evidence_classes"] = list(world_model["evidence_classes"]) + ["renamed_status"]
    broken = tmp_path / "world_model_bad_evidence.json"
    broken.write_text(json.dumps(world_model, indent=2), encoding="utf-8")

    result = subprocess.run(
        [sys.executable, str(VALIDATOR), str(broken)],
        cwd=str(ROOT),
        capture_output=True,
        text=True,
        check=False,
    )
    assert result.returncode != 0
    assert "evidence_classes contains unsupported values" in result.stderr


def test_world_model_rejects_duplicate_cross_slice_invariant_ids(tmp_path: Path) -> None:
    world_model = json.loads(WORLD_MODEL.read_text(encoding="utf-8"))
    duplicate = dict(world_model["cross_slice_invariants"][0])
    world_model["cross_slice_invariants"] = list(world_model["cross_slice_invariants"]) + [duplicate]
    broken = tmp_path / "world_model_bad_invariants.json"
    broken.write_text(json.dumps(world_model, indent=2), encoding="utf-8")

    result = subprocess.run(
        [sys.executable, str(VALIDATOR), str(broken)],
        cwd=str(ROOT),
        capture_output=True,
        text=True,
        check=False,
    )
    assert result.returncode != 0
    assert "cross_slice_invariants must have unique ids" in result.stderr
