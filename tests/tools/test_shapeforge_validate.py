from __future__ import annotations

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
