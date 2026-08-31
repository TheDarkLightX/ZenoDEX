from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from tools.render_global_settlement_abi_v2_global_core_golden import (
    FIXTURE_PATH_V2,
    REPO_ROOT,
    build_fixture_v2,
    render_fixture_v2,
)


def test_committed_v2_global_core_fixture_matches_python_renderer() -> None:
    fixture_text = FIXTURE_PATH_V2.read_text(encoding="utf-8")

    assert fixture_text == render_fixture_v2()
    assert json.loads(fixture_text) == build_fixture_v2()


def test_v2_global_core_fixture_preserves_none_authority_and_nonclaims() -> None:
    fixture = build_fixture_v2()

    assert fixture["authority"] == "NONE"
    assert fixture["nonclaims"] == [
        "RISC0",
        "runtime",
        "publisher",
        "migration",
        "production",
    ]


def test_v2_global_core_renderer_cli_is_repo_location_bound(tmp_path: Path) -> None:
    result = subprocess.run(
        (
            sys.executable,
            str(REPO_ROOT / "tools/render_global_settlement_abi_v2_global_core_golden.py"),
            "--check",
            str(FIXTURE_PATH_V2),
        ),
        cwd=tmp_path,
        check=False,
        capture_output=True,
        text=True,
    )

    assert result.returncode == 0, result.stderr
    assert "fixture match" in result.stdout
