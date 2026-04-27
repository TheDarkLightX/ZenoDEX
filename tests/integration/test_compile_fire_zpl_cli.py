from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from src.fire.pathing_v1 import fire_stdlib_objects_dir, fire_zpl_dir

REPO_ROOT = Path(__file__).resolve().parents[2]
ZPL_DIR = fire_zpl_dir()
SPEC_DIR = fire_stdlib_objects_dir()
COMPILE_CLI = REPO_ROOT / "tools" / "compile_fire_zpl.py"


def test_compile_fire_zpl_cli_roundtrip_examples(tmp_path: Path) -> None:
    for zpl_path in sorted(ZPL_DIR.glob("*.zpl")):
        output_path = tmp_path / (zpl_path.stem + ".json")
        proc = subprocess.run(
            [
                sys.executable,
                str(COMPILE_CLI),
                str(zpl_path),
                "--output",
                str(output_path),
                "--pretty",
            ],
            cwd=str(REPO_ROOT),
            check=False,
            capture_output=True,
            text=True,
        )

        assert proc.returncode == 0, proc.stderr
        report = json.loads(proc.stdout)
        assert report["schema"] == "zenodex/fire-zpl-compile-report/v1"
        assert report["ok"] is True
        assert report["object_id"] == zpl_path.stem
        compiled_payload = json.loads(output_path.read_text(encoding="utf-8"))
        expected_payload = json.loads((SPEC_DIR / f"{zpl_path.stem}.json").read_text(encoding="utf-8"))
        assert compiled_payload == expected_payload


def test_compile_fire_zpl_cli_rejects_bad_program(tmp_path: Path) -> None:
    bad_source = tmp_path / "bad.zpl"
    bad_output = tmp_path / "bad.json"
    bad_source.write_text(
        "\n".join(
            [
                "object bad_v1;",
                "name Bad;",
                'cli_help "Bad";',
                "version v1;",
                "family test;",
                "settlement zUSD;",
                'summary "bad";',
                "ir_hash sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa;",
                'term x "X" Index 0 10;',
                'output y "Y" Index = exact_param(missing);',
                "expression = exact_param(missing);",
                "end",
            ]
        ),
        encoding="utf-8",
    )

    proc = subprocess.run(
        [
            sys.executable,
            str(COMPILE_CLI),
            str(bad_source),
            "--output",
            str(bad_output),
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 1
    assert "line 10, col 22" in proc.stderr
    assert "unknown exact_param reference: missing" in proc.stderr
