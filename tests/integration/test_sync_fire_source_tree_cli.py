from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[2]
SYNC_CLI = REPO_ROOT / "tools" / "sync_fire_source_tree.py"


def test_sync_fire_source_tree_cli_roundtrip(tmp_path: Path) -> None:
    legacy_specs = tmp_path / "legacy_specs"
    legacy_specs.mkdir()
    (legacy_specs / "sample_v1.json").write_text(
        json.dumps(
            {
                "schema": "zenodex/fire-math-object-spec/v1",
                "object_id": "sample_v1",
                "object_name": "Sample",
                "cli_help": "Sample help",
                "object_version": "v1",
                "object_family": "sample_family",
                "settlement_asset": "zUSD",
                "payoff_summary": "sample",
                "ir_hash": "sha256:" + "a" * 64,
                "term_fields": [
                    {
                        "name": "x",
                        "description": "sample x",
                        "unit": "Index",
                        "minimum": 0,
                        "maximum": 10,
                    }
                ],
                "source_bounds": [],
                "imports": [],
                "witnesses": [],
                "outputs": [
                    {
                        "name": "x_out",
                        "description": "sample output",
                        "unit": "Index",
                        "expression": {"kind": "exact_param", "name": "x"},
                    }
                ],
                "expression": {"kind": "exact_param", "name": "x"},
            },
            sort_keys=True,
        ),
        encoding="utf-8",
    )
    legacy_zpl = tmp_path / "legacy_zpl"
    legacy_zpl.mkdir()
    (legacy_zpl / "sample_v1.zpl").write_text(
        "\n".join(
            [
                "object sample_v1;",
                "name Sample;",
                'cli_help "Sample help";',
                "version v1;",
                "family sample_family;",
                "settlement zUSD;",
                'summary "sample";',
                "ir_hash sha256:" + "a" * 64 + ";",
                'term x "sample x" Index 0 10;',
                'output x_out "sample output" Index = exact_param(x);',
                "expression = exact_param(x);",
                "end",
            ]
        ),
        encoding="utf-8",
    )
    stdlib_dir = tmp_path / "src" / "fire" / "stdlib" / "objects"
    zpl_dir = tmp_path / "src" / "fire" / "zpl"
    manifest_path = tmp_path / "src" / "fire" / "stdlib" / "manifest.json"
    proc = subprocess.run(
        [
            sys.executable,
            str(SYNC_CLI),
            "--legacy-spec-dir",
            str(legacy_specs),
            "--legacy-zpl-dir",
            str(legacy_zpl),
            "--stdlib-object-dir",
            str(stdlib_dir),
            "--zpl-dir",
            str(zpl_dir),
            "--manifest-path",
            str(manifest_path),
            "--pretty",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["ok"] is True
    assert report["spec_count"] == 1
    assert report["zpl_count"] == 1
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    assert manifest["schema"] == "zenodex/fire-stdlib-manifest/v1"
    assert manifest["entry_count"] == 1
    assert manifest["entries"][0]["object_id"] == "sample_v1"
