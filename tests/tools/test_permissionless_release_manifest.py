from __future__ import annotations

import json
from pathlib import Path

from tools.permissionless_release_manifest import build_manifest, main


def test_build_manifest_lists_files_deterministically(tmp_path: Path) -> None:
    dist_dir = tmp_path / "dist"
    assets_dir = dist_dir / "assets"
    assets_dir.mkdir(parents=True)
    (dist_dir / "index.html").write_text("<html></html>\n", encoding="utf-8")
    (assets_dir / "app.js").write_text("console.log('ok');\n", encoding="utf-8")

    manifest = build_manifest(
        dist_dir=dist_dir,
        api_base="https://operator.example",
        base_path="./",
        cid="bafytest",
    )

    assert manifest["schema"] == "zenodex/permissionless_release_manifest/v1"
    assert manifest["artifact_kind"] == "static_frontend"
    assert manifest["file_count"] == 2
    assert [entry["path"] for entry in manifest["files"]] == ["assets/app.js", "index.html"]
    assert manifest["cid"] == "bafytest"


def test_main_writes_manifest_file(tmp_path: Path) -> None:
    dist_dir = tmp_path / "dist"
    dist_dir.mkdir()
    (dist_dir / "index.html").write_text("ok\n", encoding="utf-8")
    out_path = tmp_path / "release_manifest.json"

    rc = main(
        [
            "--dist-dir",
            str(dist_dir),
            "--out",
            str(out_path),
            "--api-base",
            "",
            "--base-path",
            "./",
        ]
    )

    assert rc == 0
    payload = json.loads(out_path.read_text(encoding="utf-8"))
    assert payload["file_count"] == 1
    assert payload["files"][0]["path"] == "index.html"
