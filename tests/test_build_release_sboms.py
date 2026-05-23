from __future__ import annotations

import base64
import json
from pathlib import Path

import pytest

from tools.build_release_sboms import build_release_sboms, main


HASH_A = "a" * 64
HASH_B = "b" * 64
HASH_C = "c" * 64


def test_build_release_sboms_from_minimal_locks(tmp_path: Path) -> None:
    core = tmp_path / "requirements-core.lock.txt"
    agents = tmp_path / "requirements-agents.lock.txt"
    ui = tmp_path / "package-lock.json"
    core.write_text(
        "canonicaljson==2.0.0 \\\n"
        f"    --hash=sha256:{HASH_A}\n"
        "py-ecc==8.0.0 \\\n"
        f"    --hash=sha256:{HASH_B}\n",
        encoding="utf-8",
    )
    agents.write_text(f"openai==2.8.1 \\\n    --hash=sha256:{HASH_C}\n", encoding="utf-8")
    digest = bytes(range(64))
    ui.write_text(
        json.dumps(
            {
                "packages": {
                    "": {"name": "dex-ui", "version": "0.0.0"},
                    "node_modules/@noble/curves": {
                        "name": "@noble/curves",
                        "version": "1.2.0",
                        "integrity": "sha512-" + base64.b64encode(digest).decode("ascii"),
                    },
                    "node_modules/@zenodex/proof-client": {
                        "link": True,
                        "resolved": "../../packages/zeno-proof-client",
                    },
                }
            }
        ),
        encoding="utf-8",
    )

    report = build_release_sboms(out_dir=tmp_path / "out", core_lock=core, agents_lock=agents, ui_lock=ui)

    assert report["ok"] is True
    paths = {Path(item["path"]).name for item in report["outputs"]}
    assert paths == {"requirements-core.cdx.json", "requirements-agents.cdx.json", "dex-ui.cdx.json"}

    core_bom = json.loads((tmp_path / "out" / "requirements-core.cdx.json").read_text(encoding="utf-8"))
    assert core_bom["bomFormat"] == "CycloneDX"
    assert [item["name"] for item in core_bom["components"]] == ["canonicaljson", "py-ecc"]
    assert core_bom["components"][0]["hashes"] == [{"alg": "SHA-256", "content": HASH_A}]

    ui_bom = json.loads((tmp_path / "out" / "dex-ui.cdx.json").read_text(encoding="utf-8"))
    assert ui_bom["components"][0]["name"] == "@noble/curves"
    assert ui_bom["components"][0]["hashes"][0]["alg"] == "SHA-512"
    assert ui_bom["components"][0]["hashes"][0]["content"] == digest.hex()
    assert all(component["version"] != "None" for component in ui_bom["components"])


def test_build_release_sboms_cli_outputs_json(tmp_path: Path, capsys) -> None:
    core = tmp_path / "requirements-core.lock.txt"
    agents = tmp_path / "requirements-agents.lock.txt"
    core.write_text(f"canonicaljson==2.0.0 \\\n    --hash=sha256:{HASH_A}\n", encoding="utf-8")
    agents.write_text(f"openai==2.8.1 \\\n    --hash=sha256:{HASH_B}\n", encoding="utf-8")

    code = main(
        [
            "--out-dir",
            str(tmp_path / "out"),
            "--core-lock",
            str(core),
            "--agents-lock",
            str(agents),
            "--ui-lock",
            str(tmp_path / "missing-package-lock.json"),
        ]
    )

    assert code == 0
    assert json.loads(capsys.readouterr().out)["ok"] is True


def test_build_release_sboms_rejects_python_lock_without_hashes(tmp_path: Path) -> None:
    core = tmp_path / "requirements-core.lock.txt"
    agents = tmp_path / "requirements-agents.lock.txt"
    core.write_text("canonicaljson==2.0.0\n", encoding="utf-8")
    agents.write_text(f"openai==2.8.1 \\\n    --hash=sha256:{HASH_A}\n", encoding="utf-8")

    with pytest.raises(ValueError, match="no package hashes"):
        build_release_sboms(out_dir=tmp_path / "out", core_lock=core, agents_lock=agents)


def test_build_release_sboms_rejects_invalid_npm_integrity(tmp_path: Path) -> None:
    core = tmp_path / "requirements-core.lock.txt"
    agents = tmp_path / "requirements-agents.lock.txt"
    ui = tmp_path / "package-lock.json"
    core.write_text(f"canonicaljson==2.0.0 \\\n    --hash=sha256:{HASH_A}\n", encoding="utf-8")
    agents.write_text(f"openai==2.8.1 \\\n    --hash=sha256:{HASH_B}\n", encoding="utf-8")
    ui.write_text(
        json.dumps(
            {
                "packages": {
                    "node_modules/@noble/curves": {
                        "name": "@noble/curves",
                        "version": "1.2.0",
                        "integrity": "sha512-not-valid-base64",
                    },
                }
            }
        ),
        encoding="utf-8",
    )

    with pytest.raises(ValueError, match="invalid SRI hash"):
        build_release_sboms(out_dir=tmp_path / "out", core_lock=core, agents_lock=agents, ui_lock=ui)
