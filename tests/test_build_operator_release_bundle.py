from __future__ import annotations

import json
import tarfile
from pathlib import Path

from tools.build_operator_release_bundle import (
    build_operator_release_bundle,
    main,
    verify_operator_release_manifest,
)

def _write(path: Path, text: str = "x\n") -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _minimal_repo(tmp_path: Path) -> Path:
    root = tmp_path / "repo"
    for relpath in (
        "bin/zenoctl",
        "scripts/install_zenodex.sh",
        "scripts/install_zenodex.ps1",
        "src/__init__.py",
        "src/integration/__init__.py",
        "tools/zenoctl.py",
        "tools/zeno_ledger_node.py",
        "tools/check_zeno_ledger_light_client_checkpoint.py",
        "tools/build_operator_release_bundle.py",
        "config/deploy/local-dev.yaml",
        ".docker/entrypoint.sh",
        "Dockerfile",
        "Dockerfile.hashlocked",
        "Dockerfile.operator-tools",
        "Dockerfile.production-hashlocked",
        "docker-compose.yml",
        "docker-compose.local.yml",
        "docker-compose.two-node.yml",
        "docker-compose.multimachine.yml",
        "docker-compose.permissionless.yml",
        "requirements-core.lock.txt",
        "requirements-dev.lock.txt",
        "requirements-agents.lock.txt",
        "pyproject.toml",
        "pytest.ini",
        "README.md",
        "docs/DEPLOYMENT_QUICKSTART.md",
        "docs/DOCKER_HASHLOCKED_DEPLOYMENT.md",
        "docs/PERMISSIONLESS_HOSTING.md",
        "docs/ZENO_LEDGER_TWO_MACHINE_TESTNET.md",
        "docs/ZENO_SDK_BROWSER_WALLET_SYNC.md",
        "docs/assurance/README.md",
        "docs/tau_supported_runtime_contract.json",
    ):
        _write(root / relpath, f"{relpath}\n")
    _write(root / "internal/secret.txt", "do not package\n")
    _write(root / "tests/test_not_packaged.py", "do not package\n")
    _write(root / "tools/_secbin/trivy", "local downloaded scanner\n")
    _write(root / "tools/confidential_attestation_verifier_rust/target/debug/build-output", "local rust build\n")
    _write(root / "src/tau_specs/.tau_history", "local tau history\n")
    _write(root / "packages/zeno-proof-client/node_modules/.package-lock.json", "local node install\n")
    return root


def test_build_operator_release_bundle_writes_archive_and_manifest(tmp_path: Path) -> None:
    root = _minimal_repo(tmp_path)
    report = build_operator_release_bundle(root=root, out_dir=tmp_path / "out", version="test")

    assert report["ok"] is True
    archive_path = Path(report["archive_path"])
    manifest_path = Path(report["manifest_path"])
    assert archive_path.is_file()
    assert manifest_path.is_file()

    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    paths = {item["path"] for item in manifest["files"]}
    assert "bin/zenoctl" in paths
    assert "scripts/install_zenodex.sh" in paths
    assert "tools/zenoctl.py" in paths
    assert "tools/check_zeno_ledger_light_client_checkpoint.py" in paths
    assert "tools/build_operator_release_bundle.py" in paths
    assert "Dockerfile.hashlocked" in paths
    assert "docs/assurance/README.md" in paths
    assert all(not path.startswith("tests/") for path in paths)
    assert all("internal/" not in path for path in paths)
    assert all("_secbin/" not in path for path in paths)
    assert all("/target/" not in path for path in paths)
    assert all("node_modules/" not in path for path in paths)
    assert all(not path.endswith(".tau_history") for path in paths)

    verify = verify_operator_release_manifest(manifest_path=manifest_path)
    assert verify["ok"] is True


def test_operator_release_bundle_archive_members_are_prefixed(tmp_path: Path) -> None:
    root = _minimal_repo(tmp_path)
    report = build_operator_release_bundle(root=root, out_dir=tmp_path / "out", version="prefixed")
    archive_path = Path(report["archive_path"])

    with tarfile.open(archive_path, "r:gz") as tar:
        names = [member.name for member in tar.getmembers() if member.isfile()]

    assert names
    assert all(name.startswith("zenodex-operator-prefixed/") for name in names)
    assert "zenodex-operator-prefixed/bin/zenoctl" in names


def test_operator_release_bundle_is_deterministic_for_same_checkout(tmp_path: Path) -> None:
    root = _minimal_repo(tmp_path)
    out_a = tmp_path / "a"
    out_b = tmp_path / "b"
    report_a = build_operator_release_bundle(root=root, out_dir=out_a, version="stable")
    report_b = build_operator_release_bundle(root=root, out_dir=out_b, version="stable")

    assert report_a["archive_sha256"] == report_b["archive_sha256"]


def test_operator_release_bundle_verify_rejects_tampered_archive(tmp_path: Path) -> None:
    root = _minimal_repo(tmp_path)
    report = build_operator_release_bundle(root=root, out_dir=tmp_path / "out", version="tamper")
    archive_path = Path(report["archive_path"])
    manifest_path = Path(report["manifest_path"])
    with archive_path.open("ab") as fh:
        fh.write(b"tamper")

    verify = verify_operator_release_manifest(manifest_path=manifest_path)

    assert verify["ok"] is False
    assert "archive_sha256 mismatch" in verify["errors"]


def test_operator_release_bundle_cli_build_and_verify(tmp_path: Path, capsys) -> None:
    root = _minimal_repo(tmp_path)
    code = main(["build", "--repo-root", str(root), "--out-dir", str(tmp_path / "out"), "--version", "cli"])
    build_out = json.loads(capsys.readouterr().out)
    assert code == 0
    assert build_out["ok"] is True

    code = main(["verify", "--manifest", build_out["manifest_path"]])
    verify_out = json.loads(capsys.readouterr().out)
    assert code == 0
    assert verify_out["ok"] is True
