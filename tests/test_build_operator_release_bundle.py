from __future__ import annotations

import hashlib
import io
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
        "bin/zenodex-local-testnet",
        "scripts/install_zenodex.sh",
        "scripts/install_zenodex.ps1",
        "scripts/zenodex_testnet_demo.sh",
        "scripts/zenodex_testnet_demo.ps1",
        "src/__init__.py",
        "src/integration/__init__.py",
        "tools/zenoctl.py",
        "tools/zeno_ledger_node.py",
        "tools/check_zeno_ledger_light_client_checkpoint.py",
        "tools/build_operator_release_bundle.py",
        "config/deploy/local-dev.yaml",
        "formal/property/production_key_management_v0.json",
        ".dockerignore",
        ".docker/entrypoint.sh",
        ".docker/nginx.conf",
        "Dockerfile",
        "Dockerfile.hashlocked",
        "Dockerfile.operator-tools",
        "Dockerfile.production-hashlocked",
        "docker-compose.yml",
        "docker-compose.local.yml",
        "docker-compose.local-testnet.yml",
        "docker-compose.two-node.yml",
        "docker-compose.multimachine.yml",
        "docker-compose.permissionless.yml",
        "docker-compose.testnet-demo.yml",
        "generated/batch_auction_settler_v1/python_ref/batch_auction_settler_v1_ref.py",
        "generated/perp_python/perp_epoch_clearinghouse_2p_v0_1_ref.py",
        "generated/perp_python/perp_epoch_clearinghouse_3p_transfer_v0_1_ref.py",
        "generated/perp_python/perp_epoch_isolated_v2_ref.py",
        "generated/perp_python/perp_epoch_isolated_v3_ref.py",
        "packages/zeno-proof-client/package.json",
        "packages/zeno-proof-client/src/index.js",
        "requirements-core.lock.txt",
        "requirements-dev.lock.txt",
        "requirements-agents.lock.txt",
        "pyproject.toml",
        "pytest.ini",
        "README.md",
        "docs/DEPLOYMENT_QUICKSTART.md",
        "docs/DOCKER_HASHLOCKED_DEPLOYMENT.md",
        "docs/LOCAL_TESTNET_QUICKSTART.md",
        "docs/PERMISSIONLESS_HOSTING.md",
        "docs/ZENO_LEDGER_PROOF_COVERAGE_MATRIX_V0.json",
        "docs/ZENO_LEDGER_TWO_MACHINE_TESTNET.md",
        "docs/ZENO_SDK_BROWSER_WALLET_SYNC.md",
        "docs/assurance/README.md",
        "docs/claims_registry.yaml",
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
    assert "bin/zenodex-local-testnet" in paths
    assert "scripts/install_zenodex.sh" in paths
    assert "scripts/zenodex_testnet_demo.sh" in paths
    assert "docker-compose.testnet-demo.yml" in paths
    assert "tools/zenoctl.py" in paths
    assert "tools/check_zeno_ledger_light_client_checkpoint.py" in paths
    assert "tools/build_operator_release_bundle.py" in paths
    assert "Dockerfile.hashlocked" in paths
    assert ".dockerignore" in paths
    assert "formal/property/production_key_management_v0.json" in paths
    assert "docker-compose.local-testnet.yml" in paths
    assert "docs/LOCAL_TESTNET_QUICKSTART.md" in paths
    assert "docs/ZENO_LEDGER_PROOF_COVERAGE_MATRIX_V0.json" in paths
    assert "docs/claims_registry.yaml" in paths
    assert "packages/zeno-proof-client/package.json" in paths
    assert "generated/perp_python/perp_epoch_clearinghouse_2p_v0_1_ref.py" in paths
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
    assert "zenodex-operator-prefixed/bin/zenodex-local-testnet" in names


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
    code = main(["build", "--repo-root", str(root), "--out-dir", str(tmp_path / "out"), "--version", "cli", "--json"])
    build_out = json.loads(capsys.readouterr().out)
    assert code == 0
    assert build_out["ok"] is True
    assert build_out["archive"] == build_out["archive_path"]
    assert build_out["manifest"] == build_out["manifest_path"]

    code = main(["verify", "--manifest", build_out["manifest_path"], "--json"])
    verify_out = json.loads(capsys.readouterr().out)
    assert code == 0
    assert verify_out["ok"] is True
    assert verify_out["status"] == "verify"


def test_operator_release_bundle_rejects_unsafe_version(tmp_path: Path, capsys) -> None:
    root = _minimal_repo(tmp_path)
    code = main(["build", "--repo-root", str(root), "--out-dir", str(tmp_path / "out"), "--version", "../bad"])

    assert code != 0
    assert "version must contain only ASCII" in capsys.readouterr().err


def _write_manifest(path: Path, *, archive_name: str, archive_sha256: str, version: str, files: list[dict[str, object]]) -> None:
    manifest = {
        "schema": "zenodex.operator_release_bundle.v0",
        "version": version,
        "archive_name": archive_name,
        "archive_sha256": archive_sha256,
        "generated_at": "2026-01-01T00:00:00Z",
        "generator": "test",
        "file_count": len(files),
        "files": files,
    }
    path.write_text(json.dumps(manifest), encoding="utf-8")


def test_verify_rejects_non_regular_archive_members(tmp_path: Path) -> None:
    archive_path = tmp_path / "bundle.tar.gz"
    payload = b"ok\n"
    with tarfile.open(archive_path, "w:gz") as tar:
        regular = tarfile.TarInfo("zenodex-operator-v1/bin/zenoctl")
        regular.size = len(payload)
        tar.addfile(regular, fileobj=io.BytesIO(payload))
        link = tarfile.TarInfo("zenodex-operator-v1/escape")
        link.type = tarfile.SYMTYPE
        link.linkname = "../../outside"
        tar.addfile(link)

    manifest_path = tmp_path / "manifest.json"
    _write_manifest(
        manifest_path,
        archive_name=archive_path.name,
        archive_sha256=hashlib.sha256(archive_path.read_bytes()).hexdigest(),
        version="v1",
        files=[
            {"path": "bin/zenoctl", "size_bytes": len(payload), "sha256": hashlib.sha256(payload).hexdigest()},
        ],
    )
    verify = verify_operator_release_manifest(manifest_path=manifest_path)

    assert verify["ok"] is False
    assert "archive contains non-regular file: escape" in verify["errors"]


def test_verify_rejects_duplicate_and_unsafe_member_paths(tmp_path: Path) -> None:
    archive_path = tmp_path / "bundle.tar.gz"
    payload = b"ok\n"
    with tarfile.open(archive_path, "w:gz") as tar:
        a = tarfile.TarInfo("zenodex-operator-v1/bin/zenoctl")
        a.size = len(payload)
        tar.addfile(a, fileobj=io.BytesIO(payload))

        dup = tarfile.TarInfo("zenodex-operator-v1/bin/zenoctl")
        dup.size = len(payload)
        tar.addfile(dup, fileobj=io.BytesIO(payload))

        bad = tarfile.TarInfo("zenodex-operator-v1/../evil.txt")
        bad.size = len(payload)
        tar.addfile(bad, fileobj=io.BytesIO(payload))

    manifest_path = tmp_path / "manifest.json"
    _write_manifest(
        manifest_path,
        archive_name=archive_path.name,
        archive_sha256=hashlib.sha256(archive_path.read_bytes()).hexdigest(),
        version="v1",
        files=[
            {"path": "bin/zenoctl", "size_bytes": len(payload), "sha256": hashlib.sha256(payload).hexdigest()},
        ],
    )
    verify = verify_operator_release_manifest(manifest_path=manifest_path)

    assert verify["ok"] is False
    assert "archive contains duplicate path: bin/zenoctl" in verify["errors"]
    assert "archive member has unsafe path: ../evil.txt" in verify["errors"]
