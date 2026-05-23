from __future__ import annotations

import importlib.util
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "check_docker_hashlocked_install", ROOT / "tools/check_docker_hashlocked_install.py"
)
assert SPEC is not None and SPEC.loader is not None
check_docker_hashlocked_install = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = check_docker_hashlocked_install
SPEC.loader.exec_module(check_docker_hashlocked_install)


def _write_temp_dockerfile(path: Path, install_line: str) -> None:
    path.write_text(
        "\n".join(
            (
                "FROM python:3.11-slim-bookworm AS python-base",
                "WORKDIR /app",
                "COPY requirements-core.lock.txt ./",
                install_line,
                "FROM python:3.11-slim-bookworm AS production",
                'ENV API_HOST="127.0.0.1"',
                "USER zenodex",
            )
        )
        + "\n",
        encoding="utf-8",
    )


def test_repo_docker_hashlocked_install_audit_passes() -> None:
    report = check_docker_hashlocked_install.check_docker_hashlocked_install(ROOT)

    assert report["ok"], report["findings"]
    assert report["path"] == "Dockerfile.hashlocked"


def test_checker_rejects_missing_require_hashes(tmp_path: Path) -> None:
    dockerfile = tmp_path / "Dockerfile.hashlocked"
    _write_temp_dockerfile(
        dockerfile,
        "RUN python -m pip install -r requirements-core.lock.txt",
    )

    report = check_docker_hashlocked_install.check_docker_hashlocked_install(
        root=tmp_path,
        dockerfile=dockerfile,
    )

    assert not report["ok"]
    assert report["findings"][0]["code"] == "missing_require_hashes"


def test_checker_rejects_unlocked_requirements_install(tmp_path: Path) -> None:
    dockerfile = tmp_path / "Dockerfile.hashlocked"
    _write_temp_dockerfile(
        dockerfile,
        "RUN python -m pip install --require-hashes -r requirements-core.txt",
    )

    report = check_docker_hashlocked_install.check_docker_hashlocked_install(
        root=tmp_path,
        dockerfile=dockerfile,
    )

    assert not report["ok"]
    assert report["findings"][0]["code"] == "unlocked_requirements_install"


def test_checker_rejects_non_local_api_host(tmp_path: Path) -> None:
    dockerfile = tmp_path / "Dockerfile.hashlocked"
    dockerfile.write_text(
        "\n".join(
            (
                "FROM python:3.11-slim-bookworm AS python-base",
                "WORKDIR /app",
                "COPY requirements-core.lock.txt ./",
                "RUN python -m pip install --require-hashes -r requirements-core.lock.txt",
                "FROM python:3.11-slim-bookworm AS production",
                'ENV API_HOST="0.0.0.0"',
                "USER zenodex",
            )
        )
        + "\n",
        encoding="utf-8",
    )

    report = check_docker_hashlocked_install.check_docker_hashlocked_install(
        root=tmp_path,
        dockerfile=dockerfile,
    )

    assert not report["ok"]
    assert any(f["code"] == "api_host_not_loopback" for f in report["findings"])


def test_checker_rejects_root_final_user(tmp_path: Path) -> None:
    dockerfile = tmp_path / "Dockerfile.hashlocked"
    dockerfile.write_text(
        "\n".join(
            (
                "FROM python:3.11-slim-bookworm AS python-base",
                "WORKDIR /app",
                "COPY requirements-core.lock.txt ./",
                "RUN python -m pip install --require-hashes -r requirements-core.lock.txt",
                "FROM python:3.11-slim-bookworm AS production",
                'ENV API_HOST="127.0.0.1"',
                "USER root",
            )
        )
        + "\n",
        encoding="utf-8",
    )

    report = check_docker_hashlocked_install.check_docker_hashlocked_install(
        root=tmp_path,
        dockerfile=dockerfile,
    )

    assert not report["ok"]
    assert any(f["code"] == "root_final_user" for f in report["findings"])


def test_checker_rejects_obvious_secrets(tmp_path: Path) -> None:
    dockerfile = tmp_path / "Dockerfile.hashlocked"
    dockerfile.write_text(
        "\n".join(
            (
                "FROM python:3.11-slim-bookworm AS python-base",
                "WORKDIR /app",
                "COPY requirements-core.lock.txt ./",
                "RUN python -m pip install --require-hashes -r requirements-core.lock.txt",
                "FROM python:3.11-slim-bookworm AS production",
                'ENV API_HOST="127.0.0.1"',
                "USER zenodex",
                "ENV PRIVATE_KEY=\"secret-stuff\"",
            )
        )
        + "\n",
        encoding="utf-8",
    )

    report = check_docker_hashlocked_install.check_docker_hashlocked_install(
        root=tmp_path,
        dockerfile=dockerfile,
    )

    assert not report["ok"]
    assert any(f["code"] == "obvious_secret_reference" for f in report["findings"])


def test_cli_accepts_existing_strict_digest_flags() -> None:
    result = subprocess.run(
        [
            sys.executable,
            str(ROOT / "tools" / "check_docker_hashlocked_install.py"),
            "--dockerfile",
            "Dockerfile.operator-tools",
            "--strict-digest",
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )

    assert result.returncode == 0, result.stdout + result.stderr
