from __future__ import annotations

import importlib.util
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "check_container_hardening", ROOT / "tools/check_container_hardening.py"
)
assert SPEC is not None and SPEC.loader is not None
check_container_hardening = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = check_container_hardening
SPEC.loader.exec_module(check_container_hardening)


def _copy_local_testnet_compose(tmp_path: Path, *, transform=lambda text: text) -> None:
    src = ROOT / "docker-compose.local-testnet.yml"
    dst = tmp_path / "docker-compose.local-testnet.yml"
    dst.write_text(transform(src.read_text(encoding="utf-8")), encoding="utf-8")


def _copy_compose(tmp_path: Path, filename: str, *, transform=lambda text: text) -> None:
    src = ROOT / filename
    dst = tmp_path / filename
    dst.write_text(transform(src.read_text(encoding="utf-8")), encoding="utf-8")


def test_container_hardening_checks_cover_repo_local_testnet_stack() -> None:
    assert check_container_hardening.run_checks() == []


def test_local_testnet_checker_rejects_optional_api_bearer_token(tmp_path, monkeypatch) -> None:
    def loosen_api_token(text: str) -> str:
        required = (
            "ZENODEX_API_BEARER_TOKEN: "
            "${ZENODEX_API_BEARER_TOKEN:?ZENODEX_API_BEARER_TOKEN must be set by the orchestrator}"
        )
        optional = "ZENODEX_API_BEARER_TOKEN: ${ZENODEX_API_BEARER_TOKEN:-}"
        assert required in text
        return text.replace(required, optional)

    _copy_local_testnet_compose(tmp_path, transform=loosen_api_token)
    monkeypatch.setattr(check_container_hardening, "ROOT", tmp_path)
    issues: list[str] = []

    check_container_hardening._check_local_testnet_compose(issues)

    assert any("zenodex-api must require orchestrator-injected ZENODEX_API_BEARER_TOKEN" in issue for issue in issues)


def test_local_testnet_checker_rejects_public_nginx_host_bind(tmp_path, monkeypatch) -> None:
    def expose_nginx(text: str) -> str:
        loopback = '"127.0.0.1:${UI_PORT:-18080}:8080"'
        public = '"${UI_PORT:-18080}:8080"'
        assert loopback in text
        return text.replace(loopback, public)

    _copy_local_testnet_compose(tmp_path, transform=expose_nginx)
    monkeypatch.setattr(check_container_hardening, "ROOT", tmp_path)
    issues: list[str] = []

    check_container_hardening._check_local_testnet_compose(issues)

    assert any("zenodex-nginx host ports must bind to 127.0.0.1 only" in issue for issue in issues)


def test_local_testnet_checker_rejects_ledger_writer_without_auth_binding(tmp_path, monkeypatch) -> None:
    def remove_writer_auth(text: str) -> str:
        needle = "      - --write-auth-token-env\n      - ZENO_LEDGER_WRITER_TOKEN\n"
        assert needle in text
        return text.replace(needle, "", 1)

    _copy_local_testnet_compose(tmp_path, transform=remove_writer_auth)
    monkeypatch.setattr(check_container_hardening, "ROOT", tmp_path)
    issues: list[str] = []

    check_container_hardening._check_local_testnet_compose(issues)

    assert any("zeno-ledger-writer must bind writes to --write-auth-token-env" in issue for issue in issues)


def test_local_compose_checker_rejects_public_host_bind(tmp_path, monkeypatch) -> None:
    def expose_local(text: str) -> str:
        loopback = '"127.0.0.1:8000:8000"'
        public = '"8000:8000"'
        assert loopback in text
        return text.replace(loopback, public)

    _copy_compose(tmp_path, "docker-compose.local.yml", transform=expose_local)
    monkeypatch.setattr(check_container_hardening, "ROOT", tmp_path)
    issues: list[str] = []

    check_container_hardening._check_local_compose(issues)

    assert any("zenodex-local host ports must bind to 127.0.0.1 only" in issue for issue in issues)


def test_multimachine_checker_rejects_default_writer_token(tmp_path, monkeypatch) -> None:
    def default_writer_token(text: str) -> str:
        required = (
            "ZENO_LEDGER_WRITER_TOKEN: "
            "${ZENO_LEDGER_WRITER_TOKEN:?ZENO_LEDGER_WRITER_TOKEN must be set by the orchestrator}"
        )
        weak = "ZENO_LEDGER_WRITER_TOKEN: ${ZENO_LEDGER_WRITER_TOKEN:-local-multidocker-token}"
        assert required in text
        return text.replace(required, weak)

    _copy_compose(tmp_path, "docker-compose.multimachine.yml", transform=default_writer_token)
    monkeypatch.setattr(check_container_hardening, "ROOT", tmp_path)
    issues: list[str] = []

    check_container_hardening._check_multimachine_compose(issues)

    assert any("must require orchestrator-injected ZENO_LEDGER_WRITER_TOKEN" in issue for issue in issues)
