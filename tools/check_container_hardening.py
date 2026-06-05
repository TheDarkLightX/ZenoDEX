#!/usr/bin/env python3
"""Fail-closed static checks for ZenoDEX container hardening artifacts."""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path
from typing import Any

import yaml


ROOT = Path(__file__).resolve().parents[1]


def _load_yaml(path: Path) -> dict[str, Any]:
    try:
        data = yaml.safe_load(path.read_text(encoding="utf-8"))
    except Exception as exc:  # pragma: no cover - message path
        raise AssertionError(f"{path}: failed to parse YAML: {exc}") from exc
    if not isinstance(data, dict):
        raise AssertionError(f"{path}: expected YAML object")
    return data


def _service(path: Path, name: str) -> dict[str, Any]:
    data = _load_yaml(path)
    services = data.get("services")
    if not isinstance(services, dict) or name not in services:
        raise AssertionError(f"{path}: missing service {name!r}")
    svc = services[name]
    if not isinstance(svc, dict):
        raise AssertionError(f"{path}: service {name!r} must be an object")
    return svc


def _as_list(value: Any) -> list[Any]:
    if value is None:
        return []
    if isinstance(value, list):
        return value
    return [value]


def _require(condition: bool, label: str, issues: list[str]) -> None:
    if not condition:
        issues.append(label)


def _has_no_new_privileges(svc: dict[str, Any]) -> bool:
    opts = [str(item) for item in _as_list(svc.get("security_opt"))]
    return "no-new-privileges:true" in opts


def _has_apparmor(svc: dict[str, Any], profile: str) -> bool:
    opts = [str(item) for item in _as_list(svc.get("security_opt"))]
    return f"apparmor:{profile}" in opts or f"apparmor={profile}" in opts


def _drops_all_caps(svc: dict[str, Any]) -> bool:
    return "ALL" in {str(item) for item in _as_list(svc.get("cap_drop"))}


def _tmpfs_entries(svc: dict[str, Any]) -> dict[str, str]:
    entries: dict[str, str] = {}
    for raw in _as_list(svc.get("tmpfs")):
        text = str(raw)
        mount = text.split(":", 1)[0]
        entries[mount] = text
    return entries


def _tmpfs_has_flags(svc: dict[str, Any], mount: str) -> bool:
    entry = _tmpfs_entries(svc).get(mount, "")
    return all(flag in entry.split(",") or flag in entry for flag in ("noexec", "nosuid", "nodev"))


def _env_value(svc: dict[str, Any], key: str) -> str | None:
    env = svc.get("environment")
    if isinstance(env, dict):
        value = env.get(key)
        return None if value is None else str(value)
    if isinstance(env, list):
        prefix = f"{key}="
        for item in env:
            text = str(item)
            if text.startswith(prefix):
                return text[len(prefix) :]
    return None


def _command_text(svc: dict[str, Any]) -> str:
    return " ".join(str(item) for item in _as_list(svc.get("command")))


def _env_requires_orchestrator(svc: dict[str, Any], key: str) -> bool:
    value = _env_value(svc, key)
    if value is None:
        return False
    return value.startswith(f"${{{key}:?")


def _host_ports_are_loopback_only(svc: dict[str, Any]) -> bool:
    ports = _as_list(svc.get("ports"))
    if not ports:
        return True
    for raw in ports:
        text = str(raw)
        if text.startswith("127.0.0.1:"):
            continue
        return False
    return True


def _check_main_compose(issues: list[str]) -> None:
    path = ROOT / "docker-compose.yml"
    svc = _service(path, "zenodex")
    _require(_has_no_new_privileges(svc), "docker-compose.yml: zenodex must set no-new-privileges:true", issues)
    _require(_drops_all_caps(svc), "docker-compose.yml: zenodex must drop ALL capabilities", issues)
    _require(svc.get("read_only") is True, "docker-compose.yml: zenodex rootfs must be read_only", issues)
    _require(svc.get("pids_limit") is not None, "docker-compose.yml: zenodex must set pids_limit", issues)
    _require(svc.get("mem_limit") is not None, "docker-compose.yml: zenodex must set mem_limit", issues)
    for mount in ("/tmp", "/var/run", "/var/cache/nginx", "/var/log/nginx"):
        _require(_tmpfs_has_flags(svc, mount), f"docker-compose.yml: zenodex tmpfs {mount} must include noexec,nosuid,nodev", issues)
    api_host = _env_value(svc, "API_HOST")
    _require(
        api_host in {"${API_HOST:-127.0.0.1}", "127.0.0.1"},
        f"docker-compose.yml: zenodex API_HOST must default to 127.0.0.1, got {api_host!r}",
        issues,
    )


def _check_local_compose(issues: list[str]) -> None:
    path = ROOT / "docker-compose.local.yml"
    svc = _service(path, "zenodex-local")
    # REVIEW [B -> A-]: docker-compose.local.yml is a separate CPMM-carrying
    # entry point from the default compose file. It should not rely on humans
    # remembering that the main compose hardening happened to be similar today.
    _require(_has_no_new_privileges(svc), f"{path.name}: zenodex-local must set no-new-privileges:true", issues)
    _require(_drops_all_caps(svc), f"{path.name}: zenodex-local must drop ALL capabilities", issues)
    _require(svc.get("read_only") is True, f"{path.name}: zenodex-local rootfs must be read_only", issues)
    _require(svc.get("pids_limit") is not None, f"{path.name}: zenodex-local must set pids_limit", issues)
    _require(svc.get("mem_limit") is not None, f"{path.name}: zenodex-local must set mem_limit", issues)
    _require(svc.get("init") is True, f"{path.name}: zenodex-local must set init: true", issues)
    for mount in ("/tmp", "/var/run", "/var/cache/nginx", "/var/log/nginx"):
        _require(_tmpfs_has_flags(svc, mount), f"{path.name}: zenodex-local tmpfs {mount} must include noexec,nosuid,nodev", issues)
    _require(_host_ports_are_loopback_only(svc), f"{path.name}: zenodex-local host ports must bind to 127.0.0.1 only", issues)
    _require(
        _env_value(svc, "API_HOST") == "127.0.0.1",
        f"{path.name}: zenodex-local API_HOST must stay 127.0.0.1",
        issues,
    )


def _check_apparmor_overlay(issues: list[str]) -> None:
    path = ROOT / "docker-compose.apparmor.yml"
    svc = _service(path, "zenodex")
    _require(_has_apparmor(svc, "zenodex"), "docker-compose.apparmor.yml: zenodex must select apparmor:zenodex", issues)


def _check_aux_compose(path: Path, service: str, issues: list[str]) -> None:
    svc = _service(path, service)
    _require(_has_no_new_privileges(svc), f"{path.name}: {service} must set no-new-privileges:true", issues)
    _require(_drops_all_caps(svc), f"{path.name}: {service} must drop ALL capabilities", issues)
    _require(svc.get("pids_limit") is not None, f"{path.name}: {service} must set pids_limit", issues)
    _require(svc.get("mem_limit") is not None, f"{path.name}: {service} must set mem_limit", issues)
    _require(svc.get("init") is True, f"{path.name}: {service} must set init: true", issues)
    _require(_tmpfs_has_flags(svc, "/tmp"), f"{path.name}: {service} tmpfs /tmp must include noexec,nosuid,nodev", issues)


def _check_local_testnet_compose(issues: list[str]) -> None:
    path = ROOT / "docker-compose.local-testnet.yml"
    service_names = (
        "zeno-ledger-bootstrap",
        "zeno-ledger-writer",
        "zeno-ledger-forwarder",
        "zeno-ledger-readonly",
        "tau-local",
        "zenodex-oracle",
        "zenodex-api",
        "zenodex-nginx",
    )
    read_only_services = set(service_names) - {"tau-local"}
    for service in service_names:
        _check_aux_compose(path, service, issues)
        svc = _service(path, service)
        if service in read_only_services:
            _require(svc.get("read_only") is True, f"{path.name}: {service} rootfs must be read_only", issues)

    writer = _service(path, "zeno-ledger-writer")
    forwarder = _service(path, "zeno-ledger-forwarder")
    api = _service(path, "zenodex-api")
    nginx = _service(path, "zenodex-nginx")

    # REVIEW [B -> A-]: the checker hardened the generic Docker paths but missed
    # the community local-testnet stack, which is where CPMM writes are exposed
    # through API/nginx/ledger containers. Keep this coverage tied to the compose
    # file that operators actually launch, and require mutation auth on the
    # write-capable services.
    for service, svc in (("zeno-ledger-writer", writer), ("zeno-ledger-forwarder", forwarder)):
        _require(
            "--write-auth-token-env" in _command_text(svc),
            f"{path.name}: {service} must bind writes to --write-auth-token-env",
            issues,
        )
        _require(
            _env_requires_orchestrator(svc, "ZENO_LEDGER_WRITER_TOKEN"),
            f"{path.name}: {service} must require orchestrator-injected ZENO_LEDGER_WRITER_TOKEN",
            issues,
        )
    _require(
        _env_requires_orchestrator(api, "ZENODEX_API_BEARER_TOKEN"),
        f"{path.name}: zenodex-api must require orchestrator-injected ZENODEX_API_BEARER_TOKEN",
        issues,
    )
    _require(
        _host_ports_are_loopback_only(nginx),
        f"{path.name}: zenodex-nginx host ports must bind to 127.0.0.1 only",
        issues,
    )


def _check_multimachine_compose(issues: list[str]) -> None:
    path = ROOT / "docker-compose.multimachine.yml"
    for service in (
        "zeno-ledger-bootstrap",
        "zeno-ledger-writer",
        "zeno-ledger-forwarder",
        "zeno-ledger-readonly",
        "zeno-ledger-multidocker-controller",
    ):
        _check_aux_compose(path, service, issues)
        svc = _service(path, service)
        _require(svc.get("read_only") is True, f"{path.name}: {service} rootfs must be read_only", issues)

    writer = _service(path, "zeno-ledger-writer")
    forwarder = _service(path, "zeno-ledger-forwarder")
    controller = _service(path, "zeno-ledger-multidocker-controller")

    # REVIEW [C -> A-]: this stack previously defaulted the mutation bearer
    # token to a known string (`local-multidocker-token`). That made the
    # multi-node smoke convenient, but it was a bad production habit for a
    # write-capable container path. Require the operator/orchestrator to inject
    # the token just like the local-testnet stack does.
    for service, svc in (
        ("zeno-ledger-writer", writer),
        ("zeno-ledger-forwarder", forwarder),
        ("zeno-ledger-multidocker-controller", controller),
    ):
        _require(
            "--write-auth-token-env" in _command_text(svc),
            f"{path.name}: {service} must bind writes to --write-auth-token-env",
            issues,
        )
        _require(
            _env_requires_orchestrator(svc, "ZENO_LEDGER_WRITER_TOKEN"),
            f"{path.name}: {service} must require orchestrator-injected ZENO_LEDGER_WRITER_TOKEN",
            issues,
        )
    _require(
        "--submit-peer-auth-token-env" in _command_text(forwarder),
        f"{path.name}: zeno-ledger-forwarder must bind peer submits to --submit-peer-auth-token-env",
        issues,
    )


def _check_apparmor_profile(issues: list[str]) -> None:
    path = ROOT / ".docker" / "apparmor" / "zenodex"
    text = path.read_text(encoding="utf-8")
    required_patterns = {
        "profile name": r"profile\s+zenodex\b",
        "deny raw sockets": r"deny\s+network\s+raw",
        "deny packet sockets": r"deny\s+network\s+packet",
        "deny capabilities": r"deny\s+capability",
        "deny mount": r"deny\s+mount",
        "deny ptrace": r"deny\s+ptrace",
        "deny proc sys": r"deny\s+@\{PROC\}/sys/\*\*",
        "deny sys writes": r"deny\s+/sys/\*\*",
        "allow app data writes": r"/app/data/\*\*\s+rwk",
    }
    for label, pattern in required_patterns.items():
        _require(re.search(pattern, text) is not None, f"{path}: missing {label}", issues)


def _check_dockerfile(path: Path, issues: list[str]) -> None:
    text = path.read_text(encoding="utf-8")
    _require(re.search(r"(?m)^USER\s+zenodex\s*$", text) is not None, f"{path.name}: production image must end as USER zenodex", issues)
    _require("EXPOSE 8080 8000" in text, f"{path.name}: expected unprivileged UI port expose", issues)


def _check_operator_dockerfile(issues: list[str]) -> None:
    path = ROOT / "Dockerfile.operator-tools"
    text = path.read_text(encoding="utf-8")
    _require("--require-hashes -r requirements-core.lock.txt" in text, "Dockerfile.operator-tools: must install hash-locked requirements", issues)
    _require("COPY tools/ ./tools/" in text, "Dockerfile.operator-tools: must copy operator tools", issues)
    _require(
        "COPY generated/batch_auction_settler_v1/python_ref/batch_auction_settler_v1_ref.py" in text,
        "Dockerfile.operator-tools: must copy generated UPBA reference model",
        issues,
    )
    _require(re.search(r"(?m)^USER\s+zenodex\s*$", text) is not None, "Dockerfile.operator-tools: must end as USER zenodex", issues)


def run_checks() -> list[str]:
    issues: list[str] = []
    _check_main_compose(issues)
    _check_local_compose(issues)
    _check_apparmor_overlay(issues)
    _check_aux_compose(ROOT / "docker-compose.permissionless.yml", "tau-local", issues)
    _check_aux_compose(ROOT / "docker-compose.chaos.yml", "toxiproxy", issues)
    _check_aux_compose(ROOT / "docker-compose.two-node.yml", "zeno-ledger-two-node-smoke", issues)
    _check_multimachine_compose(issues)
    _check_local_testnet_compose(issues)
    _check_apparmor_profile(issues)
    _check_dockerfile(ROOT / "Dockerfile", issues)
    _check_dockerfile(ROOT / "Dockerfile.production-hashlocked", issues)
    _check_operator_dockerfile(issues)
    return issues


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.parse_args()
    issues = run_checks()
    if issues:
        for issue in issues:
            print(f"error: {issue}", file=sys.stderr)
        return 1
    print("container hardening checks passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
