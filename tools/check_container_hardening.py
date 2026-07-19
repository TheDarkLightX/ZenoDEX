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
    _require(
        _env_value(svc, "ZENODEX_ENV") == "production",
        "docker-compose.yml: zenodex must set ZENODEX_ENV=production",
        issues,
    )
    chain_id = _env_value(svc, "TAU_DEX_CHAIN_ID") or ""
    _require(
        "TAU_DEX_CHAIN_ID:?" in chain_id,
        "docker-compose.yml: production chain id must be mandatory",
        issues,
    )
    volumes = [str(item) for item in _as_list(svc.get("volumes"))]
    _require(
        any(item.endswith(":/var/www/zenodex/zenodex-config.json:ro") for item in volumes),
        "docker-compose.yml: production UI runtime config must be mounted read-only",
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
    _require("ENV ZENODEX_ENV=production" in text, f"{path.name}: must set production runtime mode", issues)
    _require(
        "check_production_python_artifact.py /app/src" in text,
        f"{path.name}: must run the production Python artifact exclusion gate",
        issues,
    )
    _require(
        "COPY .docker/validate_production_ui_config.py /validate_production_ui_config.py" in text,
        f"{path.name}: must install the production UI capability validator",
        issues,
    )
    final_source_copy = text.find("COPY --from=python-base /app/src ./src")
    _require(final_source_copy >= 0, f"{path.name}: final curated source copy is missing", issues)
    artifact_gate = text.find("check_production_python_artifact.py /app/src")
    _require(
        final_source_copy >= 0 and 0 <= artifact_gate < final_source_copy,
        f"{path.name}: production Python artifact gate must run before the final source copy",
        issues,
    )
    for module in (
        "autotrader_live_api.py",
        "confidential_attestation_api.py",
        "tau_testnet_dex_plugin.py",
        "zeno_ledger_tokenomics.py",
        "zenodex_local_signer.py",
    ):
        exclusion = text.find(module)
        _require(exclusion >= 0, f"{path.name}: does not exclude {module}", issues)
        _require(
            final_source_copy >= 0 and 0 <= exclusion < final_source_copy,
            f"{path.name}: {module} must be removed before the final OCI source layer",
            issues,
        )


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
    _check_apparmor_overlay(issues)
    _check_aux_compose(ROOT / "docker-compose.permissionless.yml", "tau-local", issues)
    _check_aux_compose(ROOT / "docker-compose.chaos.yml", "toxiproxy", issues)
    _check_aux_compose(ROOT / "docker-compose.two-node.yml", "zeno-ledger-two-node-smoke", issues)
    for service in (
        "zeno-ledger-bootstrap",
        "zeno-ledger-writer",
        "zeno-ledger-forwarder",
        "zeno-ledger-readonly",
        "zeno-ledger-multidocker-controller",
    ):
        _check_aux_compose(ROOT / "docker-compose.multimachine.yml", service, issues)
    _check_apparmor_profile(issues)
    _check_dockerfile(ROOT / "Dockerfile", issues)
    _check_dockerfile(ROOT / "Dockerfile.hashlocked", issues)
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
