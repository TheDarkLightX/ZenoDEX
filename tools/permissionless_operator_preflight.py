#!/usr/bin/env python3
"""Preflight checks for permissionless/operator deployment."""

from __future__ import annotations

import argparse
import json
import shutil
from pathlib import Path
from typing import Any


def _tool_present(name: str) -> bool:
    return shutil.which(name) is not None


def _check_file(path: Path) -> dict[str, Any]:
    return {"path": str(path), "ok": path.exists()}


def build_report(*, repo_root: Path, engine: str, local_node: bool, ipfs: bool) -> dict[str, Any]:
    checks: list[dict[str, Any]] = []
    checks.append({"id": "repo_root", "ok": repo_root.is_dir(), "path": str(repo_root)})
    checks.append({"id": "base_compose", **_check_file(repo_root / "docker-compose.yml")})
    checks.append({"id": "permissionless_compose", **_check_file(repo_root / "docker-compose.permissionless.yml")})
    checks.append({"id": "env_example", **_check_file(repo_root / ".env.example")})
    checks.append({"id": "engine", "ok": _tool_present(engine), "engine": engine})

    if local_node:
        checks.append(
            {
                "id": "retired_tau_local_node",
                "ok": False,
                "reason": "historical Tau application bridge is incompatible and retired",
            }
        )
    if ipfs:
        checks.append({"id": "ipfs_cli", "ok": _tool_present("ipfs")})
        checks.append({"id": "ipfs_publish_script", **_check_file(repo_root / "tools" / "publish_ui_ipfs.sh")})

    ok = all(item.get("ok") is True for item in checks)
    return {
        "schema": "zenodex/permissionless_operator_preflight/v1",
        "ok": ok,
        "engine": engine,
        "local_node": bool(local_node),
        "ipfs": bool(ipfs),
        "checks": checks,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Preflight checks for permissionless/operator deployment")
    parser.add_argument("--repo-root", default=str(Path(__file__).resolve().parents[1]))
    parser.add_argument("--engine", default="podman", choices=["podman", "docker"])
    parser.add_argument("--local-node", action="store_true")
    parser.add_argument("--ipfs", action="store_true")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)

    report = build_report(
        repo_root=Path(args.repo_root).resolve(),
        engine=str(args.engine),
        local_node=bool(args.local_node),
        ipfs=bool(args.ipfs),
    )
    if args.json:
        print(json.dumps(report, sort_keys=True, indent=2))
    else:
        for item in report["checks"]:
            status = "OK" if item.get("ok") else "MISSING"
            detail = item.get("path") or item.get("engine") or ""
            print(f"[{status}] {item['id']}: {detail}")
    return 0 if report.get("ok") is True else 1


if __name__ == "__main__":
    raise SystemExit(main())
