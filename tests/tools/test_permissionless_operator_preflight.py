from __future__ import annotations

from pathlib import Path

from tools.permissionless_operator_preflight import build_report


def test_preflight_reports_missing_local_node_checkout(tmp_path: Path) -> None:
    (tmp_path / "docker-compose.yml").write_text("services: {}\n", encoding="utf-8")
    (tmp_path / "docker-compose.permissionless.yml").write_text("services: {}\n", encoding="utf-8")
    (tmp_path / ".env.example").write_text("TAU_NET_RPC=\n", encoding="utf-8")

    report = build_report(repo_root=tmp_path, engine="podman", local_node=True, ipfs=False)

    assert report["ok"] is False
    checks = {item["id"]: item for item in report["checks"]}
    assert checks["tau_testnet_checkout"]["ok"] is False


def test_preflight_minimal_pass_without_optional_surfaces(tmp_path: Path) -> None:
    (tmp_path / "docker-compose.yml").write_text("services: {}\n", encoding="utf-8")
    (tmp_path / "docker-compose.permissionless.yml").write_text("services: {}\n", encoding="utf-8")
    (tmp_path / ".env.example").write_text("TAU_NET_RPC=\n", encoding="utf-8")

    report = build_report(repo_root=tmp_path, engine="docker", local_node=False, ipfs=False)

    checks = {item["id"]: item for item in report["checks"]}
    assert "tau_testnet_checkout" not in checks
    assert report["engine"] == "docker"
