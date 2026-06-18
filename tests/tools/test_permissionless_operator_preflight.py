from __future__ import annotations

from pathlib import Path

from tools import permissionless_operator_preflight as preflight_tool
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


def test_preflight_rejects_truthy_string_check_ok(monkeypatch, tmp_path: Path) -> None:
    (tmp_path / "docker-compose.yml").write_text("services: {}\n", encoding="utf-8")
    (tmp_path / "docker-compose.permissionless.yml").write_text("services: {}\n", encoding="utf-8")
    (tmp_path / ".env.example").write_text("TAU_NET_RPC=\n", encoding="utf-8")

    monkeypatch.setattr(preflight_tool, "_tool_present", lambda _name: "yes")

    report = build_report(repo_root=tmp_path, engine="docker", local_node=False, ipfs=False)

    checks = {item["id"]: item for item in report["checks"]}
    assert checks["engine"]["ok"] == "yes"
    assert report["ok"] is False


def test_preflight_main_rejects_truthy_string_report_ok(monkeypatch, capsys) -> None:
    def fake_build_report(**_kwargs):
        return {
            "schema": "zenodex/permissionless_operator_preflight/v1",
            "ok": "true",
            "checks": [{"id": "engine", "ok": "true", "engine": "docker"}],
        }

    monkeypatch.setattr(preflight_tool, "build_report", fake_build_report)

    rc = preflight_tool.main(["--json"])
    output = capsys.readouterr().out

    assert rc == 1
    assert '"ok": "true"' in output
