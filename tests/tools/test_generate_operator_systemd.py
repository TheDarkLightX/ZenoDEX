from __future__ import annotations

from pathlib import Path

from tools.generate_operator_systemd import build_unit


def test_build_unit_includes_local_node_profile(tmp_path: Path) -> None:
    text = build_unit(
        repo_root=tmp_path,
        env_file="%h/.config/zenodex/operator.env",
        engine="podman",
        local_node=True,
    )
    assert "docker-compose.permissionless.yml" in text
    assert "--profile local-node" in text
    assert "podman compose" in text


def test_build_unit_without_local_node_uses_base_stack_only(tmp_path: Path) -> None:
    text = build_unit(
        repo_root=tmp_path,
        env_file="%h/.config/zenodex/operator.env",
        engine="docker",
        local_node=False,
    )
    assert "docker-compose.permissionless.yml" not in text
    assert "docker compose -f docker-compose.yml up -d" in text
