#!/usr/bin/env python3
"""Generate a rootless user-systemd service for the operator stack."""

from __future__ import annotations

import argparse
from pathlib import Path


def build_unit(
    *,
    repo_root: Path,
    env_file: str,
    engine: str,
    local_node: bool,
) -> str:
    compose_args = ["-f", "docker-compose.yml"]
    if local_node:
        compose_args.extend(["-f", "docker-compose.permissionless.yml", "--profile", "local-node"])
    compose_joined = " ".join(compose_args)
    cwd = str(repo_root)
    return "\n".join(
        [
            "[Unit]",
            "Description=ZenoDEX permissionless operator stack",
            "After=network-online.target",
            "Wants=network-online.target",
            "",
            "[Service]",
            "Type=oneshot",
            "RemainAfterExit=yes",
            f"WorkingDirectory={cwd}",
            f"EnvironmentFile={env_file}",
            f"ExecStart=/usr/bin/env bash -lc '{engine} compose {compose_joined} up -d'",
            f"ExecStop=/usr/bin/env bash -lc '{engine} compose {compose_joined} down'",
            "TimeoutStartSec=0",
            "",
            "[Install]",
            "WantedBy=default.target",
            "",
        ]
    )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Generate a rootless user-systemd service for ZenoDEX")
    parser.add_argument("--repo-root", default=str(Path(__file__).resolve().parents[1]))
    parser.add_argument("--env-file", default="%h/.config/zenodex/operator.env")
    parser.add_argument("--engine", default="podman", choices=["podman", "docker"])
    parser.add_argument("--local-node", action="store_true")
    parser.add_argument("--out", required=True)
    args = parser.parse_args(argv)

    repo_root = Path(args.repo_root).resolve()
    out_path = Path(args.out).resolve()
    out_path.parent.mkdir(parents=True, exist_ok=True)
    unit_text = build_unit(
        repo_root=repo_root,
        env_file=str(args.env_file),
        engine=str(args.engine),
        local_node=bool(args.local_node),
    )
    out_path.write_text(unit_text, encoding="utf-8")
    print(str(out_path))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
