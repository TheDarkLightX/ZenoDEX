#!/usr/bin/env python3
"""Recover one poisoned ZRPF V6 build lease through exact Docker ownership."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path
from typing import Sequence

if __package__ in {None, ""}:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from tools import plan_zrpf_source_opened_spot_v6_identity_rebuild as planner  # noqa: E402
from tools import zrpf_v6_identity_runner_resources as resources  # noqa: E402
from tools.zrpf_v6_identity_docker_runner import DockerBuildRunner  # noqa: E402
from tools.zrpf_v6_identity_executor_types import ExecutionError  # noqa: E402


def _parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--risc0-home", type=Path, required=True)
    parser.add_argument("--cargo-registry-dir", type=Path, required=True)
    parser.add_argument("--docker", type=Path, default=Path("/usr/bin/docker"))
    parser.add_argument(
        "--lease",
        type=Path,
        default=resources.HOST_BUILD_LEASE_PATH,
    )
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    try:
        runner = DockerBuildRunner(
            risc0_home=args.risc0_home,
            cargo_registry_directory=args.cargo_registry_dir,
            docker=args.docker,
        )
        recovered = runner.recover_host_build_lease(args.lease)
        result = {
            "schema": "zenodex/zrpf_v6_host_build_lease_recovery/v1",
            "status": "exact_owned_container_absent_and_lease_cleared",
            "container_name": recovered.container_name,
            "container_id_file": recovered.container_id_file.as_posix(),
            "proof_authority": False,
            "release_authority": False,
            "production_authority": False,
        }
        sys.stdout.buffer.write(planner.canonical_bytes(result))
    except (ExecutionError, OSError, planner.RebuildPlanError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
