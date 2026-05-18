#!/usr/bin/env python3
"""Run the WES recompute_batch_v4 bridge from a ZenoDEX checkout."""

from __future__ import annotations

import argparse
import os
import subprocess
import sys
from pathlib import Path
from typing import Sequence

REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_OUT_DIR = REPO_ROOT / "artifacts" / "wes" / "zenodex_recompute_batch_v4"


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Run Witness Energy Search against the real ZenoDEX recompute_batch_v4 checker."
    )
    parser.add_argument(
        "--wes-root",
        type=Path,
        default=None,
        help="WitnessEnergySearch checkout root. Defaults to WES_ROOT or a sibling checkout.",
    )
    parser.add_argument("--out-dir", type=Path, default=DEFAULT_OUT_DIR)
    parser.add_argument("--python", default=sys.executable)
    parser.add_argument("--seed", default="zenodex-recompute-batch-v4-v1")
    parser.add_argument("--repeats", type=int, default=1)
    parser.add_argument("--timeout-s", type=float, default=20.0)
    parser.add_argument("--top-k", type=int, default=5)
    parser.add_argument(
        "--allow-unhealthy",
        action="store_true",
        help="propagate WES artifacts but do not fail if the WES report is unhealthy",
    )
    args = parser.parse_args(argv)

    wes_root = _resolve_wes_root(args.wes_root)
    wes_cli = wes_root / "src" / "wes" / "cli.py"
    if not wes_cli.exists():
        sys.stderr.write(
            f"missing WES CLI at {wes_cli}; pass --wes-root or set WES_ROOT to a WitnessEnergySearch checkout\n"
        )
        return 2

    out_dir = args.out_dir.expanduser().resolve()
    cmd = _build_command(
        python_executable=args.python,
        out_dir=out_dir,
        seed=args.seed,
        repeats=args.repeats,
        timeout_s=args.timeout_s,
        top_k=args.top_k,
        allow_unhealthy=args.allow_unhealthy,
    )
    return subprocess.run(cmd, env=_child_env(wes_root), check=False).returncode


def _resolve_wes_root(provided: Path | None) -> Path:
    if provided is not None:
        return provided.expanduser().resolve()
    env_root = os.environ.get("WES_ROOT")
    if env_root:
        return Path(env_root).expanduser().resolve()
    for candidate in (
        REPO_ROOT.parent / "WitnessEnergySearch",
        REPO_ROOT.parent / "WitnessEnergySearch-main",
    ):
        if (candidate / "src" / "wes" / "cli.py").exists():
            return candidate.resolve()
    return (REPO_ROOT.parent / "WitnessEnergySearch").resolve()


def _build_command(
    *,
    python_executable: str,
    out_dir: Path,
    seed: str,
    repeats: int,
    timeout_s: float,
    top_k: int,
    allow_unhealthy: bool,
) -> list[str]:
    cmd = [
        python_executable,
        "-m",
        "wes.cli",
        "run-zenodex-recompute-batch-v4",
        "--out-dir",
        str(out_dir),
        "--zenodex-root",
        str(REPO_ROOT),
        "--python",
        python_executable,
        "--seed",
        seed,
        "--repeats",
        str(repeats),
        "--timeout-s",
        str(timeout_s),
        "--top-k",
        str(top_k),
    ]
    if allow_unhealthy:
        cmd.append("--allow-unhealthy")
    return cmd


def _child_env(wes_root: Path) -> dict[str, str]:
    env = os.environ.copy()
    wes_src = str((wes_root / "src").resolve())
    existing = env.get("PYTHONPATH")
    env["PYTHONPATH"] = wes_src if not existing else os.pathsep.join((wes_src, existing))
    return env


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
