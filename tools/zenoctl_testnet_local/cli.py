"""CLI dispatch for `zenoctl testnet local ...`.

zenoctl.py imports `register_subparser` and calls it on the existing
`testnet_sub` subparser. Argparse's `set_defaults(func=...)` then routes
each command to the matching `_cmd_*` handler, which delegates to
`lifecycle`.
"""

from __future__ import annotations

import argparse
from pathlib import Path

from . import lifecycle as lc


def register_subparser(testnet_sub: argparse._SubParsersAction) -> None:
    """Register the `local` subcommand family under the existing
    `zenoctl testnet ...` subparser."""
    local = testnet_sub.add_parser(
        "local",
        help="bring up a real local-testnet stack (3-node ledger + Tau + Oracle + UI/API)",
        description=(
            "Bring up a real local-testnet stack against live local backends. "
            "Requires Docker (or Podman) and external/tau-testnet/. See "
            "docs/LOCAL_TESTNET_QUICKSTART.md."
        ),
    )
    local_sub = local.add_subparsers(dest="local_command", required=True)

    up = local_sub.add_parser("up", help="bring up the local-testnet stack")
    up.add_argument("--out-dir", type=Path, required=True, help="directory for manifest/fixtures/rendered configs")
    up.add_argument("--chain-id", default=lc.DEFAULT_CHAIN_ID)
    up.add_argument("--network-id", default=lc.DEFAULT_NETWORK_ID)
    up.add_argument("--ui-port", type=int, default=lc.DEFAULT_UI_PORT, help="host TCP port for the UI (loopback)")
    up.add_argument(
        "--engine",
        choices=["auto", "docker", "podman"],
        default="auto",
        help="container engine (default: auto)",
    )
    up.add_argument(
        "--force",
        action="store_true",
        help="recreate even if an existing manifest is found in --out-dir",
    )
    up.add_argument(
        "--health-timeout",
        type=float,
        default=lc.DEFAULT_HEALTH_TIMEOUT_S,
        help="seconds to wait for the UI to become reachable",
    )
    seed_grp = up.add_mutually_exclusive_group()
    seed_grp.add_argument(
        "--seed",
        dest="seed_override_hex",
        default=None,
        help="64-hex-char fixture seed override (default: derived from --out-dir + --chain-id)",
    )
    seed_grp.add_argument(
        "--random",
        action="store_true",
        help="generate a fresh random fixture seed (default: deterministic per out-dir)",
    )
    up.set_defaults(func=_cmd_up)

    down = local_sub.add_parser("down", help="stop the stack (preserves volumes + manifest + fixtures)")
    down.add_argument("--out-dir", type=Path, required=True)
    down.add_argument("--engine", choices=["auto", "docker", "podman"], default="auto")
    down.set_defaults(func=_cmd_down)

    status = local_sub.add_parser("status", help="report stack health")
    status.add_argument("--out-dir", type=Path, required=True)
    status.add_argument("--engine", choices=["auto", "docker", "podman"], default="auto")
    status.add_argument("--json", dest="as_json", action="store_true", help="machine-readable output")
    status.set_defaults(func=_cmd_status)

    smoke = local_sub.add_parser(
        "smoke",
        help="exercise live local-testnet read/write feature paths",
    )
    smoke.add_argument("--out-dir", type=Path, required=True)
    smoke.add_argument("--engine", choices=["auto", "docker", "podman"], default="auto")
    smoke.add_argument(
        "--browser",
        choices=["auto", "off", "required"],
        default="auto",
        help="run browser UI smoke checks when Chrome/Chromium is available (default: auto)",
    )
    smoke.add_argument("--chrome-bin", type=Path, default=None, help="explicit Chrome/Chromium binary")
    smoke.add_argument(
        "--browser-timeout",
        type=float,
        default=60.0,
        help="seconds per browser smoke case",
    )
    smoke.set_defaults(func=_cmd_smoke)

    logs = local_sub.add_parser("logs", help="stream or tail compose logs for the stack")
    logs.add_argument("--out-dir", type=Path, required=True)
    logs.add_argument("--engine", choices=["auto", "docker", "podman"], default="auto")
    logs.add_argument("--service", default=None, help="optional compose service name")
    logs.add_argument("--tail", type=int, default=None, help="optional line tail count")
    logs.set_defaults(func=_cmd_logs)

    reset = local_sub.add_parser(
        "reset",
        help="remove the stack, volumes, manifest, and seeded state (requires --force)",
    )
    reset.add_argument("--out-dir", type=Path, required=True)
    reset.add_argument("--engine", choices=["auto", "docker", "podman"], default="auto")
    reset.add_argument(
        "--force",
        action="store_true",
        help="confirm the destructive removal of compose volumes, fixtures, and the manifest",
    )
    reset.set_defaults(func=_cmd_reset)


def _cmd_up(args: argparse.Namespace) -> int:
    # Validate --seed shape eagerly so the user gets a clear error before
    # any compose work happens.
    if args.seed_override_hex is not None:
        seed_hex = args.seed_override_hex
        if len(seed_hex) != 64:
            print(
                f"error: --seed must be exactly 64 hex characters (32 bytes), got {len(seed_hex)}",
                file=__import__("sys").stderr,
            )
            return 2
        try:
            bytes.fromhex(seed_hex)
        except ValueError as exc:
            print(f"error: --seed is not valid hex: {exc}", file=__import__("sys").stderr)
            return 2
    return lc.cmd_up(
        lc.UpOptions(
            out_dir=args.out_dir,
            chain_id=args.chain_id,
            network_id=args.network_id,
            ui_port=int(args.ui_port),
            engine=args.engine,
            force=bool(args.force),
            health_timeout_s=float(args.health_timeout),
            seed_override_hex=args.seed_override_hex,
            use_random_seed=bool(args.random),
        )
    )


def _cmd_down(args: argparse.Namespace) -> int:
    return lc.cmd_down(lc.DownOptions(out_dir=args.out_dir, engine=args.engine))


def _cmd_status(args: argparse.Namespace) -> int:
    return lc.cmd_status(
        lc.StatusOptions(out_dir=args.out_dir, engine=args.engine, as_json=bool(args.as_json))
    )


def _cmd_smoke(args: argparse.Namespace) -> int:
    return lc.cmd_smoke(
        lc.SmokeOptions(
            out_dir=args.out_dir,
            engine=args.engine,
            browser=args.browser,
            chrome_bin=args.chrome_bin,
            browser_timeout_s=float(args.browser_timeout),
        )
    )


def _cmd_logs(args: argparse.Namespace) -> int:
    return lc.cmd_logs(
        lc.LogsOptions(
            out_dir=args.out_dir,
            engine=args.engine,
            service=args.service,
            tail=args.tail,
        )
    )


def _cmd_reset(args: argparse.Namespace) -> int:
    import sys as _sys

    if not bool(args.force):
        _sys.stderr.write(
            "error: `zenoctl testnet local reset` removes compose volumes, "
            "the fixture bundle, and the manifest. Re-run with --force to "
            "confirm.\n"
        )
        return 2
    return lc.cmd_reset(lc.ResetOptions(out_dir=args.out_dir, engine=args.engine))
