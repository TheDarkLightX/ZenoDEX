#!/usr/bin/env python3
"""Join and verify a public ZenoDEX testnet follower from one config URL."""

from __future__ import annotations

import argparse
import json
import os
import socket
import sys
import time
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.zeno_ledger_node import (  # noqa: E402
    _lp_duration_risk_policy_from_name_v0,
    check_peer_status_v0,
    join_public_node_from_network_config_url_v0,
    pull_live_from_peer_v0,
    serve_node_v0,
)


PUBLIC_FOLLOWER_ACCEPTANCE_SCHEMA = "zenodex.public_testnet_follower_acceptance.v0"


def _write_json(path: Path, value: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _load_json(path: Path) -> Mapping[str, Any]:
    parsed = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(parsed, Mapping):
        raise ValueError(f"{path} must contain a JSON object")
    return parsed


def _safe_node_id(raw: str) -> str:
    lowered = raw.lower()
    chars = [ch if ch.isalnum() else "-" for ch in lowered]
    compact = "-".join(part for part in "".join(chars).split("-") if part)
    return compact[:48] or "public-follower"


def default_node_id() -> str:
    return "public-follower-" + _safe_node_id(socket.gethostname())


def default_data_dir(node_id: str) -> Path:
    base = Path(os.environ.get("ZENODEX_HOME", str(Path.home() / ".zenodex")))
    return base / "public-follower" / _safe_node_id(node_id)


def _first_peer_report(peer_check: Mapping[str, Any] | None) -> Mapping[str, Any]:
    if not isinstance(peer_check, Mapping):
        return {}
    peers = peer_check.get("peers")
    if isinstance(peers, list) and peers and isinstance(peers[0], Mapping):
        return peers[0]
    return {}


def _join_config_peer_url(data_dir: Path) -> str | None:
    path = data_dir / "node_join_config.json"
    if not path.is_file():
        return None
    config = _load_json(path)
    submit_peer = config.get("submit_peer_url")
    if isinstance(submit_peer, str) and submit_peer:
        return submit_peer
    peers = config.get("peer_urls")
    if isinstance(peers, list):
        for peer in peers:
            if isinstance(peer, str) and peer:
                return peer
    return None


def _join_config_follow_policy(data_dir: Path) -> tuple[int, Any | None]:
    path = data_dir / "node_join_config.json"
    if not path.is_file():
        return 0, None
    config = _load_json(path)
    raw_age = config.get("min_lp_position_age_seconds", 0)
    if not isinstance(raw_age, int) or isinstance(raw_age, bool) or raw_age < 0:
        raise ValueError("min_lp_position_age_seconds must be a nonnegative int")
    policy = _lp_duration_risk_policy_from_name_v0(config.get("lp_duration_risk_policy", "none"))
    return int(raw_age), policy


def _join_config_report_fields(data_dir: Path) -> dict[str, Any]:
    path = data_dir / "node_join_config.json"
    if not path.is_file():
        return {"min_lp_position_age_seconds": None, "lp_duration_risk_policy": None}
    config = _load_json(path)
    return {
        "min_lp_position_age_seconds": config.get("min_lp_position_age_seconds"),
        "lp_duration_risk_policy": config.get("lp_duration_risk_policy"),
    }


def join_and_accept_public_follower(
    *,
    config_url: str,
    node_id: str,
    data_dir: Path,
    bundle_root: Path,
    host: str,
    port: int,
    poll_seconds: int,
    pull_live: bool,
    require_live: bool,
    report_path: Path | None,
) -> dict[str, Any]:
    started_at_epoch = int(time.time())
    errors: list[str] = []
    join_report: Mapping[str, Any] | None = None
    pull_report: Mapping[str, Any] | None = None
    peer_check: Mapping[str, Any] | None = None
    network_config: Mapping[str, Any] | None = None
    peer_url: str | None = None

    try:
        join_report = join_public_node_from_network_config_url_v0(
            config_url=config_url,
            node_id=node_id,
            bundle_root=bundle_root,
            data_dir=data_dir,
            host=host,
            port=port,
            poll_seconds=poll_seconds,
            serve=False,
        )
    except Exception as exc:  # pragma: no cover - exercised through CLI error path
        errors.append(f"join_failed:{exc}")

    network_config_path = data_dir / "public_network_config.json"
    if network_config_path.is_file():
        try:
            network_config = _load_json(network_config_path)
        except Exception as exc:
            errors.append(f"network_config_read_failed:{exc}")

    if isinstance(join_report, Mapping) and join_report.get("ok") is not True:
        errors.append(f"join_report_rejected:{join_report.get('status', 'unknown')}")

    if isinstance(join_report, Mapping) and join_report.get("ok") is True:
        peer_url = _join_config_peer_url(data_dir)
        if not peer_url:
            errors.append("peer_url_missing")
        elif pull_live:
            try:
                min_lp_age, lp_policy = _join_config_follow_policy(data_dir)
                pull_report = pull_live_from_peer_v0(
                    data_dir=data_dir,
                    peer_url=peer_url,
                    min_lp_position_age_seconds=min_lp_age,
                    lp_duration_risk_policy=lp_policy,
                )
            except Exception as exc:
                errors.append(f"pull_live_failed:{exc}")
        if peer_url:
            try:
                peer_check = check_peer_status_v0(data_dir=data_dir, peer_urls=[peer_url])
            except Exception as exc:
                errors.append(f"peer_check_failed:{exc}")

    peer_report = _first_peer_report(peer_check)
    local_tip = peer_check.get("local_tip") if isinstance(peer_check, Mapping) else None
    peer_tip = peer_report.get("peer_tip") if isinstance(peer_report, Mapping) else None
    common_header_match = peer_report.get("common_header_match") is True
    live_observed = (
        isinstance(local_tip, Mapping)
        and isinstance(peer_tip, Mapping)
        and local_tip.get("live") is True
        and peer_tip.get("live") is True
    )
    if require_live and not live_observed and isinstance(join_report, Mapping) and join_report.get("ok") is True:
        errors.append("live_tip_not_observed")

    join_config_fields = _join_config_report_fields(data_dir)
    ok = (
        isinstance(join_report, Mapping)
        and join_report.get("ok") is True
        and (not pull_live or (isinstance(pull_report, Mapping) and pull_report.get("ok") is True))
        and isinstance(peer_check, Mapping)
        and peer_check.get("ok") is True
        and common_header_match
        and (live_observed or not require_live)
        and not errors
    )
    report: dict[str, Any] = {
        "schema": PUBLIC_FOLLOWER_ACCEPTANCE_SCHEMA,
        "ok": ok,
        "status": "accepted" if ok else "rejected",
        "node_id": node_id,
        "config_url": config_url,
        "network_config_hash": (
            network_config.get("network_config_hash")
            if isinstance(network_config, Mapping)
            else (join_report.get("network_config_hash") if isinstance(join_report, Mapping) else None)
        ),
        "public_config_url_posture": (
            network_config.get("public_config_url_posture") if isinstance(network_config, Mapping) else None
        ),
        "data_dir": str(data_dir),
        "bundle_root": str(bundle_root),
        "peer_url": peer_url,
        "min_lp_position_age_seconds": join_config_fields["min_lp_position_age_seconds"],
        "lp_duration_risk_policy": join_config_fields["lp_duration_risk_policy"],
        "pull_live": pull_live,
        "require_live": require_live,
        "common_header_match": common_header_match,
        "live_observed": live_observed,
        "height_relation": peer_report.get("height_relation") if isinstance(peer_report, Mapping) else None,
        "local_tip": local_tip,
        "peer_tip": peer_tip,
        "pulled_count": pull_report.get("pulled_count") if isinstance(pull_report, Mapping) else None,
        "join_report_path": str(data_dir / "node_join_report.json"),
        "peer_check": peer_check,
        "pull_report": pull_report,
        "errors": errors,
        "started_at_epoch": started_at_epoch,
        "finished_at_epoch": int(time.time()),
    }
    out_path = report_path or (data_dir / "public_follower_acceptance_report.json")
    _write_json(out_path, report)
    report["report_path"] = str(out_path)
    _write_json(out_path, report)
    return report


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description=(
            "Join a public ZenoDEX testnet from public_network_config.json, "
            "pull live blocks, and write a follower acceptance report."
        )
    )
    parser.add_argument("--config-url", required=True, help="public_network_config.json URL from the seed")
    parser.add_argument("--node-id", default=default_node_id(), help="local follower node id")
    parser.add_argument("--data-dir", type=Path, help="follower data directory")
    parser.add_argument("--bundle-root", type=Path, help="downloaded bundle directory")
    parser.add_argument("--report-path", type=Path, help="acceptance report JSON path")
    parser.add_argument("--host", default="127.0.0.1", help="read-only follower bind host when --serve is used")
    parser.add_argument("--port", type=int, default=8788, help="read-only follower bind port when --serve is used")
    parser.add_argument("--poll-seconds", type=int, default=5, help="peer polling interval when --serve is used")
    parser.add_argument("--skip-pull-live", action="store_true", help="only verify the bootstrap common header")
    parser.add_argument("--no-require-live", action="store_true", help="allow acceptance without observing live tips")
    parser.add_argument("--serve", action="store_true", help="serve the accepted follower as a read-only node")
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    data_dir = args.data_dir or default_data_dir(args.node_id)
    bundle_root = args.bundle_root or (data_dir / "bundle")
    report = join_and_accept_public_follower(
        config_url=args.config_url,
        node_id=args.node_id,
        data_dir=data_dir,
        bundle_root=bundle_root,
        host=args.host,
        port=args.port,
        poll_seconds=args.poll_seconds,
        pull_live=not args.skip_pull_live,
        require_live=not args.no_require_live,
        report_path=args.report_path,
    )
    print(json.dumps(report, indent=2, sort_keys=True))
    if report.get("ok") is not True:
        return 1
    if args.serve:
        peer_url = report.get("peer_url")
        min_lp_age = report.get("min_lp_position_age_seconds")
        if not isinstance(min_lp_age, int) or isinstance(min_lp_age, bool) or min_lp_age < 0:
            min_lp_age = 0
        serve_node_v0(
            data_dir=data_dir,
            host=args.host,
            port=args.port,
            peer_urls=[peer_url] if isinstance(peer_url, str) and peer_url else [],
            poll_seconds=args.poll_seconds,
            enable_testnet_intake=False,
            enable_testnet_faucet=False,
            expose_testnet_faucet_http=False,
            allow_unauthenticated_testnet_writes=False,
            min_lp_position_age_seconds=min_lp_age,
            lp_duration_risk_policy=_lp_duration_risk_policy_from_name_v0(report.get("lp_duration_risk_policy")),
            submit_peer_url=None,
            write_auth_token=None,
            submit_peer_auth_token=None,
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
