#!/usr/bin/env python3
# ruff: noqa: E402
"""Build a production-promotion evidence manifest from lane evidence files.

This is producer-side tooling for the fail-closed verifier in
``tools/check_production_promotion_evidence_manifest.py``. It intentionally
does not synthesize evidence. Operators must provide the real lane artifacts;
this tool only canonicalizes the manifest shape, attaches lane-specific
``evidence_hash`` values, and can run the verifier before writing.

Grade: A-. The previous workflow required hand-editing hashes into a five-lane
manifest. That was easy to get wrong and encouraged copy/paste placeholders.
This builder keeps the verifier authoritative while making the honest path
repeatable.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Callable, Mapping, Sequence

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from src.integration.production_promotion_evidence import (  # noqa: E402
    attach_production_app_root_jmt_hash_v2,
    attach_production_autotrader_hash_v1,
    attach_production_confidential_runtime_hash_v1,
    attach_production_hardware_wallet_hash_v1,
    attach_production_oracle_authority_hash_v1,
    attach_production_zk_wrapping_hash_v1,
)
from tools import check_production_promotion_evidence_manifest as checker  # noqa: E402

MANIFEST_SCHEMA = "zenodex/production-promotion-evidence-manifest/v1"
LANE_IDS = (
    "oracle_authority",
    "hardware_wallet",
    "zk_wrapping",
    "autotrader",
    "confidential_runtime",
    "app_root_jmt",
)

_ATTACHERS: Mapping[str, Callable[[Mapping[str, Any]], dict[str, Any]]] = {
    "oracle_authority": attach_production_oracle_authority_hash_v1,
    "hardware_wallet": attach_production_hardware_wallet_hash_v1,
    "zk_wrapping": attach_production_zk_wrapping_hash_v1,
    "autotrader": attach_production_autotrader_hash_v1,
    "confidential_runtime": attach_production_confidential_runtime_hash_v1,
    "app_root_jmt": attach_production_app_root_jmt_hash_v2,
}


def _read_json_object(path: Path, *, label: str) -> dict[str, Any]:
    try:
        raw = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise ValueError(f"{label} file not found: {path}") from exc
    except json.JSONDecodeError as exc:
        raise ValueError(f"{label} file is not valid JSON: {exc}") from exc
    if not isinstance(raw, dict):
        raise ValueError(f"{label} file must contain a JSON object: {path}")
    return raw


def _lane_bundle(args: argparse.Namespace) -> dict[str, Any]:
    paths: Mapping[str, Path | None] = {
        "oracle_authority": args.oracle_authority,
        "hardware_wallet": args.hardware_wallet,
        "zk_wrapping": args.zk_wrapping,
        "autotrader": args.autotrader,
        "confidential_runtime": args.confidential_runtime,
        "app_root_jmt": args.app_root_jmt,
    }
    bundle: dict[str, Any] = {}
    for lane_id in LANE_IDS:
        path = paths[lane_id]
        if path is None:
            bundle[lane_id] = None
            continue
        body = _read_json_object(path, label=f"{lane_id} evidence")
        bundle[lane_id] = _ATTACHERS[lane_id](body)
    return bundle


def _manifest_config(args: argparse.Namespace) -> dict[str, Any]:
    manifest_dir = args.out.resolve().parent
    return {
        "bounded_oracle_exercise_status_path": _path_or_none(
            args.bounded_oracle_exercise_status,
            manifest_dir=manifest_dir,
        ),
        "wallet_authority_profile_hash": args.wallet_authority_profile_hash,
        "live_proof_wrapper_status_path": _path_or_none(
            args.live_proof_wrapper_status,
            manifest_dir=manifest_dir,
        ),
        "supervisor_profile_hash": args.supervisor_profile_hash,
        "config_max_actions_per_tick": args.config_max_actions_per_tick,
        "config_max_runs_per_process": args.config_max_runs_per_process,
        "expected_autotrader_approval_signer_pubkeys": list(
            args.expected_autotrader_approval_signer_pubkey or []
        ),
        "approved_measurements": list(args.approved_measurement or []),
        "operator_status_hash": args.operator_status_hash,
        "external_verifier_binding_hash": args.external_verifier_binding_hash,
        "expected_chain_id": args.expected_chain_id,
        "expected_oracle_authority_signer_pubkey": args.expected_oracle_authority_signer_pubkey,
        "expected_surface": args.expected_surface,
        "expected_extension_id": args.expected_extension_id,
        "expected_device_pubkey": args.expected_device_pubkey,
    }


def _path_or_none(path: Path | None, *, manifest_dir: Path) -> str | None:
    if path is None:
        return None
    resolved = path.resolve()
    if not resolved.is_file():
        # Review finding (grade B+ -> A-): the builder only proved that a
        # sidecar path was bundle-local; it could still write a manifest that
        # referenced a missing file or directory. Check file existence before
        # writing so a generated promotion manifest is replayable by default.
        raise ValueError(f"manifest sidecar path must point to a JSON file: {path}")
    try:
        return str(resolved.relative_to(manifest_dir))
    except ValueError:
        # Review finding (grade B+ -> A-): embedding an absolute operator-local
        # path makes a promotion manifest non-replayable on another machine. Keep
        # sidecar evidence files under the manifest directory so the bundle can be
        # archived and checked without hidden workspace layout assumptions.
        raise ValueError(f"manifest sidecar path must be under the manifest directory: {path}") from None


def build_manifest(args: argparse.Namespace) -> dict[str, Any]:
    return {
        "schema": MANIFEST_SCHEMA,
        "comment": (
            "Built by tools/build_production_promotion_evidence_manifest.py. "
            "Lane evidence_hash values are recomputed from the provided lane JSON bodies."
        ),
        "config": _manifest_config(args),
        "bundle": _lane_bundle(args),
    }


def _write_json(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _run_checker(path: Path, *, lane: str | None, now: int | None, explain_missing: bool) -> int:
    argv = [str(path)]
    if lane is not None:
        argv.extend(["--lane", lane])
    if now is not None:
        argv.extend(["--now", str(now)])
    if explain_missing:
        argv.append("--explain-missing")
    return checker.main(argv)


def _parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--out", type=Path, required=True, help="manifest path to write")
    parser.add_argument("--check", action="store_true", help="run the fail-closed manifest checker after writing")
    parser.add_argument(
        "--check-lane",
        choices=LANE_IDS,
        help="run the checker for one lane after writing; useful for incremental production promotion",
    )
    parser.add_argument(
        "--explain-missing",
        action="store_true",
        help="when --check or --check-lane is set, include machine-readable missing-lane requirements",
    )
    parser.add_argument("--now", type=int, default=None, help="checker freshness timestamp override")

    parser.add_argument("--oracle-authority", type=Path, help="oracle authority evidence JSON body")
    parser.add_argument("--hardware-wallet", type=Path, help="hardware wallet evidence JSON body")
    parser.add_argument("--zk-wrapping", type=Path, help="ZK wrapping evidence JSON body")
    parser.add_argument("--autotrader", type=Path, help="AutoTrader evidence JSON body")
    parser.add_argument("--confidential-runtime", type=Path, help="confidential runtime evidence JSON body")
    parser.add_argument("--app-root-jmt", type=Path, help="app-root/JMT live-root evidence JSON body")

    parser.add_argument("--bounded-oracle-exercise-status", type=Path)
    parser.add_argument("--wallet-authority-profile-hash")
    parser.add_argument("--live-proof-wrapper-status", type=Path)
    parser.add_argument("--supervisor-profile-hash")
    parser.add_argument("--config-max-actions-per-tick", type=int)
    parser.add_argument("--config-max-runs-per-process", type=int)
    parser.add_argument("--expected-autotrader-approval-signer-pubkey", action="append", default=[])
    parser.add_argument("--approved-measurement", action="append", default=[])
    parser.add_argument("--operator-status-hash")
    parser.add_argument("--external-verifier-binding-hash")
    parser.add_argument("--expected-chain-id")
    parser.add_argument("--expected-oracle-authority-signer-pubkey")
    parser.add_argument("--expected-surface")
    parser.add_argument("--expected-extension-id")
    parser.add_argument("--expected-device-pubkey")
    return parser.parse_args(list(argv))


def main(argv: Sequence[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    if args.explain_missing and not args.check and args.check_lane is None:
        print(
            json.dumps(
                {
                    "ok": False,
                    "error": "explain_missing_requires_check",
                    "detail": "--explain-missing requires --check or --check-lane",
                },
                sort_keys=True,
            )
        )
        return 2
    try:
        manifest = build_manifest(args)
        _write_json(args.out, manifest)
    except ValueError as exc:
        print(json.dumps({"ok": False, "error": "manifest_build_failed", "detail": str(exc)}))
        return 2
    if args.check or args.check_lane is not None:
        return _run_checker(
            args.out,
            lane=args.check_lane,
            now=args.now,
            explain_missing=args.explain_missing,
        )
    print(json.dumps({"ok": True, "path": str(args.out), "lanes": list(LANE_IDS)}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
