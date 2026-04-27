from __future__ import annotations

import argparse
import json
import os
import sys
from pathlib import Path
from typing import Sequence

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.integration.tau_net_client import bls_pubkey_hex_from_privkey  # noqa: E402
from src.fire.registry.snapshot_v1 import DEMO_SIGNER_PRIVKEY, build_fire_registry_snapshot  # noqa: E402
from src.fire.registry.deployment_contract_v1 import (  # noqa: E402
    enforce_fire_registry_deployment_contract,
    write_fire_registry_deployment_receipt,
)


PUBLISH_REPORT_SCHEMA = "zenodex/fire-registry-snapshot-publish-report/v1"
DEFAULT_SIGNER_ENV = "FIRE_REGISTRY_SIGNER_PRIVKEY"
DEFAULT_EXPECTED_SIGNER_PUBKEY_ENV = "FIRE_REGISTRY_EXPECTED_SIGNER_PUBKEY"


def _require_signer_from_env(env_var: str) -> str:
    signer_privkey = os.environ.get(env_var)
    if signer_privkey is None or signer_privkey == "":
        raise ValueError(f"missing required signer env var: {env_var}")
    return signer_privkey


def _read_optional_env(env_var: str) -> str | None:
    value = os.environ.get(env_var)
    if value is None or value == "":
        return None
    return value


def _derive_signer_pubkey(signer_privkey: str) -> str:
    return "0x" + bls_pubkey_hex_from_privkey(int(signer_privkey))


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Publish a FIRE registry snapshot using an env-backed signer key.")
    parser.add_argument("--output-dir", type=Path, required=True, help="Directory that will receive the published snapshot")
    parser.add_argument("--snapshot-name", required=True, help="Logical snapshot name recorded in release metadata")
    parser.add_argument(
        "--signer-privkey-env",
        default=DEFAULT_SIGNER_ENV,
        help=f"Environment variable holding the BLS signer private key (default: {DEFAULT_SIGNER_ENV})",
    )
    parser.add_argument(
        "--expected-signer-pubkey",
        help="Expected 0x-prefixed signer pubkey; fail closed if the derived signer differs",
    )
    parser.add_argument(
        "--expected-signer-pubkey-env",
        default=DEFAULT_EXPECTED_SIGNER_PUBKEY_ENV,
        help=(
            "Environment variable holding the expected signer pubkey. "
            f"If set, the derived signer must match it (default: {DEFAULT_EXPECTED_SIGNER_PUBKEY_ENV})"
        ),
    )
    parser.add_argument(
        "--deployment-contract-file",
        type=Path,
        help="Optional FIRE registry deployment contract; if provided, publish must satisfy it and emit a deployment receipt",
    )
    parser.add_argument(
        "--allow-demo-signer",
        action="store_true",
        help="Permit the demo signer key for non-release/dev use",
    )
    parser.add_argument(
        "--emit-proof-tree-cert",
        action="store_true",
        help="Emit non-authoritative draft proof-tree cert sidecars in every bundle",
    )
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args(argv)

    try:
        signer_privkey = _require_signer_from_env(args.signer_privkey_env)
        expected_signer_pubkey = args.expected_signer_pubkey or _read_optional_env(args.expected_signer_pubkey_env)
        if signer_privkey == DEMO_SIGNER_PRIVKEY and not args.allow_demo_signer:
            raise ValueError("demo signer key rejected for publish path")
        derived_signer_pubkey = _derive_signer_pubkey(signer_privkey)
        if expected_signer_pubkey is not None and derived_signer_pubkey != expected_signer_pubkey:
            raise ValueError("expected signer pubkey mismatch for publish path")
        deployment_contract = None
        if args.deployment_contract_file is not None:
            ok, err, deployment_contract = enforce_fire_registry_deployment_contract(
                args.deployment_contract_file,
                snapshot_name=args.snapshot_name,
                signer_pubkey=derived_signer_pubkey,
                require_signature=True,
            )
            if not ok:
                raise ValueError(err or "deployment contract rejected publish path")
        build_report = build_fire_registry_snapshot(
            output_dir=args.output_dir,
            snapshot_name=args.snapshot_name,
            signer_privkey=signer_privkey,
            emit_proof_tree_cert=args.emit_proof_tree_cert,
        )
        deployment_receipt_path = None
        deployment_receipt = None
        if args.deployment_contract_file is not None:
            deployment_receipt_path = args.output_dir.resolve() / "deployment_receipt.json"
            deployment_receipt = write_fire_registry_deployment_receipt(
                deployment_receipt_path,
                args.deployment_contract_file,
                build_report["release_metadata_path"],
            )
    except (OSError, RuntimeError, ValueError, TypeError, json.JSONDecodeError) as exc:
        print(str(exc), file=sys.stderr)
        return 1

    payload = {
        "schema": PUBLISH_REPORT_SCHEMA,
        "ok": True,
        "output_dir": build_report["output_dir"],
        "snapshot_name": build_report["snapshot_name"],
        "index_path": build_report["index_path"],
        "index_hash": build_report["index_hash"],
        "index_file_sha256": build_report["index_file_sha256"],
        "release_metadata_path": build_report["release_metadata_path"],
        "release_metadata_file_sha256": build_report["release_metadata_file_sha256"],
        "contract_count": build_report["contract_count"],
        "instance_gate_summary": build_report["instance_gate_summary"],
        "certificate_instance_gate_summary": build_report["certificate_instance_gate_summary"],
        "contracts": build_report["contracts"],
        "signature_present": build_report["signature_present"],
        "compile_receipt_emitted": build_report["compile_receipt_emitted"],
        "kernel_receipt_emitted": build_report["kernel_receipt_emitted"],
        "kernel_eval_receipt_emitted": build_report["kernel_eval_receipt_emitted"],
        "kernel_replay_receipt_emitted": build_report["kernel_replay_receipt_emitted"],
        "kernel_settlement_receipt_emitted": build_report["kernel_settlement_receipt_emitted"],
        "proof_tree_cert_emitted": build_report["proof_tree_cert_emitted"],
        "signer_pubkey": build_report["signer_pubkey"],
        "signer_env_var": args.signer_privkey_env,
        "expected_signer_pubkey": expected_signer_pubkey,
        "expected_signer_pubkey_env": args.expected_signer_pubkey_env,
        "signer_pubkey_matches_expected": (
            expected_signer_pubkey is None or build_report["signer_pubkey"] == expected_signer_pubkey
        ),
        "deployment_contract_file": None if args.deployment_contract_file is None else str(args.deployment_contract_file.resolve()),
        "deployment_contract_enforced": args.deployment_contract_file is not None,
        "deployment_contract_id": None if deployment_contract is None else deployment_contract["contract_id"],
        "deployment_contract_expected_contract_count": 0 if deployment_contract is None else len(deployment_contract.get("contracts", [])),
        "deployment_contract_expected_contracts": [] if deployment_contract is None else deployment_contract.get("contracts", []),
        "deployment_receipt_path": None if deployment_receipt_path is None else str(deployment_receipt_path),
        "demo_signer_allowed": args.allow_demo_signer,
        "bundles": build_report["bundles"],
    }
    if args.pretty:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        print(json.dumps(payload, sort_keys=True, separators=(",", ":")))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
