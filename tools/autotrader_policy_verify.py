#!/usr/bin/env python3
"""Verify a signed auto-trader policy artifact against its Tau bundle."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.agents.policy_artifacts import (  # noqa: E402
    strategy_policy_artifact_from_dict,
    strategy_source_artifact_from_dict,
    tau_policy_bundle_from_dict,
    verify_strategy_policy_artifact_signature,
)
from src.agents.tau_policy_adapter import build_compilation_witness_tau_policy_receipt  # noqa: E402
from src.kernels.python.strategy_compilation_witness_v1_adapter import (  # noqa: E402
    check_strategy_compilation_witness,
)
from src.kernels.python.strategy_policy_artifact_contract_v1_adapter import (  # noqa: E402
    check_strategy_policy_artifact_contract,
)
from src.kernels.python.strategy_policy_bundle_contract_v1_adapter import (  # noqa: E402
    check_strategy_policy_bundle_contract,
)


def _load_json(path: str) -> dict[str, object]:
    obj = json.loads(Path(path).expanduser().resolve().read_text(encoding="utf-8"))
    if not isinstance(obj, dict):
        raise ValueError("input file must be a JSON object")
    return obj


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--source-artifact-file", required=True)
    ap.add_argument("--policy-artifact-file", required=True)
    ap.add_argument("--tau-policy-bundle-file", required=True)
    ap.add_argument("--telemetry-out")
    ap.add_argument("--pretty", action="store_true")
    return ap.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv)
    try:
        source_artifact = strategy_source_artifact_from_dict(_load_json(args.source_artifact_file))
        artifact = strategy_policy_artifact_from_dict(_load_json(args.policy_artifact_file))
        bundle = tau_policy_bundle_from_dict(_load_json(args.tau_policy_bundle_file))
        bundle_result = check_strategy_policy_bundle_contract(bundle)
        artifact_result = check_strategy_policy_artifact_contract(artifact, tau_policy_bundle=bundle)
        source_artifact_hash_ok = (
            source_artifact.source_artifact_hash_hex() == bundle.source_artifact_hash
            and source_artifact.source_artifact_hash_hex() == artifact.source_artifact_hash
        )
        compilation_witness_result = check_strategy_compilation_witness(
            source_artifact=source_artifact,
            strategy=artifact.strategy,
            compile_contract_ok=bool(bundle.compile_contract_tau_receipt.get("expected_ok"))
            and bundle.compile_contract_tau_receipt.get("spec_id") == "autotrader_compile_contract_v1",
        )
        compilation_witness_receipt = build_compilation_witness_tau_policy_receipt(
            strategy=artifact.strategy,
            source_artifact=source_artifact,
            compile_contract_tau_receipt=bundle.compile_contract_tau_receipt,
        )
        compilation_witness_receipt_ok = (
            dict(bundle.compilation_witness_tau_receipt) == compilation_witness_receipt.to_dict()
        )
        signature_ok = verify_strategy_policy_artifact_signature(artifact)
        ok = (
            bundle_result.ok
            and artifact_result.ok
            and source_artifact_hash_ok
            and compilation_witness_result.ok
            and compilation_witness_receipt_ok
            and signature_ok
        )
        payload = {
            "schema": "zenodex/autotrader-policy-verify/v1",
            "ok": ok,
            "strategy_hash": artifact.strategy.strategy_hash_hex(),
            "source_artifact_hash": source_artifact.source_artifact_hash_hex(),
            "tau_policy_bundle_hash": bundle.tau_policy_bundle_hash_hex(),
            "policy_artifact_hash": artifact.policy_artifact_hash_hex(),
            "signature_ok": signature_ok,
            "source_artifact_hash_ok": source_artifact_hash_ok,
            "tau_policy_bundle_contract": {"ok": bundle_result.ok, "error": bundle_result.error},
            "policy_artifact_contract": {"ok": artifact_result.ok, "error": artifact_result.error},
            "compilation_witness_contract": {
                "ok": compilation_witness_result.ok,
                "error": compilation_witness_result.error,
            },
            "compilation_witness_receipt_ok": compilation_witness_receipt_ok,
        }
        text = json.dumps(payload, sort_keys=True, indent=2 if args.pretty else None) + "\n"
        target = sys.stdout if ok else sys.stderr
        target.write(text)
        if args.telemetry_out:
            out = Path(args.telemetry_out).expanduser().resolve()
            out.parent.mkdir(parents=True, exist_ok=True)
            out.write_text(text, encoding="utf-8")
        return 0 if ok else 1
    except Exception as exc:
        payload = {"schema": "zenodex/autotrader-policy-verify/v1", "ok": False, "error": f"{type(exc).__name__}: {exc}"}
        text = json.dumps(payload, sort_keys=True, indent=2 if args.pretty else None) + "\n"
        sys.stderr.write(text)
        if args.telemetry_out:
            out = Path(args.telemetry_out).expanduser().resolve()
            out.parent.mkdir(parents=True, exist_ok=True)
            out.write_text(text, encoding="utf-8")
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
