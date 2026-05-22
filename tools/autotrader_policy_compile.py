#!/usr/bin/env python3
"""Deterministic text-to-policy compiler for the bounded auto-trader."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.agents.krr_bundle_artifacts import load_autotrader_krr_bundle_file  # noqa: E402
from src.agents.krr_policy_advisor import advise_autotrader_krr  # noqa: E402
from src.agents.local_policy import dump_local_policy_document  # noqa: E402
from src.agents.policy_artifacts import (  # noqa: E402
    build_strategy_policy_artifact,
    build_strategy_source_artifact,
    build_tau_policy_bundle,
    sign_strategy_policy_artifact,
)
from src.agents.policy_text_compiler import compile_policy_text  # noqa: E402
from src.agents.tau_policy_adapter import build_compile_contract_tau_policy_receipt  # noqa: E402


def _load_text(path: str | None, inline_text: str | None) -> str:
    if inline_text is not None:
        return str(inline_text)
    if path is None:
        raise ValueError("either --text or --text-file is required")
    p = Path(path).expanduser().resolve()
    return p.read_text(encoding="utf-8")

def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    ap = argparse.ArgumentParser(description=__doc__)
    src_group = ap.add_mutually_exclusive_group(required=True)
    src_group.add_argument("--text", help="Inline controlled policy text")
    src_group.add_argument("--text-file", help="Path to controlled policy text file")
    ap.add_argument("--owner-pubkey", required=True, help="Owner pubkey bound into the compiled policy")
    ap.add_argument("--signer-privkey", help="Optional privkey to sign the emitted policy artifact")
    ap.add_argument(
        "--krr-backend",
        choices=("off", "python", "auto", "prolog", "souffle"),
        default="python",
        help="Optional advisory KRR backend",
    )
    ap.add_argument("--krr-bundle-file", help="Optional reviewed signed offline KRR bundle JSON")
    ap.add_argument("--krr-kb", help="Optional KRR KB JSON path")
    ap.add_argument("--telemetry-out", help="Optional JSON artifact output path")
    ap.add_argument("--pretty", action="store_true", help="Pretty-print JSON output")
    return ap.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv)
    try:
        source_text = _load_text(args.text_file, args.text)
        compilation = compile_policy_text(source_text, owner_pubkey=args.owner_pubkey)
        krr_advice: dict[str, Any] | None = None
        bundle = None
        bundle_krr_kb: dict[str, Any] | None = None
        bundle_history: dict[str, Any] | None = None
        if args.krr_bundle_file:
            if args.krr_kb:
                raise ValueError("--krr-bundle-file cannot be combined with --krr-kb")
            bundle = load_autotrader_krr_bundle_file(args.krr_bundle_file)
            bundle_krr_kb = dict(bundle.runtime_krr_kb) if isinstance(bundle.runtime_krr_kb, dict) else None
            bundle_history = dict(bundle.runtime_history) if isinstance(bundle.runtime_history, dict) else None
        if args.krr_backend != "off":
            krr_advice = advise_autotrader_krr(
                strategy=compilation.compiled.strategy,
                phase="compile",
                current_epoch=compilation.compiled.strategy.strategy_window.valid_from_epoch,
                backend=args.krr_backend,
                kb_path=args.krr_kb,
                kb=bundle_krr_kb,
                history_check_stats=bundle_history or {},
                source_form=compilation.source_form,
            )
        compile_tau_receipt = build_compile_contract_tau_policy_receipt(
            strategy=compilation.compiled.strategy
        )
        source_artifact = build_strategy_source_artifact(
            strategy=compilation.compiled.strategy,
            source_form=compilation.source_form,
            source_text=source_text,
        )
        tau_policy_bundle = build_tau_policy_bundle(
            strategy=compilation.compiled.strategy,
            compile_contract_tau_receipt=compile_tau_receipt.to_dict(),
            source_artifact=source_artifact,
        )
        policy_artifact = build_strategy_policy_artifact(
            strategy=compilation.compiled.strategy,
            tau_policy_bundle=tau_policy_bundle,
            source_artifact=source_artifact,
        )
        if args.signer_privkey is not None:
            policy_artifact = sign_strategy_policy_artifact(
                policy_artifact,
                privkey=args.signer_privkey,
            )
        payload = {
            "schema": "zenodex/autotrader-policy-compile/v1",
            "ok": True,
            "source_form": compilation.source_form,
            "explain": list(compilation.explain),
            "candidate": compilation.candidate,
            "strategy": compilation.compiled.strategy.to_dict(),
            "strategy_hash": compilation.compiled.strategy.strategy_hash_hex(),
            "decision_model_version": tau_policy_bundle.decision_model_version,
            "local_policy": dump_local_policy_document(compilation.compiled.strategy),
            "source_artifact_hash": source_artifact.source_artifact_hash_hex(),
            "source_artifact": source_artifact.to_dict(),
            "compile_contract_tau_receipt": compile_tau_receipt.to_dict(),
            "tau_policy_bundle_hash": tau_policy_bundle.tau_policy_bundle_hash_hex(),
            "tau_policy_bundle": tau_policy_bundle.to_dict(),
            "policy_artifact_hash": policy_artifact.policy_artifact_hash_hex(),
            "policy_artifact": policy_artifact.to_dict(),
            "krr_bundle": None if bundle is None else bundle.to_dict(),
            "krr_advice": krr_advice,
        }
        text = json.dumps(payload, sort_keys=True, indent=2 if args.pretty else None) + "\n"
        sys.stdout.write(text)
        if args.telemetry_out:
            out = Path(args.telemetry_out).expanduser().resolve()
            out.parent.mkdir(parents=True, exist_ok=True)
            out.write_text(text, encoding="utf-8")
        return 0
    except Exception as exc:
        payload = {
            "schema": "zenodex/autotrader-policy-compile/v1",
            "ok": False,
            "error": f"{type(exc).__name__}: {exc}",
        }
        text = json.dumps(payload, sort_keys=True, indent=2 if args.pretty else None) + "\n"
        sys.stderr.write(text)
        if args.telemetry_out:
            out = Path(args.telemetry_out).expanduser().resolve()
            out.parent.mkdir(parents=True, exist_ok=True)
            out.write_text(text, encoding="utf-8")
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
