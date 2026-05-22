#!/usr/bin/env python3
"""Sign a compiled auto-trader policy artifact."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.agents.policy_artifacts import (  # noqa: E402
    sign_strategy_policy_artifact,
    strategy_policy_artifact_from_dict,
)


def _load_json(path: str) -> dict[str, object]:
    obj = json.loads(Path(path).expanduser().resolve().read_text(encoding="utf-8"))
    if not isinstance(obj, dict):
        raise ValueError("policy artifact file must be a JSON object")
    return obj


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--policy-artifact-file", required=True)
    ap.add_argument("--signer-privkey", required=True)
    ap.add_argument("--telemetry-out")
    ap.add_argument("--pretty", action="store_true")
    return ap.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv)
    try:
        artifact = strategy_policy_artifact_from_dict(_load_json(args.policy_artifact_file))
        signed = sign_strategy_policy_artifact(artifact, privkey=args.signer_privkey)
        payload = {"schema": "zenodex/autotrader-policy-sign/v1", "ok": True, "policy_artifact": signed.to_dict()}
        text = json.dumps(payload, sort_keys=True, indent=2 if args.pretty else None) + "\n"
        sys.stdout.write(text)
        if args.telemetry_out:
            out = Path(args.telemetry_out).expanduser().resolve()
            out.parent.mkdir(parents=True, exist_ok=True)
            out.write_text(text, encoding="utf-8")
        return 0
    except Exception as exc:
        payload = {"schema": "zenodex/autotrader-policy-sign/v1", "ok": False, "error": f"{type(exc).__name__}: {exc}"}
        text = json.dumps(payload, sort_keys=True, indent=2 if args.pretty else None) + "\n"
        sys.stderr.write(text)
        if args.telemetry_out:
            out = Path(args.telemetry_out).expanduser().resolve()
            out.parent.mkdir(parents=True, exist_ok=True)
            out.write_text(text, encoding="utf-8")
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
