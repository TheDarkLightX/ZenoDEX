#!/usr/bin/env python3
"""Subprocess verifier for public replay-backed ZenoProof artifacts."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools import zenoproof_verify as zv  # noqa: E402


def _emit(ok: bool, error: str | None = None) -> int:
    payload: dict[str, Any] = {"ok": bool(ok)}
    if error:
        payload["error"] = str(error)
    sys.stdout.write(json.dumps(payload, sort_keys=True) + "\n")
    return 0


def _load_payload() -> Mapping[str, Any] | None:
    try:
        payload = json.loads(sys.stdin.read())
    except Exception:
        _emit(False, "payload_json_invalid")
        return None
    if not isinstance(payload, Mapping):
        _emit(False, "payload_must_be_object")
        return None
    return payload


def verify_public_replay_artifact(profile: str, artifact: Mapping[str, Any]) -> str | None:
    cfg = zv.PUBLIC_REPLAY_PROFILE_CONFIGS[profile]
    expected = {
        "proof_kind": cfg["proof_kind"],
        "claim_id": cfg["claim_id"],
        "verifier_id": cfg["verifier_id"],
        "verifier_policy_root": cfg["policy_root"],
        "toolchain_id": cfg["toolchain_id"],
        "input_commitment_root": zv.public_replay_input_root(profile),
    }
    for key, value in expected.items():
        if artifact.get(key) != value:
            return f"{key}_mismatch"

    try:
        observed_output_root = zv.public_replay_output_root(profile)
    except Exception as exc:
        return f"public_replay_failed:{type(exc).__name__}:{exc}"
    if artifact.get("output_commitment_root") != observed_output_root:
        return "output_commitment_root_mismatch"
    return None


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--profile", required=True, choices=tuple(zv.PUBLIC_REPLAY_PROFILE_CONFIGS))
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    payload = _load_payload()
    if payload is None:
        return 0
    error = verify_public_replay_artifact(args.profile, payload)
    return _emit(error is None, error)


if __name__ == "__main__":
    raise SystemExit(main())
