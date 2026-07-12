#!/usr/bin/env python3
"""Check the profile hash binding shared by the Firecracker ABI mirrors."""

from __future__ import annotations

import argparse
import importlib
import json
import re
import sys
from pathlib import Path
from typing import Any

if __package__:
    _MODULE_PREFIX = "tools."
else:
    sys.path.insert(0, Path(__file__).resolve().parent.as_posix())
    _MODULE_PREFIX = ""

profile_checker = importlib.import_module(
    f"{_MODULE_PREFIX}check_zrpf_v3_firecracker_replay_profile"
)
direct_replay_checker = importlib.import_module(
    f"{_MODULE_PREFIX}check_zrpf_v3_firecracker_direct_replay_evidence"
)
protocol = importlib.import_module(f"{_MODULE_PREFIX}zrpf_v3_firecracker_output_protocol")
runtime_manifest = importlib.import_module(f"{_MODULE_PREFIX}zrpf_v3_firecracker_runtime_manifest")

REPO_ROOT = Path(__file__).resolve().parents[1]
PROFILE_PATH = REPO_ROOT / "config/proof_profiles/zrpf_v3_firecracker_replay_profile_v1.json"
RUST_PROTOCOL_PATH = REPO_ROOT / "zk/zrpf_risc0/replay_verifier/src/firecracker_protocol.rs"
RUNTIME_MANIFEST_PATH = (
    REPO_ROOT / "config/proof_profiles/zrpf_v3_firecracker_runtime_artifact_manifest_v2.json"
)
DIRECT_REPLAY_EVIDENCE_PATH = (
    REPO_ROOT / "docs/research/ZRPF_V3_FIRECRACKER_GOVERNED_DIRECT_REPLAY_EVIDENCE_20260712.json"
)
REPORT_SCHEMA = "zenodex/zrpf_firecracker_protocol_binding_check/v1"
_RUST_CONSTANT_PATTERN = re.compile(
    rb"CANDIDATE_PROFILE_CANONICAL_SHA256_V1:\s*\[u8;\s*32\]\s*=\s*\[(.*?)\];",
    re.DOTALL,
)
_RUST_BYTE_PATTERN = re.compile(rb"0x([0-9a-f]{2})")


def build_report(
    *,
    profile_path: Path = PROFILE_PATH,
    rust_protocol_path: Path = RUST_PROTOCOL_PATH,
    runtime_artifact_manifest_path: Path = RUNTIME_MANIFEST_PATH,
    direct_replay_evidence_path: Path = DIRECT_REPLAY_EVIDENCE_PATH,
) -> dict[str, Any]:
    errors: list[str] = []
    try:
        profile_raw = runtime_manifest.read_bounded_regular(
            profile_path,
            maximum=profile_checker.MAX_PROFILE_BYTES,
        )
        profile = _strict_profile(profile_raw)
        profile_sha256 = runtime_manifest.canonical_sha256_hex(profile)
    except (OSError, RecursionError, UnicodeDecodeError, ValueError):
        profile_sha256 = None
        errors.append("profile_input_rejected")
    try:
        rust_raw = runtime_manifest.read_bounded_regular(
            rust_protocol_path,
            maximum=256 * 1024,
        )
        rust_profile_sha256 = _extract_rust_profile_sha256(rust_raw)
    except (OSError, RuntimeError, ValueError):
        rust_profile_sha256 = None
        errors.append("rust_profile_constant_rejected")
    try:
        manifest = _load_canonical_object(runtime_artifact_manifest_path, maximum=64 * 1024)
        manifest_profile_sha256 = _require_sha256(
            manifest.get("firecracker_profile_canonical_sha256")
        )
    except (OSError, RecursionError, UnicodeDecodeError, ValueError):
        manifest_profile_sha256 = None
        errors.append("runtime_artifact_manifest_input_rejected")
    try:
        evidence = _load_canonical_object(direct_replay_evidence_path, maximum=64 * 1024)
        governed_bindings = evidence.get("governed_bindings")
        request = evidence.get("request")
        if not isinstance(governed_bindings, dict) or not isinstance(request, dict):
            raise ValueError("direct replay evidence binding objects missing")
        evidence_governed_profile_sha256 = _require_sha256(
            governed_bindings.get("profile_canonical_sha256")
        )
        evidence_request_profile_sha256 = _require_sha256(request.get("profile_sha256"))
    except (OSError, RecursionError, UnicodeDecodeError, ValueError):
        evidence_governed_profile_sha256 = None
        evidence_request_profile_sha256 = None
        errors.append("direct_replay_evidence_input_rejected")

    expected = profile_sha256
    observed = {
        "profile_checker": profile_checker.EXPECTED_PROFILE_CANONICAL_SHA256,
        "direct_replay_checker": direct_replay_checker.EXPECTED_PROFILE_CANONICAL_SHA256,
        "direct_replay_evidence_governed_bindings": evidence_governed_profile_sha256,
        "direct_replay_evidence_request": evidence_request_profile_sha256,
        "python_output_protocol": protocol.CANDIDATE_PROFILE_CANONICAL_SHA256_V1.hex(),
        "runtime_artifact_manifest": manifest_profile_sha256,
        "runtime_manifest": runtime_manifest.PROFILE_CANONICAL_SHA256,
        "rust_output_protocol": rust_profile_sha256,
    }
    if expected is not None and any(value != expected for value in observed.values()):
        errors.append("profile_hash_binding_mismatch")
    return {
        "authority": {
            "microvm_replay_verified": False,
            "production_authority": False,
            "release_authority": False,
            "settlement_authority": False,
        },
        "errors": errors,
        "ok": not errors,
        "observed_bindings": observed,
        "profile_canonical_sha256": profile_sha256,
        "schema": REPORT_SCHEMA,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--profile", type=Path, default=PROFILE_PATH)
    parser.add_argument("--rust-protocol", type=Path, default=RUST_PROTOCOL_PATH)
    parser.add_argument(
        "--runtime-artifact-manifest", type=Path, default=RUNTIME_MANIFEST_PATH
    )
    parser.add_argument(
        "--direct-replay-evidence", type=Path, default=DIRECT_REPLAY_EVIDENCE_PATH
    )
    arguments = parser.parse_args(argv)
    report = build_report(
        profile_path=arguments.profile,
        rust_protocol_path=arguments.rust_protocol,
        runtime_artifact_manifest_path=arguments.runtime_artifact_manifest,
        direct_replay_evidence_path=arguments.direct_replay_evidence,
    )
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["ok"] else 1


def _strict_profile(raw: bytes) -> dict[str, Any]:
    value = profile_checker.support.strict_json_loads(raw)
    if not isinstance(value, dict):
        raise ValueError("profile root is not an object")
    if raw != profile_checker._canonical_bytes(value):
        raise ValueError("profile is not canonical")
    return value


def _extract_rust_profile_sha256(raw: bytes) -> str:
    match = _RUST_CONSTANT_PATTERN.search(raw)
    if match is None:
        raise ValueError("Rust profile constant missing")
    values = _RUST_BYTE_PATTERN.findall(match.group(1))
    if len(values) != 32:
        raise ValueError("Rust profile constant has wrong width")
    return bytes(int(value, 16) for value in values).hex()


def _load_canonical_object(path: Path, *, maximum: int) -> dict[str, Any]:
    raw = runtime_manifest.read_bounded_regular(path, maximum=maximum)
    value = profile_checker.support.strict_json_loads(raw)
    if not isinstance(value, dict) or raw != runtime_manifest.canonical_document_bytes(value):
        raise ValueError("document is not a canonical object")
    return value


def _require_sha256(value: Any) -> str:
    if (
        not isinstance(value, str)
        or len(value) != 64
        or any(character not in "0123456789abcdef" for character in value)
    ):
        raise ValueError("SHA-256 value invalid")
    return value


if __name__ == "__main__":
    raise SystemExit(main())
