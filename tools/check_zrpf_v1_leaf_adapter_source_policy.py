#!/usr/bin/env python3
"""Fail-closed consistency checker for the ZRPF V1 leaf-adapter source policy."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_POLICY = (
    REPO_ROOT / "config/proof_profiles/zrpf_v1_leaf_adapter_source_policy_v1.json"
)
RUST_POLICY = REPO_ROOT / "zk/zrpf_risc0/shared/src/source_policy_v1.rs"
RUST_ADAPTER = REPO_ROOT / "zk/zrpf_risc0/shared/src/v1_leaf_adapter.rs"
MAX_POLICY_BYTES = 64 * 1024
EXPECTED_SCHEMA = "zenodex/zrpf_v1_leaf_adapter_source_policy/v1"
EXPECTED_TOP_LEVEL_FIELDS = {
    "schema",
    "status",
    "adapter_profile",
    "count_unit",
    "receipt_authority",
    "source_reference",
    "sources",
    "unsupported_compatibility_fields",
    "non_claims",
}
EXPECTED_REFERENCE_FIELDS = {"path", "sha256", "schema", "source_tree_root"}
EXPECTED_ANCHOR_FIELDS = {
    "historical_reference",
    "non_claims",
    "production_authority",
    "schema",
    "source_tree_root",
    "spot_program",
    "status",
}
EXPECTED_HISTORICAL_REFERENCE_FIELDS = {
    "git_commit",
    "git_tag",
    "path",
    "schema",
    "sha256",
}
EXPECTED_ANCHOR_NON_CLAIMS = {
    "does_not_embed_complete_historical_reference_bytes",
    "does_not_assert_current_source_closure_identity",
    "does_not_authorize_release_or_production",
    "does_not_replace_retained_receipt_verification",
}
HISTORICAL_REFERENCE_COMMIT = "1d1559fd402cdb906d52e6d572d39aec99a5ebda"
HISTORICAL_REFERENCE_PATH = "config/proof_profiles/risc0_recursive_rebuild_reference.json"
HISTORICAL_REFERENCE_SHA256 = (
    "ae562f0ecca00d3eb106526199efb0712660d11c77350027b39f29d2281af8a9"
)
EXPECTED_SOURCE_FIELDS = {
    "source_kind",
    "proof_type",
    "proof_profile",
    "lane_kind",
    "image_id",
    "image_id_words",
    "program_sha256",
}
EXPECTED_UNSUPPORTED_FIELDS = {
    "data_availability_certificate_root",
    "carry_queue_pre_root",
    "carry_queue_post_root",
}
REQUIRED_NON_CLAIMS = {
    "no_receipt_authentication_in_pure_mapping",
    "no_durable_data_availability",
    "no_carry_queue_evidence",
    "no_settlement_or_ledger_admission_authority",
    "no_release_provenance_from_local_source_tree_root",
}


class PolicyInputError(ValueError):
    """A source-policy or referenced input is malformed."""


def _unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise PolicyInputError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def load_policy(path: Path = DEFAULT_POLICY) -> tuple[Any | None, list[str]]:
    try:
        raw = path.read_bytes()
    except OSError as exc:
        return None, [f"policy read failed: {exc}"]
    if not raw or len(raw) > MAX_POLICY_BYTES:
        return None, ["policy byte length is empty or exceeds the cap"]
    try:
        return json.loads(raw.decode("utf-8"), object_pairs_hook=_unique_object), []
    except (UnicodeDecodeError, json.JSONDecodeError, PolicyInputError) as exc:
        return None, [f"policy JSON rejected: {exc}"]


def validate_policy(policy: Any, *, repo_root: Path = REPO_ROOT) -> dict[str, Any]:
    errors: list[str] = []
    if not isinstance(policy, dict):
        return {"ok": False, "errors": ["policy root must be an object"]}
    _require_exact_fields(policy, EXPECTED_TOP_LEVEL_FIELDS, "policy", errors)
    if policy.get("schema") != EXPECTED_SCHEMA:
        errors.append("policy schema mismatch")
    if policy.get("status") != "compatibility_mapping_only":
        errors.append("policy status mismatch")
    if policy.get("adapter_profile") != "zrpf_v1_leaf_adapter_compatibility_v1":
        errors.append("adapter profile mismatch")
    if policy.get("count_unit") != "source_transition_receipt":
        errors.append("count unit mismatch")
    if policy.get("receipt_authority") is not False:
        errors.append("pure mapping must deny receipt authority")
    if set(policy.get("unsupported_compatibility_fields", [])) != EXPECTED_UNSUPPORTED_FIELDS:
        errors.append("unsupported compatibility field set mismatch")
    if set(policy.get("non_claims", [])) != REQUIRED_NON_CLAIMS:
        errors.append("required source-policy non-claims mismatch")

    reference = policy.get("source_reference")
    if isinstance(reference, dict):
        _require_exact_fields(reference, EXPECTED_REFERENCE_FIELDS, "source_reference", errors)
        _validate_reference(reference, repo_root, policy.get("sources"), errors)
    else:
        errors.append("source_reference must be an object")

    sources = policy.get("sources")
    if not isinstance(sources, list) or len(sources) != 1 or not isinstance(sources[0], dict):
        errors.append("sources must contain exactly one source object")
    else:
        _require_exact_fields(sources[0], EXPECTED_SOURCE_FIELDS, "sources[0]", errors)
        _validate_spot_source(sources[0], errors)
        _validate_rust_constants(sources[0], reference, repo_root, errors)

    return {
        "ok": not errors,
        "errors": errors,
        "facts": {
            "source_count": len(sources) if isinstance(sources, list) else 0,
            "receipt_authority": policy.get("receipt_authority"),
            "status": policy.get("status"),
        },
    }


def _require_exact_fields(
    value: dict[str, Any], expected: set[str], label: str, errors: list[str]
) -> None:
    actual = set(value)
    missing = sorted(expected - actual)
    extra = sorted(actual - expected)
    if missing:
        errors.append(f"{label} missing fields: {','.join(missing)}")
    if extra:
        errors.append(f"{label} has unknown fields: {','.join(extra)}")


def _validate_reference(
    reference: dict[str, Any],
    repo_root: Path,
    sources: Any,
    errors: list[str],
) -> None:
    relative = reference.get("path")
    if relative != "config/proof_profiles/zrpf_v1_retained_source_anchor_v1.json":
        errors.append("source reference path mismatch")
        return
    path = repo_root / relative
    try:
        raw = path.read_bytes()
        document = json.loads(raw)
    except (OSError, json.JSONDecodeError) as exc:
        errors.append(f"source reference rejected: {exc}")
        return
    if hashlib.sha256(raw).hexdigest() != reference.get("sha256"):
        errors.append("source reference SHA-256 mismatch")
    if document.get("schema") != reference.get("schema"):
        errors.append("source reference schema mismatch")
    _require_exact_fields(document, EXPECTED_ANCHOR_FIELDS, "source anchor", errors)
    if document.get("status") != "historical_generation_record":
        errors.append("source anchor status mismatch")
    if document.get("production_authority") is not False:
        errors.append("source anchor production authority must remain false")
    if set(document.get("non_claims", [])) != EXPECTED_ANCHOR_NON_CLAIMS:
        errors.append("source anchor non-claims mismatch")
    source_root = document.get("source_tree_root")
    if source_root != reference.get("source_tree_root"):
        errors.append("source tree root mismatch")
    _validate_historical_reference(document.get("historical_reference"), errors)
    if isinstance(sources, list) and len(sources) == 1 and isinstance(sources[0], dict):
        program = document.get("spot_program")
        if not isinstance(program, dict):
            errors.append("source anchor must contain one spot program")
        else:
            for policy_key, reference_key in (
                ("image_id", "image_id"),
                ("image_id_words", "image_id_words"),
                ("program_sha256", "program_sha256"),
            ):
                if sources[0].get(policy_key) != program.get(reference_key):
                    errors.append(f"spot {policy_key} differs from source reference")


def _validate_historical_reference(
    value: Any,
    errors: list[str],
) -> None:
    if not isinstance(value, dict):
        errors.append("historical source reference must be an object")
        return
    _require_exact_fields(
        value,
        EXPECTED_HISTORICAL_REFERENCE_FIELDS,
        "historical source reference",
        errors,
    )
    expected = {
        "git_commit": HISTORICAL_REFERENCE_COMMIT,
        "git_tag": "zrpf-v1-retained-source-anchor-20260710",
        "path": HISTORICAL_REFERENCE_PATH,
        "schema": "zenodex/risc0_recursive_rebuild_reference/v2",
        "sha256": HISTORICAL_REFERENCE_SHA256,
    }
    if value != expected:
        errors.append("historical source reference identity mismatch")


def _validate_spot_source(source: dict[str, Any], errors: list[str]) -> None:
    expected_strings = {
        "source_kind": "spot",
        "proof_type": "risc0.zenodex_recursive_spot_leaf.v1",
        "proof_profile": "recursive_spot_leaf_v1",
        "lane_kind": "spot",
    }
    for field, expected in expected_strings.items():
        if source.get(field) != expected:
            errors.append(f"spot {field} mismatch")
    image_id = source.get("image_id")
    program_sha = source.get("program_sha256")
    if not _is_hex_digest(image_id):
        errors.append("spot image_id must be lowercase SHA-256 hex")
    if not _is_hex_digest(program_sha):
        errors.append("spot program_sha256 must be lowercase SHA-256 hex")
    words = source.get("image_id_words")
    if (
        not isinstance(words, list)
        or len(words) != 8
        or any(not isinstance(word, int) or word < 0 or word > 0xFFFFFFFF for word in words)
    ):
        errors.append("spot image_id_words must contain eight u32 values")
    elif image_id != b"".join(word.to_bytes(4, "little") for word in words).hex():
        errors.append("spot image words do not encode image_id")


def _validate_rust_constants(
    source: dict[str, Any],
    reference: Any,
    repo_root: Path,
    errors: list[str],
) -> None:
    try:
        policy_text = (repo_root / RUST_POLICY.relative_to(REPO_ROOT)).read_text("utf-8")
        adapter_text = (repo_root / RUST_ADAPTER.relative_to(REPO_ROOT)).read_text("utf-8")
    except OSError as exc:
        errors.append(f"Rust policy source read failed: {exc}")
        return
    expected_arrays = {
        "PINNED_SPOT_LEAF_IMAGE_ID_V1": source.get("image_id_words"),
        "PINNED_SPOT_LEAF_PROGRAM_SHA256_V1": list(bytes.fromhex(source.get("program_sha256", "")))
        if _is_hex_digest(source.get("program_sha256"))
        else None,
        "PINNED_V1_LOCAL_SOURCE_TREE_ROOT": list(
            bytes.fromhex(reference.get("source_tree_root", ""))
        )
        if isinstance(reference, dict) and _is_hex_digest(reference.get("source_tree_root"))
        else None,
    }
    for name, expected in expected_arrays.items():
        actual = _rust_array(policy_text, name)
        if actual != expected:
            errors.append(f"Rust constant differs from policy: {name}")
    required_fragments = (
        'lane_kind: "spot"',
        "proof_type: PROOF_TYPE_RECURSIVE_SPOT_LEAF",
        "proof_profile: RECURSIVE_SPOT_LEAF_PROFILE_V1",
    )
    for fragment in required_fragments:
        if fragment not in policy_text:
            errors.append(f"Rust source policy fragment missing: {fragment}")
    if 'V1_LEAF_ADAPTER_PROFILE: &str = "zrpf_v1_leaf_adapter_compatibility_v1"' not in adapter_text:
        errors.append("Rust adapter profile differs from policy")


def _rust_array(text: str, name: str) -> list[int] | None:
    match = re.search(rf"pub const {re.escape(name)}: \[[^;]+;\s*\d+\]\s*=\s*\[(.*?)\];", text, re.S)
    if match is None:
        return None
    return [int(token.replace("_", "")) for token in re.findall(r"\b\d[\d_]*\b", match.group(1))]


def _is_hex_digest(value: Any) -> bool:
    return isinstance(value, str) and re.fullmatch(r"[0-9a-f]{64}", value) is not None


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--policy", type=Path, default=DEFAULT_POLICY)
    args = parser.parse_args()
    policy, load_errors = load_policy(args.policy)
    report = (
        {"ok": False, "errors": load_errors}
        if load_errors
        else validate_policy(policy, repo_root=REPO_ROOT)
    )
    print(json.dumps(report, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
