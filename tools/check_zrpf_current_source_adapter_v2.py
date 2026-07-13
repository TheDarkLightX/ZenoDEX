#!/usr/bin/env python3
"""Check the fail-closed current-source and V2 adapter candidate contract."""

from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path
from typing import Any, NoReturn

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_ANCHOR = REPO_ROOT / "config/proof_profiles/zrpf_current_source_anchor_v2.json"
DEFAULT_POLICY = (
    REPO_ROOT / "config/proof_profiles/zrpf_v2_leaf_adapter_source_policy_v2.json"
)
RUST_POLICY = REPO_ROOT / "zk/zrpf_risc0/shared/src/source_policy_v2.rs"
V2_GUEST = REPO_ROOT / "zk/zrpf_risc0/methods/v2_leaf_adapter/src/main.rs"
METHODS_MANIFEST = REPO_ROOT / "zk/zrpf_risc0/methods/Cargo.toml"
MAX_DOCUMENT_BYTES = 64 * 1024

PROTECTED_V1_SHA256 = {
    "config/proof_profiles/zrpf_v1_leaf_adapter_source_policy_v1.json": (
        "209982b7fc0cce040e9af928ac3c27641edfe3df44395dfd2925ce7d3f939574"
    ),
    "config/proof_profiles/zrpf_v1_retained_source_anchor_v1.json": (
        "7e2bc7f5cf0dc4ac20fe60d935024d346257086418ea8703a4404ab3bce5b1de"
    ),
    "zk/zrpf_risc0/methods/v1_leaf_adapter/src/main.rs": (
        "6e38a20e28b283a513c9fe541b8dd9a5442fea89a01b33d2c95baf461ed1f547"
    ),
    "zk/zrpf_risc0/shared/src/source_policy_v1.rs": (
        "1292cdb2071443b67109d20ec96d565d0c8756a605510ff3cc1478db403bb433"
    ),
}

ANCHOR_FIELDS = {
    "non_claims",
    "observation_binding",
    "production_authority",
    "release_authority",
    "schema",
    "source_closure",
    "spot_program",
    "status",
}
POLICY_FIELDS = {
    "adapter_profile",
    "adapter_program",
    "count_unit",
    "non_claims",
    "production_authority",
    "receipt_authority",
    "release_authority",
    "schema",
    "source_reference",
    "sources",
    "status",
    "unsupported_compatibility_fields",
}
ANCHOR_NON_CLAIMS = {
    "source_build_observation_is_candidate_only",
    "no_complete_build_input_closure",
    "no_release_authority",
    "no_production_authority",
    "does_not_replace_receipt_verification",
}
POLICY_NON_CLAIMS = {
    "pure_mapping_does_not_authenticate_receipts",
    "candidate_adapter_identity_is_unpromoted",
    "no_durable_data_availability",
    "no_carry_queue_evidence",
    "no_settlement_or_ledger_admission_authority",
    "no_release_or_production_authority",
}


class ContractError(ValueError):
    """A governed candidate input is malformed or ambiguous."""


def _reject_float(_value: str) -> NoReturn:
    raise ContractError("floating-point JSON values are forbidden")


def _unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ContractError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _canonical_bytes(document: Any) -> bytes:
    return (
        json.dumps(document, allow_nan=False, indent=2, sort_keys=True) + "\n"
    ).encode("utf-8")


def _load_canonical(path: Path, label: str) -> tuple[dict[str, Any], bytes]:
    raw = path.read_bytes()
    if not raw or len(raw) > MAX_DOCUMENT_BYTES:
        raise ContractError(f"{label} is empty or oversized")
    try:
        document = json.loads(
            raw.decode("utf-8", errors="strict"),
            object_pairs_hook=_unique_object,
            parse_float=_reject_float,
        )
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ContractError(f"{label} JSON rejected") from exc
    if type(document) is not dict or raw != _canonical_bytes(document):
        raise ContractError(f"{label} must be one canonical JSON object")
    return document, raw


def _exact_fields(value: Any, expected: set[str], label: str) -> None:
    if type(value) is not dict or set(value) != expected:
        raise ContractError(f"{label} exact field set mismatch")


def _hex(value: Any, label: str) -> str:
    if type(value) is not str or re.fullmatch(r"[0-9a-f]{64}", value) is None:
        raise ContractError(f"{label} must be lowercase SHA-256 hex")
    return value


def _program(value: Any, *, allow_pending: bool, label: str) -> dict[str, Any] | None:
    _exact_fields(value, {"image_id", "image_id_words", "program_sha256"}, label)
    if all(value[field] is None for field in value):
        if not allow_pending:
            raise ContractError(f"{label} cannot remain pending")
        return None
    if any(value[field] is None for field in value):
        raise ContractError(f"{label} is partially populated")
    image_id = _hex(value["image_id"], f"{label} image ID")
    program_sha256 = _hex(value["program_sha256"], f"{label} program SHA-256")
    words = value["image_id_words"]
    if (
        type(words) is not list
        or len(words) != 8
        or any(type(word) is not int or not 0 <= word <= 0xFFFFFFFF for word in words)
    ):
        raise ContractError(f"{label} image words must contain eight u32 values")
    if b"".join(word.to_bytes(4, "little") for word in words).hex() != image_id:
        raise ContractError(f"{label} image words do not encode the image ID")
    return {
        "image_id": image_id,
        "image_id_words": words,
        "program_sha256": program_sha256,
    }


def check_contract(
    anchor_path: Path = DEFAULT_ANCHOR,
    policy_path: Path = DEFAULT_POLICY,
    *,
    repo_root: Path = REPO_ROOT,
) -> dict[str, Any]:
    anchor, anchor_raw = _load_canonical(anchor_path, "current-source anchor")
    policy, _policy_raw = _load_canonical(policy_path, "V2 adapter policy")
    _exact_fields(anchor, ANCHOR_FIELDS, "anchor")
    _exact_fields(policy, POLICY_FIELDS, "policy")
    pending = _check_anchor(anchor)
    source_program = _program(anchor["spot_program"], allow_pending=pending, label="source")
    _check_policy(policy, anchor, anchor_raw, source_program, pending)
    _check_rust_and_guest(repo_root, anchor, source_program, pending)
    _check_protected_v1(repo_root)
    return {
        "ok": True,
        "status": "pending_fail_closed" if pending else "observed_unpromoted_candidate",
        "facts": {
            "adapter_profile": "zrpf_v2_leaf_adapter_compatibility_v2",
            "historical_v1_artifacts_preserved": True,
            "source_identity_pending": pending,
            "receipt_authority": False,
            "release_authority": False,
            "production_authority": False,
        },
    }


def _check_anchor(anchor: dict[str, Any]) -> bool:
    if anchor["schema"] != "zenodex/zrpf_current_source_anchor/v2":
        raise ContractError("anchor schema mismatch")
    if set(anchor["non_claims"]) != ANCHOR_NON_CLAIMS:
        raise ContractError("anchor non-claims mismatch")
    if anchor["release_authority"] is not False or anchor["production_authority"] is not False:
        raise ContractError("anchor authority must remain false")
    status = anchor["status"]
    if status not in {
        "awaiting_deterministic_source_build_observation",
        "observed_unpromoted_candidate",
    }:
        raise ContractError("anchor status mismatch")
    pending = status == "awaiting_deterministic_source_build_observation"
    observation = anchor["observation_binding"]
    _exact_fields(
        observation,
        {
            "plan_schema",
            "plan_sha256",
            "source_commit",
            "source_snapshot_root_sha256",
            "stage_id",
        },
        "anchor observation",
    )
    if observation["plan_schema"] != "zenodex/zrpf_spot_v6_identity_rebuild_plan/v1":
        raise ContractError("anchor plan schema mismatch")
    if observation["stage_id"] != "source_spot":
        raise ContractError("anchor source stage mismatch")
    closure = anchor["source_closure"]
    _exact_fields(
        closure,
        {
            "complete_build_input_closure_verified",
            "inventory_root_sha256",
            "kind",
            "tracked_bytes",
            "tracked_file_count",
            "workspace_roots",
        },
        "source closure",
    )
    if closure["kind"] != "tracked_state_proof_workspace_superset_v1":
        raise ContractError("source closure kind mismatch")
    if closure["workspace_roots"] != ["zk/state_proof_risc0"]:
        raise ContractError("source closure must exclude all ZRPF policy sources")
    if closure["complete_build_input_closure_verified"] is not False:
        raise ContractError("complete build closure cannot be claimed")
    if pending:
        for field in ("plan_sha256", "source_commit", "source_snapshot_root_sha256"):
            if observation[field] is not None:
                raise ContractError("pending observation contains an invented identity")
        for field in ("inventory_root_sha256", "tracked_bytes", "tracked_file_count"):
            if closure[field] is not None:
                raise ContractError("pending source closure contains an invented identity")
    else:
        _hex(observation["plan_sha256"], "plan SHA-256")
        if type(observation["source_commit"]) is not str or re.fullmatch(
            r"[0-9a-f]{40}", observation["source_commit"]
        ) is None:
            raise ContractError("source commit must be 40 lowercase hexadecimal characters")
        _hex(observation["source_snapshot_root_sha256"], "source snapshot root")
        _hex(closure["inventory_root_sha256"], "source closure root")
        if type(closure["tracked_file_count"]) is not int or closure["tracked_file_count"] <= 0:
            raise ContractError("source closure file count must be positive")
        if type(closure["tracked_bytes"]) is not int or closure["tracked_bytes"] <= 0:
            raise ContractError("source closure byte count must be positive")
    return pending


def _check_policy(
    policy: dict[str, Any],
    anchor: dict[str, Any],
    anchor_raw: bytes,
    source_program: dict[str, Any] | None,
    pending: bool,
) -> None:
    if policy["schema"] != "zenodex/zrpf_v2_leaf_adapter_source_policy/v2":
        raise ContractError("policy schema mismatch")
    expected_status = (
        "awaiting_deterministic_source_and_adapter_observations"
        if pending
        else "observed_unpromoted_candidate"
    )
    if policy["status"] != expected_status:
        raise ContractError("policy status does not match anchor status")
    if policy["adapter_profile"] != "zrpf_v2_leaf_adapter_compatibility_v2":
        raise ContractError("adapter profile mismatch")
    if policy["count_unit"] != "source_transition_receipt":
        raise ContractError("count unit mismatch")
    if any(
        policy[field] is not False
        for field in ("receipt_authority", "release_authority", "production_authority")
    ):
        raise ContractError("adapter policy authority must remain false")
    if set(policy["non_claims"]) != POLICY_NON_CLAIMS:
        raise ContractError("adapter policy non-claims mismatch")
    if set(policy["unsupported_compatibility_fields"]) != {
        "data_availability_certificate_root",
        "carry_queue_pre_root",
        "carry_queue_post_root",
    }:
        raise ContractError("unsupported field set mismatch")
    reference = policy["source_reference"]
    _exact_fields(reference, {"path", "schema", "sha256"}, "source reference")
    if reference != {
        "path": "config/proof_profiles/zrpf_current_source_anchor_v2.json",
        "schema": anchor["schema"],
        "sha256": hashlib.sha256(anchor_raw).hexdigest(),
    }:
        raise ContractError("source reference identity mismatch")
    sources = policy["sources"]
    if type(sources) is not list or len(sources) != 1:
        raise ContractError("policy must contain exactly one source")
    source = sources[0]
    _exact_fields(
        source,
        {
            "image_id",
            "image_id_words",
            "lane_kind",
            "program_sha256",
            "proof_profile",
            "proof_type",
            "source_closure_root",
            "source_kind",
        },
        "policy source",
    )
    expected_strings = {
        "source_kind": "spot",
        "proof_type": "risc0.zenodex_recursive_spot_leaf.v1",
        "proof_profile": "recursive_spot_leaf_v1",
        "lane_kind": "spot",
    }
    if any(source[field] != value for field, value in expected_strings.items()):
        raise ContractError("policy source semantics mismatch")
    if pending:
        if any(
            source[field] is not None
            for field in ("image_id", "image_id_words", "program_sha256", "source_closure_root")
        ):
            raise ContractError("pending policy source contains an invented identity")
    else:
        if source_program is None:
            raise ContractError("observed source program is unavailable")
        for field in ("image_id", "image_id_words", "program_sha256"):
            if source[field] != source_program[field]:
                raise ContractError("policy source differs from source anchor")
        if source["source_closure_root"] != anchor["source_closure"]["inventory_root_sha256"]:
            raise ContractError("policy source closure differs from source anchor")
    _program(policy["adapter_program"], allow_pending=pending, label="adapter")


def _rust_array(text: str, name: str, expected_len: int) -> list[int]:
    match = re.search(
        rf"pub const {re.escape(name)}: \[[^;]+;\s*{expected_len}\] = \[(.*?)\];",
        text,
        flags=re.DOTALL,
    )
    if match is None:
        raise ContractError(f"Rust constant missing: {name}")
    body = match.group(1).strip()
    repeated = re.fullmatch(r"([0-9][0-9_]*)\s*;\s*([0-9][0-9_]*)", body)
    if repeated is not None:
        value = int(repeated.group(1).replace("_", ""))
        count = int(repeated.group(2).replace("_", ""))
        values = [value] * count
    else:
        values = [
            int(item.replace("_", ""))
            for item in re.findall(r"\b[0-9][0-9_]*\b", body)
        ]
    if len(values) != expected_len:
        raise ContractError(f"Rust constant length mismatch: {name}")
    return values


def _check_rust_and_guest(
    repo_root: Path,
    anchor: dict[str, Any],
    source_program: dict[str, Any] | None,
    pending: bool,
) -> None:
    policy_text = (repo_root / RUST_POLICY.relative_to(REPO_ROOT)).read_text("utf-8")
    guest_text = (repo_root / V2_GUEST.relative_to(REPO_ROOT)).read_text("utf-8")
    manifest_text = (repo_root / METHODS_MANIFEST.relative_to(REPO_ROOT)).read_text("utf-8")
    if '"zrpf_v2_leaf_adapter_compatibility_v2"' not in (
        repo_root / "zk/zrpf_risc0/shared/src/v2_leaf_adapter.rs"
    ).read_text("utf-8"):
        raise ContractError("Rust adapter profile is absent")
    arrays = {
        "image_id_words": _rust_array(policy_text, "PINNED_CURRENT_SPOT_LEAF_IMAGE_ID_V2", 8),
        "program_sha256": _rust_array(
            policy_text, "PINNED_CURRENT_SPOT_LEAF_PROGRAM_SHA256_V2", 32
        ),
        "source_closure_root": _rust_array(
            policy_text, "PINNED_CURRENT_SPOT_SOURCE_CLOSURE_ROOT_V2", 32
        ),
    }
    if pending:
        if any(any(value != 0 for value in values) for values in arrays.values()):
            raise ContractError("pending Rust source policy must retain zero sentinels")
    else:
        if source_program is None:
            raise ContractError("observed source program is unavailable")
        if arrays["image_id_words"] != source_program["image_id_words"]:
            raise ContractError("Rust source image ID differs from anchor")
        if arrays["program_sha256"] != list(bytes.fromhex(source_program["program_sha256"])):
            raise ContractError("Rust source program SHA-256 differs from anchor")
        closure_root = _hex(
            anchor["source_closure"]["inventory_root_sha256"],
            "source closure root",
        )
        if arrays["source_closure_root"] != list(bytes.fromhex(closure_root)):
            raise ContractError("Rust source closure root differs from anchor")
    verify_position = guest_text.find("env::verify(")
    project_position = guest_text.find("project_policy_bound_v2_journal(")
    if verify_position < 0 or project_position < 0 or verify_position >= project_position:
        raise ContractError("V2 guest must authenticate the exact source before projection")
    if "source_policy_v1" in guest_text:
        raise ContractError("V2 guest imports the historical V1 source policy")
    if '"v2_leaf_adapter"' not in manifest_text:
        raise ContractError("V2 guest is absent from RISC0 method metadata")


def _check_protected_v1(repo_root: Path) -> None:
    for relative, expected in PROTECTED_V1_SHA256.items():
        actual = hashlib.sha256((repo_root / relative).read_bytes()).hexdigest()
        if actual != expected:
            raise ContractError(f"protected historical V1 artifact changed: {relative}")


def main() -> int:
    try:
        report = check_contract()
    except (OSError, ContractError) as exc:
        print(json.dumps({"ok": False, "error": str(exc)}, sort_keys=True))
        return 2
    print(json.dumps(report, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
