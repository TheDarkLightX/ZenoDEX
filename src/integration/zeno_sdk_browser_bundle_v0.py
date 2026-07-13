"""Structural-diagnostic browser bundle helpers for ZenoLedger light clients.

This module packages already-verified ZenoLedger checkpoint evidence for browser
and wallet clients. It does not change ledger semantics and deliberately reuses
the existing checkpoint, signer-registry, and quorum validators.
"""

from __future__ import annotations

from typing import Any, Mapping, Sequence

from src.integration.zeno_ledger_signer_registry import (
    validate_signer_registry_v0,
    verify_signature_quorum_v0,
)
from src.integration.zeno_ledger_v0 import (
    canonical_header_hash_v0,
    hash_v0,
    validate_checkpoint_header_binding_v0,
    validate_checkpoint_v0,
    validate_header_chain_linkage_v0,
    validate_header_v0,
)

BROWSER_CHECKPOINT_BUNDLE_SCHEMA_V0 = "zenodex.zeno_sdk.browser_checkpoint_bundle.v0"
BROWSER_CHECKPOINT_VERIFICATION_SUMMARY_SCHEMA_V0 = (
    "zenodex.zeno_sdk.browser_checkpoint_verification_summary.v0"
)
BROWSER_WALLET_SYNC_STATE_SCHEMA_V0 = "zenodex.zeno_sdk.wallet_sync_state.v0"
CHECKPOINT_PAYLOAD_KIND_V0 = "checkpoint"
_BUNDLE_HASH_DOMAIN_V0 = "browser_checkpoint_bundle_v0"
_WALLET_SYNC_STATE_HASH_DOMAIN_V0 = "wallet_sync_state_v0"
_MAX_SIGNATURE_ENVELOPES_V0 = 64
_MAX_HEADER_CHAIN_HEADERS_V0 = 4096
_VERIFICATION_SUMMARY_KEYS_V0 = {
    "schema",
    "builder_id",
    "proof_authority_required",
    "proof_authority_satisfied",
    "proof_authority_capable",
    "settlement_authority",
    "production_authority",
    "python_structural_range_verified",
    "python_range_replay_verified",
    "python_bls_quorum_verified",
    "browser_header_chain_verified",
    "browser_header_chain_available",
    "browser_range_replay_verified",
    "browser_range_replay_available",
    "browser_bls_quorum_verified",
    "browser_bls_quorum_available",
    "checkpoint_hash",
    "target_header_hash",
    "expected_signature_set_root",
    "registry_hash",
    "quorum_report_hash",
    "accepted_weight",
    "threshold",
    "range_summary",
    "range_summary_hash",
}
_CAPABILITY_KEYS_V0 = {
    "proof_authority_satisfied",
    "proof_authority_capable",
    "settlement_authority",
    "production_authority",
    "python_structural_range_verified",
    "python_range_replay_verified",
    "python_bls_quorum_verified",
    "browser_shape_and_hash_available",
    "browser_shape_and_hash_verified",
    "browser_header_chain_verified",
    "browser_header_chain_available",
    "browser_range_replay_verified",
    "browser_range_replay_available",
    "browser_bls_quorum_verified",
}
_RANGE_SUMMARY_KEYS_V0 = {
    "ok",
    "verification_mode",
    "structural_diagnostic_verified",
    "range_replay_verified",
    "proof_authority_satisfied",
    "checked_heights",
    "last_header_hash",
    "from_height",
    "to_height",
    "trusted_prev_header_hash",
}


def _require_mapping(value: object, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be a JSON object")
    return value


def _require_exact_keys(value: Mapping[str, Any], expected: set[str], *, name: str) -> None:
    if set(value.keys()) != expected:
        raise ValueError(f"{name} keys mismatch")


def _require_str(value: object, *, name: str) -> str:
    if not isinstance(value, str) or value == "":
        raise ValueError(f"{name} must be a non-empty string")
    return value


def _require_bool(value: object, *, name: str) -> bool:
    if not isinstance(value, bool):
        raise TypeError(f"{name} must be a bool")
    return bool(value)


def _require_nonnegative_int(value: object, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise ValueError(f"{name} must be a non-negative int")
    return int(value)


def _require_root(value: object, *, name: str) -> str:
    if not isinstance(value, str) or not value.startswith("0x") or len(value) != 66:
        raise ValueError(f"{name} must be a 32-byte 0x-prefixed root")
    body = value[2:]
    if any(ch not in "0123456789abcdef" for ch in body):
        raise ValueError(f"{name} must be canonical lowercase hex")
    return value


def _require_sequence(value: object, *, name: str, max_len: int) -> Sequence[Any]:
    if not isinstance(value, Sequence) or isinstance(value, (str, bytes, bytearray)):
        raise TypeError(f"{name} must be a sequence")
    if len(value) > max_len:
        raise ValueError(f"{name} exceeds max length {max_len}")
    return value


def _light_client_signature_set_root_v0(registry: Mapping[str, Any]) -> str:
    validate_signer_registry_v0(registry)
    return hash_v0(
        "light_client_signature_set_root_v0",
        {
            "registry_hash": registry["registry_hash"],
            "payload_kind": CHECKPOINT_PAYLOAD_KIND_V0,
            "threshold": registry["threshold"],
        },
    )


def _light_client_checkpoint_hash_v0(checkpoint: Mapping[str, Any]) -> str:
    checkpoint_obj = dict(checkpoint)
    validate_checkpoint_v0(checkpoint_obj)
    return hash_v0("light_client_checkpoint_v0", checkpoint_obj)


def _normalize_header_chain_v0(
    header_chain: Sequence[Mapping[str, Any]],
    *,
    from_height: int,
    to_height: int,
    trusted_prev_header_hash: str,
    target_header: Mapping[str, Any],
    target_checkpoint: Mapping[str, Any],
) -> list[dict[str, Any]]:
    headers = [
        dict(_require_mapping(item, name=f"header_chain[{index}]"))
        for index, item in enumerate(
            _require_sequence(
                header_chain,
                name="header_chain",
                max_len=_MAX_HEADER_CHAIN_HEADERS_V0,
            )
        )
    ]
    if not headers:
        raise ValueError("header_chain must be non-empty")
    if len(headers) != to_height - from_height + 1:
        raise ValueError("header_chain length must match height range")

    for offset, header in enumerate(headers):
        validate_header_v0(header)
        expected_height = from_height + offset
        if int(header["height"]) != expected_height:
            raise ValueError("header_chain must be ordered by consecutive height")

    validate_header_chain_linkage_v0(headers, expected_prev_header_hash=trusted_prev_header_hash)
    if headers[-1] != dict(target_header):
        raise ValueError("header_chain tip must equal target_header")
    if canonical_header_hash_v0(headers[-1]) != target_checkpoint.get("header_hash"):
        raise ValueError("header_chain tip hash must match target checkpoint")
    return headers


def _portable_range_summary(report: Mapping[str, Any]) -> dict[str, Any]:
    range_report = report.get("range_verify_report")
    if not isinstance(range_report, Mapping):
        return {
            "ok": False,
            "verification_mode": "structural_diagnostic",
            "structural_diagnostic_verified": False,
            "range_replay_verified": False,
            "proof_authority_satisfied": False,
            "checked_heights": [],
        }
    checked = range_report.get("checked_heights", [])
    if not isinstance(checked, list):
        checked = []
    return {
        "ok": bool(range_report.get("ok")),
        "verification_mode": "structural_diagnostic",
        "structural_diagnostic_verified": report.get("structural_diagnostic_verified") is True,
        "range_replay_verified": False,
        "proof_authority_satisfied": False,
        "checked_heights": [int(item) for item in checked if isinstance(item, int) and not isinstance(item, bool)],
        "last_header_hash": range_report.get("last_header_hash"),
        "from_height": report.get("from_height"),
        "to_height": report.get("to_height"),
        "trusted_prev_header_hash": report.get("trusted_prev_header_hash"),
    }


def _validate_range_summary_v0(
    range_summary: Mapping[str, Any],
    *,
    from_height: int,
    to_height: int,
    trusted_prev_header_hash: str,
    header_chain: Sequence[Mapping[str, Any]],
) -> None:
    _require_exact_keys(range_summary, _RANGE_SUMMARY_KEYS_V0, name="range_summary")
    if range_summary.get("ok") is not True:
        raise ValueError("range_summary must be accepted")
    if range_summary.get("verification_mode") != "structural_diagnostic":
        raise ValueError("range_summary verification_mode must be structural_diagnostic")
    if range_summary.get("structural_diagnostic_verified") is not True:
        raise ValueError("range_summary structural diagnostic must be verified")
    if range_summary.get("range_replay_verified") is not False:
        raise ValueError("range_summary cannot claim range replay verification")
    if range_summary.get("proof_authority_satisfied") is not False:
        raise ValueError("range_summary cannot claim proof authority")
    checked = range_summary.get("checked_heights")
    if not isinstance(checked, list) or any(not isinstance(item, int) or isinstance(item, bool) for item in checked):
        raise ValueError("range_summary checked_heights must be ints")
    expected_checked = [int(header["height"]) for header in header_chain]
    if checked != expected_checked:
        raise ValueError("range_summary checked_heights mismatch")
    if range_summary.get("from_height") != from_height:
        raise ValueError("range_summary from_height mismatch")
    if range_summary.get("to_height") != to_height:
        raise ValueError("range_summary to_height mismatch")
    if range_summary.get("trusted_prev_header_hash") != trusted_prev_header_hash:
        raise ValueError("range_summary trusted_prev_header_hash mismatch")
    tip_hash = canonical_header_hash_v0(dict(header_chain[-1]))
    if range_summary.get("last_header_hash") != tip_hash:
        raise ValueError("range_summary last_header_hash mismatch")


def _validate_summary_authority_boundary_v0(summary: Mapping[str, Any]) -> None:
    if _require_bool(summary.get("proof_authority_required"), name="proof_authority_required"):
        raise ValueError("browser bundle v0 cannot represent a proof-required profile")
    for field in (
        "proof_authority_satisfied",
        "proof_authority_capable",
        "settlement_authority",
        "production_authority",
    ):
        if _require_bool(summary.get(field), name=field):
            raise ValueError(f"verification summary {field} must be false")


def _validate_structural_summary_flags_v0(summary: Mapping[str, Any]) -> None:
    if not _require_bool(
        summary.get("python_structural_range_verified"),
        name="python_structural_range_verified",
    ):
        raise ValueError("python structural range verification is required")
    if _require_bool(summary.get("python_range_replay_verified"), name="python_range_replay_verified"):
        raise ValueError("python range replay verification must remain false")
    if not _require_bool(
        summary.get("browser_header_chain_available"),
        name="browser_header_chain_available",
    ):
        raise ValueError("browser header-chain verification must be available")
    if _require_bool(summary.get("browser_header_chain_verified"), name="browser_header_chain_verified"):
        raise ValueError("browser header-chain verification must be performed by the browser")
    if _require_bool(summary.get("browser_range_replay_available"), name="browser_range_replay_available"):
        raise ValueError("browser range replay is unavailable in bundle v0")
    if _require_bool(summary.get("browser_range_replay_verified"), name="browser_range_replay_verified"):
        raise ValueError("browser range replay verification must remain false")


def _validate_structural_capability_flags_v0(capabilities: Mapping[str, Any]) -> None:
    for field in (
        "proof_authority_satisfied",
        "proof_authority_capable",
        "settlement_authority",
        "production_authority",
    ):
        if _require_bool(capabilities.get(field), name=field):
            raise ValueError(f"capabilities {field} must be false")
    if not _require_bool(
        capabilities.get("python_structural_range_verified"),
        name="python_structural_range_verified",
    ):
        raise ValueError("python structural range capability is required")
    if _require_bool(capabilities.get("python_range_replay_verified"), name="python_range_replay_verified"):
        raise ValueError("python range replay capability must remain false")
    if not _require_bool(
        capabilities.get("browser_shape_and_hash_available"),
        name="browser_shape_and_hash_available",
    ):
        raise ValueError("browser shape/hash capability must be available")
    if _require_bool(
        capabilities.get("browser_shape_and_hash_verified"),
        name="browser_shape_and_hash_verified",
    ):
        raise ValueError("browser shape/hash capability must start false")
    if not _require_bool(
        capabilities.get("browser_header_chain_available"),
        name="browser_header_chain_available",
    ):
        raise ValueError("browser header-chain capability is required")
    if _require_bool(
        capabilities.get("browser_header_chain_verified"),
        name="browser_header_chain_verified",
    ):
        raise ValueError("browser header-chain capability must start false")
    if _require_bool(capabilities.get("browser_range_replay_available"), name="browser_range_replay_available"):
        raise ValueError("browser range replay capability must remain unavailable")
    if _require_bool(capabilities.get("browser_range_replay_verified"), name="browser_range_replay_verified"):
        raise ValueError("browser range replay capability must start false")


def build_browser_checkpoint_bundle_v0(
    *,
    target_header: Mapping[str, Any],
    target_checkpoint: Mapping[str, Any],
    header_chain: Sequence[Mapping[str, Any]],
    signer_registry: Mapping[str, Any],
    signature_envelopes: Sequence[Mapping[str, Any]],
    light_client_report: Mapping[str, Any],
    builder_id: str = "zenoctl",
) -> dict[str, Any]:
    """Build a deterministic structural checkpoint diagnostic for SDK clients."""

    if light_client_report.get("ok") is not True:
        raise ValueError("light client report must be accepted before bundling")
    if light_client_report.get("status") != "structural_diagnostic_accepted":
        raise ValueError("browser bundle v0 requires a structural diagnostic report")
    if light_client_report.get("structural_diagnostic_verified") is not True:
        raise ValueError("browser bundle v0 requires a verified structural diagnostic")
    if light_client_report.get("range_replay_verified") is not False:
        raise ValueError("browser bundle v0 cannot promote range replay authority")
    if light_client_report.get("proof_authority_required") is not False:
        raise ValueError("browser bundle v0 rejects proof-required light-client reports")
    for field in (
        "proof_authority_satisfied",
        "proof_authority_capable",
        "settlement_authority",
        "production_authority",
    ):
        if light_client_report.get(field) is not False:
            raise ValueError(f"light client report {field} must be false")
    checkpoint = dict(_require_mapping(target_checkpoint, name="target_checkpoint"))
    header = dict(_require_mapping(target_header, name="target_header"))
    registry = dict(_require_mapping(signer_registry, name="signer_registry"))
    envelopes = [
        dict(_require_mapping(item, name=f"signature_envelopes[{index}]"))
        for index, item in enumerate(
            _require_sequence(signature_envelopes, name="signature_envelopes", max_len=_MAX_SIGNATURE_ENVELOPES_V0)
        )
    ]

    validate_checkpoint_header_binding_v0(checkpoint, header)
    if checkpoint.get("signature_set") != []:
        raise ValueError("target checkpoint signature_set must be empty")
    expected_signature_set_root = _light_client_signature_set_root_v0(registry)
    if checkpoint.get("signature_set_root") != expected_signature_set_root:
        raise ValueError("target checkpoint signature_set_root does not match signer registry root")
    checkpoint_hash = _light_client_checkpoint_hash_v0(checkpoint)
    quorum_report = verify_signature_quorum_v0(
        registry=registry,
        payload_kind=CHECKPOINT_PAYLOAD_KIND_V0,
        payload_hash=checkpoint_hash,
        envelopes=envelopes,
    )

    from_height = _require_nonnegative_int(light_client_report.get("from_height"), name="from_height")
    to_height = _require_nonnegative_int(light_client_report.get("to_height"), name="to_height")
    if to_height != checkpoint["height"]:
        raise ValueError("to_height must match target checkpoint height")
    if checkpoint_hash != light_client_report.get("checkpoint_hash"):
        raise ValueError("light client report checkpoint_hash mismatch")
    trusted_prev_header_hash = _require_root(
        light_client_report.get("trusted_prev_header_hash"),
        name="trusted_prev_header_hash",
    )
    normalized_header_chain = _normalize_header_chain_v0(
        header_chain,
        from_height=from_height,
        to_height=to_height,
        trusted_prev_header_hash=trusted_prev_header_hash,
        target_header=header,
        target_checkpoint=checkpoint,
    )

    range_summary = _portable_range_summary(light_client_report)
    _validate_range_summary_v0(
        range_summary,
        from_height=from_height,
        to_height=to_height,
        trusted_prev_header_hash=trusted_prev_header_hash,
        header_chain=normalized_header_chain,
    )
    verification_summary = {
        "schema": BROWSER_CHECKPOINT_VERIFICATION_SUMMARY_SCHEMA_V0,
        "builder_id": _require_str(builder_id, name="builder_id"),
        "proof_authority_required": False,
        "proof_authority_satisfied": False,
        "proof_authority_capable": False,
        "settlement_authority": False,
        "production_authority": False,
        "python_structural_range_verified": True,
        "python_range_replay_verified": False,
        "python_bls_quorum_verified": True,
        "browser_header_chain_verified": False,
        "browser_header_chain_available": True,
        "browser_range_replay_verified": False,
        "browser_range_replay_available": False,
        "browser_bls_quorum_verified": False,
        "browser_bls_quorum_available": False,
        "checkpoint_hash": checkpoint_hash,
        "target_header_hash": checkpoint["header_hash"],
        "expected_signature_set_root": expected_signature_set_root,
        "registry_hash": registry["registry_hash"],
        "quorum_report_hash": quorum_report["quorum_report_hash"],
        "accepted_weight": quorum_report["accepted_weight"],
        "threshold": registry["threshold"],
        "range_summary": range_summary,
        "range_summary_hash": hash_v0("browser_checkpoint_range_summary_v0", range_summary),
    }
    body = {
        "schema": BROWSER_CHECKPOINT_BUNDLE_SCHEMA_V0,
        "chain_id": checkpoint["chain_id"],
        "from_height": from_height,
        "to_height": to_height,
        "trusted_prev_header_hash": trusted_prev_header_hash,
        "header_chain": normalized_header_chain,
        "target_header": header,
        "target_checkpoint": checkpoint,
        "signer_registry": registry,
        "signature_envelopes": envelopes,
        "verification_summary": verification_summary,
        "capabilities": {
            "proof_authority_satisfied": False,
            "proof_authority_capable": False,
            "settlement_authority": False,
            "production_authority": False,
            "python_structural_range_verified": True,
            "python_range_replay_verified": False,
            "python_bls_quorum_verified": True,
            "browser_shape_and_hash_available": True,
            "browser_shape_and_hash_verified": False,
            "browser_header_chain_verified": False,
            "browser_header_chain_available": True,
            "browser_range_replay_verified": False,
            "browser_range_replay_available": False,
            "browser_bls_quorum_verified": False,
        },
        "non_claims": [
            "browser package v0 has no proof, settlement, or production authority",
            "browser package v0 packages structural diagnostics and header linkage only",
            "browser package v0 does not replay full ledger state transitions",
            "browser package v0 only verifies BLS signatures when requireIndependentBls is enabled",
            "wallet sync state is monotone checkpoint tracking, not transaction execution authority",
        ],
    }
    return {**body, "bundle_hash": hash_v0(_BUNDLE_HASH_DOMAIN_V0, body)}


def validate_browser_checkpoint_bundle_v0(
    bundle: Mapping[str, Any],
    *,
    require_python_quorum: bool = True,
) -> None:
    """Validate a browser checkpoint bundle and re-check BLS quorum in Python."""

    obj = dict(_require_mapping(bundle, name="bundle"))
    expected_keys = {
        "schema",
        "chain_id",
        "from_height",
        "to_height",
        "trusted_prev_header_hash",
        "header_chain",
        "target_header",
        "target_checkpoint",
        "signer_registry",
        "signature_envelopes",
        "verification_summary",
        "capabilities",
        "non_claims",
        "bundle_hash",
    }
    if set(obj.keys()) != expected_keys:
        raise ValueError("browser checkpoint bundle keys mismatch")
    if obj.get("schema") != BROWSER_CHECKPOINT_BUNDLE_SCHEMA_V0:
        raise ValueError("browser checkpoint bundle schema mismatch")

    bundle_hash = _require_root(obj.get("bundle_hash"), name="bundle_hash")
    body = {key: obj[key] for key in expected_keys if key != "bundle_hash"}
    if hash_v0(_BUNDLE_HASH_DOMAIN_V0, body) != bundle_hash:
        raise ValueError("browser checkpoint bundle hash mismatch")

    checkpoint = dict(_require_mapping(obj.get("target_checkpoint"), name="target_checkpoint"))
    header = dict(_require_mapping(obj.get("target_header"), name="target_header"))
    registry = dict(_require_mapping(obj.get("signer_registry"), name="signer_registry"))
    envelopes = [
        dict(_require_mapping(item, name=f"signature_envelopes[{index}]"))
        for index, item in enumerate(
            _require_sequence(obj.get("signature_envelopes"), name="signature_envelopes", max_len=_MAX_SIGNATURE_ENVELOPES_V0)
        )
    ]
    summary = _require_mapping(obj.get("verification_summary"), name="verification_summary")
    capabilities = _require_mapping(obj.get("capabilities"), name="capabilities")
    _require_exact_keys(summary, _VERIFICATION_SUMMARY_KEYS_V0, name="verification summary")
    _require_exact_keys(capabilities, _CAPABILITY_KEYS_V0, name="capabilities")

    _require_str(obj.get("chain_id"), name="chain_id")
    from_height = _require_nonnegative_int(obj.get("from_height"), name="from_height")
    to_height = _require_nonnegative_int(obj.get("to_height"), name="to_height")
    if from_height > to_height:
        raise ValueError("from_height must be <= to_height")
    if obj["chain_id"] != checkpoint.get("chain_id"):
        raise ValueError("bundle chain_id must match target checkpoint chain_id")
    if to_height != checkpoint.get("height"):
        raise ValueError("bundle to_height must match target checkpoint height")
    trusted_prev_header_hash = _require_root(obj.get("trusted_prev_header_hash"), name="trusted_prev_header_hash")

    validate_checkpoint_header_binding_v0(checkpoint, header)
    if checkpoint.get("signature_set") != []:
        raise ValueError("target checkpoint signature_set must be empty")
    expected_signature_set_root = _light_client_signature_set_root_v0(registry)
    if checkpoint.get("signature_set_root") != expected_signature_set_root:
        raise ValueError("target checkpoint signature_set_root does not match signer registry root")

    checkpoint_hash = _light_client_checkpoint_hash_v0(checkpoint)
    normalized_header_chain = _normalize_header_chain_v0(
        obj.get("header_chain"),  # type: ignore[arg-type]
        from_height=from_height,
        to_height=to_height,
        trusted_prev_header_hash=trusted_prev_header_hash,
        target_header=header,
        target_checkpoint=checkpoint,
    )
    quorum_report = verify_signature_quorum_v0(
        registry=registry,
        payload_kind=CHECKPOINT_PAYLOAD_KIND_V0,
        payload_hash=checkpoint_hash,
        envelopes=envelopes,
    )

    if summary.get("schema") != BROWSER_CHECKPOINT_VERIFICATION_SUMMARY_SCHEMA_V0:
        raise ValueError("verification summary schema mismatch")
    _validate_summary_authority_boundary_v0(summary)
    if summary.get("checkpoint_hash") != checkpoint_hash:
        raise ValueError("verification summary checkpoint_hash mismatch")
    if summary.get("target_header_hash") != checkpoint["header_hash"]:
        raise ValueError("verification summary target_header_hash mismatch")
    if summary.get("expected_signature_set_root") != expected_signature_set_root:
        raise ValueError("verification summary signature_set_root mismatch")
    if summary.get("registry_hash") != registry["registry_hash"]:
        raise ValueError("verification summary registry_hash mismatch")
    if summary.get("quorum_report_hash") != quorum_report["quorum_report_hash"]:
        raise ValueError("verification summary quorum_report_hash mismatch")
    accepted_weight = _require_nonnegative_int(summary.get("accepted_weight"), name="accepted_weight")
    threshold = _require_nonnegative_int(summary.get("threshold"), name="threshold")
    if accepted_weight <= 0:
        raise ValueError("accepted_weight must be positive")
    if threshold <= 0:
        raise ValueError("threshold must be positive")
    if accepted_weight != int(quorum_report["accepted_weight"]):
        raise ValueError("verification summary accepted_weight mismatch")
    if threshold != int(registry["threshold"]):
        raise ValueError("verification summary threshold mismatch")
    _validate_structural_summary_flags_v0(summary)
    range_summary = _require_mapping(summary.get("range_summary"), name="range_summary")
    range_summary_hash = _require_root(summary.get("range_summary_hash"), name="range_summary_hash")
    if hash_v0("browser_checkpoint_range_summary_v0", range_summary) != range_summary_hash:
        raise ValueError("verification summary range_summary_hash mismatch")
    _validate_range_summary_v0(
        range_summary,
        from_height=from_height,
        to_height=to_height,
        trusted_prev_header_hash=trusted_prev_header_hash,
        header_chain=normalized_header_chain,
    )
    if require_python_quorum and _require_bool(summary.get("python_bls_quorum_verified"), name="python_bls_quorum_verified") is not True:
        raise ValueError("python BLS quorum verification is required")
    if _require_bool(summary.get("browser_bls_quorum_available"), name="browser_bls_quorum_available"):
        raise ValueError("browser BLS quorum must be performed by the browser")
    if _require_bool(summary.get("browser_bls_quorum_verified"), name="browser_bls_quorum_verified"):
        raise ValueError("browser BLS quorum verification is not available in bundle v0")
    _validate_structural_capability_flags_v0(capabilities)
    if _require_bool(capabilities.get("python_bls_quorum_verified"), name="python_bls_quorum_verified") is not True:
        raise ValueError("python BLS quorum capability is required")
    if _require_bool(capabilities.get("browser_bls_quorum_verified"), name="browser_bls_quorum_verified"):
        raise ValueError("browser BLS quorum verification is not available in bundle v0")


def wallet_sync_state_v0(
    *,
    current_state: Mapping[str, Any] | None,
    checkpoint_bundle: Mapping[str, Any],
    surface: str,
    updated_at_ms: int,
) -> dict[str, Any]:
    """Advance a wallet sync state monotonically to a verified checkpoint bundle."""

    validate_browser_checkpoint_bundle_v0(checkpoint_bundle)
    bundle = _require_mapping(checkpoint_bundle, name="checkpoint_bundle")
    checkpoint = _require_mapping(bundle.get("target_checkpoint"), name="target_checkpoint")
    chain_id = _require_str(checkpoint.get("chain_id"), name="checkpoint.chain_id")
    height = _require_nonnegative_int(checkpoint.get("height"), name="checkpoint.height")
    app_hash = _require_root(checkpoint.get("app_hash"), name="checkpoint.app_hash")
    checkpoint_hash = _require_root(bundle.get("verification_summary", {}).get("checkpoint_hash"), name="checkpoint_hash")
    bundle_hash = _require_root(bundle.get("bundle_hash"), name="bundle_hash")

    if current_state is not None:
        validate_wallet_sync_state_v0(current_state)
        old = _require_mapping(current_state, name="current_state")
        if old.get("chain_id") != chain_id:
            raise ValueError("wallet sync chain_id mismatch")
        old_height = _require_nonnegative_int(old.get("height"), name="current_state.height")
        if height < old_height:
            raise ValueError("wallet sync rollback rejected")
        if height == old_height and (
            old.get("checkpoint_hash") != checkpoint_hash or old.get("app_hash") != app_hash
        ):
            raise ValueError("wallet sync same-height drift rejected")

    body = {
        "schema": BROWSER_WALLET_SYNC_STATE_SCHEMA_V0,
        "surface": _require_str(surface, name="surface"),
        "chain_id": chain_id,
        "height": height,
        "app_hash": app_hash,
        "checkpoint_hash": checkpoint_hash,
        "bundle_hash": bundle_hash,
        "updated_at_ms": _require_nonnegative_int(updated_at_ms, name="updated_at_ms"),
    }
    return {**body, "state_hash": hash_v0(_WALLET_SYNC_STATE_HASH_DOMAIN_V0, body)}


def validate_wallet_sync_state_v0(state: Mapping[str, Any]) -> None:
    obj = dict(_require_mapping(state, name="wallet_sync_state"))
    expected_keys = {
        "schema",
        "surface",
        "chain_id",
        "height",
        "app_hash",
        "checkpoint_hash",
        "bundle_hash",
        "updated_at_ms",
        "state_hash",
    }
    if set(obj.keys()) != expected_keys:
        raise ValueError("wallet sync state keys mismatch")
    if obj.get("schema") != BROWSER_WALLET_SYNC_STATE_SCHEMA_V0:
        raise ValueError("wallet sync state schema mismatch")
    _require_str(obj.get("surface"), name="surface")
    _require_str(obj.get("chain_id"), name="chain_id")
    _require_nonnegative_int(obj.get("height"), name="height")
    _require_root(obj.get("app_hash"), name="app_hash")
    _require_root(obj.get("checkpoint_hash"), name="checkpoint_hash")
    _require_root(obj.get("bundle_hash"), name="bundle_hash")
    _require_nonnegative_int(obj.get("updated_at_ms"), name="updated_at_ms")
    state_hash = _require_root(obj.get("state_hash"), name="state_hash")
    body = {key: obj[key] for key in expected_keys if key != "state_hash"}
    if hash_v0(_WALLET_SYNC_STATE_HASH_DOMAIN_V0, body) != state_hash:
        raise ValueError("wallet sync state hash mismatch")
