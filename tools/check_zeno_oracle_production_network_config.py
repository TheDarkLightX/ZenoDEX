#!/usr/bin/env python3
"""Fail-closed checker for a ZenoOracle production-candidate network config."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path
from typing import Any, Mapping


SCHEMA = "zenodex.oracle.production_network_config.v1"
REPORT_SCHEMA = "zenodex.oracle.production_network_config_check.v1"
RECEIPT_BUNDLE_SCHEMA = "zenodex.oracle.production_network_receipt_bundle.v1"
RECEIPT_SCHEMA = "zenodex.oracle.production_network_receipt.v1"
BPS_DENOM = 10_000
SHA256_RE = re.compile(r"^sha256:[0-9a-f]{64}$")
ADDRESS_RE = re.compile(r"^0x[0-9a-fA-F]{40}$")
PUBKEY_RE = re.compile(r"^0x[0-9a-fA-F]{96}$")
TX_RE = re.compile(r"^0x[0-9a-fA-F]{64}$")

REQUIRED_RUNTIME_CONTROLS = {
    "ZUSD_ORACLE_ADAPTER_REQUIRED",
    "ZUSD_ORACLE_AUTHORIZATION_REQUIRED",
    "DEX_ROUTING_ORACLE_ADAPTER_REQUIRED",
    "DEX_ROUTING_ORACLE_AUTHORIZATION_REQUIRED",
    "require_oracle_adapter_for_isolated_settle_epoch",
    "require_oracle_adapter_for_clearinghouse_settle_epoch",
    "require_oracle_adapter_for_isolated_partial_liquidate",
    "require_oracle_authorization_for_isolated_settle_epoch",
    "require_oracle_authorization_for_critical_settlements",
    "trigger_oracle_adapter_required",
}
REQUIRED_NOT_CLAIMS = {
    "does_not_claim_network_deployed",
    "does_not_claim_onchain_governance_executed",
    "does_not_claim_live_token_settlement",
    "does_not_claim_reporter_honesty",
    "does_not_claim_market_price_truth",
}
GO_LIVE_BLOCKERS = [
    "reporter_registry_deployment_receipt_not_verified_onchain",
    "feed_governance_deployment_receipt_not_verified_onchain",
    "signed_release_artifact_not_verified_against_public_transparency_log",
    "fund_live_settlement_escrow",
    "run_public_network_soak",
]
RECEIPT_BUNDLE_KEYS = {
    "schema",
    "config_id",
    "network_id",
    "chain_id",
    "observed_block_number",
    "observed_block_hash",
    "receipts",
    "not_claimed",
}
RECEIPT_KEYS = {
    "schema",
    "receipt_id",
    "kind",
    "chain_id",
    "contract_address",
    "tx_hash",
    "block_number",
    "block_hash",
    "log_index",
    "payload",
}
REQUIRED_RECEIPT_KINDS = {
    "feed_governance_deployment",
    "reporter_registry_deployment",
    "runtime_controls_attestation",
    "signed_release_artifact",
}
RECEIPT_NOT_CLAIMS = {
    "does_not_claim_receipts_verified_against_live_rpc",
    "does_not_claim_contract_code_verified_onchain",
    "does_not_claim_public_release_transparency_log",
    "does_not_claim_public_network_soak",
}


def _canonical_bytes(obj: Mapping[str, Any]) -> bytes:
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")


def config_content_hash(config: Mapping[str, Any]) -> str:
    payload = dict(config)
    payload.pop("config_id", None)
    return "sha256:" + hashlib.sha256(_canonical_bytes(payload)).hexdigest()


def receipt_content_hash(receipt: Mapping[str, Any]) -> str:
    payload = dict(receipt)
    payload.pop("receipt_id", None)
    return "sha256:" + hashlib.sha256(_canonical_bytes(payload)).hexdigest()


def runtime_controls_hash(config: Mapping[str, Any]) -> str:
    controls = config.get("runtime_controls")
    payload = controls if isinstance(controls, Mapping) else {}
    return "sha256:" + hashlib.sha256(_canonical_bytes(payload)).hexdigest()


def _sha_ref(label: str) -> str:
    return "sha256:" + hashlib.sha256(label.encode("utf-8")).hexdigest()


def _tx(label: str) -> str:
    return "0x" + hashlib.sha256(label.encode("utf-8")).hexdigest()


def _is_sha_ref(value: Any) -> bool:
    return isinstance(value, str) and SHA256_RE.fullmatch(value) is not None


def _is_tx(value: Any) -> bool:
    return isinstance(value, str) and TX_RE.fullmatch(value) is not None


def _is_prod_chain_id(value: Any) -> bool:
    if not isinstance(value, str):
        return False
    normalized = value.strip().lower()
    if not normalized:
        return False
    forbidden = ("local", "devnet", "test", "sample", "demo", "alpha")
    return not any(token in normalized for token in forbidden)


def _bool_field(obj: Mapping[str, Any], key: str, errors: list[str], *, required: bool = True) -> bool | None:
    value = obj.get(key)
    if not isinstance(value, bool):
        errors.append(f"{key}_must_be_bool")
        return None
    if required and value is not True:
        errors.append(f"{key}_must_be_true")
    return bool(value)


def _int_field(
    obj: Mapping[str, Any],
    key: str,
    errors: list[str],
    *,
    minimum: int,
    maximum: int | None = None,
) -> int | None:
    value = obj.get(key)
    if not isinstance(value, int) or isinstance(value, bool):
        errors.append(f"{key}_must_be_int")
        return None
    if value < minimum:
        errors.append(f"{key}_below_min:{minimum}")
    if maximum is not None and value > maximum:
        errors.append(f"{key}_above_max:{maximum}")
    return int(value)


def _object_field(obj: Mapping[str, Any], key: str, errors: list[str]) -> Mapping[str, Any]:
    value = obj.get(key)
    if not isinstance(value, Mapping):
        errors.append(f"{key}_must_be_object")
        return {}
    return value


def _list_field(obj: Mapping[str, Any], key: str, errors: list[str]) -> list[Any]:
    value = obj.get(key)
    if not isinstance(value, list):
        errors.append(f"{key}_must_be_list")
        return []
    return list(value)


def _check_governance(config: Mapping[str, Any], errors: list[str]) -> None:
    governance = _object_field(config, "governance", errors)
    if not governance:
        return
    if governance.get("mode") not in {"onchain_timelock", "multisig_timelock"}:
        errors.append("governance_mode_must_be_timelocked")
    contract = governance.get("contract_address")
    if not isinstance(contract, str) or ADDRESS_RE.fullmatch(contract) is None:
        errors.append("governance_contract_address_invalid")
    _int_field(governance, "timelock_seconds", errors, minimum=86_400)
    upgrade_delay = _int_field(governance, "upgrade_delay_seconds", errors, minimum=86_400)
    timelock = governance.get("timelock_seconds")
    if isinstance(upgrade_delay, int) and isinstance(timelock, int) and upgrade_delay < timelock:
        errors.append("upgrade_delay_below_timelock")
    pause_role = governance.get("emergency_pause_role")
    if not isinstance(pause_role, str) or not pause_role.strip():
        errors.append("emergency_pause_role_required")


def _check_signing(config: Mapping[str, Any], errors: list[str]) -> None:
    signing = _object_field(config, "signing", errors)
    if not signing:
        return
    if signing.get("report_signature_scheme") != "bls12-381-g2-basic":
        errors.append("report_signature_scheme_mismatch")
    domain = signing.get("domain_separator")
    if not isinstance(domain, str) or "prod" not in domain.lower():
        errors.append("production_domain_separator_required")
    _bool_field(signing, "receipt_signature_required", errors)
    rotation = _object_field(signing, "key_rotation_policy", errors)
    if rotation:
        _int_field(rotation, "max_key_age_days", errors, minimum=1, maximum=90)
        _bool_field(rotation, "overlap_required", errors)


def _check_code_signing(config: Mapping[str, Any], errors: list[str]) -> None:
    code_signing = _object_field(config, "code_signing", errors)
    if not code_signing:
        return
    _bool_field(code_signing, "required", errors)
    if code_signing.get("scheme") not in {"sigstore-bundle-v1", "cosign-keyless-v1", "hardware-key-signature-v1"}:
        errors.append("code_signing_scheme_unsupported")
    identity = code_signing.get("release_signer_identity")
    if not isinstance(identity, str) or not identity.strip() or "dev" in identity.lower():
        errors.append("release_signer_identity_not_production")
    if code_signing.get("artifact_digest_alg") != "sha256":
        errors.append("artifact_digest_alg_must_be_sha256")
    if not _is_sha_ref(code_signing.get("release_artifact_digest")):
        errors.append("release_artifact_digest_must_be_sha256")
    verify_command = code_signing.get("verify_command")
    if not isinstance(verify_command, list) or not verify_command or not all(isinstance(x, str) and x for x in verify_command):
        errors.append("verify_command_must_be_nonempty_string_list")


def _check_reporters(config: Mapping[str, Any], errors: list[str]) -> None:
    registry = _object_field(config, "reporter_registry", errors)
    if not registry:
        return
    contract = registry.get("contract_address")
    if not isinstance(contract, str) or ADDRESS_RE.fullmatch(contract) is None:
        errors.append("reporter_registry_contract_address_invalid")
    min_reporters = _int_field(registry, "min_reporters", errors, minimum=5, maximum=256)
    quorum = _int_field(registry, "quorum", errors, minimum=3, maximum=256)
    min_bond = _int_field(registry, "minimum_reporter_bond_e8", errors, minimum=1)
    max_operator_share = _int_field(registry, "max_operator_share_bps", errors, minimum=1, maximum=3_400)
    reporters = _list_field(registry, "registered_reporters", errors)
    if isinstance(min_reporters, int) and len(reporters) < min_reporters:
        errors.append("registered_reporter_count_below_min")
    if isinstance(quorum, int) and isinstance(min_reporters, int) and quorum > min_reporters:
        errors.append("quorum_above_min_reporters")

    reporter_ids: list[str] = []
    pubkeys: list[str] = []
    operators: list[str] = []
    active_count = 0
    for idx, raw in enumerate(reporters):
        if not isinstance(raw, Mapping):
            errors.append(f"reporter_{idx}_must_be_object")
            continue
        reporter_id = raw.get("reporter_id")
        pubkey = raw.get("signing_pubkey")
        operator_id = raw.get("operator_id")
        jurisdiction_id = raw.get("jurisdiction_id")
        if not isinstance(reporter_id, str) or not reporter_id.strip() or "local" in reporter_id.lower():
            errors.append(f"reporter_{idx}_id_invalid")
        else:
            reporter_ids.append(reporter_id)
        if not isinstance(pubkey, str) or PUBKEY_RE.fullmatch(pubkey) is None:
            errors.append(f"reporter_{idx}_signing_pubkey_invalid")
        else:
            pubkeys.append(pubkey)
        if not isinstance(operator_id, str) or not operator_id.strip():
            errors.append(f"reporter_{idx}_operator_id_required")
        else:
            operators.append(operator_id)
        if not isinstance(jurisdiction_id, str) or not jurisdiction_id.strip():
            errors.append(f"reporter_{idx}_jurisdiction_id_required")
        if raw.get("active") is True:
            active_count += 1
        bond = raw.get("bond_e8")
        if not isinstance(bond, int) or isinstance(bond, bool) or (isinstance(min_bond, int) and bond < min_bond):
            errors.append(f"reporter_{idx}_bond_below_min")

    if len(set(reporter_ids)) != len(reporter_ids):
        errors.append("duplicate_reporter_id")
    if len(set(pubkeys)) != len(pubkeys):
        errors.append("duplicate_reporter_pubkey")
    if isinstance(quorum, int) and active_count < quorum:
        errors.append("active_reporter_count_below_quorum")
    if isinstance(quorum, int) and len(set(operators)) < quorum:
        errors.append("distinct_operator_count_below_quorum")
    if isinstance(max_operator_share, int) and reporters:
        for operator in set(operators):
            share = (operators.count(operator) * BPS_DENOM) // len(reporters)
            if share > max_operator_share:
                errors.append(f"operator_share_exceeds_policy:{operator}")


def _check_feeds(config: Mapping[str, Any], errors: list[str]) -> None:
    feeds = _list_field(config, "feeds", errors)
    if not feeds:
        errors.append("feeds_must_be_nonempty")
    registry = _object_field(config, "reporter_registry", errors)
    quorum = registry.get("quorum") if isinstance(registry, Mapping) else None
    seen_query_ids: set[str] = set()
    for idx, raw in enumerate(feeds):
        if not isinstance(raw, Mapping):
            errors.append(f"feed_{idx}_must_be_object")
            continue
        query_id = raw.get("query_id")
        if not _is_sha_ref(query_id):
            errors.append(f"feed_{idx}_query_id_invalid")
        elif query_id in seen_query_ids:
            errors.append(f"duplicate_feed_query_id:{query_id}")
        else:
            seen_query_ids.add(query_id)
        if not _is_sha_ref(raw.get("profile_id")):
            errors.append(f"feed_{idx}_profile_id_invalid")
        feed_min_reporters = _int_field(raw, "min_reporters", errors, minimum=3, maximum=256)
        if isinstance(feed_min_reporters, int) and isinstance(quorum, int) and feed_min_reporters < quorum:
            errors.append(f"feed_{idx}_min_reporters_below_registry_quorum")
        _int_field(raw, "min_sources", errors, minimum=3, maximum=256)
        _int_field(raw, "max_staleness_epochs", errors, minimum=1, maximum=100_000)
        _int_field(raw, "max_deviation_bps", errors, minimum=1, maximum=5_000)


def _check_economics(config: Mapping[str, Any], errors: list[str]) -> list[str]:
    economics = _object_field(config, "economics", errors)
    blockers: list[str] = []
    if not economics:
        return GO_LIVE_BLOCKERS
    if economics.get("settlement_asset") in {None, "", "DEV", "dev"}:
        errors.append("settlement_asset_must_be_production_asset")
    _int_field(economics, "reward_pool_cap_e8", errors, minimum=1)
    _int_field(economics, "dispute_window_epochs", errors, minimum=1)
    _int_field(economics, "slash_delay_epochs", errors, minimum=1)
    live_settlement = economics.get("live_token_settlement")
    if not isinstance(live_settlement, bool):
        errors.append("live_token_settlement_must_be_bool")
    elif not live_settlement:
        blockers.append("live_token_settlement_disabled")
    escrow = economics.get("settlement_escrow_contract")
    if live_settlement is True and (not isinstance(escrow, str) or ADDRESS_RE.fullmatch(escrow) is None):
        errors.append("settlement_escrow_contract_required_for_live_settlement")
    elif live_settlement is False:
        blockers.append("settlement_escrow_contract_not_live")
    return blockers


def _check_runtime_controls(config: Mapping[str, Any], errors: list[str]) -> None:
    controls = _object_field(config, "runtime_controls", errors)
    if not controls:
        return
    missing = sorted(REQUIRED_RUNTIME_CONTROLS - set(controls))
    errors.extend(f"missing_runtime_control:{key}" for key in missing)
    for key in sorted(REQUIRED_RUNTIME_CONTROLS & set(controls)):
        if controls.get(key) is not True:
            errors.append(f"runtime_control_not_enabled:{key}")


def _check_not_claimed(config: Mapping[str, Any], errors: list[str]) -> None:
    not_claimed = config.get("not_claimed")
    if not isinstance(not_claimed, list):
        errors.append("not_claimed_must_be_list")
        return
    values = {str(item) for item in not_claimed if isinstance(item, str)}
    missing = sorted(REQUIRED_NOT_CLAIMS - values)
    errors.extend(f"missing_not_claim:{item}" for item in missing)


def _unknown_fields(obj: Mapping[str, Any], *, allowed: set[str], label: str, errors: list[str]) -> None:
    for key in obj:
        if not isinstance(key, str):
            errors.append(f"{label}_field_must_be_string")
        elif key not in allowed:
            errors.append(f"unknown_{label}_field:{key}")


def _receipt(
    *,
    kind: str,
    chain_id: str,
    contract_address: str,
    tx_hash: str,
    block_number: int,
    block_hash: str,
    log_index: int,
    payload: Mapping[str, Any],
) -> dict[str, Any]:
    receipt: dict[str, Any] = {
        "schema": RECEIPT_SCHEMA,
        "kind": kind,
        "chain_id": chain_id,
        "contract_address": contract_address,
        "tx_hash": tx_hash,
        "block_number": int(block_number),
        "block_hash": block_hash,
        "log_index": int(log_index),
        "payload": dict(payload),
    }
    receipt["receipt_id"] = receipt_content_hash(receipt)
    return receipt


def _active_reporter_count(config: Mapping[str, Any]) -> int:
    registry = config.get("reporter_registry")
    if not isinstance(registry, Mapping):
        return 0
    reporters = registry.get("registered_reporters")
    if not isinstance(reporters, list):
        return 0
    return sum(1 for reporter in reporters if isinstance(reporter, Mapping) and reporter.get("active") is True)


def _distinct_operator_count(config: Mapping[str, Any]) -> int:
    registry = config.get("reporter_registry")
    if not isinstance(registry, Mapping):
        return 0
    reporters = registry.get("registered_reporters")
    if not isinstance(reporters, list):
        return 0
    operators = {
        str(reporter.get("operator_id"))
        for reporter in reporters
        if isinstance(reporter, Mapping) and isinstance(reporter.get("operator_id"), str)
    }
    return len(operators)


def _feed_query_ids(config: Mapping[str, Any]) -> list[str]:
    feeds = config.get("feeds")
    if not isinstance(feeds, list):
        return []
    return sorted(str(feed.get("query_id")) for feed in feeds if isinstance(feed, Mapping) and isinstance(feed.get("query_id"), str))


def _enabled_runtime_controls(config: Mapping[str, Any]) -> list[str]:
    controls = config.get("runtime_controls")
    if not isinstance(controls, Mapping):
        return []
    return sorted(str(key) for key, value in controls.items() if isinstance(key, str) and value is True)


def sample_receipt_bundle(config: Mapping[str, Any] | None = None) -> dict[str, Any]:
    active_config = sample_config() if config is None else config
    config_id = config_content_hash(active_config)
    chain_id = str(active_config.get("chain_id"))
    network_id = str(active_config.get("network_id"))
    governance = active_config.get("governance") if isinstance(active_config.get("governance"), Mapping) else {}
    registry = active_config.get("reporter_registry") if isinstance(active_config.get("reporter_registry"), Mapping) else {}
    signing = active_config.get("signing") if isinstance(active_config.get("signing"), Mapping) else {}
    code_signing = active_config.get("code_signing") if isinstance(active_config.get("code_signing"), Mapping) else {}
    governance_contract = str(governance.get("contract_address"))
    registry_contract = str(registry.get("contract_address"))
    receipts = [
        _receipt(
            kind="reporter_registry_deployment",
            chain_id=chain_id,
            contract_address=registry_contract,
            tx_hash=_tx("zeno_oracle.production_network.reporter_registry_deployment"),
            block_number=3_000,
            block_hash=_sha_ref("zeno_oracle.production_network.block.3000"),
            log_index=0,
            payload={
                "active_reporter_count": _active_reporter_count(active_config),
                "config_id": config_id,
                "deployed": True,
                "distinct_operator_count": _distinct_operator_count(active_config),
                "minimum_reporter_bond_e8": registry.get("minimum_reporter_bond_e8"),
                "min_reporters": registry.get("min_reporters"),
                "network_id": network_id,
                "quorum": registry.get("quorum"),
                "reporter_registry_contract_address": registry_contract,
            },
        ),
        _receipt(
            kind="feed_governance_deployment",
            chain_id=chain_id,
            contract_address=governance_contract,
            tx_hash=_tx("zeno_oracle.production_network.feed_governance_deployment"),
            block_number=3_100,
            block_hash=_sha_ref("zeno_oracle.production_network.block.3100"),
            log_index=0,
            payload={
                "config_id": config_id,
                "deployed": True,
                "feed_count": len(_feed_query_ids(active_config)),
                "feed_governance_contract_address": governance_contract,
                "feed_query_ids": _feed_query_ids(active_config),
                "network_id": network_id,
                "timelock_seconds": governance.get("timelock_seconds"),
                "upgrade_delay_seconds": governance.get("upgrade_delay_seconds"),
            },
        ),
        _receipt(
            kind="signed_release_artifact",
            chain_id=chain_id,
            contract_address=governance_contract,
            tx_hash=_tx("zeno_oracle.production_network.signed_release_artifact"),
            block_number=3_200,
            block_hash=_sha_ref("zeno_oracle.production_network.block.3200"),
            log_index=0,
            payload={
                "artifact_digest_alg": code_signing.get("artifact_digest_alg"),
                "config_id": config_id,
                "domain_separator": signing.get("domain_separator"),
                "network_id": network_id,
                "receipt_signature_required": signing.get("receipt_signature_required"),
                "release_artifact_digest": code_signing.get("release_artifact_digest"),
                "release_signer_identity": code_signing.get("release_signer_identity"),
                "report_signature_scheme": signing.get("report_signature_scheme"),
                "scheme": code_signing.get("scheme"),
                "verified": True,
            },
        ),
        _receipt(
            kind="runtime_controls_attestation",
            chain_id=chain_id,
            contract_address=governance_contract,
            tx_hash=_tx("zeno_oracle.production_network.runtime_controls_attestation"),
            block_number=3_300,
            block_hash=_sha_ref("zeno_oracle.production_network.block.3300"),
            log_index=0,
            payload={
                "config_id": config_id,
                "enabled_runtime_controls": _enabled_runtime_controls(active_config),
                "network_id": network_id,
                "runtime_controls_hash": runtime_controls_hash(active_config),
                "verified": True,
            },
        ),
    ]
    return {
        "schema": RECEIPT_BUNDLE_SCHEMA,
        "config_id": config_id,
        "network_id": network_id,
        "chain_id": chain_id,
        "observed_block_number": 3_300,
        "observed_block_hash": _sha_ref("zeno_oracle.production_network.block.3300"),
        "receipts": receipts,
        "not_claimed": sorted(RECEIPT_NOT_CLAIMS),
    }


def _check_payload_common(
    config: Mapping[str, Any],
    payload: Mapping[str, Any],
    *,
    label: str,
    errors: list[str],
) -> None:
    if payload.get("config_id") != config_content_hash(config):
        errors.append(f"{label}_config_id_mismatch")
    if payload.get("network_id") != config.get("network_id"):
        errors.append(f"{label}_network_id_mismatch")


def _check_receipt_payload(
    config: Mapping[str, Any],
    receipt: Mapping[str, Any],
    payload: Mapping[str, Any],
    errors: list[str],
) -> None:
    kind = receipt.get("kind")
    _check_payload_common(config, payload, label=str(kind), errors=errors)
    governance = config.get("governance") if isinstance(config.get("governance"), Mapping) else {}
    registry = config.get("reporter_registry") if isinstance(config.get("reporter_registry"), Mapping) else {}
    signing = config.get("signing") if isinstance(config.get("signing"), Mapping) else {}
    code_signing = config.get("code_signing") if isinstance(config.get("code_signing"), Mapping) else {}

    if kind == "reporter_registry_deployment":
        if payload.get("deployed") is not True:
            errors.append("reporter_registry_deployment_not_deployed")
        if payload.get("reporter_registry_contract_address") != registry.get("contract_address"):
            errors.append("reporter_registry_contract_address_mismatch")
        if receipt.get("contract_address") != registry.get("contract_address"):
            errors.append("reporter_registry_receipt_contract_mismatch")
        for key in ("min_reporters", "quorum", "minimum_reporter_bond_e8"):
            if payload.get(key) != registry.get(key):
                errors.append(f"reporter_registry_{key}_mismatch")
        if payload.get("active_reporter_count") != _active_reporter_count(config):
            errors.append("reporter_registry_active_reporter_count_mismatch")
        if payload.get("distinct_operator_count") != _distinct_operator_count(config):
            errors.append("reporter_registry_distinct_operator_count_mismatch")
    elif kind == "feed_governance_deployment":
        if payload.get("deployed") is not True:
            errors.append("feed_governance_deployment_not_deployed")
        if payload.get("feed_governance_contract_address") != governance.get("contract_address"):
            errors.append("feed_governance_contract_address_mismatch")
        if receipt.get("contract_address") != governance.get("contract_address"):
            errors.append("feed_governance_receipt_contract_mismatch")
        if payload.get("timelock_seconds") != governance.get("timelock_seconds"):
            errors.append("feed_governance_timelock_seconds_mismatch")
        if payload.get("upgrade_delay_seconds") != governance.get("upgrade_delay_seconds"):
            errors.append("feed_governance_upgrade_delay_seconds_mismatch")
        if payload.get("feed_count") != len(_feed_query_ids(config)):
            errors.append("feed_governance_feed_count_mismatch")
        if payload.get("feed_query_ids") != _feed_query_ids(config):
            errors.append("feed_governance_query_ids_mismatch")
    elif kind == "signed_release_artifact":
        if payload.get("verified") is not True:
            errors.append("signed_release_artifact_not_verified")
        for key in ("scheme", "release_signer_identity", "artifact_digest_alg", "release_artifact_digest"):
            if payload.get(key) != code_signing.get(key):
                errors.append(f"signed_release_{key}_mismatch")
        for key in ("report_signature_scheme", "domain_separator", "receipt_signature_required"):
            if payload.get(key) != signing.get(key):
                errors.append(f"signed_release_{key}_mismatch")
    elif kind == "runtime_controls_attestation":
        if payload.get("verified") is not True:
            errors.append("runtime_controls_attestation_not_verified")
        if payload.get("runtime_controls_hash") != runtime_controls_hash(config):
            errors.append("runtime_controls_hash_mismatch")
        if payload.get("enabled_runtime_controls") != _enabled_runtime_controls(config):
            errors.append("runtime_controls_enabled_set_mismatch")


def check_receipt_bundle(config: Mapping[str, Any], receipt_bundle: Mapping[str, Any] | None) -> dict[str, Any]:
    errors: list[str] = []
    if receipt_bundle is None:
        return {
            "schema": RECEIPT_BUNDLE_SCHEMA,
            "ok": False,
            "status": "rejected",
            "error_count": 1,
            "errors": ["receipt_bundle_required"],
            "receipt_count": 0,
            "receipt_kinds": [],
        }

    _unknown_fields(receipt_bundle, allowed=RECEIPT_BUNDLE_KEYS, label="receipt_bundle", errors=errors)
    if receipt_bundle.get("schema") != RECEIPT_BUNDLE_SCHEMA:
        errors.append("receipt_bundle_schema_mismatch")
    if receipt_bundle.get("config_id") != config_content_hash(config):
        errors.append("receipt_bundle_config_id_mismatch")
    if receipt_bundle.get("network_id") != config.get("network_id"):
        errors.append("receipt_bundle_network_id_mismatch")
    if receipt_bundle.get("chain_id") != config.get("chain_id"):
        errors.append("receipt_bundle_chain_id_mismatch")
    observed_block = receipt_bundle.get("observed_block_number")
    if not isinstance(observed_block, int) or isinstance(observed_block, bool) or observed_block <= 0:
        errors.append("observed_block_number_must_be_positive_int")
    if not _is_sha_ref(receipt_bundle.get("observed_block_hash")):
        errors.append("observed_block_hash_must_be_sha256")
    not_claimed = receipt_bundle.get("not_claimed")
    if not isinstance(not_claimed, list):
        errors.append("receipt_bundle_not_claimed_must_be_list")
    else:
        values = {str(item) for item in not_claimed if isinstance(item, str)}
        errors.extend(f"missing_receipt_not_claim:{item}" for item in sorted(RECEIPT_NOT_CLAIMS - values))

    raw_receipts = receipt_bundle.get("receipts")
    if not isinstance(raw_receipts, list):
        errors.append("receipts_must_be_list")
        raw_receipts = []

    receipts_by_kind: dict[str, Mapping[str, Any]] = {}
    for index, receipt in enumerate(raw_receipts):
        if not isinstance(receipt, Mapping):
            errors.append(f"receipt_{index}_must_be_object")
            continue
        _unknown_fields(receipt, allowed=RECEIPT_KEYS, label=f"receipt_{index}", errors=errors)
        if receipt.get("schema") != RECEIPT_SCHEMA:
            errors.append(f"receipt_{index}_schema_mismatch")
        if receipt.get("receipt_id") != receipt_content_hash(receipt):
            errors.append(f"receipt_{index}_id_mismatch")
        kind = receipt.get("kind")
        if kind not in REQUIRED_RECEIPT_KINDS:
            errors.append(f"receipt_{index}_kind_unknown:{kind}")
        elif isinstance(kind, str) and kind in receipts_by_kind:
            errors.append(f"duplicate_receipt_kind:{kind}")
        elif isinstance(kind, str):
            receipts_by_kind[kind] = receipt
        if receipt.get("chain_id") != config.get("chain_id"):
            errors.append(f"receipt_{index}_chain_id_mismatch")
        if not isinstance(receipt.get("contract_address"), str) or ADDRESS_RE.fullmatch(str(receipt.get("contract_address"))) is None:
            errors.append(f"receipt_{index}_contract_address_invalid")
        if not _is_tx(receipt.get("tx_hash")):
            errors.append(f"receipt_{index}_tx_hash_invalid")
        block_number = receipt.get("block_number")
        if not isinstance(block_number, int) or isinstance(block_number, bool) or block_number <= 0:
            errors.append(f"receipt_{index}_block_number_must_be_positive_int")
        if not _is_sha_ref(receipt.get("block_hash")):
            errors.append(f"receipt_{index}_block_hash_must_be_sha256")
        log_index = receipt.get("log_index")
        if not isinstance(log_index, int) or isinstance(log_index, bool) or log_index < 0:
            errors.append(f"receipt_{index}_log_index_must_be_nonnegative_int")
        payload = receipt.get("payload")
        if not isinstance(payload, Mapping):
            errors.append(f"receipt_{index}_payload_must_be_object")
            continue
        _check_receipt_payload(config, receipt, payload, errors)

    missing = sorted(REQUIRED_RECEIPT_KINDS - set(receipts_by_kind))
    errors.extend(f"missing_receipt_kind:{kind}" for kind in missing)
    return {
        "schema": RECEIPT_BUNDLE_SCHEMA,
        "ok": not errors,
        "status": "accepted" if not errors else "rejected",
        "error_count": len(errors),
        "errors": errors,
        "receipt_count": len(raw_receipts),
        "receipt_kinds": sorted(receipts_by_kind),
    }


def check_config(config: Mapping[str, Any], receipt_bundle: Mapping[str, Any] | None = None) -> dict[str, Any]:
    errors: list[str] = []
    warnings: list[str] = []
    if config.get("schema") != SCHEMA:
        errors.append("schema_mismatch")
    if not _is_prod_chain_id(config.get("chain_id")):
        errors.append("chain_id_must_be_production_candidate")
    if config.get("environment") != "production-candidate":
        errors.append("environment_must_be_production_candidate")
    config_id = config.get("config_id")
    expected_id = config_content_hash(config)
    if config_id is not None and config_id != expected_id:
        errors.append("config_id_mismatch")

    _check_governance(config, errors)
    _check_signing(config, errors)
    _check_code_signing(config, errors)
    _check_reporters(config, errors)
    _check_feeds(config, errors)
    _check_runtime_controls(config, errors)
    _check_not_claimed(config, errors)
    go_live_blockers = _check_economics(config, errors)
    if go_live_blockers:
        warnings.extend(go_live_blockers)
    warnings.extend(GO_LIVE_BLOCKERS)
    warnings = sorted(set(warnings))
    receipt_report = check_receipt_bundle(config, receipt_bundle)
    if not receipt_report["ok"]:
        errors.append("receipt_bundle_rejected")
        errors.extend(f"receipt:{error}" for error in receipt_report["errors"])

    return {
        "schema": REPORT_SCHEMA,
        "ok": not errors,
        "status": "accepted" if not errors else "rejected",
        "config_id": expected_id,
        "environment": config.get("environment"),
        "chain_id": config.get("chain_id"),
        "error_count": len(errors),
        "errors": errors,
        "go_live_blockers": warnings,
        "receipt_bundle_status": receipt_report["status"],
        "receipt_bundle_kind_count": len(receipt_report["receipt_kinds"]),
        "receipt_bundle_errors": receipt_report["errors"],
        "not_claimed": sorted(REQUIRED_NOT_CLAIMS),
    }


def _pubkey(seed: int) -> str:
    return "0x" + f"{seed:096x}"[-96:]


def sample_config() -> dict[str, Any]:
    reporters = []
    for idx, jurisdiction in enumerate(("US", "CH", "SG", "DE", "BR"), start=1):
        reporters.append(
            {
                "reporter_id": f"reporter.prod.{idx}",
                "signing_pubkey": _pubkey(idx),
                "operator_id": f"operator.prod.{idx}",
                "jurisdiction_id": jurisdiction,
                "bond_e8": 10_000_000_000,
                "active": True,
            }
        )
    config: dict[str, Any] = {
        "schema": SCHEMA,
        "network_id": "zeno-oracle-production-candidate-1",
        "chain_id": "zenodex.oracle.mainnet-candidate-1",
        "environment": "production-candidate",
        "governance": {
            "mode": "onchain_timelock",
            "contract_address": "0x1111111111111111111111111111111111111111",
            "timelock_seconds": 172_800,
            "upgrade_delay_seconds": 259_200,
            "emergency_pause_role": "guardian-council-1",
        },
        "signing": {
            "report_signature_scheme": "bls12-381-g2-basic",
            "domain_separator": "zenodex.oracle.prod.report.v1",
            "receipt_signature_required": True,
            "key_rotation_policy": {
                "max_key_age_days": 45,
                "overlap_required": True,
            },
        },
        "code_signing": {
            "required": True,
            "scheme": "sigstore-bundle-v1",
            "release_signer_identity": "release@zenodex.org",
            "artifact_digest_alg": "sha256",
            "release_artifact_digest": _sha_ref("zenodex.oracle.production_network.release_artifact"),
            "verify_command": ["cosign", "verify-blob"],
        },
        "reporter_registry": {
            "contract_address": "0x2222222222222222222222222222222222222222",
            "min_reporters": 5,
            "quorum": 3,
            "minimum_reporter_bond_e8": 10_000_000_000,
            "max_operator_share_bps": 3_400,
            "registered_reporters": reporters,
        },
        "feeds": [
            {
                "feed_id": "feed.prod.tau_usd",
                "query_id": _sha_ref("zenodex.oracle.query.prod.tau_usd"),
                "profile_id": _sha_ref("zenodex.oracle.profile.prod.tau_usd"),
                "min_reporters": 3,
                "min_sources": 3,
                "max_staleness_epochs": 4,
                "max_deviation_bps": 500,
            }
        ],
        "economics": {
            "settlement_asset": "ZENO",
            "reward_pool_cap_e8": 100_000_000_000,
            "dispute_window_epochs": 32,
            "slash_delay_epochs": 32,
            "live_token_settlement": False,
            "settlement_escrow_contract": None,
        },
        "runtime_controls": {key: True for key in sorted(REQUIRED_RUNTIME_CONTROLS)},
        "not_claimed": sorted(REQUIRED_NOT_CLAIMS),
    }
    config["config_id"] = config_content_hash(config)
    return config


def _load_config(path: Path) -> Mapping[str, Any]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise ValueError("config must be a JSON object")
    return obj


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, help="config JSON to verify")
    parser.add_argument("--receipts", type=Path, help="production network receipt bundle JSON")
    parser.add_argument("--sample", action="store_true", help="emit a sample production-candidate config")
    parser.add_argument("--sample-receipts", action="store_true", help="emit a sample receipt bundle")
    parser.add_argument("--format", choices=("json", "text"), default="json")
    parser.add_argument("--require-live", action="store_true", help="fail if go-live blockers remain")
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    if args.sample:
        print(json.dumps(sample_config(), indent=2, sort_keys=True))
        return 0
    config = _load_config(args.input) if args.input else sample_config()
    if args.sample_receipts:
        print(json.dumps(sample_receipt_bundle(config), indent=2, sort_keys=True))
        return 0
    using_default_samples = args.input is None and args.receipts is None
    receipt_bundle = sample_receipt_bundle(config) if using_default_samples else None
    if args.receipts is not None:
        receipt_bundle = _load_config(args.receipts)
    result = check_config(config, receipt_bundle)
    if args.require_live and result["go_live_blockers"]:
        result = dict(result)
        result["ok"] = False
        result["status"] = "rejected"
        result["errors"] = [*result["errors"], "go_live_blockers_present"]
        result["error_count"] = len(result["errors"])
    if args.format == "json":
        print(json.dumps(result, indent=2, sort_keys=True))
    else:
        print(f"status = {result['status']}")
        print(f"error_count = {result['error_count']}")
        print(f"receipt_bundle_status = {result['receipt_bundle_status']}")
        print(f"go_live_blocker_count = {len(result['go_live_blockers'])}")
        print(f"config_id = {result['config_id']}")
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
