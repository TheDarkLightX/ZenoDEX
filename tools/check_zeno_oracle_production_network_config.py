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
BPS_DENOM = 10_000
SHA256_RE = re.compile(r"^sha256:[0-9a-f]{64}$")
ADDRESS_RE = re.compile(r"^0x[0-9a-fA-F]{40}$")
PUBKEY_RE = re.compile(r"^0x[0-9a-fA-F]{96}$")

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
    "deploy_reporter_registry_contract",
    "deploy_feed_governance_contract",
    "publish_signed_release_artifacts",
    "fund_live_settlement_escrow",
    "run_public_network_soak",
]


def _canonical_bytes(obj: Mapping[str, Any]) -> bytes:
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")


def config_content_hash(config: Mapping[str, Any]) -> str:
    payload = dict(config)
    payload.pop("config_id", None)
    return "sha256:" + hashlib.sha256(_canonical_bytes(payload)).hexdigest()


def _is_sha_ref(value: Any) -> bool:
    return isinstance(value, str) and SHA256_RE.fullmatch(value) is not None


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
    verify_command = code_signing.get("verify_command")
    if not isinstance(verify_command, list) or not verify_command or not all(isinstance(x, str) and x for x in verify_command):
        errors.append("verify_command_must_be_nonempty_string_list")


def _check_reporters(config: Mapping[str, Any], errors: list[str]) -> None:
    registry = _object_field(config, "reporter_registry", errors)
    if not registry:
        return
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


def check_config(config: Mapping[str, Any]) -> dict[str, Any]:
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
        "not_claimed": sorted(REQUIRED_NOT_CLAIMS),
    }


def _sha_ref(label: str) -> str:
    return "sha256:" + hashlib.sha256(label.encode("utf-8")).hexdigest()


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
            "verify_command": ["cosign", "verify-blob"],
        },
        "reporter_registry": {
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
    parser.add_argument("--sample", action="store_true", help="emit a sample production-candidate config")
    parser.add_argument("--format", choices=("json", "text"), default="json")
    parser.add_argument("--require-live", action="store_true", help="fail if go-live blockers remain")
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    if args.sample:
        print(json.dumps(sample_config(), indent=2, sort_keys=True))
        return 0
    config = _load_config(args.input) if args.input else sample_config()
    result = check_config(config)
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
        print(f"go_live_blocker_count = {len(result['go_live_blockers'])}")
        print(f"config_id = {result['config_id']}")
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
