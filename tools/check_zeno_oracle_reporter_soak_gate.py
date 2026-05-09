#!/usr/bin/env python3
"""Check local reporter-soak observations for ZenoOracle production readiness."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
TOOLS = ROOT / "tools"
if str(TOOLS) not in sys.path:
    sys.path.insert(1, str(TOOLS))

from zenodex_oracle_source_diversity import (  # noqa: E402
    sample_source_diversity,
    verify_source_diversity,
)

POLICY_SCHEMA = "zenodex.oracle.reporter_soak_policy.v1"
BUNDLE_SCHEMA = "zenodex.oracle.reporter_soak_observation_bundle.v1"
OBSERVATION_SCHEMA = "zenodex.oracle.reporter_soak_observation.v1"
REPORT_SCHEMA = "zenodex.oracle.reporter_soak_gate_check.v1"
BPS_DENOM = 10_000
SHA_RE = re.compile(r"^sha256:[0-9a-f]{64}$")
REQUIRED_NOT_CLAIMS = {
    "does_not_claim_live_oracle_network_safety",
    "does_not_claim_public_soak_completed",
    "does_not_claim_real_world_operator_independence",
    "does_not_claim_reporter_honesty",
}
BUNDLE_NOT_CLAIMS = {
    "does_not_claim_observations_verified_against_public_telemetry",
    "does_not_claim_operator_legal_independence",
}
GO_LIVE_BLOCKERS = [
    "public_soak_not_completed",
    "observations_not_verified_against_public_telemetry",
    "operator_independence_not_legally_attested",
]
POLICY_KEYS = {
    "schema",
    "policy_id",
    "policy_name",
    "environment",
    "query_id",
    "min_soak_epochs",
    "min_reporters",
    "min_distinct_operators",
    "max_operator_share_bps",
    "min_success_rate_bps",
    "max_dispute_rate_bps",
    "source_diversity",
    "not_claimed",
}
BUNDLE_KEYS = {
    "schema",
    "policy_id",
    "query_id",
    "observed_epoch",
    "reporter_observations",
    "not_claimed",
}
OBSERVATION_KEYS = {
    "schema",
    "observation_id",
    "reporter_id",
    "operator_id",
    "active_epochs",
    "successful_report_count",
    "disputed_report_count",
    "rejected_report_count",
    "signed_report_root",
}


def _canonical_bytes(obj: Mapping[str, Any]) -> bytes:
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")


def policy_content_hash(policy: Mapping[str, Any]) -> str:
    payload = dict(policy)
    payload.pop("policy_id", None)
    return "sha256:" + hashlib.sha256(_canonical_bytes(payload)).hexdigest()


def observation_content_hash(observation: Mapping[str, Any]) -> str:
    payload = dict(observation)
    payload.pop("observation_id", None)
    return "sha256:" + hashlib.sha256(_canonical_bytes(payload)).hexdigest()


def _sha(label: str) -> str:
    return "sha256:" + hashlib.sha256(label.encode("utf-8")).hexdigest()


def _is_sha(value: Any) -> bool:
    return isinstance(value, str) and SHA_RE.fullmatch(value) is not None


def _unknown_fields(obj: Mapping[str, Any], *, allowed: set[str], label: str, errors: list[str]) -> None:
    for key in obj:
        if not isinstance(key, str):
            errors.append(f"{label}_field_must_be_string")
        elif key not in allowed:
            errors.append(f"unknown_{label}_field:{key}")


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


def _string_field(obj: Mapping[str, Any], key: str, errors: list[str]) -> str | None:
    value = obj.get(key)
    if not isinstance(value, str) or not value.strip():
        errors.append(f"{key}_must_be_nonempty_string")
        return None
    return str(value)


def _check_not_claims(
    obj: Mapping[str, Any],
    *,
    required: set[str],
    label: str,
    errors: list[str],
) -> None:
    raw = obj.get("not_claimed")
    if not isinstance(raw, list):
        errors.append(f"{label}_not_claimed_must_be_list")
        return
    values = {item for item in raw if isinstance(item, str)}
    errors.extend(f"missing_{label}_not_claim:{item}" for item in sorted(required - values))


def _observation(
    *,
    reporter_id: str,
    operator_id: str,
    active_epochs: int,
    successful_report_count: int,
    disputed_report_count: int = 0,
    rejected_report_count: int = 1,
) -> dict[str, Any]:
    observation: dict[str, Any] = {
        "schema": OBSERVATION_SCHEMA,
        "reporter_id": reporter_id,
        "operator_id": operator_id,
        "active_epochs": int(active_epochs),
        "successful_report_count": int(successful_report_count),
        "disputed_report_count": int(disputed_report_count),
        "rejected_report_count": int(rejected_report_count),
        "signed_report_root": _sha(f"{reporter_id}:{operator_id}:{active_epochs}:{successful_report_count}"),
    }
    observation["observation_id"] = observation_content_hash(observation)
    return observation


def sample_policy() -> dict[str, Any]:
    source_diversity = sample_source_diversity()
    policy: dict[str, Any] = {
        "schema": POLICY_SCHEMA,
        "policy_name": "zeno-oracle-reporter-soak-candidate-v1",
        "environment": "production-candidate",
        "query_id": source_diversity["query_id"],
        "min_soak_epochs": 72,
        "min_reporters": 5,
        "min_distinct_operators": 5,
        "max_operator_share_bps": 3_400,
        "min_success_rate_bps": 9_500,
        "max_dispute_rate_bps": 500,
        "source_diversity": source_diversity,
        "not_claimed": sorted(REQUIRED_NOT_CLAIMS),
    }
    policy["policy_id"] = policy_content_hash(policy)
    return policy


def sample_observation_bundle(policy: Mapping[str, Any] | None = None) -> dict[str, Any]:
    active_policy = sample_policy() if policy is None else policy
    observations = [
        _observation(reporter_id=f"reporter.prod.{idx}", operator_id=f"operator.prod.{idx}", active_epochs=96, successful_report_count=191)
        for idx in range(1, 6)
    ]
    return {
        "schema": BUNDLE_SCHEMA,
        "policy_id": active_policy.get("policy_id"),
        "query_id": active_policy.get("query_id"),
        "observed_epoch": 10_000,
        "reporter_observations": observations,
        "not_claimed": sorted(BUNDLE_NOT_CLAIMS),
    }


def _validate_policy(policy: Mapping[str, Any], errors: list[str]) -> None:
    _unknown_fields(policy, allowed=POLICY_KEYS, label="policy", errors=errors)
    if policy.get("schema") != POLICY_SCHEMA:
        errors.append("policy_schema_mismatch")
    if policy.get("policy_id") != policy_content_hash(policy):
        errors.append("policy_id_mismatch")
    if policy.get("environment") != "production-candidate":
        errors.append("environment_must_be_production_candidate")
    _string_field(policy, "policy_name", errors)
    query_id = _string_field(policy, "query_id", errors)
    _int_field(policy, "min_soak_epochs", errors, minimum=1)
    _int_field(policy, "min_reporters", errors, minimum=3)
    _int_field(policy, "min_distinct_operators", errors, minimum=3)
    _int_field(policy, "max_operator_share_bps", errors, minimum=1, maximum=BPS_DENOM)
    _int_field(policy, "min_success_rate_bps", errors, minimum=1, maximum=BPS_DENOM)
    _int_field(policy, "max_dispute_rate_bps", errors, minimum=0, maximum=BPS_DENOM)
    source_diversity = policy.get("source_diversity")
    if not isinstance(source_diversity, Mapping):
        errors.append("source_diversity_must_be_object")
    else:
        diversity_result = verify_source_diversity(source_diversity).to_json_obj()
        if diversity_result["status"] != "accepted":
            errors.append("source_diversity_rejected")
            errors.extend(f"source_diversity:{error}" for error in diversity_result["errors"])
        if query_id is not None and source_diversity.get("query_id") != query_id:
            errors.append("source_diversity_query_id_mismatch")
    _check_not_claims(policy, required=REQUIRED_NOT_CLAIMS, label="policy", errors=errors)


def _validate_observation(raw: Any, *, index: int, errors: list[str]) -> Mapping[str, Any] | None:
    if not isinstance(raw, Mapping):
        errors.append(f"observation_{index}_must_be_object")
        return None
    _unknown_fields(raw, allowed=OBSERVATION_KEYS, label=f"observation_{index}", errors=errors)
    if raw.get("schema") != OBSERVATION_SCHEMA:
        errors.append(f"observation_{index}_schema_mismatch")
    if raw.get("observation_id") != observation_content_hash(raw):
        errors.append(f"observation_{index}_id_mismatch")
    _string_field(raw, "reporter_id", errors)
    _string_field(raw, "operator_id", errors)
    _int_field(raw, "active_epochs", errors, minimum=0)
    _int_field(raw, "successful_report_count", errors, minimum=0)
    _int_field(raw, "disputed_report_count", errors, minimum=0)
    _int_field(raw, "rejected_report_count", errors, minimum=0)
    if not _is_sha(raw.get("signed_report_root")):
        errors.append(f"observation_{index}_signed_report_root_must_be_sha256")
    return raw


def check_reporter_soak_gate(
    policy: Mapping[str, Any],
    observation_bundle: Mapping[str, Any] | None,
    *,
    require_live: bool = False,
) -> dict[str, Any]:
    errors: list[str] = []
    _validate_policy(policy, errors)
    observations: list[Mapping[str, Any]] = []
    if observation_bundle is None:
        errors.append("observation_bundle_required")
        bundle_status = "missing"
    else:
        bundle_status = "accepted"
        _unknown_fields(observation_bundle, allowed=BUNDLE_KEYS, label="observation_bundle", errors=errors)
        if observation_bundle.get("schema") != BUNDLE_SCHEMA:
            errors.append("observation_bundle_schema_mismatch")
        if observation_bundle.get("policy_id") != policy.get("policy_id"):
            errors.append("observation_bundle_policy_id_mismatch")
        if observation_bundle.get("query_id") != policy.get("query_id"):
            errors.append("observation_bundle_query_id_mismatch")
        observed_epoch = _int_field(observation_bundle, "observed_epoch", errors, minimum=0)
        _check_not_claims(observation_bundle, required=BUNDLE_NOT_CLAIMS, label="observation_bundle", errors=errors)
        raw_observations = observation_bundle.get("reporter_observations")
        if not isinstance(raw_observations, list):
            errors.append("reporter_observations_must_be_list")
            raw_observations = []
        for index, raw in enumerate(raw_observations):
            observation = _validate_observation(raw, index=index, errors=errors)
            if observation is not None:
                active_epochs = observation.get("active_epochs")
                if (
                    isinstance(observed_epoch, int)
                    and isinstance(active_epochs, int)
                    and not isinstance(active_epochs, bool)
                    and active_epochs > observed_epoch
                ):
                    errors.append(f"reporter_active_epochs_exceeds_observed_epoch:{observation.get('reporter_id')}")
                observations.append(observation)

    reporter_ids = [str(observation.get("reporter_id")) for observation in observations if isinstance(observation.get("reporter_id"), str)]
    operator_ids = [str(observation.get("operator_id")) for observation in observations if isinstance(observation.get("operator_id"), str)]
    signed_report_roots = [
        str(observation.get("signed_report_root"))
        for observation in observations
        if isinstance(observation.get("signed_report_root"), str)
    ]
    if len(set(reporter_ids)) != len(reporter_ids):
        errors.append("duplicate_reporter_id")
    if len(set(signed_report_roots)) != len(signed_report_roots):
        errors.append("duplicate_signed_report_root")
    min_reporters = policy.get("min_reporters")
    if isinstance(min_reporters, int) and len(set(reporter_ids)) < min_reporters:
        errors.append("reporter_count_below_policy")
    min_distinct_operators = policy.get("min_distinct_operators")
    if isinstance(min_distinct_operators, int) and len(set(operator_ids)) < min_distinct_operators:
        errors.append("distinct_operator_count_below_policy")
    max_operator_share_bps = policy.get("max_operator_share_bps")
    if isinstance(max_operator_share_bps, int) and operator_ids:
        for operator in set(operator_ids):
            share = (operator_ids.count(operator) * BPS_DENOM) // len(operator_ids)
            if share > max_operator_share_bps:
                errors.append(f"operator_share_exceeds_policy:{operator}")
    min_soak_epochs = policy.get("min_soak_epochs")
    min_success_rate_bps = policy.get("min_success_rate_bps")
    max_dispute_rate_bps = policy.get("max_dispute_rate_bps")
    for observation in observations:
        reporter_id = observation.get("reporter_id")
        active_epochs = observation.get("active_epochs")
        if isinstance(active_epochs, int) and isinstance(min_soak_epochs, int) and active_epochs < min_soak_epochs:
            errors.append(f"reporter_soak_epochs_below_policy:{reporter_id}")
        success = observation.get("successful_report_count")
        disputed = observation.get("disputed_report_count")
        rejected = observation.get("rejected_report_count")
        if isinstance(success, int) and isinstance(disputed, int) and isinstance(rejected, int):
            total = success + disputed + rejected
            if total <= 0:
                errors.append(f"reporter_observation_total_zero:{reporter_id}")
                continue
            if isinstance(active_epochs, int) and not isinstance(active_epochs, bool) and total < active_epochs:
                errors.append(f"reporter_total_reports_below_active_epochs:{reporter_id}")
            success_rate_bps = (success * BPS_DENOM) // total
            dispute_rate_bps = (disputed * BPS_DENOM) // total
            if isinstance(min_success_rate_bps, int) and success_rate_bps < min_success_rate_bps:
                errors.append(f"reporter_success_rate_below_policy:{reporter_id}")
            if isinstance(max_dispute_rate_bps, int) and dispute_rate_bps > max_dispute_rate_bps:
                errors.append(f"reporter_dispute_rate_above_policy:{reporter_id}")

    if require_live:
        errors.extend(GO_LIVE_BLOCKERS)
    if bundle_status == "accepted" and errors:
        bundle_status = "rejected"
    return {
        "schema": REPORT_SCHEMA,
        "ok": not errors,
        "status": "accepted" if not errors else "rejected",
        "error_count": len(errors),
        "errors": errors,
        "policy_id": policy.get("policy_id"),
        "observation_bundle_status": bundle_status,
        "reporter_count": len(set(reporter_ids)),
        "distinct_operator_count": len(set(operator_ids)),
        "go_live_blockers": list(GO_LIVE_BLOCKERS),
        "not_claimed": sorted(REQUIRED_NOT_CLAIMS),
    }


def _load_json(path: Path) -> Mapping[str, Any]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise ValueError(f"{path} must be a JSON object")
    return obj


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--policy", type=Path, help="reporter soak policy JSON")
    parser.add_argument("--observations", type=Path, help="reporter soak observation bundle JSON")
    parser.add_argument("--sample-policy", action="store_true", help="emit the built-in sample policy")
    parser.add_argument("--sample-observations", action="store_true", help="emit the built-in sample observation bundle")
    parser.add_argument("--format", choices=("json", "text"), default="json")
    parser.add_argument("--require-live", action="store_true", help="fail while public reporter-soak blockers remain")
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    policy = _load_json(args.policy) if args.policy else sample_policy()
    if args.sample_policy:
        print(json.dumps(policy, indent=2, sort_keys=True))
        return 0
    if args.sample_observations:
        print(json.dumps(sample_observation_bundle(policy), indent=2, sort_keys=True))
        return 0
    using_default_samples = args.policy is None and args.observations is None
    observation_bundle = sample_observation_bundle(policy) if using_default_samples else None
    if args.observations is not None:
        observation_bundle = _load_json(args.observations)
    result = check_reporter_soak_gate(policy, observation_bundle, require_live=args.require_live)
    if args.format == "json":
        print(json.dumps(result, indent=2, sort_keys=True))
    else:
        print(f"status = {result['status']}")
        print(f"observation_bundle_status = {result['observation_bundle_status']}")
        print(f"reporter_count = {result['reporter_count']}")
        print(f"distinct_operator_count = {result['distinct_operator_count']}")
        print(f"error_count = {result['error_count']}")
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
