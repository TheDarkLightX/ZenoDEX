#!/usr/bin/env python3
"""Verify the first-shell Zeno Oracle critical consumer profile catalog."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping

sys.path.insert(0, str(Path(__file__).resolve().parent))

from zenodex_oracle import EVIDENCE_RANK  # noqa: E402
from zenodex_oracle_adapter import PROFILE_SCHEMA, profile_content_hash  # noqa: E402


CATALOG_SCHEMA = "zenodex.oracle.consumer_profile_catalog.v1"
RESULT_SCHEMA = "zenodex.oracle.consumer_profile_catalog_verify_result.v1"
MAX_CATALOG_BYTES = 500_000
SHA256_RE = re.compile(r"^sha256:[0-9a-f]{64}$")
TOKEN_RE = re.compile(r"^[a-z][a-z0-9_.:-]{0,127}$")
CATALOG_KEYS = {"schema", "profiles"}
PROFILE_KEYS = {
    "schema",
    "profile_id",
    "consumer_module",
    "action_kind",
    "query_id",
    "required_evidence_floor",
    "max_freshness_window_epochs",
    "critical",
}
NOT_CLAIMED = [
    "does_not_claim_downstream_modules_runtime_wired",
    "does_not_claim_query_semantics_final",
    "does_not_claim_true_market_price",
    "does_not_claim_production_oracle_network_live",
]


def sample_hash(tag: str) -> str:
    return "sha256:" + hashlib.sha256(tag.encode("utf-8")).hexdigest()


REQUIRED_PROFILE_SPECS: dict[tuple[str, str], dict[str, Any]] = {
    ("zenodex.perps", "settle_epoch"): {
        "query_id": sample_hash("zenodex.oracle.query.perps.index_price_e8"),
        "required_evidence_floor": "O3",
        "max_freshness_window_epochs": 2,
    },
    ("zenodex.perps", "liquidate_account"): {
        "query_id": sample_hash("zenodex.oracle.query.perps.index_price_e8"),
        "required_evidence_floor": "O3",
        "max_freshness_window_epochs": 1,
    },
    ("zenodex.zusd", "mint"): {
        "query_id": sample_hash("zenodex.oracle.query.zusd.collateral_price_e8"),
        "required_evidence_floor": "O3",
        "max_freshness_window_epochs": 2,
    },
    ("zenodex.zusd", "liquidate_vault"): {
        "query_id": sample_hash("zenodex.oracle.query.zusd.collateral_price_e8"),
        "required_evidence_floor": "O3",
        "max_freshness_window_epochs": 1,
    },
    ("zenodex.routing", "guarded_quote"): {
        "query_id": sample_hash("zenodex.oracle.query.routing.reference_price_e8"),
        "required_evidence_floor": "O3",
        "max_freshness_window_epochs": 4,
    },
    ("zenodex.trigger", "execute_trigger"): {
        "query_id": sample_hash("zenodex.oracle.query.trigger.reference_price_e8"),
        "required_evidence_floor": "O3",
        "max_freshness_window_epochs": 2,
    },
}


@dataclass(frozen=True)
class ConsumerProfileCatalogResult:
    status: str
    errors: list[str]
    profile_count: int | None = None
    required_profile_count: int | None = None
    profile_keys: list[str] | None = None

    def to_json_obj(self) -> dict[str, Any]:
        return {
            "schema": RESULT_SCHEMA,
            "ok": self.status == "accepted",
            "status": self.status,
            "profile_count": self.profile_count,
            "required_profile_count": self.required_profile_count,
            "profile_keys": list(self.profile_keys or []),
            "errors": list(self.errors),
            "not_claimed": NOT_CLAIMED,
        }


def _build_profile(
    *,
    consumer_module: str,
    action_kind: str,
    query_id: str,
    required_evidence_floor: str,
    max_freshness_window_epochs: int,
) -> dict[str, Any]:
    profile = {
        "schema": PROFILE_SCHEMA,
        "consumer_module": consumer_module,
        "action_kind": action_kind,
        "query_id": query_id,
        "required_evidence_floor": required_evidence_floor,
        "max_freshness_window_epochs": max_freshness_window_epochs,
        "critical": True,
    }
    profile["profile_id"] = profile_content_hash(profile)
    return profile


def sample_catalog() -> dict[str, Any]:
    profiles = [
        _build_profile(
            consumer_module=consumer_module,
            action_kind=action_kind,
            query_id=str(spec["query_id"]),
            required_evidence_floor=str(spec["required_evidence_floor"]),
            max_freshness_window_epochs=int(spec["max_freshness_window_epochs"]),
        )
        for (consumer_module, action_kind), spec in sorted(REQUIRED_PROFILE_SPECS.items())
    ]
    return {
        "schema": CATALOG_SCHEMA,
        "profiles": profiles,
    }


def _is_hash(value: object) -> bool:
    return isinstance(value, str) and bool(SHA256_RE.match(value))


def _unknown_fields(
    obj: Mapping[str, Any],
    *,
    allowed: set[str],
    label: str,
    errors: list[str],
) -> None:
    for key in obj.keys():
        if not isinstance(key, str):
            errors.append(f"{label}_field_must_be_string")
        elif key not in allowed:
            errors.append(f"unknown_{label}_field:{key}")


def _hash(obj: Mapping[str, Any], key: str, errors: list[str]) -> str | None:
    value = obj.get(key)
    if not _is_hash(value):
        errors.append(f"{key}_must_be_sha256")
        return None
    return str(value)


def _token(obj: Mapping[str, Any], key: str, errors: list[str]) -> str | None:
    value = obj.get(key)
    if not isinstance(value, str) or not TOKEN_RE.match(value):
        errors.append(f"{key}_must_be_token")
        return None
    return str(value)


def _int_ge_zero(obj: Mapping[str, Any], key: str, errors: list[str]) -> int | None:
    value = obj.get(key)
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        errors.append(f"{key}_must_be_int_ge_0")
        return None
    return int(value)


def _evidence_floor(profile: Mapping[str, Any], errors: list[str]) -> str | None:
    value = profile.get("required_evidence_floor")
    if not isinstance(value, str) or value not in EVIDENCE_RANK:
        errors.append("required_evidence_floor_invalid")
        return None
    if EVIDENCE_RANK[value] < EVIDENCE_RANK["O3"]:
        errors.append("required_evidence_floor_below_critical_minimum")
    return value


def _profiles(obj: Mapping[str, Any], errors: list[str]) -> list[Mapping[str, Any]]:
    raw = obj.get("profiles")
    if not isinstance(raw, list):
        errors.append("profiles_must_be_list")
        return []
    if len(raw) != len(REQUIRED_PROFILE_SPECS):
        errors.append(f"profile_count_mismatch:{len(raw)}!={len(REQUIRED_PROFILE_SPECS)}")
    profiles: list[Mapping[str, Any]] = []
    for pos, profile in enumerate(raw):
        if not isinstance(profile, Mapping):
            errors.append(f"profile_{pos}_must_be_object")
            continue
        profiles.append(profile)
    return profiles


def _profile_key(consumer_module: str | None, action_kind: str | None) -> tuple[str, str] | None:
    if consumer_module is None or action_kind is None:
        return None
    return consumer_module, action_kind


def verify_consumer_profile_catalog(obj: Mapping[str, Any]) -> ConsumerProfileCatalogResult:
    errors: list[str] = []
    _unknown_fields(obj, allowed=CATALOG_KEYS, label="catalog", errors=errors)
    if obj.get("schema") != CATALOG_SCHEMA:
        errors.append("catalog_schema_mismatch")

    profiles = _profiles(obj, errors)
    seen_keys: set[tuple[str, str]] = set()
    seen_ids: set[str] = set()
    profile_key_labels: list[str] = []

    for pos, profile in enumerate(profiles):
        _unknown_fields(profile, allowed=PROFILE_KEYS, label=f"profile_{pos}", errors=errors)
        if profile.get("schema") != PROFILE_SCHEMA:
            errors.append(f"profile_schema_mismatch:{pos}")
        profile_id = _hash(profile, "profile_id", errors)
        if profile_id is not None:
            try:
                expected_profile_id = profile_content_hash(profile)
            except (TypeError, ValueError):
                expected_profile_id = None
                errors.append(f"profile_content_hash_unencodable:{profile_id}")
            if expected_profile_id is not None and profile_id != expected_profile_id:
                errors.append(f"profile_content_hash_mismatch:{profile_id}")
            if profile_id in seen_ids:
                errors.append(f"duplicate_profile_id:{profile_id}")
            seen_ids.add(profile_id)
        consumer_module = _token(profile, "consumer_module", errors)
        action_kind = _token(profile, "action_kind", errors)
        query_id = _hash(profile, "query_id", errors)
        required_evidence_floor = _evidence_floor(profile, errors)
        max_freshness_window_epochs = _int_ge_zero(profile, "max_freshness_window_epochs", errors)
        if profile.get("critical") is not True:
            errors.append(f"profile_must_be_critical:{pos}")

        key = _profile_key(consumer_module, action_kind)
        if key is None:
            continue
        label = f"{key[0]}:{key[1]}"
        profile_key_labels.append(label)
        if key in seen_keys:
            errors.append(f"duplicate_profile_key:{label}")
        seen_keys.add(key)

        spec = REQUIRED_PROFILE_SPECS.get(key)
        if spec is None:
            errors.append(f"unsupported_profile_key:{label}")
            continue
        if query_id is not None and query_id != spec["query_id"]:
            errors.append(f"profile_query_id_mismatch:{label}")
        if (
            required_evidence_floor is not None
            and EVIDENCE_RANK[required_evidence_floor] < EVIDENCE_RANK[str(spec["required_evidence_floor"])]
        ):
            errors.append(f"profile_evidence_floor_below_required:{label}")
        if (
            max_freshness_window_epochs is not None
            and max_freshness_window_epochs > int(spec["max_freshness_window_epochs"])
        ):
            errors.append(f"profile_freshness_window_exceeds_required:{label}")

    for required_key in sorted(REQUIRED_PROFILE_SPECS):
        if required_key not in seen_keys:
            errors.append(f"missing_required_profile:{required_key[0]}:{required_key[1]}")

    return ConsumerProfileCatalogResult(
        status="rejected" if errors else "accepted",
        errors=errors,
        profile_count=len(profiles),
        required_profile_count=len(REQUIRED_PROFILE_SPECS),
        profile_keys=sorted(profile_key_labels),
    )


def _load_json(path: Path) -> Mapping[str, Any]:
    size = path.stat().st_size
    if size > MAX_CATALOG_BYTES:
        raise ValueError(f"consumer_profile_catalog_file_too_large:{size}>{MAX_CATALOG_BYTES}")
    with path.open("r", encoding="utf-8") as handle:
        obj = json.load(handle)
    if not isinstance(obj, Mapping):
        raise ValueError("consumer profile catalog root must be a JSON object")
    return obj


def _write_result(result: ConsumerProfileCatalogResult, output: Path | None) -> None:
    text = json.dumps(result.to_json_obj(), indent=2, sort_keys=True) + "\n"
    if output is None:
        sys.stdout.write(text)
    else:
        output.write_text(text, encoding="utf-8")


def cmd_verify(args: argparse.Namespace) -> int:
    try:
        catalog = _load_json(Path(args.catalog))
    except Exception as exc:  # pragma: no cover - exercised through CLI tests
        result = ConsumerProfileCatalogResult(
            status="inconclusive",
            errors=[f"consumer_profile_catalog_load_failed:{exc}"],
        )
        _write_result(result, Path(args.output) if args.output else None)
        return 3

    result = verify_consumer_profile_catalog(catalog)
    _write_result(result, Path(args.output) if args.output else None)
    return 0 if result.status == "accepted" else 2


def cmd_sample(args: argparse.Namespace) -> int:
    text = json.dumps(sample_catalog(), indent=2, sort_keys=True) + "\n"
    if args.output:
        Path(args.output).write_text(text, encoding="utf-8")
    else:
        sys.stdout.write(text)
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    verify = subparsers.add_parser("verify", help="verify an Oracle consumer profile catalog JSON file")
    verify.add_argument("catalog", help="path to a consumer profile catalog JSON file")
    verify.add_argument("--output", help="optional output path for the verifier result JSON")
    verify.set_defaults(func=cmd_verify)

    sample = subparsers.add_parser("sample", help="emit a minimal accepted consumer profile catalog")
    sample.add_argument("--output", help="optional output path for the sample catalog JSON")
    sample.set_defaults(func=cmd_sample)
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
