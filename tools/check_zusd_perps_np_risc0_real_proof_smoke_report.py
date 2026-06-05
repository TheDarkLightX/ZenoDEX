#!/usr/bin/env python3
"""Validate scoped zUSD and perps NP RISC0 real-proof smoke reports."""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping

CHECK_SCHEMA = "zenodex.scoped_risc0_real_proof_smoke_report_check.v1"


@dataclass(frozen=True)
class SurfaceSpec:
    surface: str
    report_schema: str
    proof_type: str
    proof_type_key: str
    required_cases: frozenset[str]
    required_tamper_rejections: frozenset[str]


ZUSD_SPEC = SurfaceSpec(
    surface="zusd",
    report_schema="zenodex.zusd_risc0_real_proof_smoke_report.v1",
    proof_type="risc0.zenodex_zusd_transition.v1",
    proof_type_key="proof_type",
    required_cases=frozenset({"mint"}),
    required_tamper_rejections=frozenset(
        {
            "chain_id",
            "operation_hash",
            "oracle_binding_hash",
            "participant_set_hash",
            "post_app_hash",
            "pre_app_hash",
            "state_delta_hash",
            "wrong_image_id",
            "wrong_proof_type",
            "zusd_balance_root_hash",
            "zusd_vault_root_hash",
        }
    ),
)

PERPS_NP_SPEC = SurfaceSpec(
    surface="perps_np",
    report_schema="zenodex.perps_np_risc0_real_proof_smoke.v1",
    proof_type="risc0.zenodex_perps_np_transition.v1",
    proof_type_key="proof_surface",
    required_cases=frozenset({"four_wallet"}),
    required_tamper_rejections=frozenset(
        {
            "chain_id",
            "collateral_binding_hash",
            "operation_hash",
            "oracle_binding_hash",
            "participant_set_hash",
            "post_app_hash",
            "pre_app_hash",
            "receipt_root",
            "state_delta_hash",
            "wrong_image_id",
            "wrong_proof_type",
        }
    ),
)

SPECS_BY_SURFACE = {spec.surface: spec for spec in (ZUSD_SPEC, PERPS_NP_SPEC)}
SPECS_BY_SCHEMA = {spec.report_schema: spec for spec in SPECS_BY_SURFACE.values()}


def validate_scoped_risc0_real_proof_smoke_report_v1(
    report: Any,
    *,
    surface: str | None = None,
    require_proof_files: bool = False,
    min_positive: int = 1,
    min_negative: int = 0,
    required_cases: set[str] | frozenset[str] | None = None,
) -> dict[str, Any]:
    errors: list[str] = []
    obj = _mapping(report, "report", errors)
    spec = _resolve_spec(obj, surface=surface, errors=errors)
    expected_cases = set(required_cases if required_cases is not None else (spec.required_cases if spec else set()))

    if obj.get("ok") is not True:
        errors.append("ok must be true")
    if obj.get("production_security_claim") is not False:
        errors.append("production_security_claim must be false")
    if spec is not None:
        if obj.get("schema") != spec.report_schema:
            errors.append("schema mismatch")
        if obj.get(spec.proof_type_key) != spec.proof_type:
            errors.append(f"{spec.proof_type_key} mismatch")
        if spec.surface == "perps_np":
            floor = _positive_int(obj.get("dynamic_membership_floor"), "dynamic_membership_floor", errors)
            if floor is not None and floor < 4:
                errors.append("dynamic_membership_floor must be at least 4")

    cases = _list(obj.get("cases"), "cases", errors)
    case_count = _nonnegative_int(obj.get("case_count"), "case_count", errors)
    if case_count is not None and case_count != len(cases):
        errors.append("case_count must match cases length")

    reported_positive = _nonnegative_int(obj.get("positive"), "positive", errors)
    reported_negative = _nonnegative_int(obj.get("negative"), "negative", errors)

    positive_count = 0
    negative_count = 0
    seen_cases: set[str] = set()
    case_reports: list[dict[str, Any]] = []
    for index, raw_case in enumerate(cases):
        item_errors: list[str] = []
        item = _mapping(raw_case, f"cases[{index}]", item_errors)
        case_name = _str(item.get("case"), f"cases[{index}].case", item_errors)
        kind = _str(item.get("kind"), f"cases[{index}].kind", item_errors)
        if case_name is not None:
            if case_name in seen_cases:
                item_errors.append(f"cases[{index}].case must be unique")
            seen_cases.add(case_name)
        if item.get("ok") is not True:
            item_errors.append(f"cases[{index}].ok must be true")
        if kind == "positive":
            positive_count += 1
            if spec is not None:
                _validate_positive_case(
                    item,
                    index=index,
                    spec=spec,
                    require_proof_files=require_proof_files,
                    errors=item_errors,
                )
        elif kind == "negative":
            negative_count += 1
            _validate_negative_case(item, index=index, errors=item_errors)
        else:
            item_errors.append(f"cases[{index}].kind must be positive or negative")
        errors.extend(item_errors)
        case_reports.append({"case": case_name, "kind": kind, "ok": not item_errors, "errors": item_errors})

    if reported_positive is not None and reported_positive != positive_count:
        errors.append("positive count mismatch")
    if reported_negative is not None and reported_negative != negative_count:
        errors.append("negative count mismatch")
    if positive_count < min_positive:
        errors.append(f"positive count below minimum:{min_positive}")
    if negative_count < min_negative:
        errors.append(f"negative count below minimum:{min_negative}")
    missing_cases = sorted(expected_cases - seen_cases)
    if missing_cases:
        errors.append(f"missing required cases: {','.join(missing_cases)}")

    return {
        "schema": CHECK_SCHEMA,
        "ok": not errors,
        "status": "accepted" if not errors else "rejected",
        "surface": spec.surface if spec is not None else surface,
        "proof_type": spec.proof_type if spec is not None else None,
        "errors": errors,
        "required_cases": sorted(expected_cases),
        "case_count": len(cases),
        "positive": positive_count,
        "negative": negative_count,
        "cases": case_reports,
    }


def _validate_positive_case(
    item: Mapping[str, Any],
    *,
    index: int,
    spec: SurfaceSpec,
    require_proof_files: bool,
    errors: list[str],
) -> None:
    if item.get("proof_type") != spec.proof_type:
        errors.append(f"cases[{index}].proof_type mismatch")
    if item.get("strict_verify") is not True:
        errors.append(f"cases[{index}].strict_verify must be true")
    image_id = _str(item.get("risc0_image_id"), f"cases[{index}].risc0_image_id", errors)
    if image_id is not None:
        if not _is_hex(image_id, 64):
            errors.append(f"cases[{index}].risc0_image_id must be 64-char hex")
        elif _hex_text(image_id) == "0" * 64:
            errors.append(f"cases[{index}].risc0_image_id must be nonzero")
    proof_base64_len = _positive_int(item.get("proof_base64_len"), f"cases[{index}].proof_base64_len", errors)
    proof_path = _str(item.get("proof_path"), f"cases[{index}].proof_path", errors)
    if require_proof_files and proof_path is not None:
        path = Path(proof_path)
        if not path.is_file():
            errors.append(f"cases[{index}].proof_path does not exist")
        elif path.stat().st_size == 0:
            errors.append(f"cases[{index}].proof_path must be non-empty")
        else:
            _validate_proof_artifact_binding(
                item,
                index=index,
                spec=spec,
                proof_path=path,
                proof_base64_len=proof_base64_len,
                errors=errors,
            )
    tamper = _string_set(item.get("tamper_rejections"), f"cases[{index}].tamper_rejections", errors)
    missing_tamper = sorted(spec.required_tamper_rejections - tamper)
    if missing_tamper:
        errors.append(f"cases[{index}].tamper_rejections missing: {','.join(missing_tamper)}")
    if spec.surface == "zusd":
        _validate_zusd_positive_case(item, index=index, errors=errors)
    elif spec.surface == "perps_np":
        _validate_perps_np_positive_case(item, index=index, errors=errors)


def _validate_zusd_positive_case(item: Mapping[str, Any], *, index: int, errors: list[str]) -> None:
    minted = _intish(item.get("minted_zusd_e8"), f"cases[{index}].minted_zusd_e8", errors)
    collateral_value = _intish(item.get("collateral_value_e8"), f"cases[{index}].collateral_value_e8", errors)
    mcr_bps = _positive_int(item.get("mcr_bps"), f"cases[{index}].mcr_bps", errors)
    if minted is not None and minted <= 0:
        errors.append(f"cases[{index}].minted_zusd_e8 must be positive")
    if collateral_value is not None and collateral_value <= 0:
        errors.append(f"cases[{index}].collateral_value_e8 must be positive")
    if mcr_bps is not None and mcr_bps < 10_000:
        errors.append(f"cases[{index}].mcr_bps must be at least 10000")


def _validate_perps_np_positive_case(item: Mapping[str, Any], *, index: int, errors: list[str]) -> None:
    if item.get("current_surface_binding_check") is not True:
        errors.append(f"cases[{index}].current_surface_binding_check must be true")
    participant_count = _positive_int(item.get("participant_count"), f"cases[{index}].participant_count", errors)
    if participant_count is not None and participant_count < 4:
        errors.append(f"cases[{index}].participant_count must be at least 4")
    intent_count = _nonnegative_int(item.get("intent_count"), f"cases[{index}].intent_count", errors)
    if _intish(item.get("net_position_base"), f"cases[{index}].net_position_base", errors) != 0:
        errors.append(f"cases[{index}].net_position_base must be zero")
    if _intish(item.get("funding_residual_e8"), f"cases[{index}].funding_residual_e8", errors) != 0:
        errors.append(f"cases[{index}].funding_residual_e8 must be zero")
    matched = _intish(item.get("matched_base_volume"), f"cases[{index}].matched_base_volume", errors)
    case_name = _str(item.get("case"), f"cases[{index}].case", errors)
    transition_kind = _perps_np_transition_kind(item, case_name=case_name, intent_count=intent_count, matched=matched)

    # REVIEW [B -> A-]: the old checker treated every positive perps proof as
    # match evidence, so the strictly verified ADL smoke was rejected because it
    # correctly has zero new intents and zero matched volume. Positive evidence is
    # now typed by transition kind: match epochs still require live fills, while
    # ADL epochs require a settlement-only proof shape.
    if transition_kind == "match_epoch":
        if intent_count is None or intent_count <= 0:
            errors.append(f"cases[{index}].intent_count must be positive for match_epoch")
        if participant_count is not None and intent_count is not None and intent_count < participant_count:
            errors.append(f"cases[{index}].intent_count must cover participant_count")
        if matched is not None and matched <= 0:
            errors.append(f"cases[{index}].matched_base_volume must be positive for match_epoch")
    elif transition_kind == "adl_epoch":
        if intent_count is not None and intent_count != 0:
            errors.append(f"cases[{index}].intent_count must be zero for adl_epoch")
        if matched is not None and matched != 0:
            errors.append(f"cases[{index}].matched_base_volume must be zero for adl_epoch")
        claims_delta = _intish(item.get("claims_paid_delta_e8"), f"cases[{index}].claims_paid_delta_e8", errors)
        if claims_delta is not None and claims_delta <= 0:
            errors.append(f"cases[{index}].claims_paid_delta_e8 must be positive for adl_epoch")
        position_reduction = _intish(
            item.get("position_abs_reduction_base"),
            f"cases[{index}].position_abs_reduction_base",
            errors,
        )
        if position_reduction is not None and position_reduction <= 0:
            errors.append(f"cases[{index}].position_abs_reduction_base must be positive for adl_epoch")
    else:
        errors.append(f"cases[{index}].transition_kind must be match_epoch or adl_epoch")


def _perps_np_transition_kind(
    item: Mapping[str, Any],
    *,
    case_name: str | None,
    intent_count: int | None,
    matched: int | None,
) -> str | None:
    if "transition_kind" in item:
        raw = item.get("transition_kind")
        # Review grade: A- boundary. Explicit malformed values are report
        # integrity failures; only truly absent legacy fields may be inferred.
        return raw if isinstance(raw, str) else None
    # Backward-compatible inference for already-produced proof reports. New
    # smoke reports write transition_kind explicitly.
    if case_name == "adl_wallet" and intent_count == 0 and matched == 0:
        return "adl_epoch"
    return "match_epoch"


def _validate_negative_case(item: Mapping[str, Any], *, index: int, errors: list[str]) -> None:
    if item.get("rejected_as_expected") is not True:
        errors.append(f"cases[{index}].rejected_as_expected must be true")
    exit_code = item.get("exit_code")
    if exit_code is not None:
        value = _nonnegative_int(exit_code, f"cases[{index}].exit_code", errors)
        if value == 0:
            errors.append(f"cases[{index}].exit_code must be nonzero")


ZUSD_META_HEX_KEYS = frozenset(
    {
        "operation_hash",
        "oracle_binding_hash",
        "participant_set_hash",
        "post_app_hash",
        "pre_app_hash",
        "state_delta_hash",
        "zusd_balance_root_hash",
        "zusd_vault_root_hash",
    }
)

PERPS_NP_META_HEX_KEYS = frozenset(
    {
        "collateral_binding_hash",
        "operation_hash",
        "oracle_binding_hash",
        "participant_set_hash",
        "post_app_hash",
        "pre_app_hash",
        "receipt_root",
        "state_delta_hash",
    }
)


def _validate_proof_artifact_binding(
    item: Mapping[str, Any],
    *,
    index: int,
    spec: SurfaceSpec,
    proof_path: Path,
    proof_base64_len: int | None,
    errors: list[str],
) -> None:
    prefix = f"cases[{index}].proof"
    proof = _load_json_mapping(proof_path, prefix, errors)
    if proof is None:
        return

    # REVIEW [B -> A-]: `--require-proof-files` used to check only
    # file-exists/non-empty. Any unrelated local file could satisfy that. The
    # checker now binds the positive report row to the JSON proof envelope shape
    # emitted by the real smoke tools: proof_type, proof byte length, image ID,
    # and the surface-specific journal/meta fields.
    if proof.get("proof_type") != spec.proof_type:
        errors.append(f"{prefix}.proof_type mismatch")
    proof_b64 = proof.get("proof")
    if not isinstance(proof_b64, str) or not proof_b64:
        errors.append(f"{prefix}.proof must be a non-empty string")
    elif proof_base64_len is not None and proof_base64_len != len(proof_b64):
        errors.append(f"{prefix}.proof_base64_len mismatch")
    if not _is_hex(proof.get("state_hash"), 64):
        errors.append(f"{prefix}.state_hash must be 64-char hex")

    meta = proof.get("meta")
    if not isinstance(meta, Mapping):
        errors.append(f"{prefix}.meta must be an object")
        return
    _expect_equal(
        item.get("risc0_image_id"),
        meta.get("risc0_image_id"),
        f"{prefix}.risc0_image_id",
        errors,
    )
    if not _is_hex(meta.get("risc0_image_id"), 64):
        errors.append(f"{prefix}.risc0_image_id must be 64-char hex")

    if spec.surface == "zusd":
        _require_meta_hex_keys(meta, keys=ZUSD_META_HEX_KEYS, prefix=prefix, errors=errors)
        for key in ("minted_zusd_e8", "collateral_value_e8", "mcr_bps"):
            _expect_intish_equal(item.get(key), meta.get(key), f"{prefix}.{key}", errors)
    elif spec.surface == "perps_np":
        _require_meta_hex_keys(meta, keys=PERPS_NP_META_HEX_KEYS, prefix=prefix, errors=errors)
        _expect_intish_equal(
            item.get("participant_count"),
            meta.get("participant_count"),
            f"{prefix}.participant_count",
            errors,
        )
        for key in ("funding_residual_e8", "matched_base_volume", "net_position_base"):
            _expect_intish_equal(item.get(key), meta.get(key), f"{prefix}.{key}", errors)


def _require_meta_hex_keys(
    meta: Mapping[str, Any],
    *,
    keys: frozenset[str],
    prefix: str,
    errors: list[str],
) -> None:
    for key in sorted(keys):
        if not _is_hex(meta.get(key), 64):
            errors.append(f"{prefix}.{key} must be 64-char hex")


def _expect_equal(actual: Any, expected: Any, name: str, errors: list[str]) -> None:
    if actual != expected:
        errors.append(f"{name} mismatch")


def _expect_intish_equal(actual: Any, expected: Any, name: str, errors: list[str]) -> None:
    actual_i = _intish(actual, f"{name}.report", errors)
    expected_i = _intish(expected, f"{name}.artifact", errors)
    if actual_i is not None and expected_i is not None and actual_i != expected_i:
        errors.append(f"{name} mismatch")


def _resolve_spec(obj: Mapping[str, Any], *, surface: str | None, errors: list[str]) -> SurfaceSpec | None:
    if surface:
        spec = SPECS_BY_SURFACE.get(surface)
        if spec is None:
            errors.append(f"unknown surface: {surface}")
            return None
        return spec
    schema = obj.get("schema")
    spec = SPECS_BY_SCHEMA.get(schema)
    if spec is None:
        errors.append("unknown report schema")
    return spec


def _mapping(value: Any, name: str, errors: list[str]) -> Mapping[str, Any]:
    if isinstance(value, Mapping):
        return value
    errors.append(f"{name} must be an object")
    return {}


def _list(value: Any, name: str, errors: list[str]) -> list[Any]:
    if isinstance(value, list):
        return value
    errors.append(f"{name} must be a list")
    return []


def _str(value: Any, name: str, errors: list[str]) -> str | None:
    if isinstance(value, str) and value:
        return value
    errors.append(f"{name} must be a non-empty string")
    return None


def _nonnegative_int(value: Any, name: str, errors: list[str]) -> int | None:
    if isinstance(value, int) and not isinstance(value, bool) and value >= 0:
        return int(value)
    errors.append(f"{name} must be a non-negative int")
    return None


def _positive_int(value: Any, name: str, errors: list[str]) -> int | None:
    if isinstance(value, int) and not isinstance(value, bool) and value > 0:
        return int(value)
    errors.append(f"{name} must be a positive int")
    return None


def _intish(value: Any, name: str, errors: list[str]) -> int | None:
    if isinstance(value, int) and not isinstance(value, bool):
        return int(value)
    if isinstance(value, str):
        try:
            return int(value, 10)
        except ValueError:
            pass
    errors.append(f"{name} must be an integer or decimal integer string")
    return None


def _string_set(value: Any, name: str, errors: list[str]) -> set[str]:
    if not isinstance(value, list):
        errors.append(f"{name} must be a list")
        return set()
    out: set[str] = set()
    for item in value:
        if not isinstance(item, str) or not item:
            errors.append(f"{name} entries must be non-empty strings")
            continue
        out.add(item)
    return out


def _load_json_mapping(path: Path, name: str, errors: list[str]) -> Mapping[str, Any] | None:
    try:
        value = _load_json(path)
    except Exception as exc:  # noqa: BLE001
        errors.append(f"{name} could not be loaded: {exc}")
        return None
    if not isinstance(value, Mapping):
        errors.append(f"{name} must be an object")
        return None
    return value


def _is_hex(value: Any, length: int) -> bool:
    text = _hex_text(value)
    return text is not None and len(text) == length and all(ch in "0123456789abcdef" for ch in text)


def _hex_text(value: Any) -> str | None:
    if not isinstance(value, str):
        return None
    text = value[2:] if value.startswith("0x") else value
    return text.lower()


def _load_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("report", type=Path)
    parser.add_argument("--surface", choices=("zusd", "perps_np"), default=None)
    parser.add_argument("--require-proof-files", action="store_true")
    parser.add_argument("--min-positive", type=int, default=1)
    parser.add_argument("--min-negative", type=int, default=0)
    parser.add_argument("--required-case", action="append", default=[])
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args(argv)

    check = validate_scoped_risc0_real_proof_smoke_report_v1(
        _load_json(args.report),
        surface=args.surface,
        require_proof_files=bool(args.require_proof_files),
        min_positive=int(args.min_positive),
        min_negative=int(args.min_negative),
        required_cases=set(args.required_case) if args.required_case else None,
    )
    if args.pretty:
        print(json.dumps(check, indent=2, sort_keys=True))
    else:
        print(json.dumps(check, separators=(",", ":"), sort_keys=True))
    return 0 if check["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
