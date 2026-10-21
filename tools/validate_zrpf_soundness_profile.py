#!/usr/bin/env python3
"""Fail-closed validator for the research-only ZRPF soundness profile V1.

This validator intentionally recognizes one pinned backend release and grants no
authority.  It validates the profile's arithmetic and assumption labels; it
does not validate a RISC Zero proof or establish cryptographic soundness.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import math
import re
import sys
from pathlib import Path
from typing import Any, NoReturn


SCHEMA = "zenodex/zrpf_soundness_profile/v1"
MAX_PROFILE_BYTES = 256 * 1024
MAX_COUNT = (1 << 63) - 1
PINNED_COMMIT = "8eb06ab020a92dc5b63ba6dd0836d432aba6d890"
PINNED_BLOB_PREFIX = f"https://github.com/risc0/risc0/blob/{PINNED_COMMIT}/"

TOP_LEVEL_FIELDS = {
    "schema",
    "status",
    "generated_at",
    "authority",
    "backend",
    "circuit_parameters",
    "models",
    "topology",
    "event_ledger",
    "composition",
    "policy",
    "sources",
    "non_claims",
}

AUTHORITY_FIELDS = {
    "public_claim_allowed",
    "production_ready",
    "admission_authority",
    "settlement_authority",
    "release_authority",
}

MODEL_ORDER = (
    "proven_list_decoding",
    "conjectured_strict",
    "toy_problem_conjecture",
)

PINNED_MODELS: dict[str, dict[str, Any]] = {
    "proven_list_decoding": {
        "label": "Proven FRI list-decoding regime",
        "assumption_class": "proven_list_decoding_bound",
        "assumption_identity": "RISC Zero v3.0.5 soundness::proven; FRI list-decoding through Johnson-radius analysis; RHO=1/4; M=16; ePrint 2022/1216",
        "source_function": "proven",
        "rv20": 41.567039489746094,
        "rv22": 37.585384368896484,
        "rec18": 46.018375396728516,
    },
    "conjectured_strict": {
        "label": "Conjectured strict list-decoding regime",
        "assumption_class": "proximity_gap_and_deep_fri_conjectures",
        "assumption_identity": "RISC Zero v3.0.5 soundness::conjectured_strict; Proximity Gaps Conjecture 8.4 (ePrint 2020/654) with c1=1,c2=1,ETA=0.05; DEEP-FRI Conjecture 2.3 (ePrint 2019/336) with c_rho=1",
        "source_function": "conjectured_strict",
        "rv20": 74.87677764892578,
        "rv22": 70.95629119873047,
        "rec18": 78.86270904541016,
    },
    "toy_problem_conjecture": {
        "label": "ethSTARK Toy Problem conjecture regime",
        "assumption_class": "toy_problem_conjecture",
        "assumption_identity": "RISC Zero v3.0.5 soundness::toy_model_security; ethSTARK Toy Problem conjecture; RHO=1/4; QUERIES=50",
        "source_function": "toy_model_security",
        "rv20": 97.14198303222656,
        "rv22": 95.29951477050781,
        "rec18": 99.75871276855469,
    },
}

REQUIRED_SOURCE_URLS = {
    "risc0_soundness_calculator_v3_0_5": PINNED_BLOB_PREFIX
    + "risc0/zkp/src/prove/soundness.rs",
    "risc0_rv32im_soundness_tests_v3_0_5": PINNED_BLOB_PREFIX
    + "risc0/zkvm/src/host/server/prove/tests.rs#L1087-L1134",
    "risc0_recursion_tapset_v3_0_5": PINNED_BLOB_PREFIX
    + "risc0/circuit/recursion/src/taps.rs",
    "risc0_recursion_po2_v3_0_5": PINNED_BLOB_PREFIX
    + "risc0/zkvm/src/host/recursion/prove/mod.rs#L58",
    "risc0_rv32im_segment_po2_v3_0_5": PINNED_BLOB_PREFIX
    + "risc0/circuit/rv32im/src/execute/mod.rs#L39",
    "risc0_max_accepted_po2_v3_0_5": PINNED_BLOB_PREFIX
    + "risc0/zkvm/src/receipt.rs#L898-L902",
    "risc0_recursive_composition_v3_0_5": PINNED_BLOB_PREFIX
    + "risc0/zkvm/src/host/recursion/prove/mod.rs#L73-L256",
    "deep_fri": "https://eprint.iacr.org/2019/336",
    "proximity_gaps": "https://eprint.iacr.org/2020/654",
    "fri_low_degree_summary": "https://eprint.iacr.org/2022/1216",
    "crites_stewart_2025_2046": "https://eprint.iacr.org/2025/2046",
}


class ValidationError(ValueError):
    """A profile failed a fail-closed validation rule."""


def _fail(path: str, message: str) -> NoReturn:
    raise ValidationError(f"{path}: {message}")


def _reject_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValidationError(f"$: duplicate JSON object key {key!r}")
        result[key] = value
    return result


def _reject_nonfinite(token: str) -> NoReturn:
    raise ValidationError(f"$: non-finite JSON number {token!r} is forbidden")


def _expect_object(value: Any, path: str) -> dict[str, Any]:
    if type(value) is not dict:
        _fail(path, "expected object")
    return value


def _expect_array(value: Any, path: str) -> list[Any]:
    if type(value) is not list:
        _fail(path, "expected array")
    return value


def _expect_keys(value: dict[str, Any], expected: set[str], path: str) -> None:
    actual = set(value)
    missing = sorted(expected - actual)
    unknown = sorted(actual - expected)
    if missing or unknown:
        _fail(path, f"field mismatch; missing={missing}, unknown={unknown}")


def _expect_const(value: Any, expected: Any, path: str) -> None:
    if type(value) is not type(expected) or value != expected:
        _fail(path, f"expected exactly {expected!r}")


def _expect_false(value: Any, path: str) -> None:
    if type(value) is not bool or value:
        _fail(path, "must be the Boolean false")


def _expect_null(value: Any, path: str) -> None:
    if value is not None:
        _fail(path, "must be null")


def _expect_string(value: Any, path: str, *, maximum: int = 512) -> str:
    if type(value) is not str or not value or len(value) > maximum:
        _fail(path, f"expected nonempty string of at most {maximum} characters")
    return value


def _expect_int(value: Any, path: str, *, minimum: int, maximum: int) -> int:
    if type(value) is not int or not minimum <= value <= maximum:
        _fail(path, f"expected integer in [{minimum}, {maximum}]")
    return value


def _expect_number(value: Any, path: str, *, minimum: float, maximum: float) -> float:
    if type(value) not in (int, float):
        _fail(path, "expected finite JSON number")
    result = float(value)
    if not math.isfinite(result) or not minimum < result <= maximum:
        _fail(path, f"expected finite number in ({minimum}, {maximum}]")
    return result


def _expect_close(actual: float, expected: float, path: str, *, bits: bool = True) -> None:
    if bits:
        close = math.isclose(actual, expected, rel_tol=0.0, abs_tol=1e-11)
    else:
        close = math.isclose(actual, expected, rel_tol=1e-12, abs_tol=0.0)
    if not close:
        _fail(path, f"expected pinned/recomputed value {expected!r}, got {actual!r}")


def _validate_authority(raw: Any) -> None:
    authority = _expect_object(raw, "$.authority")
    _expect_keys(authority, AUTHORITY_FIELDS, "$.authority")
    for field in sorted(AUTHORITY_FIELDS):
        _expect_false(authority[field], f"$.authority.{field}")


def _validate_backend(raw: Any) -> None:
    backend = _expect_object(raw, "$.backend")
    fields = {"name", "version", "commit", "proof_kind", "zrpf_receipt_profile_id"}
    _expect_keys(backend, fields, "$.backend")
    expected = {
        "name": "risc0",
        "version": "v3.0.5",
        "commit": PINNED_COMMIT,
        "proof_kind": "Succinct",
        "zrpf_receipt_profile_id": "risc0_succinct_poseidon2_resolve_3_0_5_v1",
    }
    for field, value in expected.items():
        _expect_const(backend[field], value, f"$.backend.{field}")


def _validate_circuit_parameters(raw: Any) -> None:
    params = _expect_object(raw, "$.circuit_parameters")
    _expect_keys(params, {"global", "rv32im", "recursion"}, "$.circuit_parameters")

    global_params = _expect_object(params["global"], "$.circuit_parameters.global")
    global_expected = {
        "field": "BabyBear",
        "extension_degree": 4,
        "fri_inverse_rate": 4,
        "fri_queries": 50,
        "fri_fold": 16,
        "fri_min_degree": 256,
    }
    _expect_keys(global_params, set(global_expected), "$.circuit_parameters.global")
    for field, value in global_expected.items():
        _expect_const(global_params[field], value, f"$.circuit_parameters.global.{field}")

    rv = _expect_object(params["rv32im"], "$.circuit_parameters.rv32im")
    rv_expected: dict[str, Any] = {
        "default_segment_po2": 20,
        "max_accepted_segment_po2": 22,
        "group_widths": [103, 1, 211],
        "largest_combo": 6,
    }
    _expect_keys(rv, set(rv_expected), "$.circuit_parameters.rv32im")
    for field, value in rv_expected.items():
        _expect_const(rv[field], value, f"$.circuit_parameters.rv32im.{field}")

    recursion = _expect_object(params["recursion"], "$.circuit_parameters.recursion")
    recursion_expected: dict[str, Any] = {
        "trace_po2": 18,
        "group_widths": [12, 23, 128],
        "largest_combo": 6,
    }
    _expect_keys(recursion, set(recursion_expected), "$.circuit_parameters.recursion")
    for field, value in recursion_expected.items():
        _expect_const(recursion[field], value, f"$.circuit_parameters.recursion.{field}")


def _validate_models(raw: Any) -> dict[str, dict[str, float]]:
    models = _expect_array(raw, "$.models")
    if len(models) != len(MODEL_ORDER):
        _fail("$.models", "expected exactly the three pinned model records")

    parsed: dict[str, dict[str, float]] = {}
    model_fields = {
        "id",
        "label",
        "assumption_class",
        "assumption_identity",
        "source_function",
        "accepted_for_authority",
        "rv32im_security_bits",
        "recursion_security_bits",
    }
    for index, expected_id in enumerate(MODEL_ORDER):
        path = f"$.models[{index}]"
        model = _expect_object(models[index], path)
        _expect_keys(model, model_fields, path)
        _expect_const(model["id"], expected_id, f"{path}.id")
        expected = PINNED_MODELS[expected_id]
        for field in ("label", "assumption_class", "assumption_identity", "source_function"):
            _expect_const(model[field], expected[field], f"{path}.{field}")
        _expect_false(model["accepted_for_authority"], f"{path}.accepted_for_authority")

        rv = _expect_object(model["rv32im_security_bits"], f"{path}.rv32im_security_bits")
        _expect_keys(rv, {"po2_20", "po2_22"}, f"{path}.rv32im_security_bits")
        rv20 = _expect_number(rv["po2_20"], f"{path}.rv32im_security_bits.po2_20", minimum=0, maximum=256)
        rv22 = _expect_number(rv["po2_22"], f"{path}.rv32im_security_bits.po2_22", minimum=0, maximum=256)
        _expect_close(rv20, expected["rv20"], f"{path}.rv32im_security_bits.po2_20")
        _expect_close(rv22, expected["rv22"], f"{path}.rv32im_security_bits.po2_22")
        if not rv22 < rv20:
            _fail(f"{path}.rv32im_security_bits", "PO2=22 must have fewer bits than PO2=20")

        rec = _expect_object(model["recursion_security_bits"], f"{path}.recursion_security_bits")
        _expect_keys(rec, {"po2_18"}, f"{path}.recursion_security_bits")
        rec18 = _expect_number(rec["po2_18"], f"{path}.recursion_security_bits.po2_18", minimum=0, maximum=256)
        _expect_close(rec18, expected["rec18"], f"{path}.recursion_security_bits.po2_18")
        parsed[expected_id] = {"rv20": rv20, "rv22": rv22, "rec18": rec18}
    return parsed


def _validate_topology(raw: Any) -> dict[str, int]:
    topology = _expect_object(raw, "$.topology")
    fields = {"kind", "leaf_count", "fanout", "internal_node_count", "total_node_count", "edge_count"}
    _expect_keys(topology, fields, "$.topology")
    _expect_const(topology["kind"], "full_f_ary_tree", "$.topology.kind")
    leaves = _expect_int(topology["leaf_count"], "$.topology.leaf_count", minimum=1, maximum=MAX_COUNT)
    fanout = _expect_int(topology["fanout"], "$.topology.fanout", minimum=2, maximum=65536)
    internal = _expect_int(
        topology["internal_node_count"], "$.topology.internal_node_count", minimum=0, maximum=MAX_COUNT
    )
    nodes = _expect_int(topology["total_node_count"], "$.topology.total_node_count", minimum=1, maximum=MAX_COUNT)
    edges = _expect_int(topology["edge_count"], "$.topology.edge_count", minimum=0, maximum=MAX_COUNT)
    if leaves != 1 + (fanout - 1) * internal:
        _fail("$.topology", "full f-ary tree equation leaves = 1 + (fanout - 1) * internal does not hold")
    if nodes != leaves + internal:
        _fail("$.topology.total_node_count", "must equal leaf_count + internal_node_count")
    if edges != nodes - 1:
        _fail("$.topology.edge_count", "must equal total_node_count - 1")
    return {"leaves": leaves, "fanout": fanout, "internal": internal, "nodes": nodes, "edges": edges}


def _validate_event_ledger(raw: Any, topology: dict[str, int]) -> dict[str, int]:
    ledger = _expect_object(raw, "$.event_ledger")
    fields = {
        "count_basis",
        "counts_complete",
        "base_rv32im_events",
        "recursion_lift_events",
        "recursion_join_events",
        "recursion_resolve_events",
        "recursion_total_events",
        "unknown_event_count",
    }
    _expect_keys(ledger, fields, "$.event_ledger")
    _expect_const(
        ledger["count_basis"],
        "illustrative_one_segment_per_node_minimum",
        "$.event_ledger.count_basis",
    )
    _expect_false(ledger["counts_complete"], "$.event_ledger.counts_complete")
    _expect_null(ledger["unknown_event_count"], "$.event_ledger.unknown_event_count")

    base = _expect_int(ledger["base_rv32im_events"], "$.event_ledger.base_rv32im_events", minimum=1, maximum=MAX_COUNT)
    lifts = _expect_int(
        ledger["recursion_lift_events"], "$.event_ledger.recursion_lift_events", minimum=1, maximum=MAX_COUNT
    )
    joins = _expect_int(
        ledger["recursion_join_events"], "$.event_ledger.recursion_join_events", minimum=0, maximum=MAX_COUNT
    )
    resolves = _expect_int(
        ledger["recursion_resolve_events"], "$.event_ledger.recursion_resolve_events", minimum=0, maximum=MAX_COUNT
    )
    recursion = _expect_int(
        ledger["recursion_total_events"], "$.event_ledger.recursion_total_events", minimum=1, maximum=MAX_COUNT
    )
    if base != topology["nodes"]:
        _fail("$.event_ledger.base_rv32im_events", "one-segment minimum requires one base proof per node")
    if lifts != topology["nodes"]:
        _fail("$.event_ledger.recursion_lift_events", "one-segment minimum requires one lift per node")
    if joins != 0:
        _fail("$.event_ledger.recursion_join_events", "one-segment minimum has zero joins")
    if resolves != topology["edges"]:
        _fail("$.event_ledger.recursion_resolve_events", "requires one resolve per parent-child assumption edge")
    if recursion != lifts + joins + resolves:
        _fail("$.event_ledger.recursion_total_events", "must equal lift + join + resolve events")
    return {"base": base, "recursion": recursion, "lifts": lifts, "joins": joins, "resolves": resolves}


def _validate_composition(raw: Any, models: dict[str, dict[str, float]], events: dict[str, int]) -> list[dict[str, float | str]]:
    composition = _expect_object(raw, "$.composition")
    fields = {"method", "formula", "calculation_status", "uses_rv32im_po2", "per_model"}
    _expect_keys(composition, fields, "$.composition")
    _expect_const(composition["method"], "finite_union_bound", "$.composition.method")
    _expect_const(
        composition["formula"],
        "epsilon_total <= B*2^(-b_base) + R*2^(-b_recursion)",
        "$.composition.formula",
    )
    _expect_const(
        composition["calculation_status"],
        "illustrative_only_incomplete_event_counts",
        "$.composition.calculation_status",
    )
    _expect_const(composition["uses_rv32im_po2"], 22, "$.composition.uses_rv32im_po2")
    results = _expect_array(composition["per_model"], "$.composition.per_model")
    if len(results) != len(MODEL_ORDER):
        _fail("$.composition.per_model", "expected exactly one result per pinned model")

    result_fields = {
        "model_id",
        "base_security_bits_used",
        "recursion_security_bits_used",
        "epsilon_upper_bound_if_counts_exact",
        "effective_security_bits_if_counts_exact",
    }
    calculated: list[dict[str, float | str]] = []
    for index, model_id in enumerate(MODEL_ORDER):
        path = f"$.composition.per_model[{index}]"
        result = _expect_object(results[index], path)
        _expect_keys(result, result_fields, path)
        _expect_const(result["model_id"], model_id, f"{path}.model_id")
        base_bits = _expect_number(result["base_security_bits_used"], f"{path}.base_security_bits_used", minimum=0, maximum=256)
        recursion_bits = _expect_number(
            result["recursion_security_bits_used"], f"{path}.recursion_security_bits_used", minimum=0, maximum=256
        )
        _expect_close(base_bits, models[model_id]["rv22"], f"{path}.base_security_bits_used")
        _expect_close(recursion_bits, models[model_id]["rec18"], f"{path}.recursion_security_bits_used")
        expected_epsilon = events["base"] * math.pow(2.0, -base_bits) + events["recursion"] * math.pow(
            2.0, -recursion_bits
        )
        expected_bits = -math.log2(expected_epsilon)
        epsilon = _expect_number(
            result["epsilon_upper_bound_if_counts_exact"],
            f"{path}.epsilon_upper_bound_if_counts_exact",
            minimum=0,
            maximum=1,
        )
        effective_bits = _expect_number(
            result["effective_security_bits_if_counts_exact"],
            f"{path}.effective_security_bits_if_counts_exact",
            minimum=0,
            maximum=256,
        )
        _expect_close(epsilon, expected_epsilon, f"{path}.epsilon_upper_bound_if_counts_exact", bits=False)
        _expect_close(effective_bits, expected_bits, f"{path}.effective_security_bits_if_counts_exact")
        calculated.append({"model_id": model_id, "epsilon": expected_epsilon, "effective_bits": expected_bits})
    return calculated


def _validate_policy(raw: Any) -> None:
    policy = _expect_object(raw, "$.policy")
    fields = {"selected_model_id", "minimum_system_security_bits", "promotion_gate_passed", "reason"}
    _expect_keys(policy, fields, "$.policy")
    _expect_null(policy["selected_model_id"], "$.policy.selected_model_id")
    _expect_null(policy["minimum_system_security_bits"], "$.policy.minimum_system_security_bits")
    _expect_false(policy["promotion_gate_passed"], "$.policy.promotion_gate_passed")
    _expect_string(policy["reason"], "$.policy.reason")


def _validate_sources(raw: Any) -> None:
    sources = _expect_array(raw, "$.sources")
    if not 11 <= len(sources) <= 32:
        _fail("$.sources", "expected between 11 and 32 source records")
    seen: dict[str, str] = {}
    fields = {"id", "source_class", "url", "relevance"}
    for index, raw_source in enumerate(sources):
        path = f"$.sources[{index}]"
        source = _expect_object(raw_source, path)
        _expect_keys(source, fields, path)
        source_id = _expect_string(source["id"], f"{path}.id", maximum=128)
        if re.fullmatch(r"[a-z0-9_]+", source_id) is None:
            _fail(f"{path}.id", "must match [a-z0-9_]+")
        if source_id in seen:
            _fail(f"{path}.id", "duplicate source id")
        source_class = _expect_string(source["source_class"], f"{path}.source_class", maximum=32)
        if source_class not in {"pinned_source", "pinned_test", "paper"}:
            _fail(f"{path}.source_class", "unknown source class")
        url = _expect_string(source["url"], f"{path}.url")
        if not url.startswith("https://"):
            _fail(f"{path}.url", "must use HTTPS")
        _expect_string(source["relevance"], f"{path}.relevance")
        seen[source_id] = url
    missing = sorted(set(REQUIRED_SOURCE_URLS) - set(seen))
    if missing:
        _fail("$.sources", f"missing required pinned sources: {missing}")
    for source_id, expected_url in REQUIRED_SOURCE_URLS.items():
        if seen[source_id] != expected_url:
            _fail(f"$.sources[{source_id!r}].url", f"expected exactly {expected_url!r}")


def _validate_non_claims(raw: Any) -> None:
    non_claims = _expect_array(raw, "$.non_claims")
    if not 5 <= len(non_claims) <= 32:
        _fail("$.non_claims", "expected between 5 and 32 explicit non-claims")
    for index, value in enumerate(non_claims):
        _expect_string(value, f"$.non_claims[{index}]")


def validate_profile(profile: Any) -> dict[str, Any]:
    """Validate a decoded profile and return its recomputed research summary."""

    root = _expect_object(profile, "$")
    _expect_keys(root, TOP_LEVEL_FIELDS, "$")
    _expect_const(root["schema"], SCHEMA, "$.schema")
    _expect_const(root["status"], "research_only", "$.status")
    generated_at = _expect_string(root["generated_at"], "$.generated_at", maximum=10)
    try:
        parsed_date = dt.date.fromisoformat(generated_at)
    except ValueError as exc:
        _fail("$.generated_at", f"invalid ISO calendar date: {exc}")
    if parsed_date.isoformat() != generated_at:
        _fail("$.generated_at", "must be canonical YYYY-MM-DD")

    _validate_authority(root["authority"])
    _validate_backend(root["backend"])
    _validate_circuit_parameters(root["circuit_parameters"])
    models = _validate_models(root["models"])
    topology = _validate_topology(root["topology"])
    events = _validate_event_ledger(root["event_ledger"], topology)
    calculated = _validate_composition(root["composition"], models, events)
    _validate_policy(root["policy"])
    _validate_sources(root["sources"])
    _validate_non_claims(root["non_claims"])
    return {
        "ok": True,
        "schema": SCHEMA,
        "status": "research_only",
        "authority": False,
        "promotion_gate_passed": False,
        "counts_complete": False,
        "topology": topology,
        "events": events,
        "models": calculated,
    }


def load_profile(path: Path) -> tuple[dict[str, Any], bytes]:
    """Load strict UTF-8 JSON, rejecting oversize, duplicate, and non-finite input."""

    try:
        raw = path.read_bytes()
    except OSError as exc:
        raise ValidationError(f"{path}: cannot read profile: {exc}") from exc
    if len(raw) > MAX_PROFILE_BYTES:
        raise ValidationError(f"{path}: profile exceeds {MAX_PROFILE_BYTES} bytes")
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise ValidationError(f"{path}: profile is not strict UTF-8: {exc}") from exc
    if text.startswith("\ufeff"):
        raise ValidationError(f"{path}: UTF-8 BOM is forbidden")
    try:
        value = json.loads(
            text,
            object_pairs_hook=_reject_duplicate_keys,
            parse_constant=_reject_nonfinite,
        )
    except ValidationError:
        raise
    except json.JSONDecodeError as exc:
        raise ValidationError(f"{path}: invalid JSON: {exc}") from exc
    return _expect_object(value, "$"), raw


def load_and_validate(path: Path) -> dict[str, Any]:
    profile, raw = load_profile(path)
    report = validate_profile(profile)
    report["profile_path"] = str(path)
    report["profile_sha256"] = hashlib.sha256(raw).hexdigest()
    return report


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "profile",
        nargs="?",
        type=Path,
        default=Path(__file__).with_name("zrpf_soundness_profile_v1.example.json"),
        help="profile JSON (defaults to the bundled research-only example)",
    )
    parser.add_argument("--json", action="store_true", help="emit a machine-readable validation report")
    return parser


def main(argv: list[str] | None = None) -> int:
    args = _build_parser().parse_args(argv)
    try:
        report = load_and_validate(args.profile)
    except ValidationError as exc:
        if args.json:
            print(json.dumps({"ok": False, "error": str(exc)}, sort_keys=True, separators=(",", ":")))
        else:
            print(f"INVALID: {exc}", file=sys.stderr)
        return 1
    if args.json:
        print(json.dumps(report, sort_keys=True, separators=(",", ":")))
    else:
        print(
            "VALID research-only profile; authority=false; "
            f"counts_complete=false; sha256={report['profile_sha256']}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
