#!/usr/bin/env python3
"""Plan and validate finite, level-specific ZRPF image ladders.

This module is deliberately non-authoritative.  It validates research-manifest
structure and exact integer topology arithmetic; it does not verify receipts,
derive RISC Zero image IDs, attest builds, or compute cryptographic soundness.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping, Sequence


PLAN_SCHEMA = "zrpf/finite-image-ladder-plan/v1"
MANIFEST_SCHEMA = "zrpf/finite-image-ladder-manifest/v1"
VALIDATION_SCHEMA = "zrpf/finite-image-ladder-validation/v1"
ARTIFACT_CLASS = "non_authority_research_plan"

MIN_FANOUT = 2
MAX_FANOUT = 8
MIN_DEPTH = 1
MAX_DEPTH = 7
MAX_MANIFEST_BYTES = 1 << 20

FIRST_GATE_FANOUT = 2
FIRST_GATE_DEPTH = 3

ID_RE = re.compile(r"^[a-z0-9][a-z0-9._-]{0,127}$")
DIGEST_RE = re.compile(r"^[0-9a-f]{64}$")

NEGATIVE_TESTS = (
    "child_omission_rejects",
    "child_duplication_rejects",
    "child_reordering_rejects",
    "child_image_substitution_rejects",
    "level_substitution_rejects",
    "unresolved_assumption_rejects",
    "profile_or_control_substitution_rejects",
    "sealed_host_rejects_non_root_image",
)

REQUIRED_BEFORE_ANY_AUTHORITY = (
    "cryptographic_fanout2_depth3_receipt_evidence",
    "sealed_host_verifier_negative_evidence",
    "exact_backend_and_build_provenance",
    "executable_end_to_end_soundness_budget",
    "resource_and_storage_benchmarks",
    "governed_release_review",
)

REQUIRED_NON_CLAIMS = (
    "This artifact grants no settlement, admission, release, or production authority.",
    "Capacity arithmetic is not measured throughput, latency, storage viability, or scalability evidence.",
    "Manifest validation does not verify RISC Zero receipts, image derivation, build reproducibility, or cryptographic soundness.",
    "The bounded fanout-2 depth-3 ESSO model is not an unbounded correctness proof.",
    "A constant-size root receipt does not make child journals, witnesses, or data available.",
)


@dataclass(frozen=True)
class LadderValidationError(ValueError):
    """A deterministic, machine-readable validation failure."""

    code: str
    path: str
    message: str

    def __str__(self) -> str:
        return f"{self.code} at {self.path}: {self.message}"

    def to_dict(self) -> dict[str, str]:
        return {"code": self.code, "path": self.path, "message": self.message}


@dataclass(frozen=True)
class LadderPlan:
    fanout: int
    depth: int
    leaf_count: int
    internal_node_count: int
    total_node_count: int
    edge_count: int
    level_node_counts: tuple[int, ...]
    aggregate_rounds: int
    program_image_count: int
    capacity_class: str

    def to_dict(self) -> dict[str, Any]:
        level_plan = []
        for level, node_count in enumerate(self.level_node_counts):
            level_plan.append(
                {
                    "level": level,
                    "role": "leaf_adapter" if level == 0 else "aggregate",
                    "node_count": node_count,
                    "child_level": None if level == 0 else level - 1,
                    "exact_children_per_node": 0 if level == 0 else self.fanout,
                    "program_image_must_be_distinct": True,
                }
            )
        warnings = [
            "NON_AUTHORITY_CAPACITY_ARITHMETIC_ONLY",
            "NO_CRYPTOGRAPHIC_RECEIPT_EVIDENCE",
            "NO_END_TO_END_SOUNDNESS_BUDGET",
        ]
        if self.capacity_class == "first_validation_gate":
            warnings.append("FIRST_STRUCTURAL_GATE_NOT_EXECUTED")
        else:
            warnings.append("FIRST_FANOUT2_DEPTH3_GATE_REQUIRED_BEFORE_SCALE_CLAIMS")
        return {
            "schema": PLAN_SCHEMA,
            "authority": False,
            "capacity_class": self.capacity_class,
            "fanout": self.fanout,
            "depth": self.depth,
            "leaf_count": self.leaf_count,
            "internal_node_count": self.internal_node_count,
            "total_node_count": self.total_node_count,
            "edge_count": self.edge_count,
            "level_node_counts": list(self.level_node_counts),
            "aggregate_rounds": self.aggregate_rounds,
            "program_image_count": self.program_image_count,
            "build_order": [f"level_{level}" for level in range(self.program_image_count)],
            "level_plan": level_plan,
            "warnings": warnings,
        }


def _fail(code: str, path: str, message: str) -> None:
    raise LadderValidationError(code=code, path=path, message=message)


def _require(condition: bool, code: str, path: str, message: str) -> None:
    if not condition:
        _fail(code, path, message)


def _require_int(value: Any, path: str) -> int:
    _require(type(value) is int, "type.integer", path, "expected an integer, not a boolean or float")
    return value


def _require_bool(value: Any, path: str) -> bool:
    _require(type(value) is bool, "type.boolean", path, "expected a boolean")
    return value


def _require_string(value: Any, path: str) -> str:
    _require(isinstance(value, str) and bool(value), "type.string", path, "expected a non-empty string")
    return value


def _require_list(value: Any, path: str) -> list[Any]:
    _require(isinstance(value, list), "type.array", path, "expected an array")
    return value


def _require_object(value: Any, path: str) -> dict[str, Any]:
    _require(isinstance(value, dict), "type.object", path, "expected an object")
    return value


def _check_fields(obj: Mapping[str, Any], required: set[str], path: str) -> None:
    actual = set(obj.keys())
    missing = sorted(required - actual)
    unknown = sorted(actual - required)
    _require(not missing, "schema.missing_field", path, f"missing fields: {missing}")
    _require(not unknown, "schema.unknown_field", path, f"unknown fields: {unknown}")


def _require_exact(value: Any, expected: Any, path: str) -> None:
    _require(value == expected and type(value) is type(expected), "value.exact", path, f"expected {expected!r}")


def _require_identifier(value: Any, path: str) -> str:
    text = _require_string(value, path)
    _require(bool(ID_RE.fullmatch(text)), "value.identifier", path, "expected a lowercase bounded identifier")
    return text


def _require_digest(value: Any, path: str) -> str:
    text = _require_string(value, path)
    _require(bool(DIGEST_RE.fullmatch(text)), "value.digest", path, "expected 64 lowercase hexadecimal characters")
    return text


def plan_ladder(fanout: int, depth: int) -> LadderPlan:
    """Return exact full-tree topology arithmetic within the research bounds."""

    fanout = _require_int(fanout, "$.fanout")
    depth = _require_int(depth, "$.depth")
    _require(
        MIN_FANOUT <= fanout <= MAX_FANOUT,
        "bounds.fanout",
        "$.fanout",
        f"expected {MIN_FANOUT}..{MAX_FANOUT}",
    )
    _require(
        MIN_DEPTH <= depth <= MAX_DEPTH,
        "bounds.depth",
        "$.depth",
        f"expected {MIN_DEPTH}..{MAX_DEPTH}",
    )

    level_node_counts = tuple(fanout ** exponent for exponent in range(depth, -1, -1))
    leaf_count = level_node_counts[0]
    internal_node_count = sum(level_node_counts[1:])
    total_node_count = leaf_count + internal_node_count
    capacity_class = (
        "first_validation_gate"
        if fanout == FIRST_GATE_FANOUT and depth == FIRST_GATE_DEPTH
        else "capacity_only_projection"
    )
    return LadderPlan(
        fanout=fanout,
        depth=depth,
        leaf_count=leaf_count,
        internal_node_count=internal_node_count,
        total_node_count=total_node_count,
        edge_count=total_node_count - 1,
        level_node_counts=level_node_counts,
        aggregate_rounds=depth,
        program_image_count=depth + 1,
        capacity_class=capacity_class,
    )


def _reject_duplicate_keys(pairs: Sequence[tuple[str, Any]]) -> dict[str, Any]:
    obj: dict[str, Any] = {}
    for key, value in pairs:
        if key in obj:
            _fail("json.duplicate_key", "$", f"duplicate object key {key!r}")
        obj[key] = value
    return obj


def _reject_json_constant(value: str) -> None:
    _fail("json.non_finite_number", "$", f"non-finite JSON number {value!r} is forbidden")


def loads_json_strict(text: str) -> Any:
    """Parse JSON while rejecting duplicate keys and non-standard numbers."""

    try:
        return json.loads(
            text,
            object_pairs_hook=_reject_duplicate_keys,
            parse_constant=_reject_json_constant,
        )
    except LadderValidationError:
        raise
    except json.JSONDecodeError as exc:
        _fail("json.syntax", "$", f"line {exc.lineno}, column {exc.colno}: {exc.msg}")


def load_manifest(path: str | Path) -> dict[str, Any]:
    manifest_path = Path(path)
    try:
        size = manifest_path.stat().st_size
    except OSError as exc:
        _fail("io.stat", "$", str(exc))
    _require(
        size <= MAX_MANIFEST_BYTES,
        "bounds.manifest_bytes",
        "$",
        f"manifest is {size} bytes; maximum is {MAX_MANIFEST_BYTES}",
    )
    try:
        raw = manifest_path.read_bytes()
    except OSError as exc:
        _fail("io.read", "$", str(exc))
    try:
        text = raw.decode("utf-8", errors="strict")
    except UnicodeDecodeError as exc:
        _fail("json.utf8", "$", str(exc))
    return _require_object(loads_json_strict(text), "$")


def _validate_backend(value: Any) -> None:
    path = "$.backend"
    obj = _require_object(value, path)
    fields = {"backend_id", "version", "receipt_kind", "hash_profile", "composition_mode"}
    _check_fields(obj, fields, path)
    _require_exact(obj["backend_id"], "risc0_zkvm_3_0_5_succinct_poseidon2", path + ".backend_id")
    _require_exact(obj["version"], "3.0.5", path + ".version")
    _require_exact(obj["receipt_kind"], "succinct", path + ".receipt_kind")
    _require_exact(obj["hash_profile"], "poseidon2", path + ".hash_profile")
    _require_exact(
        obj["composition_mode"],
        "env_verify_assumption_resolve",
        path + ".composition_mode",
    )


def _validate_topology(value: Any) -> LadderPlan:
    path = "$.topology"
    obj = _require_object(value, path)
    fields = {
        "fanout",
        "depth",
        "full_tree",
        "leaf_count",
        "internal_node_count",
        "total_node_count",
        "edge_count",
        "level_node_counts",
        "aggregate_rounds",
        "program_image_count",
        "capacity_class",
    }
    _check_fields(obj, fields, path)
    plan = plan_ladder(obj["fanout"], obj["depth"])
    _require_exact(obj["full_tree"], True, path + ".full_tree")
    _require_exact(obj["leaf_count"], plan.leaf_count, path + ".leaf_count")
    _require_exact(obj["internal_node_count"], plan.internal_node_count, path + ".internal_node_count")
    _require_exact(obj["total_node_count"], plan.total_node_count, path + ".total_node_count")
    _require_exact(obj["edge_count"], plan.edge_count, path + ".edge_count")
    counts = _require_list(obj["level_node_counts"], path + ".level_node_counts")
    _require_exact(counts, list(plan.level_node_counts), path + ".level_node_counts")
    _require_exact(obj["aggregate_rounds"], plan.aggregate_rounds, path + ".aggregate_rounds")
    _require_exact(obj["program_image_count"], plan.program_image_count, path + ".program_image_count")
    _require_exact(obj["capacity_class"], plan.capacity_class, path + ".capacity_class")
    return plan


def _validate_gate(value: Any, plan: LadderPlan) -> None:
    path = "$.validation_gate"
    obj = _require_object(value, path)
    fields = {"gate_id", "evidence_status", "authority", "required_negative_tests"}
    _check_fields(obj, fields, path)
    expected_gate_id = f"zrpf_finite_ladder_f{plan.fanout}_d{plan.depth}_v1"
    _require_exact(obj["gate_id"], expected_gate_id, path + ".gate_id")
    _require_exact(obj["evidence_status"], "specified_not_executed", path + ".evidence_status")
    _require_exact(obj["authority"], False, path + ".authority")
    tests = _require_list(obj["required_negative_tests"], path + ".required_negative_tests")
    _require_exact(tests, list(NEGATIVE_TESTS), path + ".required_negative_tests")


def _validate_image(value: Any, path: str) -> tuple[str, str, str, str]:
    obj = _require_object(value, path)
    fields = {"risc0_image_id_hex", "elf_sha256_hex", "source_sha256_hex", "provenance_status"}
    _check_fields(obj, fields, path)
    image_id = _require_digest(obj["risc0_image_id_hex"], path + ".risc0_image_id_hex")
    elf_digest = _require_digest(obj["elf_sha256_hex"], path + ".elf_sha256_hex")
    source_digest = _require_digest(obj["source_sha256_hex"], path + ".source_sha256_hex")
    provenance_status = _require_string(obj["provenance_status"], path + ".provenance_status")
    _require(
        provenance_status in {"synthetic_example_only", "recorded_unverified"},
        "value.provenance_status",
        path + ".provenance_status",
        "expected 'synthetic_example_only' or 'recorded_unverified'",
    )
    return image_id, elf_digest, source_digest, provenance_status


def _validate_child_binding(value: Any, path: str, plan: LadderPlan, level: int, child_image_id: str) -> None:
    obj = _require_object(value, path)
    fields = {"child_level", "child_image_id_hex", "child_count_exact", "ordered"}
    _check_fields(obj, fields, path)
    _require_exact(obj["child_level"], level - 1, path + ".child_level")
    _require_exact(obj["child_image_id_hex"], child_image_id, path + ".child_image_id_hex")
    _require_exact(obj["child_count_exact"], plan.fanout, path + ".child_count_exact")
    _require_exact(obj["ordered"], True, path + ".ordered")


def _validate_levels(value: Any, plan: LadderPlan) -> set[str]:
    path = "$.levels"
    levels = _require_list(value, path)
    _require_exact(len(levels), plan.program_image_count, path + ".length")

    seen_program_ids: set[str] = set()
    seen_image_ids: set[str] = set()
    seen_elf_digests: set[str] = set()
    seen_source_digests: set[str] = set()
    provenance_statuses: set[str] = set()
    prior_image_id: str | None = None

    fields = {"level", "role", "program_id", "node_count", "fanout", "image", "child_binding"}
    for expected_level, raw in enumerate(levels):
        level_path = f"{path}[{expected_level}]"
        obj = _require_object(raw, level_path)
        _check_fields(obj, fields, level_path)
        _require_exact(obj["level"], expected_level, level_path + ".level")
        _require_exact(obj["node_count"], plan.level_node_counts[expected_level], level_path + ".node_count")
        program_id = _require_identifier(obj["program_id"], level_path + ".program_id")
        _require(
            program_id not in seen_program_ids,
            "ladder.duplicate_program_id",
            level_path + ".program_id",
            "every level requires a distinct program ID",
        )
        seen_program_ids.add(program_id)

        image_id, elf_digest, source_digest, provenance_status = _validate_image(
            obj["image"], level_path + ".image"
        )
        for value_, seen, code, field_name in (
            (image_id, seen_image_ids, "ladder.duplicate_image_id", "risc0_image_id_hex"),
            (elf_digest, seen_elf_digests, "ladder.duplicate_elf_digest", "elf_sha256_hex"),
            (source_digest, seen_source_digests, "ladder.duplicate_source_digest", "source_sha256_hex"),
        ):
            _require(value_ not in seen, code, level_path + ".image." + field_name, "value must be level-specific")
            seen.add(value_)
        provenance_statuses.add(provenance_status)

        if expected_level == 0:
            _require_exact(obj["role"], "leaf_adapter", level_path + ".role")
            _require_exact(obj["fanout"], 0, level_path + ".fanout")
            _require_exact(obj["child_binding"], None, level_path + ".child_binding")
        else:
            _require_exact(obj["role"], "aggregate", level_path + ".role")
            _require_exact(obj["fanout"], plan.fanout, level_path + ".fanout")
            _require(prior_image_id is not None, "ladder.internal", level_path, "missing prior image")
            _validate_child_binding(
                obj["child_binding"],
                level_path + ".child_binding",
                plan,
                expected_level,
                prior_image_id,
            )
        prior_image_id = image_id

    _require_exact(levels[-1]["node_count"], 1, path + "[-1].node_count")
    return provenance_statuses


def _validate_assurance(value: Any, provenance_statuses: set[str]) -> None:
    path = "$.assurance"
    obj = _require_object(value, path)
    fields = {
        "soundness_budget_status",
        "backend_capability_status",
        "build_provenance_status",
        "admission_eligible",
        "required_before_any_authority",
    }
    _check_fields(obj, fields, path)
    _require_exact(obj["soundness_budget_status"], "not_computed", path + ".soundness_budget_status")
    _require_exact(obj["backend_capability_status"], "not_attested", path + ".backend_capability_status")
    expected_provenance = (
        "synthetic_example_only"
        if provenance_statuses == {"synthetic_example_only"}
        else "recorded_unverified"
    )
    _require_exact(obj["build_provenance_status"], expected_provenance, path + ".build_provenance_status")
    _require_exact(obj["admission_eligible"], False, path + ".admission_eligible")
    obligations = _require_list(obj["required_before_any_authority"], path + ".required_before_any_authority")
    _require_exact(obligations, list(REQUIRED_BEFORE_ANY_AUTHORITY), path + ".required_before_any_authority")


def validate_manifest(manifest: Mapping[str, Any]) -> LadderPlan:
    """Validate one manifest and return its derived non-authority plan."""

    obj = _require_object(manifest, "$")
    fields = {
        "schema",
        "manifest_id",
        "artifact_class",
        "status",
        "authority",
        "backend",
        "topology",
        "validation_gate",
        "levels",
        "assurance",
        "non_claims",
    }
    _check_fields(obj, fields, "$")
    _require_exact(obj["schema"], MANIFEST_SCHEMA, "$.schema")
    _require_identifier(obj["manifest_id"], "$.manifest_id")
    _require_exact(obj["artifact_class"], ARTIFACT_CLASS, "$.artifact_class")
    _require_exact(obj["status"], "specified_not_executed", "$.status")
    _require_bool(obj["authority"], "$.authority")
    _require_exact(obj["authority"], False, "$.authority")

    _validate_backend(obj["backend"])
    plan = _validate_topology(obj["topology"])
    _validate_gate(obj["validation_gate"], plan)
    provenance_statuses = _validate_levels(obj["levels"], plan)
    _validate_assurance(obj["assurance"], provenance_statuses)
    non_claims = _require_list(obj["non_claims"], "$.non_claims")
    _require_exact(non_claims, list(REQUIRED_NON_CLAIMS), "$.non_claims")
    return plan


def validation_receipt(manifest: Mapping[str, Any], plan: LadderPlan) -> dict[str, Any]:
    return {
        "schema": VALIDATION_SCHEMA,
        "status": "VALID_NON_AUTHORITY",
        "authority": False,
        "manifest_id": manifest["manifest_id"],
        "capacity_class": plan.capacity_class,
        "fanout": plan.fanout,
        "depth": plan.depth,
        "leaf_count": plan.leaf_count,
        "total_node_count": plan.total_node_count,
        "evidence_status": "specified_not_executed",
        "non_claim": "Internal manifest consistency is not cryptographic or production evidence.",
    }


def _emit_json(value: Mapping[str, Any], *, pretty: bool, stream: Any) -> None:
    indent = 2 if pretty else None
    text = json.dumps(value, sort_keys=True, indent=indent, separators=None if pretty else (",", ":"))
    stream.write(text + "\n")


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    plan_parser = subparsers.add_parser("plan", help="print exact non-authority capacity arithmetic")
    plan_parser.add_argument("--fanout", type=int, required=True)
    plan_parser.add_argument("--depth", type=int, required=True)
    plan_parser.add_argument("--pretty", action="store_true")

    validate_parser = subparsers.add_parser("validate", help="validate a strict v1 research manifest")
    validate_parser.add_argument("manifest")
    validate_parser.add_argument("--pretty", action="store_true")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    parser = _build_parser()
    args = parser.parse_args(argv)
    try:
        if args.command == "plan":
            _emit_json(plan_ladder(args.fanout, args.depth).to_dict(), pretty=args.pretty, stream=sys.stdout)
            return 0
        manifest = load_manifest(args.manifest)
        plan = validate_manifest(manifest)
        _emit_json(validation_receipt(manifest, plan), pretty=args.pretty, stream=sys.stdout)
        return 0
    except LadderValidationError as exc:
        _emit_json(
            {
                "schema": VALIDATION_SCHEMA,
                "status": "INVALID",
                "authority": False,
                "error": exc.to_dict(),
            },
            pretty=getattr(args, "pretty", False),
            stream=sys.stderr,
        )
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
