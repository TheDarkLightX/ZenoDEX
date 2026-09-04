#!/usr/bin/env python3
"""Fail-closed integrity and regeneration gate for the research packet."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

from reference_semantics import build_report
from run_mutation_checks import run_mutations
from run_tau_contract import EXPECTED as TAU_EXPECTED

EXPERIMENT = Path(__file__).resolve().parent
REPO = EXPERIMENT.parents[1]
GENERATED = EXPERIMENT / "generated"
EXPECTED_PATHS = {
    "docs/research/NAMED_CHOICE_FIBER_POLYNOMIAL_V1.md",
    "experiments/named_choice_fiber_polynomial_v1/README.md",
    "experiments/named_choice_fiber_polynomial_v1/benchmark_tau_affine.py",
    "experiments/named_choice_fiber_polynomial_v1/check_packet.py",
    "experiments/named_choice_fiber_polynomial_v1/choice_fiber_polynomial_v1.py",
    "experiments/named_choice_fiber_polynomial_v1/generated/benchmark_observation.json",
    "experiments/named_choice_fiber_polynomial_v1/generated/mutation_receipt.json",
    "experiments/named_choice_fiber_polynomial_v1/generated/reference_report.json",
    "experiments/named_choice_fiber_polynomial_v1/generated/tau_receipt.json",
    "experiments/named_choice_fiber_polynomial_v1/named_choice_fiber_polynomial_v1.tau",
    "experiments/named_choice_fiber_polynomial_v1/reference_semantics.py",
    "experiments/named_choice_fiber_polynomial_v1/run_mutation_checks.py",
    "experiments/named_choice_fiber_polynomial_v1/run_tau_contract.py",
    "experiments/named_choice_fiber_polynomial_v1/tau_profile.json",
    "experiments/named_choice_fiber_polynomial_v1/test_choice_fiber_polynomial_v1.py",
}
FORBIDDEN_PUBLIC_TEXT = (
    "/" + "home" + "/",
    "/" + "tmp" + "/",
    "sandbox" + ":/",
)
EXPECTED_MANIFEST_METADATA = {
    "authority": "NONE",
    "base_commit": "b6842cd26aadf32b7ee774f58665570479cacfe6",
    "base_tree": "d166dc8dff0baa00c7eea9cd04935e468b1fde3d",
    "claim_status": "BOUNDED_RESEARCH_ONLY",
    "manifest_scope": (
        "closed authoritative packet inputs and retained evidence; excludes self "
        "and packet_receipt to avoid a hash cycle"
    ),
    "object": "named_choice_fiber_polynomial_v1",
    "schema": "zenodex.choice_fiber_source_manifest.v1",
}
EXPECTED_TAU_PROFILE = {
    "binary_sha256": "4be1965b15a4a6d074e8b4b93d7134e3edcd38ebce1109550d280e724ea6d6a7",
    "claim_status": "BOUNDED_RESEARCH_ONLY",
    "parser_commit": "9e789493fabffaeadf9e4f1acaab88b4a3c52533",
    "source_commit": "1c1e58aea7ddec04e48ce11cb0e6ed0cbe2a0d43",
    "version": "Tau Language Framework version 0.7.0-alpha (1c1e58ae)",
}
MANIFEST_FIELDS = {
    "authority",
    "base_commit",
    "base_tree",
    "claim_status",
    "entries",
    "manifest_scope",
    "object",
    "schema",
}
REFERENCE_FIELDS = {
    "authority",
    "claim_status",
    "invariants",
    "nonclaims",
    "object",
    "oracle",
    "results",
    "schema",
    "strongest_claim",
}
MUTATION_FIELDS = {
    "authority",
    "claim_status",
    "killed",
    "mutants",
    "object",
    "schema",
    "survived",
}
TAU_FIELDS = {
    "actual",
    "authority",
    "claim_status",
    "expected",
    "object",
    "query_count",
    "schema",
    "spec_sha256",
    "tau_binary_sha256",
    "tau_source_commit",
    "tau_version",
}
BENCHMARK_FIELDS = {"authority", "claim_status", "nonclaims", "rows", "schema"}
PACKET_FIELDS = {
    "authority",
    "claim_status",
    "components",
    "object",
    "packet_root",
    "schema",
}
PACKET_COMPONENT_FIELDS = {
    "benchmark_observation_sha256",
    "mutation_receipt_sha256",
    "reference_report_sha256",
    "source_manifest_sha256",
    "tau_receipt_sha256",
}
PROFILE_FIELDS = {
    "binary_sha256",
    "claim_status",
    "parser_commit",
    "source_commit",
    "version",
}


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _load(path: Path) -> object:
    return json.loads(path.read_text(encoding="utf-8"))


def _canonical(value: object) -> bytes:
    return json.dumps(value, separators=(",", ":"), sort_keys=True).encode()


def _assert_receipt_ceiling(value: object, name: str) -> dict[str, object]:
    if not isinstance(value, dict):
        raise SystemExit(f"{name}:NOT_OBJECT")
    if value.get("authority") != "NONE":
        raise SystemExit(f"{name}:AUTHORITY_CEILING_VIOLATION")
    if value.get("claim_status") not in {
        "BOUNDED_RESEARCH_ONLY",
        "SINGLE_HOST_TIMING_OBSERVATION_ONLY",
    }:
        raise SystemExit(f"{name}:CLAIM_STATUS_VIOLATION")
    return value


def _assert_closed_fields(
    value: dict[str, object],
    expected: set[str],
    name: str,
) -> None:
    if set(value) != expected:
        raise SystemExit(f"{name}:FIELD_SET_MISMATCH")


def _assert_manifest_identity(manifest: dict[str, object]) -> None:
    _assert_closed_fields(manifest, MANIFEST_FIELDS, "MANIFEST")
    actual = {key: manifest.get(key) for key in EXPECTED_MANIFEST_METADATA}
    if actual != EXPECTED_MANIFEST_METADATA:
        raise SystemExit("MANIFEST_IDENTITY_MISMATCH")


def _assert_tau_receipt(
    tau: dict[str, object],
    profile: dict[str, object],
) -> None:
    _assert_closed_fields(tau, TAU_FIELDS, "TAU")
    _assert_closed_fields(profile, PROFILE_FIELDS, "TAU_PROFILE")
    if profile != EXPECTED_TAU_PROFILE:
        raise SystemExit("TAU_PROFILE_IDENTITY_MISMATCH")
    if tau.get("tau_source_commit") != profile.get("source_commit"):
        raise SystemExit("TAU_SOURCE_COMMIT_MISMATCH")
    if tau.get("tau_binary_sha256") != profile.get("binary_sha256"):
        raise SystemExit("TAU_BINARY_IDENTITY_MISMATCH")
    if tau.get("tau_version") != profile.get("version"):
        raise SystemExit("TAU_VERSION_MISMATCH")
    if tau.get("spec_sha256") != _sha256(EXPERIMENT / "named_choice_fiber_polynomial_v1.tau"):
        raise SystemExit("TAU_SPEC_IDENTITY_MISMATCH")
    if (
        tau.get("actual") != TAU_EXPECTED
        or tau.get("expected") != TAU_EXPECTED
        or tau.get("query_count") != len(TAU_EXPECTED)
    ):
        raise SystemExit("TAU_VERDICT_MISMATCH")
    if tau.get("object") != "named_choice_fiber_polynomial_v1":
        raise SystemExit("TAU_OBJECT_MISMATCH")
    if tau.get("schema") != "zenodex.tau_experiment_receipt.v1":
        raise SystemExit("TAU_SCHEMA_MISMATCH")


def main() -> int:
    manifest_path = GENERATED / "source_manifest.json"
    manifest = _load(manifest_path)
    if not isinstance(manifest, dict):
        raise SystemExit("MANIFEST_NOT_OBJECT")
    _assert_manifest_identity(manifest)
    entries = manifest.get("entries")
    if not isinstance(entries, list):
        raise SystemExit("MANIFEST_ENTRIES_NOT_LIST")
    paths = [entry.get("path") for entry in entries if isinstance(entry, dict)]
    if len(paths) != len(entries) or len(set(paths)) != len(paths):
        raise SystemExit("MANIFEST_PATH_CARDINALITY_ERROR")
    if set(paths) != EXPECTED_PATHS:
        raise SystemExit("MANIFEST_CLOSED_WORLD_MISMATCH")

    for entry in entries:
        if not isinstance(entry, dict) or set(entry) != {"bytes", "path", "sha256"}:
            raise SystemExit("MANIFEST_ENTRY_FIELD_SET_MISMATCH")
        path_text = entry["path"]
        path = Path(path_text)
        if path.is_absolute() or ".." in path.parts or path.as_posix() != path_text:
            raise SystemExit(f"UNSAFE_MANIFEST_PATH:{path_text}")
        resolved = (REPO / path).resolve()
        if REPO.resolve() not in resolved.parents:
            raise SystemExit(f"MANIFEST_PATH_ESCAPE:{path_text}")
        if not resolved.is_file():
            raise SystemExit(f"MANIFEST_FILE_MISSING:{path_text}")
        if entry.get("bytes") != resolved.stat().st_size:
            raise SystemExit(f"MANIFEST_SIZE_MISMATCH:{path_text}")
        if entry.get("sha256") != _sha256(resolved):
            raise SystemExit(f"MANIFEST_SHA256_MISMATCH:{path_text}")
        if resolved.suffix in {".md", ".py", ".tau", ".json"}:
            text = resolved.read_text(encoding="utf-8")
            if any(marker in text for marker in FORBIDDEN_PUBLIC_TEXT):
                raise SystemExit(f"MACHINE_LOCAL_PATH:{path_text}")

    reference = _assert_receipt_ceiling(_load(GENERATED / "reference_report.json"), "REFERENCE")
    _assert_closed_fields(reference, REFERENCE_FIELDS, "REFERENCE")
    if reference != build_report():
        raise SystemExit("REFERENCE_REGENERATION_MISMATCH")

    mutation = _assert_receipt_ceiling(_load(GENERATED / "mutation_receipt.json"), "MUTATION")
    _assert_closed_fields(mutation, MUTATION_FIELDS, "MUTATION")
    expected_mutation = {
        "authority": "NONE",
        "claim_status": "BOUNDED_RESEARCH_ONLY",
        "killed": len(run_mutations()),
        "mutants": run_mutations(),
        "object": "named_choice_fiber_polynomial_v1",
        "schema": "zenodex.choice_fiber_mutation_receipt.v1",
        "survived": 0,
    }
    if mutation != expected_mutation:
        raise SystemExit("MUTATION_REGENERATION_MISMATCH")

    tau = _assert_receipt_ceiling(_load(GENERATED / "tau_receipt.json"), "TAU")
    profile = _load(EXPERIMENT / "tau_profile.json")
    if not isinstance(profile, dict):
        raise SystemExit("TAU_PROFILE_NOT_OBJECT")
    _assert_tau_receipt(tau, profile)

    benchmark = _assert_receipt_ceiling(
        _load(GENERATED / "benchmark_observation.json"), "BENCHMARK"
    )
    _assert_closed_fields(benchmark, BENCHMARK_FIELDS, "BENCHMARK")

    packet = _assert_receipt_ceiling(_load(GENERATED / "packet_receipt.json"), "PACKET")
    _assert_closed_fields(packet, PACKET_FIELDS, "PACKET")
    components = {
        "benchmark_observation_sha256": _sha256(GENERATED / "benchmark_observation.json"),
        "mutation_receipt_sha256": _sha256(GENERATED / "mutation_receipt.json"),
        "reference_report_sha256": _sha256(GENERATED / "reference_report.json"),
        "source_manifest_sha256": _sha256(manifest_path),
        "tau_receipt_sha256": _sha256(GENERATED / "tau_receipt.json"),
    }
    expected_packet_root = hashlib.sha256(
        b"zenodex.choice-fiber.packet.v1\x00" + _canonical(components)
    ).hexdigest()
    if packet.get("components") != components:
        raise SystemExit("PACKET_COMPONENT_MISMATCH")
    if set(components) != PACKET_COMPONENT_FIELDS:
        raise SystemExit("PACKET_COMPONENT_FIELD_SET_MISMATCH")
    if packet.get("packet_root") != expected_packet_root:
        raise SystemExit("PACKET_ROOT_MISMATCH")
    if packet.get("object") != "named_choice_fiber_polynomial_v1":
        raise SystemExit("PACKET_OBJECT_MISMATCH")
    if packet.get("schema") != "zenodex.choice_fiber_packet_receipt.v1":
        raise SystemExit("PACKET_SCHEMA_MISMATCH")

    print(
        json.dumps(
            {
                "authority": "NONE",
                "claim_status": "BOUNDED_RESEARCH_ONLY",
                "manifest_entries": len(entries),
                "mutants_killed": mutation["killed"],
                "packet_root": expected_packet_root,
                "status": "PASS",
                "tau_queries": tau["query_count"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
