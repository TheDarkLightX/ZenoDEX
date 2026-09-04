#!/usr/bin/env python3
"""Fail-closed integrity and regeneration gate for the research packet."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

from reference_semantics import build_report
from run_mutation_checks import run_mutations

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


def main() -> int:
    manifest_path = GENERATED / "source_manifest.json"
    manifest = _load(manifest_path)
    if not isinstance(manifest, dict):
        raise SystemExit("MANIFEST_NOT_OBJECT")
    if manifest.get("authority") != "NONE":
        raise SystemExit("MANIFEST_AUTHORITY_CEILING_VIOLATION")
    entries = manifest.get("entries")
    if not isinstance(entries, list):
        raise SystemExit("MANIFEST_ENTRIES_NOT_LIST")
    paths = [entry.get("path") for entry in entries if isinstance(entry, dict)]
    if len(paths) != len(entries) or len(set(paths)) != len(paths):
        raise SystemExit("MANIFEST_PATH_CARDINALITY_ERROR")
    if set(paths) != EXPECTED_PATHS:
        raise SystemExit("MANIFEST_CLOSED_WORLD_MISMATCH")

    for entry in entries:
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
    if reference != build_report():
        raise SystemExit("REFERENCE_REGENERATION_MISMATCH")

    mutation = _assert_receipt_ceiling(_load(GENERATED / "mutation_receipt.json"), "MUTATION")
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
    if tau.get("tau_source_commit") != profile.get("source_commit"):
        raise SystemExit("TAU_SOURCE_COMMIT_MISMATCH")
    if tau.get("tau_binary_sha256") != profile.get("binary_sha256"):
        raise SystemExit("TAU_BINARY_IDENTITY_MISMATCH")
    if tau.get("spec_sha256") != _sha256(EXPERIMENT / "named_choice_fiber_polynomial_v1.tau"):
        raise SystemExit("TAU_SPEC_IDENTITY_MISMATCH")
    if tau.get("actual") != tau.get("expected") or tau.get("query_count") != 15:
        raise SystemExit("TAU_VERDICT_MISMATCH")

    _assert_receipt_ceiling(_load(GENERATED / "benchmark_observation.json"), "BENCHMARK")

    packet = _assert_receipt_ceiling(_load(GENERATED / "packet_receipt.json"), "PACKET")
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
    if packet.get("packet_root") != expected_packet_root:
        raise SystemExit("PACKET_ROOT_MISMATCH")

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
