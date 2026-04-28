#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Mapping, Sequence

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.check_formal_proof_hygiene import CRITICAL_FORMAL_PROOF_ARTIFACTS
from tools.stateful_scenario_bridge import CLOSED_DISASTER_SEARCH_AXIS_IDS

DISASTER_PROOF_SCHEMA_MAP_SCHEMA = "zenodex/disaster-proof-schema-map/v1"

PROOF_SCHEMA_FILES: dict[str, str] = {
    "amm_integer_runtime_bridge": "lean-mathlib/Proofs/AMMIntegerRuntimeBridge.lean",
    "certificate_gluing": "lean-mathlib/Proofs/CertificateGluing.lean",
    "disaster_antichain_basis": "lean-mathlib/Proofs/DisasterAntichainBasis.lean",
    "disaster_trace_lifting": "lean-mathlib/Proofs/DisasterTraceDiscoveryChallenge.lean",
    "forbidden_trace_minor": "lean-mathlib/Proofs/ForbiddenTraceMinor.lean",
    "no_free_resource_trace_ledger": "lean-mathlib/Proofs/NoFreeResourceTraceLedger.lean",
    "zenodex_disaster_schema_instantiations": (
        "lean-mathlib/Proofs/ZenoDEXDisasterSchemaInstantiations.lean"
    ),
}

PROOF_SUPPORT_FILES: dict[str, str] = {
    "zenodex_closed_axis_proof_schema_map": (
        "lean-mathlib/Proofs/ZenoDEXClosedAxisProofSchemaMap.lean"
    ),
}

# This is a schema-alignment map, not a claim that every axis is fully proved.
# Each closed axis must name the reusable proof shapes that would discharge or
# strengthen its replay receipt once instantiated against concrete trace/state
# predicates.
CLOSED_AXIS_PROOF_SCHEMA_MAP: dict[str, tuple[str, ...]] = {
    "epoch_split_brain": (
        "disaster_trace_lifting",
        "certificate_gluing",
        "forbidden_trace_minor",
    ),
    "identity_registry_drift": (
        "disaster_trace_lifting",
        "certificate_gluing",
    ),
    "canonicalization_equivocation": (
        "certificate_gluing",
        "disaster_antichain_basis",
    ),
    "serialization_width_aliasing": (
        "forbidden_trace_minor",
        "disaster_antichain_basis",
    ),
    "resource_budget_abort": (
        "no_free_resource_trace_ledger",
        "zenodex_disaster_schema_instantiations",
    ),
    "repair_after_tamper": (
        "forbidden_trace_minor",
        "certificate_gluing",
    ),
    "external_state_drift": (
        "disaster_trace_lifting",
        "certificate_gluing",
    ),
    "atomicity_partial_side_effect": (
        "no_free_resource_trace_ledger",
        "certificate_gluing",
    ),
    "restart_replay_persistence": (
        "disaster_trace_lifting",
        "forbidden_trace_minor",
    ),
    "dependency_outage_fail_closed": (
        "forbidden_trace_minor",
        "disaster_trace_lifting",
    ),
    "reciprocal_netting_pair_forgery": (
        "forbidden_trace_minor",
        "zenodex_disaster_schema_instantiations",
    ),
    "bounded_advisory_search_envelope": (
        "no_free_resource_trace_ledger",
        "zenodex_disaster_schema_instantiations",
    ),
    "exact_out_candidate_domain_explosion": (
        "no_free_resource_trace_ledger",
        "disaster_antichain_basis",
    ),
    "tau_gate_policy_aliasing": (
        "forbidden_trace_minor",
        "disaster_antichain_basis",
    ),
    "confidential_receipt_attestation_drift": (
        "certificate_gluing",
        "disaster_trace_lifting",
    ),
    "batch_clearing_fragmentation_ordering": (
        "disaster_antichain_basis",
        "certificate_gluing",
    ),
    "perp_funding_liquidation_oracle_window": (
        "forbidden_trace_minor",
        "zenodex_disaster_schema_instantiations",
    ),
    "proof_mining_packet_envelope_replay": (
        "no_free_resource_trace_ledger",
        "zenodex_disaster_schema_instantiations",
        "certificate_gluing",
    ),
    "tau_net_client_transport_boundary": (
        "forbidden_trace_minor",
        "disaster_trace_lifting",
    ),
    "settlement_proof_recompute_gate": (
        "certificate_gluing",
        "disaster_trace_lifting",
    ),
    "operations_parser_canonical_envelope": (
        "forbidden_trace_minor",
        "disaster_antichain_basis",
    ),
    "dex_engine_sequence_anomaly_surface": (
        "disaster_trace_lifting",
        "forbidden_trace_minor",
    ),
    "dex_core_ref_parity_drift": (
        "amm_integer_runtime_bridge",
        "disaster_trace_lifting",
    ),
    "boundary_concolic_wrapper_consistency": (
        "forbidden_trace_minor",
        "disaster_antichain_basis",
    ),
    "exact_out_prefilter_winner_repair_boundary": (
        "disaster_antichain_basis",
        "certificate_gluing",
    ),
    "perp_engine_integration_oracle_bootstrap_boundary": (
        "forbidden_trace_minor",
        "zenodex_disaster_schema_instantiations",
    ),
    "quote_receipt_transport_intent_boundary": (
        "certificate_gluing",
        "forbidden_trace_minor",
    ),
    "tau_runner_subprocess_transport_boundary": (
        "forbidden_trace_minor",
        "no_free_resource_trace_ledger",
    ),
    "dex_settlement_recovery_proof_unit_boundary": (
        "certificate_gluing",
        "disaster_trace_lifting",
    ),
}


def _resolve(path: str) -> Path:
    return REPO_ROOT / path


def build_disaster_proof_schema_map_report(
    *,
    axis_map: Mapping[str, Sequence[str]] = CLOSED_AXIS_PROOF_SCHEMA_MAP,
    expected_axis_ids: Sequence[str] = CLOSED_DISASTER_SEARCH_AXIS_IDS,
    schema_files: Mapping[str, str] = PROOF_SCHEMA_FILES,
    support_files: Mapping[str, str] = PROOF_SUPPORT_FILES,
) -> dict[str, Any]:
    errors: list[str] = []
    warnings: list[str] = []
    expected = tuple(str(axis_id) for axis_id in expected_axis_ids)
    expected_set = set(expected)
    actual_set = set(axis_map)

    missing_axes = sorted(expected_set - actual_set)
    unexpected_axes = sorted(actual_set - expected_set)
    if missing_axes:
        errors.append(f"missing proof-schema map axis id(s): {', '.join(missing_axes)}")
    if unexpected_axes:
        errors.append(f"unexpected proof-schema map axis id(s): {', '.join(unexpected_axes)}")

    hygiene_set = set(CRITICAL_FORMAL_PROOF_ARTIFACTS)
    rows: list[dict[str, Any]] = []
    schema_usage: dict[str, int] = {name: 0 for name in schema_files}
    for axis_id in expected:
        schemas = tuple(str(name) for name in axis_map.get(axis_id, ()))
        if not schemas:
            errors.append(f"{axis_id}: must declare at least one proof schema")
        unknown = sorted(set(schemas) - set(schema_files))
        if unknown:
            errors.append(f"{axis_id}: unknown proof schema(s): {', '.join(unknown)}")
        for schema in schemas:
            if schema in schema_usage:
                schema_usage[schema] += 1
        rows.append(
            {
                "axis_id": axis_id,
                "proof_schemas": list(schemas),
                "proof_files": [schema_files[name] for name in schemas if name in schema_files],
            }
        )

    for schema_name, proof_file in sorted(schema_files.items()):
        path = _resolve(proof_file)
        if not path.is_file():
            errors.append(f"{schema_name}: proof file missing: {proof_file}")
        if proof_file not in hygiene_set:
            errors.append(f"{schema_name}: proof file is not in formal hygiene ratchet: {proof_file}")
        if schema_usage.get(schema_name, 0) == 0:
            warnings.append(f"{schema_name}: schema is tracked but unused by closed axes")

    for support_name, proof_file in sorted(support_files.items()):
        path = _resolve(proof_file)
        if not path.is_file():
            errors.append(f"{support_name}: support proof file missing: {proof_file}")
        if proof_file not in hygiene_set:
            errors.append(f"{support_name}: support proof file is not in formal hygiene ratchet: {proof_file}")

    return {
        "schema": DISASTER_PROOF_SCHEMA_MAP_SCHEMA,
        "ok": not errors,
        "errors": errors,
        "warnings": warnings,
        "axis_count": len(expected),
        "schema_count": len(schema_files),
        "support_proof_file_count": len(support_files),
        "schema_usage": dict(sorted(schema_usage.items())),
        "support_proof_files": dict(sorted(support_files.items())),
        "axes": rows,
    }


def _print_text(payload: dict[str, Any]) -> None:
    print("Disaster Proof Schema Map")
    print(f"ok: {'yes' if payload['ok'] else 'no'}")
    print(f"axis_count: {payload['axis_count']}")
    print(f"schema_count: {payload['schema_count']}")
    print(f"support_proof_file_count: {payload['support_proof_file_count']}")
    print("schema_usage:")
    for name, count in payload["schema_usage"].items():
        print(f"- {name}: {count}")
    if payload.get("errors"):
        print("errors:")
        for error in payload["errors"]:
            print(f"- {error}")
    if payload.get("warnings"):
        print("warnings:")
        for warning in payload["warnings"]:
            print(f"- {warning}")


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Check closed disaster axes against proof-schema adapters.")
    parser.add_argument("--output", help="Optional path to write the report JSON")
    parser.add_argument("--format", choices=("text", "json"), default="text")
    args = parser.parse_args(argv)

    payload = build_disaster_proof_schema_map_report()
    if args.output:
        out = Path(args.output)
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    if args.format == "json":
        json.dump(payload, sys.stdout, indent=2, sort_keys=True)
        sys.stdout.write("\n")
    else:
        _print_text(payload)
    return 0 if payload["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
