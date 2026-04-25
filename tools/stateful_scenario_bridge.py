from __future__ import annotations

"""Bridge LLM scenario candidates into bounded stateful fuzz evidence.

This module is deliberately tooling-only. It does not authorize settlement and
it never upgrades bounded fuzz/concolic output above tested_discovery evidence.
"""

import json
import subprocess
import sys
import time
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.stateful_feedback import DangerousSurface, load_dangerous_surface_manifest


SCENARIO_CANDIDATE_SCHEMA = "zenodex/stateful-scenario-candidate/v1"
SCENARIO_CANDIDATE_CHECK_SCHEMA = "zenodex/stateful-scenario-candidate-check/v1"
SHAPEFORGE_BRIDGE_SCHEMA = "zenodex/stateful-shapeforge-promotion-bridge/v1"
DISASTER_REACHABILITY_RATCHET_SCHEMA = "zenodex/stateful-disaster-reachability-ratchet/v1"
SCENARIO_RUN_RECEIPT_SCHEMA = "zenodex/stateful-scenario-run-receipt/v1"
PROOF_OBLIGATION_PACKET_SCHEMA = "zenodex/stateful-disaster-proof-obligation-packet/v1"
PROOF_OBLIGATION_CLOSURE_RECEIPT_SCHEMA = "zenodex/stateful-disaster-proof-obligation-closure-receipt/v1"
MINIMAL_WITNESS_LANGUAGE_AUDIT_SCHEMA = "zenodex/stateful-minimal-witness-language-audit/v1"
CROSS_SURFACE_WITNESS_EXPLORATION_SCHEMA = "zenodex/stateful-cross-surface-witness-exploration/v1"

DEFAULT_TARGET_MANIFEST = REPO_ROOT / "tools" / "acceptance_tcb_dangerous_surfaces.json"
DEFAULT_WORLD_MODEL = REPO_ROOT / "docs" / "zenodex" / "shapeforge_promoted" / "zenodex_world_model.seed.json"
DEFAULT_SHAPE_RATCHET = REPO_ROOT / "tools" / "check_shape_v1_ratchet.py"

EVIDENCE_ORDER = {
    "hypothesis": 0,
    "tested_discovery": 1,
    "implemented": 2,
    "contract": 3,
    "proved": 4,
}
MAX_SCENARIO_EVIDENCE = "tested_discovery"
SEVERITY_ORDER = {
    "unknown": -1,
    "low": 0,
    "medium": 1,
    "high": 2,
    "critical": 3,
}

FORMAL_LANE_KINDS = {"esso", "tau", "lean", "tla"}

SURFACE_FORMAL_LANES: dict[str, dict[str, Any]] = {
    "quote_receipt_certificate_boundary": {
        "obligation": "Route certificates remain bound to the quoted candidate set, quote body, winner index, and amount-out semantics.",
        "target_evidence_class": "contract_or_proved",
        "lanes": [
            {
                "kind": "esso",
                "name": "quote_receipt_certificate_gate_kernel",
                "artifacts": [
                    "src/kernels/dex/quote_receipt_certificate_gate_v1.yaml",
                    "tests/kernels/test_quote_receipt_certificate_gate_v1_native_adapter.py",
                ],
                "commands": [["pytest", "-q", "tests/kernels/test_quote_receipt_certificate_gate_v1_native_adapter.py"]],
            },
            {
                "kind": "lean",
                "name": "exact_in_route_certificate_binding",
                "artifacts": [
                    "lean-mathlib/Proofs/ZenoDEXExactInRouteCertificate.lean",
                    "tests/formal/test_lean_exact_in_route_certificate.py",
                ],
                "commands": [["pytest", "-q", "tests/formal/test_lean_exact_in_route_certificate.py"]],
            },
            {
                "kind": "fuzz_regression",
                "name": "route_certificate_sequence_witnesses",
                "artifacts": [
                    "tools/route_certificate_sequence_grammar_fuzz.py",
                    "tools/quote_receipt_cross_surface_sequence_grammar_fuzz.py",
                    "tests/integration/test_route_certificate_sequence_grammar_fuzz.py",
                    "tests/integration/test_quote_receipt_cross_surface_sequence_grammar_fuzz.py",
                ],
                "commands": [
                    ["pytest", "-q", "tests/integration/test_route_certificate_sequence_grammar_fuzz.py"],
                    ["pytest", "-q", "tests/integration/test_quote_receipt_cross_surface_sequence_grammar_fuzz.py"],
                ],
            },
        ],
    },
    "route_canonicalization_boundary": {
        "obligation": "Canonical route winner selection is stable under replay and candidate-set perturbation because the winner is the minimum under the declared total key.",
        "target_evidence_class": "proved",
        "lanes": [
            {
                "kind": "lean",
                "name": "route_rank_projection_and_certificate",
                "artifacts": [
                    "lean-mathlib/Proofs/ZenoDEXExactInRouteRankProjection.lean",
                    "lean-mathlib/Proofs/ZenoDEXExactInRouteCertificate.lean",
                    "tests/formal/test_lean_exact_in_route_rank_projection.py",
                    "tests/formal/test_lean_exact_in_route_certificate.py",
                ],
                "commands": [
                    ["pytest", "-q", "tests/formal/test_lean_exact_in_route_rank_projection.py"],
                    ["pytest", "-q", "tests/formal/test_lean_exact_in_route_certificate.py"],
                ],
            },
            {
                "kind": "esso",
                "name": "exact_in_route_rank_projection_packet",
                "artifacts": [
                    "src/kernels/dex/exact_in_route_rank_projection_packet_v1.yaml",
                    "tests/formal/test_esso_exact_in_route_rank_projection_packet.py",
                ],
                "commands": [["pytest", "-q", "tests/formal/test_esso_exact_in_route_rank_projection_packet.py"]],
            },
            {
                "kind": "fuzz_regression",
                "name": "route_canonicalization_sequence_witnesses",
                "artifacts": [
                    "tools/quote_receipt_route_canonicalization_sequence_grammar_fuzz.py",
                    "tests/integration/test_quote_receipt_route_canonicalization_sequence_grammar_fuzz.py",
                ],
                "commands": [["pytest", "-q", "tests/integration/test_quote_receipt_route_canonicalization_sequence_grammar_fuzz.py"]],
            },
        ],
    },
    "settlement_attestation_policy_boundary": {
        "obligation": "Settlement attestations fail closed on stale epochs, source allowlist drift, packet-hash mismatch, future timestamps, and signature tampering.",
        "target_evidence_class": "contract_or_proved",
        "lanes": [
            {
                "kind": "esso",
                "name": "settlement_spot_price_attestation_kernel",
                "artifacts": [
                    "src/kernels/dex/settlement_spot_price_attestation_v1.yaml",
                    "tests/formal/test_esso_settlement_spot_price_attestation.py",
                ],
                "commands": [["pytest", "-q", "tests/formal/test_esso_settlement_spot_price_attestation.py"]],
            },
            {
                "kind": "lean",
                "name": "settlement_price_history_certificate",
                "artifacts": [
                    "lean-mathlib/Proofs/ZenoDEXSettlementPriceHistoryCertificate.lean",
                    "tests/formal/test_lean_settlement_price_history_certificate.py",
                ],
                "commands": [["pytest", "-q", "tests/formal/test_lean_settlement_price_history_certificate.py"]],
            },
            {
                "kind": "fuzz_regression",
                "name": "settlement_attestation_sequence_witnesses",
                "artifacts": [
                    "tools/settlement_attestation_sequence_grammar_fuzz.py",
                    "tests/integration/test_settlement_attestation_sequence_grammar_fuzz.py",
                ],
                "commands": [["pytest", "-q", "tests/integration/test_settlement_attestation_sequence_grammar_fuzz.py"]],
            },
        ],
    },
    "stale_quote_receipt_boundary": {
        "obligation": "Quote receipts fail closed once a referenced pool snapshot drifts and cannot be repaired into a valid stale execution envelope.",
        "target_evidence_class": "contract_or_proved",
        "lanes": [
            {
                "kind": "esso",
                "name": "quote_receipt_pool_snapshot_gate",
                "artifacts": [
                    "src/kernels/dex/quote_receipt_pool_snapshot_gate_v1.yaml",
                    "tests/kernels/test_quote_receipt_pool_snapshot_gate_v1_native_adapter.py",
                ],
                "commands": [["pytest", "-q", "tests/kernels/test_quote_receipt_pool_snapshot_gate_v1_native_adapter.py"]],
            },
            {
                "kind": "tau",
                "name": "settlement_certificate_replay_compact_bundle",
                "artifacts": [
                    "src/tau_specs/recommended/settlement_v5_aligned_compact_bundle.tau",
                    "tests/tau/test_settlement_certificate_replay_compact_bundle.py",
                ],
                "commands": [["pytest", "-q", "tests/tau/test_settlement_certificate_replay_compact_bundle.py"]],
            },
            {
                "kind": "fuzz_regression",
                "name": "quote_receipt_staleness_sequences",
                "artifacts": [
                    "tools/quote_receipt_cross_surface_sequence_grammar_fuzz.py",
                    "tests/integration/test_quote_receipt_cross_surface_sequence_grammar_fuzz.py",
                    "tests/integration/test_dex_engine_quote_receipt_sequence_grammar_fuzz.py",
                ],
                "commands": [
                    ["pytest", "-q", "tests/integration/test_quote_receipt_cross_surface_sequence_grammar_fuzz.py"],
                    ["pytest", "-q", "tests/integration/test_dex_engine_quote_receipt_sequence_grammar_fuzz.py"],
                ],
            },
        ],
    },
    "stale_settlement_boundary": {
        "obligation": "Provided settlements fail closed after the execution surface changes and any applied settlement remains bound to current replayable witnesses.",
        "target_evidence_class": "contract_or_proved",
        "lanes": [
            {
                "kind": "esso",
                "name": "settlement_end_to_end_certificate_packet",
                "artifacts": [
                    "src/kernels/dex/settlement_end_to_end_certificate_packet_v1.yaml",
                    "tests/formal/test_esso_settlement_end_to_end_certificate_packet.py",
                ],
                "commands": [["pytest", "-q", "tests/formal/test_esso_settlement_end_to_end_certificate_packet.py"]],
            },
            {
                "kind": "lean",
                "name": "settlement_end_to_end_certificate_packet",
                "artifacts": [
                    "lean-mathlib/Proofs/ZenoDEXSettlementEndToEndCertificatePacket.lean",
                    "tests/formal/test_lean_settlement_end_to_end_certificate_packet.py",
                ],
                "commands": [["pytest", "-q", "tests/formal/test_lean_settlement_end_to_end_certificate_packet.py"]],
            },
            {
                "kind": "tau",
                "name": "settlement_proof_gate",
                "artifacts": [
                    "src/tau_specs/recommended/settlement_v1_proof_gate.tau",
                    "tests/tau/test_settlement_v1_proof_gate.py",
                ],
                "commands": [["pytest", "-q", "tests/tau/test_settlement_v1_proof_gate.py"]],
            },
            {
                "kind": "fuzz_regression",
                "name": "stale_settlement_sequence_witnesses",
                "artifacts": [
                    "tools/stale_settlement_sequence_grammar_fuzz.py",
                    "tests/integration/test_stale_settlement_sequence_grammar_fuzz.py",
                    "tests/integration/test_dex_engine_settlement_sequence_grammar_fuzz.py",
                ],
                "commands": [
                    ["pytest", "-q", "tests/integration/test_stale_settlement_sequence_grammar_fuzz.py"],
                    ["pytest", "-q", "tests/integration/test_dex_engine_settlement_sequence_grammar_fuzz.py"],
                ],
            },
        ],
    },
}

CRITICAL_DISASTER_SURFACE_IDS: tuple[str, ...] = (
    "quote_receipt_certificate_boundary",
    "route_canonicalization_boundary",
    "settlement_attestation_policy_boundary",
    "stale_quote_receipt_boundary",
    "stale_settlement_boundary",
)

SURFACE_WITNESS_LANGUAGE_REQUIREMENTS: dict[str, dict[str, Any]] = {
    "quote_receipt_certificate_boundary": {
        "language": "quote_certificate_binding_v1",
        "required_binding_fields": [
            "receipt_hash",
            "body_hash",
            "candidate_set_hash",
            "winner_index",
            "winner_quote_hash",
            "amount_out",
        ],
        "reject_ambiguity_tokens": [
            "candidate_set_hash mismatch",
            "winner_index mismatch",
            "candidate list mismatch",
        ],
    },
    "route_canonicalization_boundary": {
        "language": "route_total_key_certificate_v1",
        "required_binding_fields": [
            "candidate_set_hash",
            "winner_index",
            "winner_key",
            "tie_break_key",
            "canonical_route_hash",
        ],
        "reject_ambiguity_tokens": [
            "winner_quote mismatch",
            "candidate_set_hash mismatch",
            "winner_index mismatch",
        ],
    },
    "settlement_attestation_policy_boundary": {
        "language": "settlement_attestation_policy_witness_v1",
        "required_binding_fields": [
            "packet_hash",
            "signer_pubkey",
            "signed_at_epoch",
            "consumer_now_epoch",
            "source_id",
            "allowed_sources",
        ],
        "reject_ambiguity_tokens": [
            "settlement spot price attestation is stale",
            "source_id not allowlisted for signer",
            "packet_hash mismatch",
            "signature invalid",
        ],
    },
    "stale_quote_receipt_boundary": {
        "language": "quote_snapshot_freshness_witness_v1",
        "required_binding_fields": [
            "receipt_hash",
            "pool_id",
            "quote_pool_fingerprint",
            "current_pool_fingerprint",
            "quote_epoch",
        ],
        "reject_ambiguity_tokens": [
            "pool_snapshot_mismatch",
            "totals_mismatch",
        ],
    },
    "stale_settlement_boundary": {
        "language": "settlement_replay_freshness_witness_v1",
        "required_binding_fields": [
            "pre_state_commitment",
            "batch_commitment",
            "settlement_hash",
            "intent_ids",
            "nonce_snapshot",
            "pool_fingerprints",
        ],
        "reject_ambiguity_tokens": [
            "settlement mismatch",
            "missing settlement",
        ],
    },
}

CROSS_SURFACE_WITNESS_PAIRS: tuple[dict[str, Any], ...] = (
    {
        "pair_id": "quote_certificate_x_stale_quote_receipt",
        "surface_ids": ("quote_receipt_certificate_boundary", "stale_quote_receipt_boundary"),
        "bounds": {"max_depth": 3, "max_frontier": 32},
        "commands": [
            ["pytest", "-q", "tests/integration/test_quote_receipt_cross_surface_sequence_grammar_fuzz.py"],
            ["pytest", "-q", "tests/integration/test_dex_engine_quote_receipt_sequence_grammar_fuzz.py"],
        ],
    },
    {
        "pair_id": "settlement_attestation_x_stale_settlement",
        "surface_ids": ("settlement_attestation_policy_boundary", "stale_settlement_boundary"),
        "bounds": {"max_depth": 1, "max_frontier": 16},
        "commands": [
            ["pytest", "-q", "tests/integration/test_settlement_attestation_sequence_grammar_fuzz.py"],
            ["pytest", "-q", "tests/integration/test_stale_settlement_sequence_grammar_fuzz.py"],
        ],
    },
    {
        "pair_id": "route_canonicalization_x_quote_certificate",
        "surface_ids": ("route_canonicalization_boundary", "quote_receipt_certificate_boundary"),
        "bounds": {"max_depth": 4, "max_frontier": 48},
        "commands": [["pytest", "-q", "tests/integration/test_quote_receipt_route_canonicalization_sequence_grammar_fuzz.py"]],
    },
    {
        "pair_id": "stale_quote_receipt_x_stale_settlement",
        "surface_ids": ("stale_quote_receipt_boundary", "stale_settlement_boundary"),
        "bounds": {"max_depth": 2, "max_frontier": 32},
        "commands": [
            ["pytest", "-q", "tests/integration/test_dex_engine_quote_receipt_sequence_grammar_fuzz.py"],
            ["pytest", "-q", "tests/integration/test_stale_settlement_sequence_grammar_fuzz.py"],
        ],
    },
    {
        "pair_id": "route_canonicalization_x_stale_settlement",
        "surface_ids": ("route_canonicalization_boundary", "stale_settlement_boundary"),
        "bounds": {"max_depth": 4, "max_frontier": 48},
        "commands": [
            ["pytest", "-q", "tests/integration/test_quote_receipt_route_canonicalization_sequence_grammar_fuzz.py"],
            ["pytest", "-q", "tests/integration/test_stale_settlement_sequence_grammar_fuzz.py"],
        ],
    },
)


def _relpath(path: Path) -> str:
    try:
        return str(path.resolve().relative_to(REPO_ROOT))
    except ValueError:
        return str(path)


def _resolve_path(path: str | Path | None) -> Path | None:
    if path is None:
        return None
    raw = Path(path)
    if raw.is_absolute():
        return raw
    return REPO_ROOT / raw


def _load_json(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"{path}: JSON payload must be an object")
    return payload


def _require_text(errors: list[str], payload: dict[str, Any], key: str) -> str | None:
    value = payload.get(key)
    if not isinstance(value, str) or not value.strip():
        errors.append(f"{key} must be a non-empty string")
        return None
    return value.strip()


def _require_text_list(errors: list[str], value: object, key: str, *, nonempty: bool) -> list[str]:
    if not isinstance(value, list):
        errors.append(f"{key} must be a list")
        return []
    rows: list[str] = []
    for idx, item in enumerate(value):
        if not isinstance(item, str) or not item.strip():
            errors.append(f"{key}[{idx}] must be a non-empty string")
            continue
        rows.append(item.strip())
    if nonempty and not rows:
        errors.append(f"{key} must contain at least one string")
    return rows


def _surfaces_by_id(target_manifest: Path) -> dict[str, DangerousSurface]:
    return {surface.id: surface for surface in load_dangerous_surface_manifest(target_manifest)}


def _evidence_at_most(value: str, ceiling: str) -> bool:
    return EVIDENCE_ORDER.get(value, 999) <= EVIDENCE_ORDER[ceiling]


def _campaign_defaults(candidate: dict[str, Any]) -> dict[str, Any]:
    campaign = candidate.get("campaign", {})
    if not isinstance(campaign, dict):
        campaign = {}
    gate_lane = campaign.get("gate_lane", "deep")
    feedback_mode = campaign.get("feedback_mode", "stateful")
    include_slow = bool(campaign.get("include_slow_explorers", False))
    return {
        "gate_lane": gate_lane if gate_lane in {"fast", "deep"} else "deep",
        "feedback_mode": feedback_mode if feedback_mode in {"legacy", "stateful"} else "stateful",
        "include_slow_explorers": include_slow,
    }


def _scenario_replay_command(*, surface_id: str, campaign: dict[str, Any], target_manifest: Path) -> list[str]:
    command = [
        "python3",
        "tools/acceptance_tcb_fuzz_campaign.py",
        "--gate-lane",
        str(campaign["gate_lane"]),
        "--target-id",
        surface_id,
        "--feedback-mode",
        str(campaign["feedback_mode"]),
        "--stateful-exploration",
        "--target-manifest",
        _relpath(target_manifest),
        "--format",
        "json",
    ]
    if campaign["include_slow_explorers"]:
        command.append("--include-slow-explorers")
    return command


def check_scenario_candidate(
    candidate: dict[str, Any],
    *,
    target_manifest: str | Path = DEFAULT_TARGET_MANIFEST,
) -> dict[str, Any]:
    manifest_path = _resolve_path(target_manifest)
    if manifest_path is None or not manifest_path.is_file():
        raise ValueError(f"missing dangerous-surface manifest: {target_manifest}")

    errors: list[str] = []
    warnings: list[str] = []
    if candidate.get("schema") != SCENARIO_CANDIDATE_SCHEMA:
        errors.append(f"schema must equal {SCENARIO_CANDIDATE_SCHEMA}")

    scenario_id = _require_text(errors, candidate, "scenario_id")
    surface_id = _require_text(errors, candidate, "surface_id")
    disaster_state = _require_text(errors, candidate, "disaster_state")
    action_grammar = _require_text(errors, candidate, "action_grammar")
    expected_guard = _require_text(errors, candidate, "expected_guard")

    bounds = candidate.get("bounds")
    if not isinstance(bounds, dict):
        errors.append("bounds must be an object")
        bounds = {}
    max_depth = bounds.get("max_depth")
    max_frontier = bounds.get("max_frontier")
    if not isinstance(max_depth, int) or max_depth < 0:
        errors.append("bounds.max_depth must be an integer >= 0")
    if not isinstance(max_frontier, int) or max_frontier <= 0:
        errors.append("bounds.max_frontier must be an integer > 0")

    oracle = candidate.get("oracle")
    if not isinstance(oracle, dict):
        errors.append("oracle must be an object")
        oracle = {}
    expected_tokens = _require_text_list(
        errors,
        oracle.get("expected_outcome_tokens"),
        "oracle.expected_outcome_tokens",
        nonempty=True,
    )
    forbidden_tokens = _require_text_list(
        errors,
        oracle.get("forbidden_outcome_tokens", []),
        "oracle.forbidden_outcome_tokens",
        nonempty=False,
    )

    promotion_target = candidate.get("promotion_target")
    if not isinstance(promotion_target, dict):
        errors.append("promotion_target must be an object")
        promotion_target = {}
    promotion_kind = promotion_target.get("kind")
    if promotion_kind not in {"shapeforge_scenario", "dangerous_surface", "negative_knowledge"}:
        errors.append("promotion_target.kind must be shapeforge_scenario, dangerous_surface, or negative_knowledge")
    promotion_evidence = promotion_target.get("evidence_class", MAX_SCENARIO_EVIDENCE)
    if promotion_evidence not in EVIDENCE_ORDER:
        errors.append("promotion_target.evidence_class must be a known evidence class")
    elif not _evidence_at_most(str(promotion_evidence), MAX_SCENARIO_EVIDENCE):
        errors.append("promotion_target.evidence_class cannot exceed tested_discovery for fuzz-derived candidates")

    evidence_ceiling = candidate.get("evidence_class_ceiling")
    if evidence_ceiling not in EVIDENCE_ORDER:
        errors.append("evidence_class_ceiling must be a known evidence class")
        evidence_ceiling = None
    elif not _evidence_at_most(str(evidence_ceiling), MAX_SCENARIO_EVIDENCE):
        errors.append("evidence_class_ceiling cannot exceed tested_discovery for LLM scenario candidates")

    surfaces = _surfaces_by_id(manifest_path)
    surface = surfaces.get(surface_id or "")
    matched_surface: dict[str, Any] | None = None
    if surface_id is not None and surface is None:
        errors.append(f"surface_id {surface_id!r} is not declared in the dangerous-surface manifest")
    elif surface is not None:
        matched_surface = {
            "id": surface.id,
            "machine_family": surface.machine_family,
            "invariant_boundary": surface.invariant_boundary,
            "action_grammar": surface.action_grammar,
            "harnesses": list(surface.harnesses),
            "outcome_tokens": list(surface.outcome_tokens),
            "witness_ids": list(surface.witness_ids),
        }
        if expected_tokens and not (set(expected_tokens) & set(surface.outcome_tokens)):
            errors.append("oracle.expected_outcome_tokens must include at least one manifest outcome token for the surface")
        harness_hint = candidate.get("harness_hint")
        if harness_hint is not None and harness_hint not in surface.harnesses:
            errors.append("harness_hint must name a harness declared for the selected surface")
        if action_grammar and action_grammar != surface.action_grammar:
            warnings.append("candidate action_grammar differs from the manifest grammar; treating it as a scenario refinement")

    campaign = _campaign_defaults(candidate)
    replay_command = (
        _scenario_replay_command(surface_id=surface_id, campaign=campaign, target_manifest=manifest_path)
        if surface_id
        else []
    )

    return {
        "schema": SCENARIO_CANDIDATE_CHECK_SCHEMA,
        "ok": not errors,
        "generated_at_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "errors": errors,
        "warnings": warnings,
        "scenario_id": scenario_id,
        "surface_id": surface_id,
        "disaster_state": disaster_state,
        "expected_guard": expected_guard,
        "forbidden_outcome_tokens": forbidden_tokens,
        "target_manifest": _relpath(manifest_path),
        "matched_surface": matched_surface,
        "evidence_class_ceiling": evidence_ceiling,
        "promotion_policy": {
            "candidate_only": True,
            "max_evidence_class": MAX_SCENARIO_EVIDENCE,
            "reason": "LLM scenario plus bounded fuzz/concolic evidence is not theorem-grade proof.",
        },
        "replay_plan": {
            "campaign": campaign,
            "command": replay_command,
        },
    }


def _load_artifact(report: dict[str, Any], campaign_report_path: Path, key: str, schema: str, errors: list[str]) -> dict[str, Any] | None:
    artifacts = report.get("artifacts")
    if not isinstance(artifacts, dict):
        errors.append("campaign report artifacts must be an object")
        return None
    raw_path = artifacts.get(key)
    if not isinstance(raw_path, str) or not raw_path:
        errors.append(f"campaign report missing artifacts.{key}")
        return None
    path = _resolve_path(raw_path)
    if path is None or not path.is_file():
        errors.append(f"missing artifact {key}: {raw_path}")
        return None
    try:
        payload = _load_json(path)
    except Exception as exc:
        errors.append(f"failed to read artifact {key}: {exc}")
        return None
    if payload.get("schema") != schema:
        errors.append(f"{_relpath(path)} schema must equal {schema}")
        return None
    payload["_artifact_path"] = _relpath(path)
    return payload


def _surface_axis(surface: DangerousSurface) -> str:
    haystack = f"{surface.id} {surface.machine_family} {' '.join(surface.waypoint_tags)}"
    if "canonicalization" in haystack or "routing" in haystack:
        return "canonical_key"
    if any(token in haystack for token in ("auth", "nonce", "signature", "receipt", "settlement", "attestation", "replay")):
        return "guard"
    return "operator"


def _improvement_target(surface: DangerousSurface, axis: str) -> str:
    if axis == "canonical_key":
        return "canonicalization"
    if "replay" in surface.id or "stale" in surface.id:
        return "replay_and_freshness_guard_alignment"
    return "fail_closed_admissibility"


def _guard_rows_by_surface(guard_report: dict[str, Any] | None) -> dict[str, list[dict[str, Any]]]:
    rows: dict[str, list[dict[str, Any]]] = {}
    if not guard_report:
        return rows
    for witness in guard_report.get("witnesses", []):
        if not isinstance(witness, dict):
            continue
        for surface_id in witness.get("surface_ids", []):
            if isinstance(surface_id, str):
                rows.setdefault(surface_id, []).append(witness)
    return rows


def _exploit_rows_by_surface(exploit_report: dict[str, Any] | None) -> dict[str, list[dict[str, Any]]]:
    rows: dict[str, list[dict[str, Any]]] = {}
    if not exploit_report:
        return rows
    for witness in exploit_report.get("top_witnesses", []):
        if not isinstance(witness, dict):
            continue
        for surface_id in witness.get("surface_ids", []):
            if isinstance(surface_id, str):
                rows.setdefault(surface_id, []).append(witness)
    return rows


def _atlas_by_surface(atlas: dict[str, Any] | None) -> dict[str, dict[str, Any]]:
    if not atlas:
        return {}
    return {
        str(entry["surface_id"]): entry
        for entry in atlas.get("entries", [])
        if isinstance(entry, dict) and isinstance(entry.get("surface_id"), str)
    }


def _run_shape_validation(*, python_bin: str) -> dict[str, Any]:
    commands = [
        [python_bin, "tools/shapeforge_validate.py", str(DEFAULT_WORLD_MODEL)],
        [python_bin, "tools/check_shape_v1_ratchet.py"],
    ]
    results: list[dict[str, Any]] = []
    ok = True
    for command in commands:
        proc = subprocess.run(command, cwd=REPO_ROOT, check=False, capture_output=True, text=True)
        row = {
            "command": command,
            "returncode": proc.returncode,
            "ok": proc.returncode == 0,
            "stdout": proc.stdout,
            "stderr": proc.stderr,
        }
        results.append(row)
        ok = ok and bool(row["ok"])
    return {"ran": True, "ok": ok, "commands": commands, "results": results}


def _top_exploit_row(rows: list[dict[str, Any]]) -> dict[str, Any] | None:
    if not rows:
        return None
    return max(
        rows,
        key=lambda row: (
            int(row.get("proximity_score", 0) or 0),
            SEVERITY_ORDER.get(str(row.get("severity_band", "unknown")), -1),
            str(row.get("witness_id") or ""),
        ),
    )


def build_shapeforge_promotion_bridge_report(
    *,
    campaign_report: str | Path,
    target_manifest: str | Path | None = None,
    run_shapeforge_checks: bool = False,
    python_bin: str | None = None,
) -> dict[str, Any]:
    campaign_report_path = _resolve_path(campaign_report)
    if campaign_report_path is None or not campaign_report_path.is_file():
        raise ValueError(f"missing campaign report: {campaign_report}")
    report = _load_json(campaign_report_path)
    errors: list[str] = []
    if report.get("schema") != "zenodex/acceptance-tcb-fuzz-campaign-report/v1":
        errors.append("campaign report schema must equal zenodex/acceptance-tcb-fuzz-campaign-report/v1")
    if report.get("plan_only") is True:
        errors.append("campaign report is plan-only; promotion bridge requires executed artifacts")

    raw_artifacts = report.get("artifacts")
    artifacts: dict[str, Any] = raw_artifacts if isinstance(raw_artifacts, dict) else {}
    manifest_value = artifacts.get("target_manifest")
    manifest_raw = target_manifest or (manifest_value if isinstance(manifest_value, str) else DEFAULT_TARGET_MANIFEST)
    manifest_path = _resolve_path(manifest_raw)
    if manifest_path is None or not manifest_path.is_file():
        errors.append(f"missing dangerous-surface manifest: {manifest_raw}")
        surfaces: dict[str, DangerousSurface] = {}
    else:
        surfaces = _surfaces_by_id(manifest_path)

    introspection = _load_artifact(
        report,
        campaign_report_path,
        "introspection_out",
        "zenodex/acceptance-tcb-fuzz-introspection/v1",
        errors,
    )
    atlas = _load_artifact(
        report,
        campaign_report_path,
        "atlas_out",
        "zenodex/acceptance-tcb-weird-machine-atlas/v1",
        errors,
    )
    suggestions = _load_artifact(
        report,
        campaign_report_path,
        "surface_suggestions_out",
        "zenodex/acceptance-tcb-surface-suggestions/v1",
        errors,
    )
    guard_report = _load_artifact(
        report,
        campaign_report_path,
        "guard_attribution_out",
        "zenodex/acceptance-tcb-guard-attribution/v1",
        errors,
    )
    exploit_report = _load_artifact(
        report,
        campaign_report_path,
        "exploit_proximity_out",
        "zenodex/acceptance-tcb-exploit-proximity/v1",
        errors,
    )

    guard_by_surface = _guard_rows_by_surface(guard_report)
    exploit_by_surface = _exploit_rows_by_surface(exploit_report)
    atlas_entries = _atlas_by_surface(atlas)
    candidate_deltas: list[dict[str, Any]] = []
    blocked_surfaces: list[dict[str, Any]] = []

    if introspection is not None:
        for row in introspection.get("surfaces", []):
            if not isinstance(row, dict):
                continue
            surface_id = row.get("surface_id")
            if not isinstance(surface_id, str) or surface_id not in surfaces:
                errors.append(f"introspection surface {surface_id!r} is not declared in the manifest")
                continue
            surface = surfaces[surface_id]
            status = row.get("status")
            if status not in {"witnessed", "reached_no_witness", "harnessed_unreached", "unharnessed"}:
                errors.append(f"surface {surface_id} has unsupported status {status!r}")
                continue
            guards = guard_by_surface.get(surface_id, [])
            exploits = exploit_by_surface.get(surface_id, [])
            top_exploit = _top_exploit_row(exploits)
            axis = _surface_axis(surface)
            if status in {"witnessed", "reached_no_witness"}:
                candidate_deltas.append(
                    {
                        "delta_id": f"stateful_surface:{surface_id}",
                        "kind": "shapeforge_scenario_candidate",
                        "surface_id": surface_id,
                        "machine_family": surface.machine_family,
                        "axis": axis,
                        "improvement_target": _improvement_target(surface, axis),
                        "evidence_class": MAX_SCENARIO_EVIDENCE,
                        "status": "candidate_only",
                        "status_if_unproved": "blocked_for_settlement_authority",
                        "invariant_boundary": surface.invariant_boundary,
                        "action_grammar": surface.action_grammar,
                        "candidate_scenario": {
                            "scenario_id": f"stateful_{surface_id}",
                            "axis": axis,
                            "perturbation": f"Replay {surface.action_grammar} against {surface.invariant_boundary}.",
                            "expected_effects": [
                                "The boundary rejects before runtime mutation.",
                                "Any surviving state remains research-only until promoted by a stronger proof gate.",
                            ],
                            "improvement_target": _improvement_target(surface, axis),
                            "evidence_required": [MAX_SCENARIO_EVIDENCE],
                        },
                        "evidence_sources": {
                            "campaign_report": _relpath(campaign_report_path),
                            "introspection": introspection.get("_artifact_path"),
                            "atlas": None if atlas is None else atlas.get("_artifact_path"),
                            "surface_suggestions": None if suggestions is None else suggestions.get("_artifact_path"),
                            "guard_attribution": None if guard_report is None else guard_report.get("_artifact_path"),
                            "exploit_proximity": None if exploit_report is None else exploit_report.get("_artifact_path"),
                            "witness_ids": sorted(set(row.get("witness_ids", []))),
                            "guard_families": sorted({str(guard.get("guard_family")) for guard in guards if guard.get("guard_family")}),
                            "top_exploit_witness_ids": [str(exploit.get("witness_id")) for exploit in exploits[:3] if exploit.get("witness_id")],
                            "exploit_proximity": {
                                "max_severity_band": None if top_exploit is None else top_exploit.get("severity_band"),
                                "max_proximity_score": 0 if top_exploit is None else int(top_exploit.get("proximity_score", 0) or 0),
                                "flags": {} if top_exploit is None else top_exploit.get("flags", {}),
                            },
                            "atlas_witness_status": atlas_entries.get(surface_id, {}).get("witness_status"),
                        },
                        "promotion_blockers": [
                            "Do not upgrade above tested_discovery without Lean/Tau/ESSO proof or a checked certificate.",
                            "Do not authorize settlement from this bridge; only FIRE-V/runtime verifier receipts may authorize deltas.",
                        ],
                    }
                )
            else:
                blocked_surfaces.append(
                    {
                        "surface_id": surface_id,
                        "machine_family": surface.machine_family,
                        "status": status,
                        "reason": "no replayable reached state or minimized witness in campaign artifacts",
                    }
                )

    shape_validation = {
        "ran": False,
        "ok": None,
        "commands": [
            ["python3", "tools/shapeforge_validate.py", _relpath(DEFAULT_WORLD_MODEL)],
            ["python3", "tools/check_shape_v1_ratchet.py"],
        ],
        "promotion_gate": "blocked_until_run" if not run_shapeforge_checks else "required",
    }
    if run_shapeforge_checks:
        shape_validation = _run_shape_validation(python_bin=python_bin or sys.executable)
        if not shape_validation["ok"]:
            errors.append("ShapeForge validation command failed")

    return {
        "schema": SHAPEFORGE_BRIDGE_SCHEMA,
        "ok": not errors,
        "generated_at_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "errors": errors,
        "source_campaign_report": _relpath(campaign_report_path),
        "target_manifest": None if manifest_path is None else _relpath(manifest_path),
        "evidence_class_ceiling": MAX_SCENARIO_EVIDENCE,
        "promotion_policy": {
            "candidate_only": True,
            "safe_states_researchable_only": True,
            "requires_replayable_artifacts": True,
            "max_evidence_class": MAX_SCENARIO_EVIDENCE,
        },
        "shape_validation": shape_validation,
        "candidate_count": len(candidate_deltas),
        "blocked_count": len(blocked_surfaces),
        "candidate_deltas": sorted(candidate_deltas, key=lambda row: row["delta_id"]),
        "blocked_surfaces": sorted(blocked_surfaces, key=lambda row: row["surface_id"]),
    }


def _load_bridge_report(bridge_report: str | Path | dict[str, Any]) -> dict[str, Any]:
    if isinstance(bridge_report, dict):
        return bridge_report
    path = _resolve_path(bridge_report)
    if path is None or not path.is_file():
        raise ValueError(f"missing bridge report: {bridge_report}")
    return _load_json(path)


def _severity_at_least(value: str | None, threshold: str) -> bool:
    return SEVERITY_ORDER.get(str(value or "unknown"), -1) >= SEVERITY_ORDER[threshold]


def build_minimal_witness_language_audit(
    *,
    surface_ids: list[str] | None = None,
) -> dict[str, Any]:
    selected = list(surface_ids) if surface_ids is not None else list(CRITICAL_DISASTER_SURFACE_IDS)
    errors: list[str] = []
    rows: list[dict[str, Any]] = []
    for surface_id in selected:
        template = SURFACE_WITNESS_LANGUAGE_REQUIREMENTS.get(surface_id)
        if template is None:
            errors.append(f"{surface_id}: missing witness-language requirements")
            continue
        fields = [str(item) for item in template.get("required_binding_fields", []) if isinstance(item, str)]
        reject_tokens = [str(item) for item in template.get("reject_ambiguity_tokens", []) if isinstance(item, str)]
        if not fields:
            errors.append(f"{surface_id}: required_binding_fields must be non-empty")
        if not reject_tokens:
            errors.append(f"{surface_id}: reject_ambiguity_tokens must be non-empty")
        rows.append(
            {
                "surface_id": surface_id,
                "language": template.get("language"),
                "target": "Good(x) <-> exists z Proves_L(z, x)",
                "claim_tier": "bounded_witness_language",
                "required_binding_fields": fields,
                "reject_ambiguity_tokens": reject_tokens,
                "rejects_ambiguous_witnesses": bool(fields and reject_tokens),
            }
        )
    return {
        "schema": MINIMAL_WITNESS_LANGUAGE_AUDIT_SCHEMA,
        "ok": not errors,
        "generated_at_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "errors": errors,
        "surface_count": len(rows),
        "surfaces": sorted(rows, key=lambda row: str(row["surface_id"])),
    }


def build_cross_surface_witness_exploration_plan(
    *,
    pair_ids: list[str] | None = None,
) -> dict[str, Any]:
    selected_pair_ids = set(pair_ids) if pair_ids is not None else None
    errors: list[str] = []
    pairs: list[dict[str, Any]] = []
    audit = build_minimal_witness_language_audit()
    if audit.get("ok") is not True:
        errors.extend(str(error) for error in audit.get("errors", []))
    known_surfaces = {str(row["surface_id"]) for row in audit.get("surfaces", []) if isinstance(row, dict)}
    for pair in CROSS_SURFACE_WITNESS_PAIRS:
        pair_id = str(pair.get("pair_id"))
        if selected_pair_ids is not None and pair_id not in selected_pair_ids:
            continue
        surface_ids = [str(item) for item in pair.get("surface_ids", ()) if isinstance(item, str)]
        missing_surfaces = [surface_id for surface_id in surface_ids if surface_id not in known_surfaces]
        commands = pair.get("commands", [])
        if missing_surfaces:
            errors.append(f"{pair_id}: missing witness-language audit surface(s): {', '.join(missing_surfaces)}")
        if not isinstance(commands, list) or not commands:
            errors.append(f"{pair_id}: commands must be a non-empty list")
            commands = []
        for command in commands:
            if not isinstance(command, list) or not all(isinstance(item, str) for item in command):
                errors.append(f"{pair_id}: command entries must be lists of strings")
        pairs.append(
            {
                "pair_id": pair_id,
                "surface_ids": surface_ids,
                "bounds": pair.get("bounds", {}),
                "commands": commands,
                "evidence_class_ceiling": MAX_SCENARIO_EVIDENCE,
                "status": "bounded_exploration_required",
            }
        )
    if not pairs:
        errors.append("no cross-surface witness pairs selected")
    return {
        "schema": CROSS_SURFACE_WITNESS_EXPLORATION_SCHEMA,
        "ok": not errors,
        "generated_at_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "errors": errors,
        "pair_count": len(pairs),
        "witness_language_audit": audit,
        "pairs": sorted(pairs, key=lambda row: str(row["pair_id"])),
    }


def _risk_counts(candidates: list[dict[str, Any]]) -> dict[str, int]:
    counts = {key: 0 for key in ("unknown", "low", "medium", "high", "critical")}
    for candidate in candidates:
        evidence_sources = candidate.get("evidence_sources", {})
        if not isinstance(evidence_sources, dict):
            counts["unknown"] += 1
            continue
        proximity = evidence_sources.get("exploit_proximity", {})
        if not isinstance(proximity, dict):
            counts["unknown"] += 1
            continue
        band = str(proximity.get("max_severity_band") or "unknown")
        if band not in counts:
            band = "unknown"
        counts[band] += 1
    return counts


def _ledger_record_for_candidate(candidate: dict[str, Any]) -> dict[str, Any]:
    evidence_sources = candidate.get("evidence_sources", {})
    if not isinstance(evidence_sources, dict):
        evidence_sources = {}
    witness_ids = [str(row) for row in evidence_sources.get("witness_ids", []) if isinstance(row, str)]
    guard_families = [str(row) for row in evidence_sources.get("guard_families", []) if isinstance(row, str)]
    proximity = evidence_sources.get("exploit_proximity", {})
    if not isinstance(proximity, dict):
        proximity = {}
    if witness_ids and guard_families:
        reachability_status = "blocked_by_guard_witness"
    elif witness_ids:
        reachability_status = "witnessed_without_guard_attribution"
    else:
        reachability_status = "reached_without_minimized_witness"
    return {
        "record_id": f"blocked_state:{candidate.get('surface_id')}",
        "surface_id": candidate.get("surface_id"),
        "machine_family": candidate.get("machine_family"),
        "negative_kind": "blocked_promotion",
        "claim": f"Attempted disaster state for {candidate.get('surface_id')} remains research-only until replay and proof obligations close.",
        "reachability_status": reachability_status,
        "current_evidence_class": candidate.get("evidence_class"),
        "target_evidence_class": "contract_or_proved",
        "guard_families": guard_families,
        "witness_ids": witness_ids,
        "severity_band": proximity.get("max_severity_band") or "unknown",
        "proximity_score": int(proximity.get("max_proximity_score", 0) or 0),
        "replay_pointer": evidence_sources.get("campaign_report"),
    }


def build_disaster_reachability_ratchet_report(
    *,
    bridge_report: str | Path | dict[str, Any],
    require_shape_validation: bool = False,
    max_blocked_surfaces: int = 0,
    require_witnesses: bool = True,
    require_guard_attribution: bool = False,
    high_severity_requires_witness: str = "high",
) -> dict[str, Any]:
    bridge = _load_bridge_report(bridge_report)
    errors: list[str] = []
    warnings: list[str] = []

    if bridge.get("schema") != SHAPEFORGE_BRIDGE_SCHEMA:
        errors.append(f"bridge report schema must equal {SHAPEFORGE_BRIDGE_SCHEMA}")
    if bridge.get("ok") is not True:
        errors.append("bridge report is not ok")
    if bridge.get("evidence_class_ceiling") != MAX_SCENARIO_EVIDENCE:
        errors.append("bridge evidence_class_ceiling must remain tested_discovery")
    policy = bridge.get("promotion_policy")
    if not isinstance(policy, dict) or policy.get("candidate_only") is not True:
        errors.append("bridge promotion policy must be candidate_only")
    if not isinstance(policy, dict) or policy.get("safe_states_researchable_only") is not True:
        errors.append("bridge promotion policy must mark safe_states_researchable_only")

    shape_validation = bridge.get("shape_validation")
    if require_shape_validation:
        if not isinstance(shape_validation, dict) or shape_validation.get("ran") is not True:
            errors.append("shape validation must be run for this ratchet")
        elif shape_validation.get("ok") is not True:
            errors.append("shape validation failed")

    blocked_surfaces = bridge.get("blocked_surfaces", [])
    if not isinstance(blocked_surfaces, list):
        errors.append("blocked_surfaces must be a list")
        blocked_surfaces = []
    if len(blocked_surfaces) > max_blocked_surfaces:
        errors.append(f"blocked surface count {len(blocked_surfaces)} exceeds budget {max_blocked_surfaces}")

    candidates = bridge.get("candidate_deltas", [])
    if not isinstance(candidates, list):
        errors.append("candidate_deltas must be a list")
        candidates = []
    if not candidates:
        errors.append("ratchet requires at least one candidate delta")

    ledger_records: list[dict[str, Any]] = []
    for candidate in candidates:
        if not isinstance(candidate, dict):
            errors.append("candidate_deltas entries must be objects")
            continue
        surface_id = str(candidate.get("surface_id") or "<unknown>")
        if candidate.get("evidence_class") != MAX_SCENARIO_EVIDENCE:
            errors.append(f"{surface_id}: evidence_class must remain tested_discovery")
        if candidate.get("status") != "candidate_only":
            errors.append(f"{surface_id}: status must remain candidate_only")
        evidence_sources = candidate.get("evidence_sources", {})
        if not isinstance(evidence_sources, dict):
            errors.append(f"{surface_id}: evidence_sources must be an object")
            continue
        witness_ids = [row for row in evidence_sources.get("witness_ids", []) if isinstance(row, str)]
        guard_families = [row for row in evidence_sources.get("guard_families", []) if isinstance(row, str)]
        proximity = evidence_sources.get("exploit_proximity", {})
        if not isinstance(proximity, dict):
            proximity = {}
        severity = str(proximity.get("max_severity_band") or "unknown")
        if require_witnesses and not witness_ids:
            errors.append(f"{surface_id}: missing minimized witness ids")
        if require_guard_attribution and not guard_families:
            errors.append(f"{surface_id}: missing guard attribution")
        if _severity_at_least(severity, high_severity_requires_witness) and not witness_ids:
            errors.append(f"{surface_id}: {severity} severity candidate lacks a minimized witness")
        if not guard_families:
            warnings.append(f"{surface_id}: no guard attribution available")
        ledger_records.append(_ledger_record_for_candidate(candidate))

    return {
        "schema": DISASTER_REACHABILITY_RATCHET_SCHEMA,
        "ok": not errors,
        "generated_at_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "errors": errors,
        "warnings": warnings,
        "source_bridge_report": bridge.get("source_campaign_report"),
        "policy": {
            "max_blocked_surfaces": max_blocked_surfaces,
            "require_shape_validation": require_shape_validation,
            "require_witnesses": require_witnesses,
            "require_guard_attribution": require_guard_attribution,
            "high_severity_requires_witness": high_severity_requires_witness,
            "evidence_class_ceiling": MAX_SCENARIO_EVIDENCE,
        },
        "surface_count": len(candidates) + len(blocked_surfaces),
        "candidate_count": len(candidates),
        "blocked_count": len(blocked_surfaces),
        "risk_counts": _risk_counts(candidates),
        "blocked_surfaces": blocked_surfaces,
        "negative_knowledge_candidates": sorted(ledger_records, key=lambda row: str(row["record_id"])),
    }


def run_scenario_candidate(
    *,
    candidate: dict[str, Any],
    target_manifest: str | Path = DEFAULT_TARGET_MANIFEST,
    execute: bool = False,
    report_out: str | Path | None = None,
    campaign_root: str | Path | None = None,
    timestamp_utc: str | None = None,
    run_id: str | None = None,
    build_bridge: bool = True,
    run_shapeforge_checks: bool = False,
    python_bin: str | None = None,
) -> dict[str, Any]:
    check = check_scenario_candidate(candidate, target_manifest=target_manifest)
    command = list(check.get("replay_plan", {}).get("command", []))
    if report_out is not None:
        command.extend(["--report-out", str(report_out)])
    if campaign_root is not None:
        command.extend(["--campaign-root", str(campaign_root)])
    if timestamp_utc is not None:
        command.extend(["--timestamp-utc", timestamp_utc])
    if run_id is not None:
        command.extend(["--run-id", run_id])

    receipt: dict[str, Any] = {
        "schema": SCENARIO_RUN_RECEIPT_SCHEMA,
        "ok": bool(check["ok"]) and not execute,
        "plan_only": not execute,
        "generated_at_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "candidate_check": check,
        "command": command,
        "campaign_result": None,
        "bridge_report": None,
    }
    if not check["ok"]:
        receipt["ok"] = False
        return receipt
    if not execute:
        return receipt

    proc = subprocess.run(command, cwd=REPO_ROOT, check=False, capture_output=True, text=True)
    campaign_payload: dict[str, Any] | None = None
    if proc.stdout.strip():
        try:
            parsed = json.loads(proc.stdout)
            if isinstance(parsed, dict):
                campaign_payload = parsed
        except json.JSONDecodeError:
            campaign_payload = None
    receipt["campaign_result"] = {
        "returncode": proc.returncode,
        "ok": proc.returncode == 0,
        "stdout": proc.stdout,
        "stderr": proc.stderr,
        "report_out": None if campaign_payload is None else campaign_payload.get("report_out"),
    }
    if proc.returncode != 0:
        receipt["ok"] = False
        return receipt

    if build_bridge:
        campaign_report_path = None
        if campaign_payload is not None and isinstance(campaign_payload.get("report_out"), str):
            campaign_report_path = campaign_payload["report_out"]
        elif report_out is not None:
            campaign_report_path = str(report_out)
        if campaign_report_path:
            receipt["bridge_report"] = build_shapeforge_promotion_bridge_report(
                campaign_report=campaign_report_path,
                target_manifest=target_manifest,
                run_shapeforge_checks=run_shapeforge_checks,
                python_bin=python_bin,
            )
    receipt["ok"] = bool(receipt["campaign_result"]["ok"]) and (
        receipt["bridge_report"] is None or bool(receipt["bridge_report"].get("ok"))
    )
    return receipt


def _load_ratchet_report(ratchet_report: str | Path | dict[str, Any]) -> dict[str, Any]:
    if isinstance(ratchet_report, dict):
        return ratchet_report
    path = _resolve_path(ratchet_report)
    if path is None or not path.is_file():
        raise ValueError(f"missing ratchet report: {ratchet_report}")
    return _load_json(path)


def _artifact_status(artifacts: list[str]) -> tuple[list[str], list[str]]:
    present: list[str] = []
    missing: list[str] = []
    for artifact in artifacts:
        path = _resolve_path(artifact)
        if path is not None and path.exists():
            present.append(artifact)
        else:
            missing.append(artifact)
    return present, missing


def _lane_with_status(lane: dict[str, Any]) -> dict[str, Any]:
    artifacts = [str(artifact) for artifact in lane.get("artifacts", [])]
    present, missing = _artifact_status(artifacts)
    out = {
        "kind": lane.get("kind"),
        "name": lane.get("name"),
        "artifacts": artifacts,
        "commands": lane.get("commands", []),
        "present_artifacts": present,
        "missing_artifacts": missing,
        "artifact_status": "present" if not missing else "missing",
    }
    return out


def build_stateful_disaster_proof_obligation_packet(
    *,
    ratchet_report: str | Path | dict[str, Any],
    min_severity: str = "high",
    include_unknown: bool = False,
    require_formal_lane: bool = True,
) -> dict[str, Any]:
    ratchet = _load_ratchet_report(ratchet_report)
    errors: list[str] = []
    warnings: list[str] = []
    if ratchet.get("schema") != DISASTER_REACHABILITY_RATCHET_SCHEMA:
        errors.append(f"ratchet report schema must equal {DISASTER_REACHABILITY_RATCHET_SCHEMA}")
    if ratchet.get("ok") is not True:
        errors.append("ratchet report is not ok")

    rows = ratchet.get("negative_knowledge_candidates", [])
    if not isinstance(rows, list):
        errors.append("negative_knowledge_candidates must be a list")
        rows = []

    obligations: list[dict[str, Any]] = []
    classification_gaps: list[dict[str, Any]] = []
    for row in rows:
        if not isinstance(row, dict):
            errors.append("negative_knowledge_candidates entries must be objects")
            continue
        surface_id = str(row.get("surface_id") or "")
        severity = str(row.get("severity_band") or "unknown")
        if severity == "unknown":
            if include_unknown:
                classification_gaps.append(
                    {
                        "surface_id": surface_id,
                        "reason": "exploit proximity severity is unknown; run or enrich exploit proximity before formal promotion",
                        "witness_ids": row.get("witness_ids", []),
                    }
                )
            continue
        if not _severity_at_least(severity, min_severity):
            continue

        template = SURFACE_FORMAL_LANES.get(surface_id)
        if template is None:
            errors.append(f"{surface_id}: no formal lane mapping for {severity} disaster surface")
            continue
        lanes = [_lane_with_status(lane) for lane in template["lanes"]]
        missing_artifacts = sorted({artifact for lane in lanes for artifact in lane["missing_artifacts"]})
        formal_lane_count = sum(1 for lane in lanes if lane.get("kind") in FORMAL_LANE_KINDS)
        if missing_artifacts:
            errors.append(f"{surface_id}: missing proof-lane artifact(s): {', '.join(missing_artifacts)}")
        if require_formal_lane and formal_lane_count == 0:
            errors.append(f"{surface_id}: no formal closure lane declared")
        witness_ids = [str(item) for item in row.get("witness_ids", []) if isinstance(item, str)]
        if not witness_ids:
            errors.append(f"{surface_id}: proof obligation has no replay witness ids")
        obligations.append(
            {
                "obligation_id": f"proof_obligation:{surface_id}",
                "surface_id": surface_id,
                "machine_family": row.get("machine_family"),
                "severity_band": severity,
                "proximity_score": int(row.get("proximity_score", 0) or 0),
                "current_evidence_class": row.get("current_evidence_class"),
                "target_evidence_class": template["target_evidence_class"],
                "obligation": template["obligation"],
                "witness_ids": witness_ids,
                "guard_families": row.get("guard_families", []),
                "replay_pointer": row.get("replay_pointer"),
                "formal_lane_count": formal_lane_count,
                "lanes": lanes,
                "promotion_status": "blocked_until_formal_closure",
            }
        )

    if not obligations:
        warnings.append("no obligations selected under the current severity filter")

    return {
        "schema": PROOF_OBLIGATION_PACKET_SCHEMA,
        "ok": not errors,
        "generated_at_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "errors": errors,
        "warnings": warnings,
        "source_ratchet_report": ratchet.get("source_bridge_report"),
        "policy": {
            "min_severity": min_severity,
            "include_unknown": include_unknown,
            "require_formal_lane": require_formal_lane,
            "promotion_status": "blocked_until_formal_closure",
        },
        "obligation_count": len(obligations),
        "classification_gap_count": len(classification_gaps),
        "obligations": sorted(obligations, key=lambda item: str(item["obligation_id"])),
        "classification_gaps": sorted(classification_gaps, key=lambda item: str(item["surface_id"])),
    }


def _load_proof_obligation_packet(packet: str | Path | dict[str, Any]) -> dict[str, Any]:
    if isinstance(packet, dict):
        return packet
    path = _resolve_path(packet)
    if path is None or not path.is_file():
        raise ValueError(f"missing proof-obligation packet: {packet}")
    return _load_json(path)


def _selected_obligations(
    packet: dict[str, Any],
    *,
    surface_ids: set[str] | None,
) -> list[dict[str, Any]]:
    rows = packet.get("obligations", [])
    if not isinstance(rows, list):
        return []
    selected: list[dict[str, Any]] = []
    for row in rows:
        if not isinstance(row, dict):
            continue
        surface_id = str(row.get("surface_id") or "")
        if surface_ids is not None and surface_id not in surface_ids:
            continue
        selected.append(row)
    return selected


def _command_status(*, returncode: int, stdout: str, stderr: str) -> str:
    combined = f"{stdout}\n{stderr}".lower()
    if returncode != 0:
        return "failed"
    if " skipped" in combined or "skipped," in combined or "skipped in " in combined:
        return "inconclusive"
    return "passed"


def _run_obligation_command(command: list[str], *, timeout_s: int) -> dict[str, Any]:
    started = time.monotonic()
    try:
        proc = subprocess.run(
            command,
            cwd=REPO_ROOT,
            check=False,
            capture_output=True,
            text=True,
            timeout=timeout_s,
        )
        duration_s = round(time.monotonic() - started, 3)
        status = _command_status(returncode=proc.returncode, stdout=proc.stdout, stderr=proc.stderr)
        return {
            "command": command,
            "status": status,
            "ok": status == "passed",
            "returncode": proc.returncode,
            "duration_s": duration_s,
            "stdout": proc.stdout,
            "stderr": proc.stderr,
        }
    except subprocess.TimeoutExpired as exc:
        stdout = exc.stdout.decode("utf-8", errors="replace") if isinstance(exc.stdout, bytes) else (exc.stdout or "")
        stderr = exc.stderr.decode("utf-8", errors="replace") if isinstance(exc.stderr, bytes) else (exc.stderr or "")
        return {
            "command": command,
            "status": "inconclusive",
            "ok": False,
            "returncode": None,
            "duration_s": round(time.monotonic() - started, 3),
            "stdout": stdout,
            "stderr": stderr + f"\ntimeout after {timeout_s}s",
        }


def _lane_closure_status(command_results: list[dict[str, Any]]) -> str:
    if not command_results:
        return "inconclusive"
    statuses = {str(result.get("status")) for result in command_results}
    if "failed" in statuses:
        return "failed"
    if "inconclusive" in statuses:
        return "inconclusive"
    return "passed"


def _obligation_closure_status(lane_results: list[dict[str, Any]], *, selected_lane_count: int, total_lane_count: int) -> str:
    if not lane_results:
        return "inconclusive"
    lane_statuses = {str(result.get("status")) for result in lane_results}
    if "failed" in lane_statuses:
        return "failed"
    if "inconclusive" in lane_statuses:
        return "inconclusive"
    if selected_lane_count != total_lane_count:
        return "partial"
    return "closed"


def run_stateful_disaster_proof_obligations(
    *,
    packet: str | Path | dict[str, Any],
    surface_ids: list[str] | None = None,
    lane_kinds: list[str] | None = None,
    timeout_s: int = 180,
) -> dict[str, Any]:
    proof_packet = _load_proof_obligation_packet(packet)
    errors: list[str] = []
    warnings: list[str] = []
    if proof_packet.get("schema") != PROOF_OBLIGATION_PACKET_SCHEMA:
        errors.append(f"proof-obligation packet schema must equal {PROOF_OBLIGATION_PACKET_SCHEMA}")
    if proof_packet.get("ok") is not True:
        errors.append("proof-obligation packet is not ok")

    surface_filter = set(surface_ids) if surface_ids else None
    lane_filter = set(lane_kinds) if lane_kinds else None
    selected = _selected_obligations(proof_packet, surface_ids=surface_filter)
    if not selected:
        errors.append("no proof obligations selected")

    obligation_results: list[dict[str, Any]] = []
    for obligation in selected:
        lanes = obligation.get("lanes", [])
        if not isinstance(lanes, list):
            errors.append(f"{obligation.get('surface_id')}: lanes must be a list")
            continue
        total_lane_count = len([lane for lane in lanes if isinstance(lane, dict)])
        selected_lanes = [
            lane
            for lane in lanes
            if isinstance(lane, dict) and (lane_filter is None or str(lane.get("kind")) in lane_filter)
        ]
        if not selected_lanes:
            warnings.append(f"{obligation.get('surface_id')}: no lanes selected")
        lane_results: list[dict[str, Any]] = []
        for lane in selected_lanes:
            missing_artifacts = [str(item) for item in lane.get("missing_artifacts", []) if isinstance(item, str)]
            command_results: list[dict[str, Any]] = []
            if missing_artifacts:
                command_results.append(
                    {
                        "command": [],
                        "status": "failed",
                        "ok": False,
                        "returncode": None,
                        "duration_s": 0,
                        "stdout": "",
                        "stderr": "missing artifacts: " + ", ".join(missing_artifacts),
                    }
                )
            else:
                commands = lane.get("commands", [])
                if not isinstance(commands, list) or not commands:
                    command_results.append(
                        {
                            "command": [],
                            "status": "inconclusive",
                            "ok": False,
                            "returncode": None,
                            "duration_s": 0,
                            "stdout": "",
                            "stderr": "lane has no commands",
                        }
                    )
                else:
                    for command in commands:
                        if not isinstance(command, list) or not all(isinstance(item, str) for item in command):
                            command_results.append(
                                {
                                    "command": [],
                                    "status": "failed",
                                    "ok": False,
                                    "returncode": None,
                                    "duration_s": 0,
                                    "stdout": "",
                                    "stderr": "lane command must be a list of strings",
                                }
                            )
                            continue
                        command_results.append(_run_obligation_command(command, timeout_s=timeout_s))
            lane_status = _lane_closure_status(command_results)
            lane_results.append(
                {
                    "kind": lane.get("kind"),
                    "name": lane.get("name"),
                    "status": lane_status,
                    "ok": lane_status == "passed",
                    "command_results": command_results,
                }
            )
        closure_status = _obligation_closure_status(
            lane_results,
            selected_lane_count=len(selected_lanes),
            total_lane_count=total_lane_count,
        )
        obligation_results.append(
            {
                "obligation_id": obligation.get("obligation_id"),
                "surface_id": obligation.get("surface_id"),
                "target_evidence_class": obligation.get("target_evidence_class"),
                "closure_status": closure_status,
                "ok": closure_status == "closed",
                "selected_lane_count": len(selected_lanes),
                "total_lane_count": total_lane_count,
                "lane_results": lane_results,
            }
        )

    receipt_ok = not errors and bool(obligation_results) and all(result.get("closure_status") == "closed" for result in obligation_results)
    return {
        "schema": PROOF_OBLIGATION_CLOSURE_RECEIPT_SCHEMA,
        "ok": receipt_ok,
        "generated_at_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "errors": errors,
        "warnings": warnings,
        "policy": {
            "surface_ids": None if surface_ids is None else list(surface_ids),
            "lane_kinds": None if lane_kinds is None else list(lane_kinds),
            "timeout_s": timeout_s,
            "skips_are_inconclusive": True,
        },
        "selected_obligation_count": len(obligation_results),
        "closed_count": sum(1 for result in obligation_results if result.get("closure_status") == "closed"),
        "failed_count": sum(1 for result in obligation_results if result.get("closure_status") == "failed"),
        "inconclusive_count": sum(1 for result in obligation_results if result.get("closure_status") == "inconclusive"),
        "partial_count": sum(1 for result in obligation_results if result.get("closure_status") == "partial"),
        "obligation_results": obligation_results,
    }
