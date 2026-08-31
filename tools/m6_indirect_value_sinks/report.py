"""Stable public report for the bounded O-007C registry."""

from __future__ import annotations

import hashlib
from collections.abc import Mapping
from pathlib import Path
from typing import cast

from tools.m6_indirect_value_sinks.inventory import (
    NONCLAIMS,
    REGISTRY_PATH,
    build_projection,
    collect_inventory_facts,
    validate_registry,
)
from tools.m6_indirect_value_sinks.model import IndirectSinkRejectV1


def _finding(exc: Exception) -> dict[str, str]:
    return {
        "code": str(getattr(exc, "code", type(exc).__name__)),
        "detail": str(getattr(exc, "detail", str(exc))),
        "path": str(getattr(exc, "path", "O007C")),
    }


def _base_report() -> dict[str, object]:
    return {
        "all_discovered_rows_dispositioned": False,
        "bounded_inventory_status": "OPEN",
        "closed_value_movement_gates": 0,
        "finding": None,
        "migration_authority": "NONE",
        "nonclaims": list(NONCLAIMS),
        "o007a_bound_through_o007b_v3": False,
        "o007b_v3_current_applicable": False,
        "o007b_v3_historical_valid": False,
        "ok": False,
        "production_authority": "NONE",
        "release_authority": "NONE",
        "release_ready": False,
        "schema": "zenodex/m6-indirect-value-sink-check/v1",
        "settlement_authority": "NONE",
        "value_movement_authority": "NONE",
        "verifier_authority": "NONE",
        "vm01_status": "OPEN",
        "vm_gates_closed": [],
    }


def _build_indirect_value_sink_report(
    root: Path | str,
    *,
    o007b_report: Mapping[str, object] | None = None,
) -> dict[str, object]:
    root = Path(root).resolve()
    report = _base_report()
    try:
        facts = collect_inventory_facts(root, o007b_report=o007b_report)
        summary = cast(dict[str, object], facts["summary"])
        o007b = cast(dict[str, object], facts["o007b"])
        report.update(
            {
                "dynamic_declaration_count": summary["dynamic_declaration_count"],
                "indirect_alias_count": summary["indirect_alias_count"],
                "o007a_bound_through_o007b_v3": True,
                "o007b_v3_current_applicable": o007b["current_applicable"],
                "o007b_v3_historical_valid": o007b["historical_valid"],
                "scope_candidate_count": summary["scope_candidate_count"],
                "workspace_candidate_count": summary["workspace_candidate_count"],
            }
        )
        raw = (root / REGISTRY_PATH).read_bytes()
        registry = validate_registry(root, facts, raw)
        projection = build_projection(root, facts, registry)
        report.update(
            {
                "all_discovered_rows_dispositioned": projection[
                    "all_discovered_rows_dispositioned"
                ],
                "bounded_inventory_status": "COMPLETE_RESEARCH_ONLY",
                "candidate_source_root": summary["candidate_source_root"],
                "closed_local_target_set_disposition_count": summary[
                    "closed_local_target_set_disposition_count"
                ],
                "closed_static_registry_dynamic_count": summary[
                    "closed_static_registry_dynamic_count"
                ],
                "closure_gap_disposition_count": projection[
                    "closure_gap_disposition_count"
                ],
                "dynamic_declaration_count": summary["dynamic_declaration_count"],
                "dynamic_disposition_count": projection["dynamic_disposition_count"],
                "derived_closed_static_registry_disposition_count": summary[
                    "derived_closed_static_registry_disposition_count"
                ],
                "derived_external_literal_disposition_count": summary[
                    "derived_external_literal_disposition_count"
                ],
                "derived_local_literal_disposition_count": summary[
                    "derived_local_literal_disposition_count"
                ],
                "evidence_tool_exclusion_count": summary[
                    "evidence_tool_exclusion_count"
                ],
                "finding": None,
                "indirect_alias_count": summary["indirect_alias_count"],
                "inventory_summary": summary,
                "lifecycle_dispositions": projection["lifecycle_dispositions"],
                "literal_dynamic_count": summary["literal_dynamic_count"],
                "o007a_bound_through_o007b_v3": True,
                "o007b_v3_current_applicable": o007b["current_applicable"],
                "o007b_v3_historical_valid": o007b["historical_valid"],
                "ok": True,
                "projection_root": projection["projection_root"],
                "registry_sha256": hashlib.sha256(raw).hexdigest(),
                "scope_candidate_count": summary["scope_candidate_count"],
                "source_sink_observation_count": summary[
                    "source_sink_observation_count"
                ],
                "source_sink_record_count": summary["source_sink_record_count"],
                "source_bound_research_exclusion_disposition_count": summary[
                    "source_bound_research_exclusion_disposition_count"
                ],
                "special_statuses": projection["special_statuses"],
                "unresolved_dynamic_count": summary["unresolved_dynamic_count"],
                "unresolved_dynamic_nonprimary_count": summary[
                    "unresolved_dynamic_nonprimary_count"
                ],
                "unresolved_dynamic_primary_count": summary[
                    "unresolved_dynamic_primary_count"
                ],
                "workspace_candidate_count": summary["workspace_candidate_count"],
            }
        )
    except (IndirectSinkRejectV1, OSError, UnicodeError) as exc:
        report["finding"] = _finding(exc)
    return report


def build_indirect_value_sink_report(root: Path | str) -> dict[str, object]:
    return _build_indirect_value_sink_report(root, o007b_report=None)
