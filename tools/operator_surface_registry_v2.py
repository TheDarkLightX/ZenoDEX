"""Closed semantic contract for the O-004 V2 operator-surface registry."""

from __future__ import annotations

from pathlib import Path
from typing import Final, cast

from tools.operator_surface_registry_common_v2 import (
    HEX_40_V2,
    HEX_64_V2,
    OperatorSurfaceRegistryRejectV2,
    canonical_json_bytes_v2,
    decode_json_object_v2,
    reject_v2,
    sha256_hex_v2,
)
from tools.operator_surface_registry_projection_v2 import (
    expected_source_projections_v2,
    project_app_navigation_v2,
    project_compose_v2,
    project_ui_config_v2,
    validate_evidence_reference_v2,
)

SCHEMA_V2: Final = "zenodex/operator-surface-registry/v2"
CHECK_SCHEMA_V2: Final = "zenodex/operator-surface-registry-check/v2"
ARTIFACT_RELATIVE_PATH_V2: Final = Path("docs/research/ZENODEX_OPERATOR_SURFACE_REGISTRY_V2.json")
SOURCE_PATHS_V2: Final = (
    "docker-compose.local-testnet.yml",
    "tests/integration/test_api_server_confidential.py",
    "tests/integration/test_dex_ui_live_bridge.py",
    "tests/integration/test_retired_tau_bridge_startup_refusal_v2.py",
    "tests/test_check_operator_surface_registry_v2.py",
    "tests/test_operator_surface_registry_semantic_mutants_v2.py",
    "tests/test_zenodex_oracle_mvp_completion_audit.py",
    "tools/__init__.py",
    "tools/build_operator_surface_registry_v2.py",
    "tools/check_operator_surface_registry_v2.py",
    "tools/dex-ui/public/zenodex-config.json",
    "tools/dex-ui/src/App.jsx",
    "tools/operator_surface_registry_common_v2.py",
    "tools/operator_surface_registry_git_v2.py",
    "tools/operator_surface_registry_projection_v2.py",
    "tools/operator_surface_registry_v2.py",
)
ROUTE_IDS_V2: Final = (
    "spot_ledger_api",
    "oracle_api",
    "confidential_attestation_api",
    "perps_wallet_stream_8",
    "zusd_tau_wallet_stream_9",
    "zusd_monetary_wallet_stream_11",
    "autotrader_api",
)
NO_AUTHORITY_V2: Final = {
    "mount": "NONE",
    "production": "NONE",
    "release": "NONE",
    "settlement": "NONE",
    "value_movement": "NONE",
}
_PRESENTATION_ROWS_V2: Final = (
    ("swap", "Swap", ("spot_ledger_api",), "NAV_TAB"),
    ("pools", "Pools", ("spot_ledger_api",), "NAV_TAB"),
    ("stats", "ZDEX Stats", (), "NAV_TAB"),
    ("perps", "Perpetuals", ("perps_wallet_stream_8",), "NAV_TAB"),
    ("strategy", "Strategy", ("autotrader_api",), "NAV_TAB"),
    (
        "zusd",
        "zUSD",
        ("zusd_tau_wallet_stream_9", "zusd_monetary_wallet_stream_11"),
        "NAV_TAB",
    ),
    ("oracle", "Oracle", ("oracle_api",), "NAV_TAB"),
    (
        "confidential",
        "Confidential",
        ("confidential_attestation_api",),
        "NAV_TAB",
    ),
    ("governance", "Keys", (), "NAV_TAB"),
    ("proofs", "Proof Mining", (), "HIDDEN_ROUTE"),
)
_NONCLAIMS_V2: Final = (
    "The registry records source-bound local-profile references; it does not execute them.",
    "MOUNTED_LOCAL_PROFILE is an operator-profile classification, not M6 mounted authority.",
    "No release, settlement, production, or value-moving authority is granted.",
    "Git executable integrity and process containment remain external premises.",
)
_RETIRED_TEST_PATH_V2: Final = "tests/integration/test_retired_tau_bridge_startup_refusal_v2.py"
_ROUTE_ROWS_V2: Final = (
    (
        "spot_ledger_api",
        "MOUNTED_LOCAL_PROFILE",
        "positive",
        "tests/integration/test_dex_ui_live_bridge.py",
        "test_live_node_serves_ui_pools_and_accepts_ui_swap",
    ),
    (
        "oracle_api",
        "MOUNTED_LOCAL_PROFILE",
        "positive",
        "tests/test_zenodex_oracle_mvp_completion_audit.py",
        "test_oracle_mvp_completion_audit_accepts_current_local_shell",
    ),
    (
        "confidential_attestation_api",
        "MOUNTED_LOCAL_PROFILE",
        "positive",
        "tests/integration/test_api_server_confidential.py",
        "test_api_server_confidential_status_endpoint",
    ),
    (
        "perps_wallet_stream_8",
        "QUARANTINED",
        "refusal",
        _RETIRED_TEST_PATH_V2,
        "test_given_retired_route_value_when_starting_twice_then_exact_reject_has_no_effect",
    ),
    (
        "zusd_tau_wallet_stream_9",
        "QUARANTINED",
        "refusal",
        _RETIRED_TEST_PATH_V2,
        "test_given_retired_route_value_when_starting_twice_then_exact_reject_has_no_effect",
    ),
    (
        "zusd_monetary_wallet_stream_11",
        "QUARANTINED",
        "refusal",
        _RETIRED_TEST_PATH_V2,
        "test_given_retired_route_value_when_starting_twice_then_exact_reject_has_no_effect",
    ),
    (
        "autotrader_api",
        "QUARANTINED",
        "refusal",
        _RETIRED_TEST_PATH_V2,
        "test_given_direct_autotrader_attachment_when_called_then_rejects_before_state_effects",
    ),
)


def _route_registry_v2() -> list[dict[str, object]]:
    result: list[dict[str, object]] = []
    for route_id, classification, evidence_kind, path, node_id in _ROUTE_ROWS_V2:
        reference = {"path": path, "node_id": node_id, "evidence_kind": evidence_kind}
        result.append(
            {
                "route_id": route_id,
                "classification": classification,
                "positive_test_refs": [reference] if evidence_kind == "positive" else [],
                "refusal_test_refs": [reference] if evidence_kind == "refusal" else [],
            }
        )
    return result


def _presentation_registry_v2() -> list[dict[str, object]]:
    return [
        {
            "presentation_id": presentation_id,
            "label": label,
            "route_ids": list(route_ids),
            "status": "RETAINED_PRESENTATION",
            "visibility": visibility,
        }
        for presentation_id, label, route_ids, visibility in _PRESENTATION_ROWS_V2
    ]


def source_manifest_v2(sources: dict[str, bytes]) -> list[dict[str, str]]:
    if tuple(sources) != SOURCE_PATHS_V2 or any(type(raw) is not bytes for raw in sources.values()):
        reject_v2("SOURCE_DENOMINATOR", "source_manifest", "closed ordered sources required")
    return [{"path": path, "sha256": sha256_hex_v2(sources[path])} for path in SOURCE_PATHS_V2]


def build_registry_artifact_from_sources_v2(
    subject: str, sources: dict[str, bytes]
) -> dict[str, object]:
    if HEX_40_V2.fullmatch(subject) is None:
        reject_v2("IMPLEMENTATION_SUBJECT", "implementation_subject", "invalid commit")
    manifest = source_manifest_v2(sources)
    routes = _route_registry_v2()
    for route in routes:
        for field in ("positive_test_refs", "refusal_test_refs"):
            references = route[field]
            if type(references) is not list:
                reject_v2("EVIDENCE_REFERENCE_SHAPE", field, "references must be a list")
            for reference in references:
                validate_evidence_reference_v2(reference, sources)
    projections = {
        "app_navigation": project_app_navigation_v2(sources["tools/dex-ui/src/App.jsx"]),
        "compose": project_compose_v2(sources["docker-compose.local-testnet.yml"]),
        "ui_config": project_ui_config_v2(sources["tools/dex-ui/public/zenodex-config.json"]),
    }
    if projections != expected_source_projections_v2():
        reject_v2(
            "SOURCE_PROJECTION_SHAPE",
            "source_projections",
            "live projectors disagree with the closed semantic projection",
        )
    return {
        "authority": dict(NO_AUTHORITY_V2),
        "closed_gap": "operator_documentation_drift",
        "implementation_subject": subject,
        "nonclaims": list(_NONCLAIMS_V2),
        "presentation_registry": _presentation_registry_v2(),
        "route_registry": routes,
        "runtime_test_execution": "OUTSIDE_DETERMINISTIC_ARTIFACT",
        "schema": SCHEMA_V2,
        "source_manifest": manifest,
        "source_projections": projections,
        "source_root_sha256": sha256_hex_v2(canonical_json_bytes_v2(manifest)),
        "status": "COMPLETE_SOURCE_BOUND_OPERATOR_REFERENCE_REGISTRY",
        "vm_gates_closed": [],
    }


def _validate_header_v2(value: dict[str, object]) -> None:
    expected_fields = {
        "authority",
        "closed_gap",
        "implementation_subject",
        "nonclaims",
        "presentation_registry",
        "route_registry",
        "runtime_test_execution",
        "schema",
        "source_manifest",
        "source_projections",
        "source_root_sha256",
        "status",
        "vm_gates_closed",
    }
    if set(value) != expected_fields:
        reject_v2("ARTIFACT_SHAPE", "artifact", "closed top-level fields required")
    expected_scalars = {
        "schema": SCHEMA_V2,
        "status": "COMPLETE_SOURCE_BOUND_OPERATOR_REFERENCE_REGISTRY",
        "closed_gap": "operator_documentation_drift",
        "runtime_test_execution": "OUTSIDE_DETERMINISTIC_ARTIFACT",
    }
    for field, expected in expected_scalars.items():
        if value.get(field) != expected:
            reject_v2(field.upper(), field, "field drift")
    if value.get("authority") != NO_AUTHORITY_V2 or value.get("vm_gates_closed") != []:
        reject_v2("AUTHORITY_DRIFT", "authority", "all authority must remain NONE")
    subject = value.get("implementation_subject")
    if type(subject) is not str or HEX_40_V2.fullmatch(subject) is None:
        reject_v2("IMPLEMENTATION_SUBJECT", "implementation_subject", "invalid commit")


def _validate_routes_and_presentations_v2(value: dict[str, object]) -> None:
    routes = value.get("route_registry")
    expected_routes = _route_registry_v2()
    if type(routes) is not list or [
        row.get("route_id") if type(row) is dict else None for row in routes
    ] != list(ROUTE_IDS_V2):
        reject_v2("ROUTE_DENOMINATOR", "route_registry", "route denominator drift")
    if routes != expected_routes:
        observed = [row.get("classification") if type(row) is dict else None for row in routes]
        expected = [row["classification"] for row in expected_routes]
        if observed != expected:
            reject_v2("ROUTE_CLASSIFICATION", "route_registry", "classification drift")
        reject_v2("EVIDENCE_POLARITY", "route_registry", "evidence reference drift")
    if value.get("presentation_registry") != _presentation_registry_v2():
        reject_v2(
            "PRESENTATION_DENOMINATOR",
            "presentation_registry",
            "presentation denominator or mapping drift",
        )


def _validate_manifest_v2(value: dict[str, object]) -> None:
    manifest = value.get("source_manifest")
    if type(manifest) is not list or len(manifest) != len(SOURCE_PATHS_V2):
        reject_v2("SOURCE_MANIFEST_SHAPE", "source_manifest", "manifest denominator drift")
    normalized: list[dict[str, str]] = []
    for index, row in enumerate(manifest):
        if type(row) is not dict or set(row) != {"path", "sha256"}:
            reject_v2("SOURCE_MANIFEST_SHAPE", f"source_manifest[{index}]", "row shape")
        path = row.get("path")
        digest = row.get("sha256")
        if type(path) is not str or type(digest) is not str or HEX_64_V2.fullmatch(digest) is None:
            reject_v2("SOURCE_MANIFEST_SHAPE", f"source_manifest[{index}]", "row types")
        normalized.append({"path": path, "sha256": digest})
    if [row["path"] for row in normalized] != list(SOURCE_PATHS_V2):
        reject_v2("SOURCE_MANIFEST_SHAPE", "source_manifest", "path order drift")
    expected_root = sha256_hex_v2(canonical_json_bytes_v2(normalized))
    if value.get("source_root_sha256") != expected_root:
        reject_v2("SOURCE_MANIFEST_SHAPE", "source_root_sha256", "root mismatch")


def validate_registry_artifact_v2(artifact: object) -> None:
    if type(artifact) is not dict:
        reject_v2("ARTIFACT_SHAPE", "artifact", "root must be an object")
    value = cast(dict[str, object], artifact)
    _validate_header_v2(value)
    _validate_routes_and_presentations_v2(value)
    _validate_manifest_v2(value)
    if value.get("source_projections") != expected_source_projections_v2():
        reject_v2("SOURCE_PROJECTION_SHAPE", "source_projections", "projection drift")
    if value.get("nonclaims") != list(_NONCLAIMS_V2):
        reject_v2("NONCLAIM_SHAPE", "nonclaims", "nonclaim drift")


def build_registry_artifact_v2(root: Path) -> dict[str, object]:
    from tools.operator_surface_registry_git_v2 import build_registry_artifact_from_repo_v2

    return build_registry_artifact_from_repo_v2(root)


def build_registry_bytes_v2(root: Path) -> bytes:
    return canonical_json_bytes_v2(build_registry_artifact_v2(root))


def check_registry_v2(root: Path) -> dict[str, object]:
    from tools.operator_surface_registry_git_v2 import check_registry_from_repo_v2

    return check_registry_from_repo_v2(root)


__all__ = [
    "ARTIFACT_RELATIVE_PATH_V2",
    "CHECK_SCHEMA_V2",
    "NO_AUTHORITY_V2",
    "ROUTE_IDS_V2",
    "SCHEMA_V2",
    "SOURCE_PATHS_V2",
    "OperatorSurfaceRegistryRejectV2",
    "build_registry_artifact_from_sources_v2",
    "build_registry_artifact_v2",
    "build_registry_bytes_v2",
    "canonical_json_bytes_v2",
    "check_registry_v2",
    "decode_json_object_v2",
    "project_app_navigation_v2",
    "project_compose_v2",
    "project_ui_config_v2",
    "sha256_hex_v2",
    "source_manifest_v2",
    "validate_evidence_reference_v2",
    "validate_registry_artifact_v2",
]
