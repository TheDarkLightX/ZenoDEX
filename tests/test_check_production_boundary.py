from __future__ import annotations

from pathlib import Path

from tools.check_production_boundary import (
    audit_production_boundary,
    scan_apply_operations_exposure,
    scan_legacy_settlement_profile_literals,
    scan_unsafe_config_literals,
)

ROOT = Path(__file__).resolve().parents[1]


def test_current_production_boundary_audit_passes() -> None:
    payload = audit_production_boundary(ROOT)

    assert payload["ok"] is True
    check_ids = {check["check_id"] for check in payload["checks"]}
    assert {
        "dex_engine_defaults_fail_closed",
        "core_dex_defaults_use_strong_settlement_profile",
        "named_safe_profiles_force_production_closure",
        "nonce_free_value_moving_batch_rejected",
        "integration_validation_uses_strong_settlement_validator",
        "production_src_has_no_unsafe_dex_config_literals",
        "production_src_has_no_legacy_settlement_profile_literals",
        "direct_settlement_apply_helper_unexposed",
        "api_server_does_not_expose_direct_value_moving_core_ingress",
        "tau_testnet_dex_plugin_enters_through_dex_engine",
        "supported_runtime_doc_scopes_public_boundary",
        "public_operator_node_preflight_blocks_unsigned_testnet_mutation",
    } <= check_ids
    requirement_ids = {item["requirement_id"] for item in payload["requirements"]}
    assert {
        "value_moving_paths_use_safe_profile",
        "no_production_nonce_free_path",
        "no_legacy_settlement_validation_in_production",
        "no_require_settlement_match_false_in_production",
        "no_direct_pure_core_ingress_exposed",
    } == requirement_ids
    assert all(item["ok"] is True for item in payload["requirements"])
    safe_profile = next(
        check for check in payload["checks"]
        if check["check_id"] == "named_safe_profiles_force_production_closure"
    )
    assert '"require_uniform_batch_v3_exact_out_grid_optimality": true' in safe_profile["evidence"]


def test_unsafe_config_literal_scanner_rejects_production_overrides(tmp_path: Path) -> None:
    source = tmp_path / "unsafe.py"
    source.write_text(
        "\n".join(
            [
                "from src.integration.dex_engine import DexEngineConfig",
                "cfg = DexEngineConfig(require_settlement_match=False)",
                "cfg2 = DexEngineConfig(allow_missing_settlement=True)",
                "raw = {'require_settlement_match': False, \"allow_missing_settlement\": True}",
            ]
        ),
        encoding="utf-8",
    )

    findings = scan_unsafe_config_literals([source], root=tmp_path)
    assert [finding["rule_id"] for finding in findings] == [
        "require_settlement_match_false",
        "allow_missing_settlement_true",
        "require_settlement_match_false",
        "allow_missing_settlement_true",
    ]


def test_legacy_settlement_profile_scanner_rejects_legacy_config(tmp_path: Path) -> None:
    source = tmp_path / "legacy_profile.py"
    source.write_text(
        "\n".join(
            [
                "from src.core.dex import DexConfig",
                "cfg = DexConfig(settlement_validation='legacy')",
                "raw = {'settlement_validation': 'legacy'}",
            ]
        ),
        encoding="utf-8",
    )

    findings = scan_legacy_settlement_profile_literals([source], root=tmp_path)
    assert [finding["rule_id"] for finding in findings] == [
        "legacy_settlement_validation_profile",
        "legacy_settlement_validation_profile",
    ]


def test_apply_operations_exposure_scanner_rejects_import_and_call(tmp_path: Path) -> None:
    source = tmp_path / "unsafe_apply.py"
    source.write_text(
        "\n".join(
            [
                "from src.integration.validation import apply_operations",
                "def run():",
                "    return apply_operations(None, None, None)",
            ]
        ),
        encoding="utf-8",
    )

    findings = scan_apply_operations_exposure([source], root=tmp_path)
    assert [finding["rule_id"] for finding in findings] == [
        "legacy_apply_operations_import",
        "legacy_apply_operations_call",
    ]
