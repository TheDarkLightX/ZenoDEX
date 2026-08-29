from __future__ import annotations

import ast
import subprocess
from collections.abc import Callable
from copy import deepcopy
from pathlib import Path

import pytest

from tools.check_operator_surface_registry_v1 import check_operator_surface_registry_v1
from tools.operator_surface_registry_v1 import (
    ARTIFACT_RELATIVE_PATH_V1,
    IMPLEMENTATION_SUBJECT_COMMIT_V1,
    OperatorSurfaceRegistryRejectV1,
    canonical_json_bytes_v1,
    decode_json_object_v1,
    project_api_server_v1,
    project_compose_v1,
    project_keys_navigation_v1,
    project_lifecycle_v1,
    project_local_route_quarantine_v1,
    project_ui_config_v1,
    project_ui_runtime_guard_v1,
)

ROOT = Path(__file__).resolve().parents[1]


def _subject_source(path: str) -> bytes:
    return subprocess.run(
        ("git", "-C", str(ROOT), "show", f"{IMPLEMENTATION_SUBJECT_COMMIT_V1}:{path}"),
        check=True,
        capture_output=True,
    ).stdout


def _assert_structural_reject(
    projector: Callable[[bytes], dict[str, object]],
    mutant: bytes,
    expected_code: str,
) -> None:
    with pytest.raises(OperatorSurfaceRegistryRejectV1) as captured:
        projector(mutant)
    assert captured.value.code == expected_code


def _artifact() -> dict[str, object]:
    return decode_json_object_v1(
        (ROOT / ARTIFACT_RELATIVE_PATH_V1).read_bytes(),
        "checked-in operator registry",
    )


def _write(tmp_path: Path, value: object) -> Path:
    path = tmp_path / "mutant-registry.json"
    path.write_bytes(canonical_json_bytes_v1(value))
    return path


def _finding_code(report: dict[str, object]) -> object:
    findings = report["findings"]
    assert isinstance(findings, list)
    assert findings and isinstance(findings[0], dict)
    return findings[0]["code"]


def test_mutant_api_phrase_survives_while_direct_refusal_guard_changes() -> None:
    # Arrange
    source = _subject_source("src/integration/api_server.py")
    mutant = source.replace(
        b"if config.perps_wallet_enabled:",
        b"if False and config.perps_wallet_enabled:",
        1,
    )
    old_phrase = b"PERPS_WALLET_API_ENABLED depends on the retired Tau"
    assert old_phrase in mutant

    # Act / Assert
    _assert_structural_reject(project_api_server_v1, mutant, "PYTHON_AST_STRUCTURAL_DRIFT")


def test_mutant_local_refusal_phrase_survives_while_raise_becomes_return() -> None:
    # Arrange
    source = _subject_source("src/integration/local_route_quarantine.py")
    mutant = source.replace(
        b"raise CurrentLocalOperatorProfileBlockedV1(\n",
        b"return CurrentLocalOperatorProfileBlockedV1(\n",
        1,
    )
    assert b"current profile quarantines retired Tau value routes" in mutant

    # Act / Assert
    _assert_structural_reject(
        project_local_route_quarantine_v1,
        mutant,
        "PYTHON_AST_STRUCTURAL_DRIFT",
    )


def test_mutant_lifecycle_phrase_survives_after_active_function_returns_early() -> None:
    # Arrange
    source = _subject_source("tools/zenoctl_testnet_local/lifecycle.py")
    old = b'return refuse_current_local_operator_operation_v1("release_flow_smoke")'
    phrase = b'refuse_current_local_operator_operation_v1("release_flow_smoke")'
    mutant = source.replace(old, b"return {}\n    " + phrase, 1)
    assert phrase in mutant

    # Act / Assert
    _assert_structural_reject(project_lifecycle_v1, mutant, "PYTHON_AST_STRUCTURAL_DRIFT")


def test_mutant_compose_false_phrase_survives_while_typed_value_enables_route() -> None:
    # Arrange
    source = _subject_source("docker-compose.local-testnet.yml")
    old = b'PERPS_WALLET_API_ENABLED: "false"'
    mutant = source.replace(old, b'PERPS_WALLET_API_ENABLED: "true"', 1) + b"\n# " + old + b"\n"
    assert old in mutant

    # Act / Assert
    _assert_structural_reject(project_compose_v1, mutant, "COMPOSE_ROUTE_ENVIRONMENT")


def test_mutant_ui_config_false_string_survives_while_typed_value_enables_route() -> None:
    # Arrange
    source = _subject_source("tools/dex-ui/public/zenodex-config.json")
    config = decode_json_object_v1(source, "UI config mutant")
    config["perpsWalletUiEnabled"] = True
    config["retainedOldPhrase"] = '"perpsWalletUiEnabled": false'
    mutant = canonical_json_bytes_v1(config)
    assert b'\\"perpsWalletUiEnabled\\": false' in mutant

    # Act / Assert
    _assert_structural_reject(project_ui_config_v1, mutant, "UI_CONFIG_ROUTE_FLAGS")


def test_mutant_js_false_phrase_survives_in_comment_while_active_guard_is_true() -> None:
    # Arrange
    source = _subject_source("tools/dex-ui/src/lib/api.js")
    old = b"perpsWalletEnabled: false"
    mutant = source.replace(old, b"perpsWalletEnabled: true", 1) + b"\n// " + old + b"\n"
    assert old in mutant

    # Act / Assert
    _assert_structural_reject(project_ui_runtime_guard_v1, mutant, "JS_ROUTE_GUARD")


def test_mutant_keys_phrase_survives_in_comment_while_active_label_changes() -> None:
    # Arrange
    source = _subject_source("tools/dex-ui/src/App.jsx")
    old = b"{ id: 'governance', label: 'Keys' }"
    mutant = source.replace(old, b"{ id: 'governance', label: 'Admin' }", 1) + b"\n// " + old + b"\n"
    assert old in mutant

    # Act / Assert
    _assert_structural_reject(project_keys_navigation_v1, mutant, "JS_KEYS_PRESENTATION")


def test_python_main_globals_override_is_admitted_only_as_structural_fingerprint() -> None:
    # The AST fingerprint intentionally does not model Python's mutable global lookup.
    source = _subject_source("src/integration/api_server.py")
    mutant = source + b"\nglobals()['main'] = lambda: 0\n"

    assert project_api_server_v1(mutant)["terminal_result"] == "RETURN_2_BEFORE_SERVER_CONSTRUCTION"


def test_javascript_local_object_shadow_is_admitted_only_as_structural_fingerprint() -> None:
    # The tokenizer does not execute lexical bindings, so Object.freeze is source-bound only.
    source = _subject_source("tools/dex-ui/src/lib/api.js")
    mutant = b"const Object = { freeze: (value) => value };\n" + source

    projection = project_ui_runtime_guard_v1(mutant)

    assert projection["frozen_value_route_flags"] == {
        "perpsWalletEnabled": False,
        "zusdMonetaryWalletEnabled": False,
        "zusdTauWalletEnabled": False,
    }


def test_javascript_post_declaration_nav_tabs_mutation_is_admitted_only_as_structural_fingerprint() -> None:
    # The declaration fingerprint cannot decide the later mutable runtime value.
    source = _subject_source("tools/dex-ui/src/App.jsx")
    mutant = source + b"\nNAV_TABS[8].label = 'Admin';\n"

    projection = project_keys_navigation_v1(mutant)

    assert projection["keys_label"] == "Keys"


def test_mutant_mounted_classification_rejects_and_reports_no_authority(tmp_path: Path) -> None:
    # Arrange
    mutant = deepcopy(_artifact())
    routes = mutant["route_registry"]
    assert isinstance(routes, list)
    route = next(
        row
        for row in routes
        if isinstance(row, dict) and row.get("route_id") == "spot_ledger_api"
    )
    route["classification"] = "MOUNTED"

    # Act
    report = check_operator_surface_registry_v1(ROOT, _write(tmp_path, mutant))

    # Assert
    assert report["ok"] is False
    assert _finding_code(report) == "ROUTE_CLASSIFICATION"
    assert report["mounted_routes"] == []
    assert report["runtime_receipts"] == []
    assert report["mount_authority"] == "NONE"
    assert report["value_movement_authority"] == "NONE"


def test_report_never_claims_semantic_completeness_or_closes_o004() -> None:
    # Arrange / Act
    report = check_operator_surface_registry_v1(ROOT, ROOT / ARTIFACT_RELATIVE_PATH_V1)

    # Assert
    assert report["ok"] is True
    assert report["surface_registry_complete"] is False
    assert report["o004_status"] == "OPEN_BOUNDED_PARTIAL_RESEARCH_EVIDENCE"
    assert report["p2_split_debt"] == "DEFERRED_SINGLE_MODULE_HOTSPOT"


def test_runtime_validation_module_contains_no_python_assert() -> None:
    # Arrange
    source = (ROOT / "tools/operator_surface_registry_v1.py").read_text(encoding="utf-8")

    # Act
    tree = ast.parse(source)

    # Assert
    assert not any(isinstance(node, ast.Assert) for node in ast.walk(tree))
