from __future__ import annotations

from copy import deepcopy
from pathlib import Path

import pytest

from tools import operator_surface_registry_v2 as registry

ROOT = Path(__file__).resolve().parents[1]


def _registry() -> dict[str, object]:
    # The core must be usable before the final Stage B artifact is written.
    return registry.build_registry_artifact_v2(ROOT)


def _reject_artifact(mutant: dict[str, object], code: str) -> None:
    with pytest.raises(registry.OperatorSurfaceRegistryRejectV2) as captured:
        registry.validate_registry_artifact_v2(mutant)
    assert captured.value.code == code


def test_duplicate_json_key_mutant_survives_legacy_phrase_search_but_v2_rejects() -> None:
    raw = (
        b'{"perpsWalletUiEnabled":false,"allowDemoMode":false,'
        b'"perpsWalletUiEnabled":true,"zusdTauWalletUiEnabled":false,'
        b'"zusdMonetaryWalletUiEnabled":false}'
    )
    assert b'"perpsWalletUiEnabled":false' in raw
    with pytest.raises(registry.OperatorSurfaceRegistryRejectV2) as captured:
        registry.project_ui_config_v2(raw)
    assert captured.value.code == "JSON_DUPLICATE_KEY"


def test_route_reclassification_and_authority_promotion_are_rejected() -> None:
    mutant = deepcopy(_registry())
    routes = mutant["route_registry"]
    assert type(routes) is list
    routes[0]["classification"] = "QUARANTINED"
    _reject_artifact(mutant, "ROUTE_CLASSIFICATION")

    mutant = deepcopy(_registry())
    authority = mutant["authority"]
    assert type(authority) is dict
    authority["production"] = "MOUNTED"
    _reject_artifact(mutant, "AUTHORITY_DRIFT")


def test_missing_or_extra_presentation_is_rejected() -> None:
    mutant = deepcopy(_registry())
    presentations = mutant["presentation_registry"]
    assert type(presentations) is list
    presentations.pop()
    _reject_artifact(mutant, "PRESENTATION_DENOMINATOR")

    mutant = deepcopy(_registry())
    presentations = mutant["presentation_registry"]
    assert type(presentations) is list
    presentations.append(deepcopy(presentations[0]))
    _reject_artifact(mutant, "PRESENTATION_DENOMINATOR")


def test_wrong_evidence_polarity_and_duplicate_ast_node_are_rejected() -> None:
    mutant = deepcopy(_registry())
    routes = mutant["route_registry"]
    assert type(routes) is list
    routes[0]["refusal_test_refs"] = [
        {
            "path": "tests/integration/test_dex_ui_live_bridge.py",
            "node_id": "test_live_node_serves_ui_pools_and_accepts_ui_swap",
            "evidence_kind": "refusal",
        }
    ]
    _reject_artifact(mutant, "EVIDENCE_POLARITY")

    sources = {"test_duplicate.py": b"def test_same():\n    pass\ndef test_same():\n    pass\n"}
    with pytest.raises(registry.OperatorSurfaceRegistryRejectV2) as captured:
        registry.validate_evidence_reference_v2(
            {"path": "test_duplicate.py", "node_id": "test_same", "evidence_kind": "positive"},
            sources,
        )
    assert captured.value.code == "EVIDENCE_AST_NODE"


def test_navigation_projector_rejects_missing_importer_and_render_branch() -> None:
    source = (ROOT / "tools/dex-ui/src/App.jsx").read_bytes()
    missing_importer = source.replace(
        b"  governance: () => import('./components/PerpsGovernanceSurface.jsx'),\n",
        b"",
        1,
    )
    with pytest.raises(registry.OperatorSurfaceRegistryRejectV2) as captured:
        registry.project_app_navigation_v2(missing_importer)
    assert captured.value.code == "JS_NAV_IMPORTER_SET"

    missing_render = source.replace(
        b"          {activeTab === 'governance' && (\n",
        b"          {false && (\n",
        1,
    )
    with pytest.raises(registry.OperatorSurfaceRegistryRejectV2) as captured:
        registry.project_app_navigation_v2(missing_render)
    assert captured.value.code == "JS_NAV_RENDER_SET"


def test_source_manifest_and_canonicalization_mutants_are_rejected() -> None:
    artifact = _registry()
    manifest = artifact["source_manifest"]
    assert type(manifest) is list
    manifest[0]["sha256"] = "0" * 64
    _reject_artifact(artifact, "SOURCE_MANIFEST_SHAPE")

    encoded = registry.canonical_json_bytes_v2(_registry())
    assert encoded == registry.canonical_json_bytes_v2(
        registry.decode_json_object_v2(encoded, "registry")
    )


def test_projection_and_nonclaim_mutants_are_rejected() -> None:
    mutant = deepcopy(_registry())
    projections = mutant["source_projections"]
    assert type(projections) is dict
    navigation = projections["app_navigation"]
    assert type(navigation) is dict
    render_ids = navigation["render_ids"]
    assert type(render_ids) is list
    render_ids.pop()
    _reject_artifact(mutant, "SOURCE_PROJECTION_SHAPE")

    mutant = deepcopy(_registry())
    nonclaims = mutant["nonclaims"]
    assert type(nonclaims) is list
    nonclaims.append("This mutation attempts to broaden the claim.")
    _reject_artifact(mutant, "NONCLAIM_SHAPE")
