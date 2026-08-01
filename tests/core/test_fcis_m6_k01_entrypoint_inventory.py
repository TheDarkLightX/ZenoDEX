"""K01 source-bound value-moving entrypoint inventory tests."""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from experiments.fcis_m6_k01_entrypoint_inventory_check import run_checks
from src.core.fcis_m6_k01_entrypoint_inventory import (
    FCISM6K01Error,
    K01CommitRequirementV1,
    K01EntrypointV1,
    K01LegacyStatusV1,
    K01ReachabilityV1,
    K01SurfaceKindV1,
)
from tools.build_fcis_m6_k01_entrypoint_inventory import (
    DEFAULT_CONFIG_PATH,
    DEFAULT_OUTPUT_PATH,
    _load_inventory,
    build_payload,
)

_ROOT = Path(__file__).resolve().parents[2]


def test_k01_checker_passes_the_regenerated_vector() -> None:
    run_checks()


def test_k01_vector_is_canonical_json_and_has_required_fields() -> None:
    payload = json.loads((_ROOT / DEFAULT_OUTPUT_PATH).read_text(encoding="utf-8"))
    assert set(payload) == {
        "schema",
        "profile_id",
        "configuration_path",
        "configuration_sha256",
        "coverage_status",
        "deployment_source_paths",
        "sources",
        "entrypoints",
        "coverage_notes",
        "entrypoint_inventory_root",
    }
    assert payload == build_payload(_ROOT / DEFAULT_CONFIG_PATH)


def test_k01_entrypoints_are_canonically_ordered_and_source_bound() -> None:
    inventory = _load_inventory(_ROOT / DEFAULT_CONFIG_PATH)
    assert tuple(item.publisher_id for item in inventory.entrypoints) == tuple(
        sorted(
            (item.publisher_id for item in inventory.entrypoints),
            key=lambda item: item.encode("utf-8"),
        )
    )
    source_paths = {item.path for item in inventory.sources}
    assert all(
        set(entrypoint.source_paths).issubset(source_paths) for entrypoint in inventory.entrypoints
    )


def test_k01_rejects_proof_verifier_value_movement() -> None:
    with pytest.raises(FCISM6K01Error, match="proof-only"):
        K01EntrypointV1(
            publisher_id="proof_verifier",
            kind=K01SurfaceKindV1.PROOF_VERIFIER,
            symbol_path="src/integration/proof_verifier.py",
            caller="proof admission callback",
            input_type="proof bytes",
            state_effect_touched="verification result",
            required_anf_commit_port_call=K01CommitRequirementV1.PROOF_VERIFIER_ONLY_NO_VALUE_WRITE,
            legacy_status=K01LegacyStatusV1.NOT_VALUE_MOVING,
            runtime_reachability_evidence=K01ReachabilityV1.PROOF_INPUT_ONLY,
            value_moving=True,
            authority_sink=False,
            source_paths=("src/integration/proof_verifier.py",),
        )


def test_k01_rejects_legacy_path_without_post_switch_rejection() -> None:
    with pytest.raises(FCISM6K01Error, match="legacy path"):
        K01EntrypointV1(
            publisher_id="legacy_fcis_runtime",
            kind=K01SurfaceKindV1.LEGACY_RUNTIME,
            symbol_path="src/core/fcis_legacy_refinement.py:evaluate_refinement_v1",
            caller="legacy dispatcher",
            input_type="legacy observation pair",
            state_effect_touched="legacy state and receipts",
            required_anf_commit_port_call=K01CommitRequirementV1.ANF_VERIFIED_ATOMIC_PUBLICATION_PORT,
            legacy_status=K01LegacyStatusV1.LEGACY_PATH,
            runtime_reachability_evidence=K01ReachabilityV1.LEGACY_REACHABILITY_UNVERIFIED,
            value_moving=True,
            authority_sink=True,
            source_paths=("src/core/fcis_legacy_refinement.py",),
        )
