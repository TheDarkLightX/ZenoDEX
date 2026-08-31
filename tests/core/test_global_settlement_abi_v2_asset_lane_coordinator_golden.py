"""Source-generation checks for the V2 asset-lane coordinator fixture."""

from __future__ import annotations

import hashlib
import json
from dataclasses import replace
from typing import cast

import pytest

import src.core.asset_lane_coordinator_v2 as coordinator_module
import tools.render_global_settlement_abi_v2_asset_lane_coordinator_golden as renderer
from src.core.asset_lane_coordinator_v2 import (
    AssetLaneCoordinatorRejectCodeV2,
    AssetLaneRejectedV2,
    AssetLaneRouteV2,
    transition_asset_lane_v2,
)
from src.core.asset_transfer_types_v2 import (
    AssetTransferAcceptedV2,
    AssetTransferRejectCodeV2,
)
from src.core.global_settlement_types_v2 import canonical_global_bytes_v2
from src.core.managed_asset_lifecycle_types_v2 import (
    ManagedAssetLifecycleRejectCodeV2,
)
from tools.render_global_settlement_abi_v2_asset_lane_coordinator_golden import (
    EXPECTED_PLAN_SHA256_V2,
    FIXTURE_PATH_V2,
    build_vectors_v2,
    render_vectors_v2,
)


def _mapping(value: object) -> dict[str, object]:
    return cast(dict[str, object], value)


def test_committed_asset_lane_coordinator_fixture_matches_renderer() -> None:
    fixture_text = FIXTURE_PATH_V2.read_text(encoding="utf-8")

    assert fixture_text == render_vectors_v2()
    assert json.loads(fixture_text) == build_vectors_v2()


def test_fixture_scope_code_registries_and_nonclaims_are_exact() -> None:
    fixture = build_vectors_v2()

    assert fixture["authority"] == "NONE"
    assert fixture["profile_authentication"] == "SHADOW"
    assert fixture["plan_sha256"] == EXPECTED_PLAN_SHA256_V2
    assert fixture["limits"] == {
        "max_assets": 256,
        "max_balance_rows": 4_096,
        "max_state_canonical_bytes": 1_048_576,
    }
    assert fixture["coordinator_reject_codes"] == [
        code.value for code in AssetLaneCoordinatorRejectCodeV2
    ]
    assert fixture["transfer_reject_codes"] == [
        code.value for code in AssetTransferRejectCodeV2
    ]
    assert fixture["managed_reject_codes"] == [
        code.value for code in ManagedAssetLifecycleRejectCodeV2
    ]
    assert tuple(_mapping(fixture["accepted"])) == ("managed_issue", "transfer")
    assert tuple(_mapping(fixture["rejections"])) == (
        "01_registry_binding_precedes_transfer_leaf",
        "02_transfer_leaf_unauthorized",
        "03_managed_leaf_authorization_root",
    )
    assert fixture["nonclaims"] == [
        "no RISC0 circuit or receipt",
        "no runtime mount, migration, or UI",
        "no settlement, release, or production authority",
    ]


def test_every_fixture_vector_has_exact_canonical_bytes_and_root_shape() -> None:
    fixture = build_vectors_v2()
    case_groups = (
        _mapping(fixture["accepted"]),
        _mapping(fixture["rejections"]),
    )

    for cases in case_groups:
        for case_value in cases.values():
            vectors = _mapping(_mapping(case_value)["vectors"])
            for vector_value in vectors.values():
                vector = _mapping(vector_value)
                raw = canonical_global_bytes_v2(vector["canonical"])
                assert hashlib.sha256(raw).hexdigest() == vector["canonical_bytes_sha256"]
                expected_root = vector["expected_root"]
                assert isinstance(expected_root, str)
                assert len(expected_root) == 66


def test_python_coordinator_rejects_a_forged_leaf_binding_as_an_exact_noop(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    state = renderer._state()
    command = renderer._transfer_command()
    context = renderer._context(
        command,
        subject_id="alice",
        grant_root=renderer._root(9),
        nonce=1,
    )
    leaf = coordinator_module.transition_asset_transfer_v2(
        context.transfer_context(),
        state.transfer_leaf_state(),
        command,
    )
    assert isinstance(leaf, AssetTransferAcceptedV2)
    object.__setattr__(
        leaf,
        "_module_journal",
        replace(leaf.module_journal, chain_id="forged-chain"),
    )
    monkeypatch.setattr(
        coordinator_module,
        "transition_asset_transfer_v2",
        lambda leaf_context, leaf_state, leaf_command: leaf,
    )

    result = transition_asset_lane_v2(context, state, command)

    assert isinstance(result, AssetLaneRejectedV2)
    assert result.route is AssetLaneRouteV2.TRANSFER
    assert result.code is AssetLaneCoordinatorRejectCodeV2.CANDIDATE_BINDING_MISMATCH
    assert result.pre_state_root == result.post_state_root == state.state_root
    assert result.effects.is_empty
