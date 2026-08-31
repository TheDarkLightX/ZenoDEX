"""Boundary and count-before-deep-validation evidence for shared V2 limits."""

from __future__ import annotations

from typing import cast

import pytest

from src.core.asset_lane_state_v2 import AssetLaneStateV2
from src.core.asset_origin_registry_types_v2 import (
    AssetOriginKindV2,
    AssetOriginRecordV2,
    AssetOriginRegistrationPolicyV2,
    AssetOriginRegistryStateV2,
)
from src.core.asset_origin_registry_v2 import (
    asset_transfer_policy_root_v2,
    managed_asset_policy_root_v2,
)
from src.core.asset_transfer_types_v2 import (
    ACCOUNT_CUSTODY_DOMAIN_V2,
    ASSET_ATOM_DECIMALS_V2,
    ASSET_TRANSFER_MODULE_SCHEMA_V2,
    AssetClassV2,
    AssetTransferPolicyV2,
    AssetTransferStateV2,
)
from src.core.global_economic_proof_v2 import EconomicCommandOccurrenceV2
from src.core.global_economic_state_effect_refinement_v2 import (
    GlobalEconomicStateEffectRefinementCandidateV2,
    refine_global_economic_state_effects_v2,
)
from src.core.global_economic_state_v2 import GlobalEconomicStateV2, LaneStateRootV2
from src.core.global_settlement_effect_plan_v2 import (
    MAX_OCCURRENCE_CONSUMPTIONS_PER_PLAN_V2,
)
from src.core.global_settlement_resource_limits_v2 import (
    MAX_ASSETS_PER_ASSET_STATE_V2,
    MAX_BALANCE_ROWS_PER_ASSET_STATE_V2,
    MAX_CONSUMED_OBJECT_IDS_PER_OCCURRENCE_V2,
    MAX_CONSUMED_OCCURRENCES_PER_REFINEMENT_V2,
    MAX_ECONOMIC_COMMAND_OCCURRENCE_OBJECT_IDS_V2,
    MAX_GLOBAL_ECONOMIC_REFINEMENT_CONSUMED_OCCURRENCES_V2,
    MAX_ROOTABLE_ASSET_STATE_ASSETS_V2,
    MAX_ROOTABLE_ASSET_STATE_BALANCE_ROWS_V2,
    MAX_ROOTABLE_ASSET_STATE_CANONICAL_BYTES_V2,
    require_rootable_asset_state_bytes_v2,
)
from src.core.global_settlement_types_v2 import (
    ALL_LANE_IDS_V2,
    ZERO_ROOT_V2,
    AssetSupplyV2,
    EconomicAmountV2,
    GlobalEconomicEffectPlanV2,
    GlobalOracleOccurrencePlanV2,
    GlobalTerminalObligationPlanV2,
    LaneIdV2,
    canonical_global_bytes_v2,
)
from src.core.managed_asset_lifecycle_state_v2 import ManagedAssetLifecycleStateV2
from src.core.managed_asset_lifecycle_types_v2 import ManagedAssetLifecyclePolicyV2


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _asset(index: int) -> str:
    return f"asset-{index:03d}"


def _transfer_policy(index: int) -> AssetTransferPolicyV2:
    return AssetTransferPolicyV2(
        asset=_asset(index),
        fee_owner="fee-owner",
        transfer_fee_atoms=0,
        enabled=True,
        asset_class=AssetClassV2.REGISTERED_ORDINARY_TOKEN,
        asset_origin_root=_root(1_000 + index),
        atom_decimals=ASSET_ATOM_DECIMALS_V2,
    )


def _managed_policy(index: int) -> ManagedAssetLifecyclePolicyV2:
    return ManagedAssetLifecyclePolicyV2(
        asset=_asset(index),
        asset_class=AssetClassV2.REGISTERED_ORDINARY_TOKEN,
        asset_origin_root=_root(1_000 + index),
        atom_decimals=ASSET_ATOM_DECIMALS_V2,
        issue_authority_subject="issuer",
        issue_authorization_root=_root(2_000 + index),
        burn_authorization_root=_root(3_000 + index),
        enabled=True,
    )


def _policy_tables(
    count: int,
) -> tuple[tuple[AssetTransferPolicyV2, ...], tuple[ManagedAssetLifecyclePolicyV2, ...]]:
    return (
        tuple(_transfer_policy(index) for index in range(count)),
        tuple(_managed_policy(index) for index in range(count)),
    )


def _registry(
    count: int,
    transfer: tuple[AssetTransferPolicyV2, ...] | None = None,
    managed: tuple[ManagedAssetLifecyclePolicyV2, ...] | None = None,
) -> AssetOriginRegistryStateV2:
    if transfer is None or managed is None:
        transfer, managed = _policy_tables(count)
    return AssetOriginRegistryStateV2(
        module_release_id=_root(10),
        policy=AssetOriginRegistrationPolicyV2(
            authority_subject="governance",
            authority_grant_root=_root(11),
            allow_native=True,
            allow_tau_originated=True,
        ),
        assets=tuple(
            AssetOriginRecordV2(
                asset=_asset(index),
                origin_kind=AssetOriginKindV2.TAU_ORIGINATED,
                origin_root=_root(1_000 + index),
                transfer_policy_root=asset_transfer_policy_root_v2(transfer[index]),
                issue_policy_root=managed_asset_policy_root_v2(managed[index]),
                decimals=ASSET_ATOM_DECIMALS_V2,
                asset_class=AssetClassV2.REGISTERED_ORDINARY_TOKEN,
            )
            for index in range(count)
        ),
    )


def _supplies(count: int, amount_atoms: int = 0) -> tuple[AssetSupplyV2, ...]:
    return tuple(AssetSupplyV2(_asset(index), amount_atoms) for index in range(count))


def _empty_candidate() -> GlobalEconomicStateEffectRefinementCandidateV2:
    state = GlobalEconomicStateV2(
        chain_id="resource-bound-probe",
        deployment_root=_root(900),
        writer_epoch=1,
        height=1,
        profile_root=_root(901),
        lane_roots=tuple(
            LaneStateRootV2(
                lane,
                _root(index + 920),
                lane is not LaneIdV2.EXTERNAL_CUSTODY,
                _root(index + 940),
            )
            for index, lane in enumerate(ALL_LANE_IDS_V2)
        ),
        history_root=ZERO_ROOT_V2,
    )
    return GlobalEconomicStateEffectRefinementCandidateV2(
        state,
        state,
        GlobalEconomicEffectPlanV2.empty(),
        (),
        GlobalTerminalObligationPlanV2.empty(),
        GlobalOracleOccurrencePlanV2.empty(),
    )


def _occurrence_with_object_ids(count: int) -> EconomicCommandOccurrenceV2:
    return EconomicCommandOccurrenceV2(
        chain_id="resource-bound-probe",
        deployment_root=_root(910),
        height=1,
        tx_index=0,
        op_index=0,
        command_kind="resource-bound-probe",
        command_body_hash=_root(911),
        route_release_id=_root(912),
        subject_id="alice",
        grant_root=_root(913),
        nonce=1,
        profile_root=_root(914),
        pre_state_root=_root(915),
        consumed_object_ids=tuple(f"object-{index:03d}" for index in range(count)),
    )


def test_primary_shared_limits_and_compatibility_aliases_are_exact() -> None:
    assert MAX_ASSETS_PER_ASSET_STATE_V2 == MAX_ROOTABLE_ASSET_STATE_ASSETS_V2 == 256
    assert MAX_BALANCE_ROWS_PER_ASSET_STATE_V2 == MAX_ROOTABLE_ASSET_STATE_BALANCE_ROWS_V2 == 4_096
    assert MAX_ROOTABLE_ASSET_STATE_CANONICAL_BYTES_V2 == 1_048_576
    assert MAX_CONSUMED_OBJECT_IDS_PER_OCCURRENCE_V2 == 64
    assert MAX_CONSUMED_OCCURRENCES_PER_REFINEMENT_V2 == 64
    assert MAX_ECONOMIC_COMMAND_OCCURRENCE_OBJECT_IDS_V2 == 64
    assert MAX_GLOBAL_ECONOMIC_REFINEMENT_CONSUMED_OCCURRENCES_V2 == 64
    assert MAX_CONSUMED_OBJECT_IDS_PER_OCCURRENCE_V2 == MAX_OCCURRENCE_CONSUMPTIONS_PER_PLAN_V2
    assert MAX_CONSUMED_OCCURRENCES_PER_REFINEMENT_V2 == MAX_OCCURRENCE_CONSUMPTIONS_PER_PLAN_V2


@pytest.mark.parametrize("count", (63, 64))
def test_occurrence_object_id_boundary_accepts_63_and_64(count: int) -> None:
    occurrence = _occurrence_with_object_ids(count)

    assert len(occurrence.consumed_object_ids) == count


def test_occurrence_object_id_65_rejects_before_deep_item_validation() -> None:
    candidate = _occurrence_with_object_ids(64)
    poisoned_ids = tuple(object() for _ in range(65))

    with pytest.raises(ValueError, match="exceeds its 64-item ceiling"):
        EconomicCommandOccurrenceV2(
            candidate.chain_id,
            candidate.deployment_root,
            candidate.height,
            candidate.tx_index,
            candidate.op_index,
            candidate.command_kind,
            candidate.command_body_hash,
            candidate.route_release_id,
            candidate.subject_id,
            candidate.grant_root,
            candidate.nonce,
            candidate.profile_root,
            candidate.pre_state_root,
            poisoned_ids,  # type: ignore[arg-type]
        )

    with pytest.raises(TypeError, match="must be a string"):
        EconomicCommandOccurrenceV2(
            candidate.chain_id,
            candidate.deployment_root,
            candidate.height,
            candidate.tx_index,
            candidate.op_index,
            candidate.command_kind,
            candidate.command_body_hash,
            candidate.route_release_id,
            candidate.subject_id,
            candidate.grant_root,
            candidate.nonce,
            candidate.profile_root,
            candidate.pre_state_root,
            tuple(object() for _ in range(64)),  # type: ignore[misc]
        )


@pytest.mark.parametrize("count", (255, 256))
def test_asset_table_boundary_accepts_255_and_256_across_all_rootable_states(
    count: int,
) -> None:
    transfer, managed = _policy_tables(count)
    registry = _registry(count, transfer, managed)
    supplies = _supplies(count)

    transfer_state = AssetTransferStateV2(_root(10), transfer, (), supplies)
    managed_state = ManagedAssetLifecycleStateV2(_root(10), managed, (), supplies)
    asset_lane_state = AssetLaneStateV2(
        _root(10),
        registry,
        transfer,
        managed,
        (),
        supplies,
    )

    assert len(registry.assets) == count
    assert len(transfer_state.policies) == count
    assert len(managed_state.policies) == count
    assert len(asset_lane_state.transfer_policies) == count


def test_257_poisoned_asset_rows_fail_before_snapshot_or_deep_validation() -> None:
    poisoned = tuple(object() for _ in range(257))
    registry = _registry(0)

    with pytest.raises(ValueError, match="asset transfer policies exceeds its 256-item ceiling"):
        AssetTransferStateV2(_root(10), poisoned, (), ())  # type: ignore[arg-type]
    with pytest.raises(ValueError, match="managed asset policies exceeds its 256-item ceiling"):
        ManagedAssetLifecycleStateV2(_root(10), poisoned, (), ())  # type: ignore[arg-type]
    with pytest.raises(ValueError, match="asset origin registry rows exceeds its 256-item ceiling"):
        AssetOriginRegistryStateV2(_root(10), registry.policy, poisoned)  # type: ignore[arg-type]
    with pytest.raises(
        ValueError, match="asset lane transfer policies exceeds its 256-item ceiling"
    ):
        AssetLaneStateV2(_root(10), registry, poisoned, (), (), ())  # type: ignore[arg-type]


def _balance_rows(count: int, *, asset: str = "asset-000") -> tuple[EconomicAmountV2, ...]:
    return tuple(
        EconomicAmountV2(
            f"owner-{index:04d}",
            asset,
            ACCOUNT_CUSTODY_DOMAIN_V2,
            1,
        )
        for index in range(count)
    )


@pytest.mark.parametrize("count", (4_095, 4_096))
def test_balance_row_boundary_accepts_4095_and_4096(count: int) -> None:
    transfer_policies = (_transfer_policy(0),)
    managed_policies = (_managed_policy(0),)
    registry = _registry(1, transfer_policies, managed_policies)
    balances = _balance_rows(count)
    supplies = (AssetSupplyV2("asset-000", count),)
    transfer_state = AssetTransferStateV2(
        _root(10),
        transfer_policies,
        balances,
        supplies,
    )
    managed_state = ManagedAssetLifecycleStateV2(
        _root(10),
        managed_policies,
        balances,
        supplies,
    )
    asset_lane_state = AssetLaneStateV2(
        _root(10),
        registry,
        transfer_policies,
        managed_policies,
        balances,
        supplies,
    )

    assert len(transfer_state.balances) == count
    assert len(managed_state.balances) == count
    assert len(asset_lane_state.balances) == count


def test_4097_poisoned_balance_rows_fail_before_deep_validation_for_every_state() -> None:
    poisoned = tuple(object() for _ in range(4_097))
    registry = _registry(0)

    with pytest.raises(ValueError, match="asset transfer balances exceeds its 4096-item ceiling"):
        AssetTransferStateV2(_root(10), (), poisoned, ())
    with pytest.raises(ValueError, match="managed asset balances exceeds its 4096-item ceiling"):
        ManagedAssetLifecycleStateV2(_root(10), (), poisoned, ())
    with pytest.raises(ValueError, match="asset lane balances exceeds its 4096-item ceiling"):
        AssetLaneStateV2(_root(10), registry, (), (), poisoned, ())


@pytest.mark.parametrize("count", (63, 64))
def test_refinement_occurrence_boundary_reaches_deep_validation_after_count(
    count: int,
) -> None:
    candidate = _empty_candidate()
    object.__setattr__(candidate, "_consumed_occurrences", tuple(object() for _ in range(count)))

    with pytest.raises(TypeError):
        refine_global_economic_state_effects_v2(candidate)


def test_refinement_65_occurrences_rejects_before_replace_or_occurrence_traversal() -> None:
    candidate = _empty_candidate()
    object.__setattr__(candidate, "_consumed_occurrences", tuple(object() for _ in range(65)))

    with pytest.raises(ValueError, match="consumed occurrences exceeds its 64-item ceiling"):
        refine_global_economic_state_effects_v2(candidate)


def test_candidate_constructor_65_poisoned_occurrences_fails_before_item_validation() -> None:
    poisoned_occurrences = tuple(object() for _ in range(65))

    with pytest.raises(ValueError, match="consumed occurrences exceeds its 64-item ceiling"):
        GlobalEconomicStateEffectRefinementCandidateV2(
            cast(GlobalEconomicStateV2, object()),
            cast(GlobalEconomicStateV2, object()),
            cast(GlobalEconomicEffectPlanV2, object()),
            poisoned_occurrences,  # type: ignore[arg-type]
            cast(GlobalTerminalObligationPlanV2, object()),
            cast(GlobalOracleOccurrencePlanV2, object()),
        )


@pytest.mark.parametrize("count", (63, 64))
def test_candidate_constructor_occurrence_boundary_accepts_63_and_64(count: int) -> None:
    template = _occurrence_with_object_ids(0)
    source = _empty_candidate()
    candidate = GlobalEconomicStateEffectRefinementCandidateV2(
        source.pre_state,
        source.post_state,
        source.effect_plan,
        tuple(template for _ in range(count)),
        source.terminal_plan,
        source.oracle_plan,
    )

    assert len(candidate.consumed_occurrences) == count


def test_exact_one_mebibyte_helper_boundary_and_actual_oversized_state() -> None:
    require_rootable_asset_state_bytes_v2(
        b"x" * MAX_ROOTABLE_ASSET_STATE_CANONICAL_BYTES_V2,
        name="test bytes",
    )
    with pytest.raises(ValueError, match="1048576-byte ceiling"):
        require_rootable_asset_state_bytes_v2(
            b"x" * (MAX_ROOTABLE_ASSET_STATE_CANONICAL_BYTES_V2 + 1),
            name="test bytes",
        )

    asset = "asset-" + "a" * 154
    policy = AssetTransferPolicyV2(
        asset=asset,
        fee_owner="fee-owner-" + "f" * 150,
        transfer_fee_atoms=0,
        enabled=True,
        asset_class=AssetClassV2.REGISTERED_ORDINARY_TOKEN,
        asset_origin_root=_root(2_000),
        atom_decimals=ASSET_ATOM_DECIMALS_V2,
    )
    balances = tuple(
        EconomicAmountV2(
            f"owner-{index:04d}-" + "o" * 149,
            asset,
            ACCOUNT_CUSTODY_DOMAIN_V2,
            1,
        )
        for index in range(MAX_BALANCE_ROWS_PER_ASSET_STATE_V2)
    )
    state_shape = {
        "schema": ASSET_TRANSFER_MODULE_SCHEMA_V2,
        "module_release_id": _root(10),
        "policies": (policy,),
        "balances": balances,
        "supplies": (AssetSupplyV2(asset, len(balances)),),
    }
    assert len(canonical_global_bytes_v2(state_shape)) > (
        MAX_ROOTABLE_ASSET_STATE_CANONICAL_BYTES_V2
    )

    with pytest.raises(ValueError, match="asset transfer state exceeds its 1048576-byte ceiling"):
        AssetTransferStateV2(
            _root(10),
            (policy,),
            balances,
            (AssetSupplyV2(asset, len(balances)),),
        )
