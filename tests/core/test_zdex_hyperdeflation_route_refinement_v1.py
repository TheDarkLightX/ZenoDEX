from __future__ import annotations

from dataclasses import replace
from typing import Any, cast

import pytest

from src.core.global_settlement_types_v1 import MAX_ATOMS_V1
from src.core.zdex_hyperdeflation_route_refinement_v1 import (
    ZDEXBurnLeafProjectionV1,
    refine_zdex_burn_leaf_v1,
)
from src.core.zdex_hyperdeflation_v1 import (
    ZDEXAmountBucketV1,
    ZDEXBurnRouteContextV1,
    ZDEXHyperdeflationPolicyV1,
    ZDEXPurchaseAndBurnAcceptedV1,
    ZDEXPurchaseAndBurnCommandV1,
    ZDEXSupplyStateV1,
    transition_zdex_purchase_and_burn_v1,
)
from src.core.zdex_purchase_burn_effects_v1 import (
    burn_effects_v1,
    purchase_effects_v1,
)
from src.core.zdex_purchase_burn_route_types_v1 import (
    ZDEXAMMPurchaseJournalV1,
)


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _policy() -> ZDEXHyperdeflationPolicyV1:
    return ZDEXHyperdeflationPolicyV1(
        asset_id=_root(1),
        retained_numerator=9,
        retained_denominator=10,
        maximum_decimals=64,
        maximum_decimal_step=8,
    )


def _purchase(policy: ZDEXHyperdeflationPolicyV1) -> ZDEXAMMPurchaseJournalV1:
    draft = ZDEXAMMPurchaseJournalV1(
        chain_id="tau-testnet",
        deployment_root=_root(10),
        profile_root=_root(11),
        writer_epoch=7,
        route_release_id=_root(2),
        command_occurrence_id=_root(12),
        spot_module_release_id=_root(13),
        issue_burn_policy_root=policy.policy_root,
        buyback_budget_occurrence_root=_root(14),
        quote_asset_id=_root(15),
        zdex_asset_id=policy.asset_id,
        quote_source_bucket_id="protocol:buyback:quote",
        quote_pool_bucket_id="pool:quote",
        zdex_pool_bucket_id="pool:zdex",
        burn_bucket_id="route:buyburn:source",
        quote_amount_in_atoms=50,
        purchased_zdex_atoms=100,
        quote_source_pre_atoms=1000,
        quote_source_post_atoms=950,
        quote_pool_pre_atoms=200,
        quote_pool_post_atoms=250,
        zdex_pool_pre_atoms=600,
        zdex_pool_post_atoms=500,
        burn_bucket_pre_atoms=0,
        burn_bucket_post_atoms=100,
        quote_owned_atoms=1200,
        quote_supply_atoms=2000,
        zdex_owned_atoms=1000,
        zdex_supply_atoms=1000,
        pre_spot_lane_root=_root(16),
        post_spot_lane_root=_root(17),
        effect_plan_root=_root(18),
    )
    return replace(draft, effect_plan_root=purchase_effects_v1(draft).effect_plan_root)


def _accepted(
    policy: ZDEXHyperdeflationPolicyV1,
    purchase: ZDEXAMMPurchaseJournalV1,
    *,
    source_atoms: int = 100,
    burned_atoms: int | None = None,
    checked_supply_atoms: int | None = None,
) -> ZDEXPurchaseAndBurnAcceptedV1:
    checked_burn_atoms = (
        purchase.purchased_zdex_atoms if burned_atoms is None else burned_atoms
    )
    live_supply_atoms = (
        purchase.zdex_supply_atoms
        if checked_supply_atoms is None
        else checked_supply_atoms
    )
    holder_atoms = live_supply_atoms - source_atoms
    state = ZDEXSupplyStateV1(
        asset_id=policy.asset_id,
        policy_root=policy.policy_root,
        decimals=8,
        precision_epoch=0,
        live_supply_atoms=live_supply_atoms,
        buckets=(
            ZDEXAmountBucketV1(purchase.burn_bucket_id, source_atoms),
            ZDEXAmountBucketV1("wallet:alice", holder_atoms),
        ),
        burn_budget_epoch=5,
        remaining_epoch_burn_cap_atoms=100,
    )
    context = ZDEXBurnRouteContextV1(
        route_release_id=purchase.route_release_id,
        policy_root=policy.policy_root,
        purchase_occurrence_root=purchase.journal_root,
        burn_source_bucket_id=purchase.burn_bucket_id,
        purchased_zdex_atoms=checked_burn_atoms,
        source_reserve_floor_atoms=0,
        remaining_epoch_burn_cap_atoms=MAX_ATOMS_V1,
        route_safe_output_cap_atoms=MAX_ATOMS_V1,
        burn_budget_epoch=state.burn_budget_epoch,
    )
    command = ZDEXPurchaseAndBurnCommandV1(
        expected_pre_state_root=state.state_root,
        expected_precision_epoch=state.precision_epoch,
        expected_purchase_occurrence_root=purchase.journal_root,
        source_bucket_id=purchase.burn_bucket_id,
        purchased_zdex_atoms=checked_burn_atoms,
    )
    result = transition_zdex_purchase_and_burn_v1(policy, state, context, command)
    assert type(result) is ZDEXPurchaseAndBurnAcceptedV1
    return result


def _fixture() -> tuple[
    ZDEXHyperdeflationPolicyV1,
    ZDEXAMMPurchaseJournalV1,
    ZDEXPurchaseAndBurnAcceptedV1,
]:
    policy = _policy()
    purchase = _purchase(policy)
    return policy, purchase, _accepted(policy, purchase)


def test_refinement_derives_exact_burn_journal_and_effects() -> None:
    # Arrange
    _, purchase, accepted = _fixture()

    # Act
    projection = refine_zdex_burn_leaf_v1(accepted, purchase, _root(20))

    # Assert
    assert type(projection) is ZDEXBurnLeafProjectionV1
    journal = projection.journal
    assert journal.purchase_occurrence_root == purchase.journal_root
    assert journal.pre_tokenomics_lane_root == accepted.pre_state.state_root
    assert journal.post_tokenomics_lane_root == accepted.post_state.state_root
    assert journal.burn_bucket_pre_atoms == journal.burned_zdex_atoms == 100
    assert journal.burn_bucket_post_atoms == 0
    assert journal.zdex_owned_pre_atoms == journal.zdex_supply_pre_atoms == 1000
    assert journal.zdex_owned_post_atoms == journal.zdex_supply_post_atoms == 900
    assert projection.effects == burn_effects_v1(journal)
    assert journal.effect_plan_root == projection.effects.effect_plan_root
    assert projection.effects.external_outbox_enqueue == ()
    assert purchase.journal_root == (
        "0xc7bc06f6e2475adba501f493450ca57fcf24a738e179f7ba11079281a9144dc8"
    )
    assert journal.journal_root == (
        "0x969a3954b8de1bf26bfb6ae9ed22bfd4eac2843506d1d3d3721164e891143085"
    )
    assert projection.effects.effect_plan_root == (
        "0x120e8cb20cf041b14dae207099bc1c1f9e309e8e16e3578fdcc89a0507171373"
    )


def test_refinement_rejects_purchase_effect_root_substitution() -> None:
    # Arrange
    _, purchase, accepted = _fixture()
    substituted = replace(purchase, effect_plan_root=_root(99))

    # Act / Assert
    with pytest.raises(ValueError, match="purchase effect plan"):
        refine_zdex_burn_leaf_v1(accepted, substituted, _root(20))


@pytest.mark.parametrize(
    ("field", "replacement"),
    (
        ("route_release_id", _root(99)),
        ("issue_burn_policy_root", _root(99)),
        ("zdex_asset_id", _root(99)),
        ("burn_bucket_id", "route:other-burn-source"),
        ("zdex_owned_atoms", 1100),
        ("zdex_supply_atoms", 1100),
    ),
)
def test_refinement_rejects_purchase_or_economic_binding_substitution(
    field: str,
    replacement: str | int,
) -> None:
    # Arrange
    _, purchase, accepted = _fixture()
    substituted = replace(
        purchase,
        **cast(dict[str, Any], {field: replacement}),
    )

    # Act / Assert
    with pytest.raises(ValueError):
        refine_zdex_burn_leaf_v1(accepted, substituted, _root(20))


def test_refinement_rejects_partial_route_bucket_drain() -> None:
    # Arrange
    policy = _policy()
    purchase = _purchase(policy)
    accepted = _accepted(policy, purchase, source_atoms=150)

    # Act / Assert
    with pytest.raises(ValueError, match="transient burn bucket"):
        refine_zdex_burn_leaf_v1(accepted, purchase, _root(20))


def test_refinement_rejects_coherent_purchase_amount_substitution() -> None:
    # Arrange
    policy = _policy()
    original = _purchase(policy)
    draft = replace(
        original,
        purchased_zdex_atoms=99,
        zdex_pool_post_atoms=501,
        burn_bucket_post_atoms=99,
        effect_plan_root=_root(99),
    )
    purchase = replace(
        draft,
        effect_plan_root=purchase_effects_v1(draft).effect_plan_root,
    )
    accepted = _accepted(policy, purchase, burned_atoms=100)

    # Act / Assert
    with pytest.raises(ValueError, match="purchased amount"):
        refine_zdex_burn_leaf_v1(accepted, purchase, _root(20))


@pytest.mark.parametrize(
    ("overrides", "checked_supply_atoms"),
    (
        ({"issue_burn_policy_root": _root(99)}, 1000),
        ({"zdex_asset_id": _root(99)}, 1000),
        ({"zdex_owned_atoms": 1100, "zdex_supply_atoms": 1100}, 1000),
    ),
)
def test_refinement_rejects_self_consistent_semantic_substitution(
    overrides: dict[str, str | int],
    checked_supply_atoms: int,
) -> None:
    # Arrange
    policy = _policy()
    original = _purchase(policy)
    draft = replace(
        original,
        **cast(dict[str, Any], overrides),
        effect_plan_root=_root(99),
    )
    purchase = replace(
        draft,
        effect_plan_root=purchase_effects_v1(draft).effect_plan_root,
    )
    accepted = _accepted(
        policy,
        purchase,
        checked_supply_atoms=checked_supply_atoms,
    )

    # Act / Assert
    with pytest.raises(ValueError):
        refine_zdex_burn_leaf_v1(accepted, purchase, _root(20))


def test_refinement_output_revalidates_effect_root() -> None:
    # Arrange
    _, purchase, accepted = _fixture()
    projection = refine_zdex_burn_leaf_v1(accepted, purchase, _root(20))

    # Act / Assert
    with pytest.raises(ValueError, match="effect plan root"):
        replace(
            projection,
            journal=replace(projection.journal, effect_plan_root=_root(99)),
        )


def test_refinement_revalidates_hostile_accepted_value() -> None:
    # Arrange
    _, purchase, accepted = _fixture()
    object.__setattr__(
        accepted.post_state,
        "remaining_epoch_burn_cap_atoms",
        accepted.pre_state.remaining_epoch_burn_cap_atoms,
    )

    # Act / Assert
    with pytest.raises(ValueError, match="epoch capacity"):
        refine_zdex_burn_leaf_v1(accepted, purchase, _root(20))


def test_burn_effects_revalidates_hostile_journal() -> None:
    # Arrange
    _, purchase, accepted = _fixture()
    projection = refine_zdex_burn_leaf_v1(accepted, purchase, _root(20))
    object.__setattr__(projection.journal, "authorized_quote_input_atoms", 0)

    # Act / Assert
    with pytest.raises(ValueError, match="authorized quote input"):
        burn_effects_v1(projection.journal)
