from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.asset_lane_coordinator_v1 import compose_asset_lane_single_v1
from src.core.asset_lane_projection_v1 import (
    AssetLaneCoordinatorRejectCodeV1,
    AssetLaneModuleCompatibilityV1,
    project_asset_transfer_state_v1,
)
from src.core.asset_transfer_types_v1 import (
    ASSET_TRANSFER_MODULE_SCHEMA_V1,
)
from src.core.global_settlement_types_v1 import (
    AssetSupplyV1,
    EconomicEffectKindV1,
    EconomicEffectRowV1,
    ExternalOutboxEnqueueV1,
    LaneIdV1,
    LaneWriteV1,
)
from tests.core.test_asset_lane_coordinator_v1 import (
    _assert_noop,
    _bound_journal,
    _coordinator_context,
    _root,
    _transfer_fixture,
    _transfer_port,
)


@pytest.mark.parametrize(
    ("mutation", "code"),
    (
        ("wrong_chain", AssetLaneCoordinatorRejectCodeV1.CHAIN_MISMATCH),
        ("unregistered", AssetLaneCoordinatorRejectCodeV1.MODULE_NOT_REGISTERED),
        ("wrong_schema", AssetLaneCoordinatorRejectCodeV1.MODULE_SCHEMA_MISMATCH),
        ("wrong_occurrence", AssetLaneCoordinatorRejectCodeV1.OCCURRENCE_MISMATCH),
        ("wrong_port", AssetLaneCoordinatorRejectCodeV1.PRIVATE_PORT_ROOT_MISMATCH),
        ("wrong_effect", AssetLaneCoordinatorRejectCodeV1.EFFECT_PLAN_MISMATCH),
        ("wrong_policy", AssetLaneCoordinatorRejectCodeV1.POLICY_ROOT_MISMATCH),
    ),
)
def test_every_binding_mutation_rejects_without_effects(
    mutation: str,
    code: AssetLaneCoordinatorRejectCodeV1,
) -> None:
    _, state, accepted = _transfer_fixture()
    port = _transfer_port(state, accepted)
    context = _coordinator_context()
    journal = _bound_journal(accepted, port)
    if mutation == "wrong_chain":
        journal = replace(journal, chain_id="other-chain")
    elif mutation == "unregistered":
        context = replace(
            context,
            compatible_modules=(
                AssetLaneModuleCompatibilityV1(_root(99), ASSET_TRANSFER_MODULE_SCHEMA_V1),
            ),
        )
    elif mutation == "wrong_schema":
        port = replace(port, producer_module_schema="zenodex/unknown-module/v1")
        journal = replace(journal, private_port_root=port.port_root)
    elif mutation == "wrong_occurrence":
        journal = replace(journal, command_occurrence_id=_root(99))
    elif mutation == "wrong_port":
        journal = replace(journal, private_port_root=_root(99))
    elif mutation == "wrong_effect":
        journal = replace(journal, effect_plan_root=_root(99))
    elif mutation == "wrong_policy":
        context = replace(context, asset_policy_registry_root=_root(99))

    _assert_noop(
        compose_asset_lane_single_v1(context, journal, port, accepted.effects),
        port.pre_state,
        code,
    )


def test_state_effect_mutation_rejects_after_valid_bindings() -> None:
    _, state, accepted = _transfer_fixture()
    normal_port = _transfer_port(state, accepted)
    mutated_balances = tuple(
        replace(row, amount_atoms=row.amount_atoms + (1 if row.owner == "alice" else -1))
        if row.owner in {"alice", "bob"}
        else row
        for row in normal_port.post_state.balances
    )
    mutated_post = replace(normal_port.post_state, balances=mutated_balances)
    port = _transfer_port(state, accepted, post_state=mutated_post)

    _assert_noop(
        compose_asset_lane_single_v1(
            _coordinator_context(),
            _bound_journal(accepted, port),
            port,
            accepted.effects,
        ),
        port.pre_state,
        AssetLaneCoordinatorRejectCodeV1.STATE_EFFECT_MISMATCH,
    )


@pytest.mark.parametrize(
    ("mutation", "code"),
    (
        ("deployment", AssetLaneCoordinatorRejectCodeV1.DEPLOYMENT_MISMATCH),
        ("profile", AssetLaneCoordinatorRejectCodeV1.PROFILE_MISMATCH),
        ("writer_epoch", AssetLaneCoordinatorRejectCodeV1.WRITER_EPOCH_MISMATCH),
        ("lane", AssetLaneCoordinatorRejectCodeV1.WRONG_LANE),
        ("module_release", AssetLaneCoordinatorRejectCodeV1.MODULE_RELEASE_MISMATCH),
        (
            "terminal_obligation",
            AssetLaneCoordinatorRejectCodeV1.TERMINAL_OBLIGATION_MISMATCH,
        ),
        (
            "occurrence_effect",
            AssetLaneCoordinatorRejectCodeV1.OCCURRENCE_EFFECT_MISMATCH,
        ),
        ("lane_write", AssetLaneCoordinatorRejectCodeV1.LANE_WRITE_SHAPE_MISMATCH),
        ("effect_kind", AssetLaneCoordinatorRejectCodeV1.EFFECT_KIND_FORBIDDEN),
        (
            "conservation_coverage",
            AssetLaneCoordinatorRejectCodeV1.CONSERVATION_COVERAGE_MISMATCH,
        ),
        (
            "conservation_state",
            AssetLaneCoordinatorRejectCodeV1.CONSERVATION_STATE_MISMATCH,
        ),
        ("outbox", AssetLaneCoordinatorRejectCodeV1.EXTERNAL_OUTBOX_FORBIDDEN),
    ),
)
def test_remaining_binding_and_economic_mutations_are_exact_noops(
    mutation: str,
    code: AssetLaneCoordinatorRejectCodeV1,
) -> None:
    _, state, accepted = _transfer_fixture()
    context = _coordinator_context()
    effects = accepted.effects
    post_state = project_asset_transfer_state_v1(
        accepted.post_state,
        asset_policy_registry_root=_root(11),
        fee_policy_registry_root=_root(12),
    )
    if mutation == "occurrence_effect":
        effects = replace(effects, occurrence_consumptions=(_root(99),))
    elif mutation == "lane_write":
        effects = replace(
            effects,
            lane_writes=(
                LaneWriteV1(
                    LaneIdV1.ASSET_TRANSFER,
                    accepted.module_journal.pre_lane_root,
                    _root(99),
                ),
            ),
        )
    elif mutation == "conservation_coverage":
        effects = replace(effects, asset_conservation=())
    elif mutation == "effect_kind":
        effects = replace(
            effects,
            rows=tuple(
                sorted(
                    (
                        *effects.rows,
                        EconomicEffectRowV1(
                            EconomicEffectKindV1.LIABILITY,
                            "alice",
                            "USD",
                            "liability:test",
                            1,
                        ),
                    ),
                    key=lambda row: row.key,
                )
            ),
        )
    elif mutation == "conservation_state":
        post_state = replace(
            post_state,
            balances=tuple(
                replace(row, amount_atoms=row.amount_atoms + 1)
                if row.owner == "alice"
                else row
                for row in post_state.balances
            ),
            supplies=(AssetSupplyV1("USD", 116),),
        )
    elif mutation == "outbox":
        effects = replace(
            effects,
            external_outbox_enqueue=(
                ExternalOutboxEnqueueV1(_root(40), "external:test", _root(41), _root(42)),
            ),
        )

    port = _transfer_port(state, accepted, post_state=post_state, effects=effects)
    journal = _bound_journal(accepted, port, effects=effects)
    if mutation == "deployment":
        journal = replace(journal, deployment_root=_root(99))
    elif mutation == "profile":
        journal = replace(journal, profile_root=_root(99))
    elif mutation == "writer_epoch":
        journal = replace(journal, writer_epoch=99)
    elif mutation == "lane":
        journal = replace(journal, lane_id=LaneIdV1.SPOT_LIQUIDITY)
    elif mutation == "module_release":
        port = replace(port, module_release_id=_root(99))
        journal = replace(journal, private_port_root=port.port_root)
    elif mutation == "terminal_obligation":
        journal = replace(journal, terminal_obligations_root=_root(99))

    _assert_noop(
        compose_asset_lane_single_v1(context, journal, port, effects),
        port.pre_state,
        code,
    )
