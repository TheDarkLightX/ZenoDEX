"""Runtime, generated-reference, and migration checks for isolated perps v4.

The suite requires total runtime/reference agreement over the exercised domain.
"""

from __future__ import annotations

import importlib.util
import random
import re
import sys
from dataclasses import replace
from pathlib import Path
from typing import Any

from src.core import perp_v2, perp_v4
from src.core.perp_epoch import (
    perp_epoch_isolated_default_apply,
    perp_epoch_isolated_v3_to_v4_migrate,
    perp_epoch_isolated_v4_native_apply,
)
from src.core.perp_v2 import math as math_v3
from src.core.perp_v2.state import state_to_dict
from src.core.perp_v2.types import Action, ActionParams, EpochPhase
from src.core.perp_v4 import math as math_v4
from src.kernels.python.perp_epoch_isolated_v4_adapter import IR_HASH as ADAPTER_IR_HASH
from tools.build_perp_epoch_isolated_v4 import TARGET_MODEL, TARGET_REF, render_v4_model


def _import_generated_ref() -> Any:
    root = Path(__file__).resolve().parents[2]
    ref_path = root / "generated" / "perp_python" / "perp_epoch_isolated_v4_ref.py"
    module_name = "generated.perp_python.perp_epoch_isolated_v4_ref"
    spec = importlib.util.spec_from_file_location(module_name, ref_path)
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module


REF = _import_generated_ref()


def test_v4_model_is_current_and_reference_is_hash_bound() -> None:
    assert TARGET_MODEL.read_bytes() == render_v4_model()
    reference_source = TARGET_REF.read_text(encoding="utf-8")
    match = re.search(r"^IR hash: (sha256:[0-9a-f]{64})$", reference_source, re.MULTILINE)
    assert match is not None
    assert match.group(1) == ADAPTER_IR_HASH


def _state_dict_for_ref(state: Any) -> dict[str, Any]:
    return state_to_dict(state)


def _to_ref_command(params: ActionParams) -> Any:
    args: dict[str, Any] = {}
    if params.action is Action.BOOTSTRAP_ORACLE:
        args = {"price_e8": params.price_e8, "auth_ok": params.auth_ok}
    elif params.action is Action.ADVANCE_EPOCH:
        args = {"delta": params.delta}
    elif params.action is Action.PUBLISH_CLEARING_PRICE:
        args = {"price_e8": params.price_e8, "auth_ok": params.auth_ok}
    elif params.action in {Action.DEPOSIT_COLLATERAL, Action.WITHDRAW_COLLATERAL}:
        args = {"amount": params.amount, "auth_ok": params.auth_ok}
    elif params.action is Action.SET_POSITION:
        args = {"new_position_base": params.new_position_base, "auth_ok": params.auth_ok}
    elif params.action in {Action.CLEAR_BREAKER}:
        args = {"auth_ok": params.auth_ok}
    elif params.action is Action.APPLY_FUNDING:
        args = {"new_rate_bps": params.new_rate_bps, "auth_ok": params.auth_ok}
    elif params.action is Action.DEPOSIT_INSURANCE:
        args = {"amount": params.amount}
    elif params.action is Action.APPLY_INSURANCE_CLAIM:
        args = {"claim_amount": params.claim_amount, "auth_ok": params.auth_ok}
    return REF.Command(tag=params.action.value, args=args)


def _effect_dict(effect: Any) -> dict[str, Any]:
    return {
        "event": effect.event.value,
        "oracle_fresh": effect.oracle_fresh,
        "notional_quote": effect.notional_quote,
        "effective_maint_bps": effect.effective_maint_bps,
        "maint_req_quote": effect.maint_req_quote,
        "init_req_quote": effect.init_req_quote,
        "margin_ok": effect.margin_ok,
        "liquidated": effect.liquidated,
        "collateral_after": effect.collateral_after,
        "fee_pool_after": effect.fee_pool_after,
        "insurance_after": effect.insurance_after,
    }


def _random_action(rng: random.Random) -> ActionParams:
    action = rng.choice(
        [
            Action.BOOTSTRAP_ORACLE,
            Action.ADVANCE_EPOCH,
            Action.PUBLISH_CLEARING_PRICE,
            Action.SETTLE_EPOCH,
            Action.DEPOSIT_COLLATERAL,
            Action.WITHDRAW_COLLATERAL,
            Action.SET_POSITION,
            Action.CLEAR_BREAKER,
            Action.APPLY_FUNDING,
            Action.DEPOSIT_INSURANCE,
            Action.APPLY_INSURANCE_CLAIM,
        ]
    )
    if action is Action.BOOTSTRAP_ORACLE:
        return ActionParams(
            action=action,
            price_e8=rng.randint(1, 2_000_000_000),
            auth_ok=True,
        )
    if action is Action.ADVANCE_EPOCH:
        return ActionParams(action=action, delta=rng.randint(1, 3))
    if action is Action.PUBLISH_CLEARING_PRICE:
        return ActionParams(
            action=action,
            price_e8=rng.randint(1, 2_000_000_000),
            auth_ok=True,
        )
    if action in {Action.DEPOSIT_COLLATERAL, Action.WITHDRAW_COLLATERAL}:
        return ActionParams(action=action, amount=rng.randint(1, 50_000), auth_ok=True)
    if action is Action.SET_POSITION:
        return ActionParams(
            action=action, new_position_base=rng.randint(-1_000, 1_000), auth_ok=True
        )
    if action is Action.CLEAR_BREAKER:
        return ActionParams(action=action, auth_ok=True)
    if action is Action.APPLY_FUNDING:
        return ActionParams(action=action, new_rate_bps=rng.randint(-100, 100), auth_ok=True)
    if action is Action.DEPOSIT_INSURANCE:
        return ActionParams(action=action, amount=rng.randint(1, 100_000))
    if action is Action.APPLY_INSURANCE_CLAIM:
        return ActionParams(action=action, claim_amount=rng.randint(1, 50_000), auth_ok=True)
    return ActionParams(action=action)


def test_v4_rejects_zero_collateral_positive_risk_position() -> None:
    state = replace(
        perp_v4.initial_state(),
        now_epoch=1,
        oracle_seen=True,
        oracle_last_update_epoch=1,
        index_price_e8=100_000_000,
        collateral_quote=0,
    )
    command = ActionParams(action=Action.SET_POSITION, new_position_base=1, auth_ok=True)

    assert perp_v2.step(state, command).accepted is True
    assert perp_v4.step(state, command).accepted is False

    ref_result = REF.step(REF.State(**_state_dict_for_ref(state)), _to_ref_command(command))
    assert ref_result.ok is False


def test_v4_margin_is_the_least_quote_integer_covering_raw_risk() -> None:
    denominator = math_v4.PRICE_SCALE * math_v4.BPS_SCALE
    for position in (0, 1, 2, 99, 1_000):
        for price_e8 in (1, 99_999_999, 100_000_000, 200_000_000):
            for margin_bps in (0, 1, 500, 1_000, 10_000):
                requirement = math_v4.risk_margin_requirement(position, price_e8, margin_bps)
                raw = abs(position) * price_e8 * margin_bps
                assert raw <= requirement * denominator
                if requirement > 0:
                    assert (requirement - 1) * denominator < raw


def test_v4_optimized_partial_selector_matches_exact_predicate_scan() -> None:
    rng = random.Random(0xCE11)
    for _ in range(64):
        args = {
            "position_base": rng.randint(-2_000, 2_000),
            "collateral_after_pnl": rng.randint(-50, 2_000),
            "settle_price_e8": rng.randint(1, 300_000_000),
            "maintenance_margin_bps": rng.randint(0, 3_000),
            "depeg_buffer_bps": rng.randint(0, 1_000),
            "liquidation_penalty_bps": rng.randint(0, 3_000),
            "min_notional_for_bounty": rng.randint(0, 2_000),
        }
        selected = math_v4.compute_partial_close_fraction(**args)
        if args["position_base"] == 0 or not math_v4.is_liquidatable(
            args["position_base"],
            args["collateral_after_pnl"],
            args["settle_price_e8"],
            args["maintenance_margin_bps"],
            args["depeg_buffer_bps"],
        ):
            expected = 0
        else:
            expected = next(
                fraction_bps
                for fraction_bps in range(1, math_v4.BPS_SCALE + 1)
                if math_v4._is_partial_fraction_sufficient(
                    fraction_bps=fraction_bps,
                    **args,
                )
            )
        assert selected == expected


def test_v4_preserves_nonrisk_rounding_policies() -> None:
    for position in (-1_000, -1, 0, 1, 1_000):
        for price_e8 in (1, 100_000_000, 200_000_000):
            assert math_v4.notional_quote(position, price_e8) == math_v3.notional_quote(
                position, price_e8
            )
            assert math_v4.funding_payment(position, price_e8, 37) == math_v3.funding_payment(
                position, price_e8, 37
            )
            assert math_v4.liq_penalty(position, price_e8, 500, 5) == math_v3.liq_penalty(
                position, price_e8, 500, 5
            )


def test_v4_native_matches_generated_reference_over_common_domain() -> None:
    rng = random.Random(0x4D415247494E)
    native = replace(
        perp_v4.initial_state(),
        oracle_seen=True,
        oracle_last_update_epoch=0,
        index_price_e8=100_000_000,
    )
    reference = replace(
        REF.init_state(),
        oracle_seen=True,
        oracle_last_update_epoch=0,
        index_price_e8=100_000_000,
    )

    for _ in range(500):
        params = _random_action(rng)
        native_result = perp_v4.step(native, params)
        reference_result = REF.step(reference, _to_ref_command(params))
        assert native_result.accepted == reference_result.ok
        if not native_result.accepted:
            continue
        assert native_result.state is not None
        assert native_result.effect is not None
        assert reference_result.state is not None
        assert reference_result.effects is not None
        assert _state_dict_for_ref(native_result.state) == vars(reference_result.state)
        assert _effect_dict(native_result.effect) == dict(reference_result.effects)
        native = native_result.state
        reference = reference_result.state


def test_v4_unsettled_epoch_advance_rejects_in_both_implementations() -> None:
    state = replace(
        perp_v4.initial_state(),
        now_epoch=5,
        epoch_phase=EpochPhase.PRICE_PUBLISHED,
        clearing_price_seen=True,
        clearing_price_epoch=5,
        clearing_price_e8=100_000_000,
        oracle_seen=True,
        oracle_last_update_epoch=4,
        index_price_e8=100_000_000,
    )
    command = ActionParams(action=Action.ADVANCE_EPOCH, delta=1)

    native = perp_v4.step(state, command)
    reference = REF.step(
        REF.State(**_state_dict_for_ref(state)),
        _to_ref_command(command),
    )

    assert native.accepted is False
    assert native.state is None
    assert native.effect is None
    assert reference.ok is False
    assert reference.state is None
    assert reference.effects is None


def test_v4_settlement_oracle_boundaries_match_generated_reference() -> None:
    base = replace(
        perp_v4.initial_state(),
        now_epoch=5,
        epoch_phase=perp_v4.EpochPhase.PRICE_PUBLISHED,
        clearing_price_seen=True,
        clearing_price_epoch=5,
        clearing_price_e8=100_000_000,
        oracle_seen=True,
        oracle_last_update_epoch=4,
        index_price_e8=100_000_000,
        max_oracle_staleness_epochs=2,
    )
    command = ActionParams(action=Action.SETTLE_EPOCH)

    cases = {
        "unseen": (
            {
                "oracle_seen": False,
                "oracle_last_update_epoch": 0,
                "index_price_e8": 0,
            },
            "pre_invariant:inv_phase_published_has_settlement_path",
        ),
        "zero_index": (
            {"index_price_e8": 0},
            "pre_invariant:inv_oracle_seen_positive_index,inv_phase_published_has_settlement_path",
        ),
        "stale_by_one": (
            {"oracle_last_update_epoch": 2},
            "pre_invariant:inv_phase_published_has_settlement_path",
        ),
    }
    for patch, expected_rejection in cases.values():
        state = replace(base, **patch)
        native_result = perp_v4.step(state, command)
        reference_result = REF.step(
            REF.State(**_state_dict_for_ref(state)),
            _to_ref_command(command),
        )

        assert native_result.accepted is False
        assert native_result.rejection == expected_rejection
        assert native_result.state is None
        assert native_result.effect is None
        assert reference_result.ok is False


def test_default_native_alias_is_v4() -> None:
    assert perp_epoch_isolated_default_apply is perp_epoch_isolated_v4_native_apply


def test_v3_to_v4_migration_is_identity_for_safe_state() -> None:
    perp_v3_state = perp_v2.initial_state()
    state = _state_dict_for_ref(perp_v3_state)

    assert perp_epoch_isolated_v3_to_v4_migrate(state) == _state_dict_for_ref(perp_v3_state)


def test_v3_to_v4_migration_rejects_floor_dependent_dust_state() -> None:
    dust_state = replace(
        perp_v2.initial_state(),
        now_epoch=1,
        oracle_seen=True,
        oracle_last_update_epoch=1,
        index_price_e8=100_000_000,
        position_base=1,
        entry_price_e8=100_000_000,
        collateral_quote=0,
    )

    try:
        perp_epoch_isolated_v3_to_v4_migrate(_state_dict_for_ref(dust_state))
    except ValueError as exc:
        assert str(exc) == "v4_migration_invariant:inv_maint_margin_ok"
    else:
        raise AssertionError("unsafe v3 dust state migrated into v4")


def test_v4_funding_preserves_published_settlement_path_in_reference() -> None:
    state = replace(
        perp_v4.initial_state(),
        now_epoch=1,
        epoch_phase=EpochPhase.PRICE_PUBLISHED,
        clearing_price_seen=True,
        clearing_price_epoch=1,
        clearing_price_e8=101_000_000,
        oracle_seen=True,
        oracle_last_update_epoch=0,
        index_price_e8=100_000_000,
        max_oracle_move_bps=500,
        initial_margin_bps=1_000,
        maintenance_margin_bps=600,
        liquidation_penalty_bps=500,
        funding_cap_bps=100,
        position_base=-100,
        entry_price_e8=100_000_000,
        collateral_quote=8,
        fee_pool_quote=math_v4.MAX_COLLATERAL,
        fee_income=math_v4.MAX_COLLATERAL,
        insurance_balance=math_v4.MAX_COLLATERAL,
        min_notional_for_bounty=1,
    )
    command = ActionParams(
        action=Action.APPLY_FUNDING,
        new_rate_bps=-100,
        auth_ok=True,
    )

    native = perp_v4.step(state, command)
    reference = REF.step(
        REF.State(**_state_dict_for_ref(state)),
        _to_ref_command(command),
    )

    assert native.accepted is False
    assert native.state is None
    assert native.effect is None
    assert reference.ok is False
    assert reference.state is None
    assert reference.effects is None
