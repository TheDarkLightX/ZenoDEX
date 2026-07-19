from __future__ import annotations

from itertools import product

from src.core.zusd import E8, ZUSDCommand, init_state, step
from src.integration.zusd_oracle_contracts import build_zusd_oracle_pending_gate_contract
from src.integration.zusd_recovery_mode_gate_regions import (
    ZUSDRecoveryModeGateInputs,
    action_allowed,
    build_zusd_recovery_mode_gate_regions,
    contract_input_region,
    input_region,
    risky_ops_allowed,
)


def _single_ok(state, tag: str, **args):
    res = step(state, ZUSDCommand(tag=tag, args=args))  # type: ignore[arg-type]
    assert res.ok, res.error
    assert res.state is not None
    return res.state


def test_zusd_recovery_mode_gate_regions_partition_ok_surface() -> None:
    regions = build_zusd_recovery_mode_gate_regions()

    assert (regions.risky_action_allowed & regions.safe_non_risky_action_allowed).is_empty()
    assert (regions.risky_action_allowed & regions.denied).is_empty()
    assert (regions.safe_non_risky_action_allowed & regions.denied).is_empty()
    assert regions.partition_is_total()


def test_zusd_recovery_mode_gate_regions_accept_aligned_risky_state() -> None:
    state = _single_ok(init_state(), "bootstrap_oracle", price_e8=100 * E8, auth_ok=True)
    contract = build_zusd_oracle_pending_gate_contract(state, risky_requested=True, tcr_ok=True)
    regions = build_zusd_recovery_mode_gate_regions()
    region = contract_input_region(contract)

    assert region <= regions.env_ok
    assert region <= regions.risky_action_allowed
    assert region <= regions.action_allowed


def test_zusd_recovery_mode_gate_regions_block_recovery_risky_request() -> None:
    state = _single_ok(init_state(), "bootstrap_oracle", price_e8=100 * E8, auth_ok=True)
    contract = build_zusd_oracle_pending_gate_contract(state, risky_requested=True, tcr_ok=False)
    regions = build_zusd_recovery_mode_gate_regions()
    region = contract_input_region(contract)

    assert region <= regions.blocked_by_recovery
    assert region <= regions.recovery_blocked_request
    assert region <= regions.denied


def test_zusd_recovery_mode_gate_regions_allow_non_risky_action_in_recovery() -> None:
    state = _single_ok(init_state(), "bootstrap_oracle", price_e8=100 * E8, auth_ok=True)
    contract = build_zusd_oracle_pending_gate_contract(state, risky_requested=False, tcr_ok=False)
    regions = build_zusd_recovery_mode_gate_regions()
    region = contract_input_region(contract)

    assert region <= regions.blocked_by_recovery
    assert region <= regions.safe_non_risky_action_allowed
    assert (region & regions.denied).is_empty()


def test_zusd_recovery_mode_gate_python_formulas_match_region_membership() -> None:
    regions = build_zusd_recovery_mode_gate_regions()

    for word in product((0, 1), repeat=6):
        inputs = ZUSDRecoveryModeGateInputs.from_word(word)
        region = input_region(inputs)
        assert (region <= regions.action_allowed) == action_allowed(inputs)
        assert (region <= regions.risky_ops_allowed) == risky_ops_allowed(inputs)
