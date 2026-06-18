import pytest

from src.core.perps_fixed_validation import (
    validate_three_party_transfer_clearinghouse_invariants,
    validate_two_party_clearinghouse_invariants,
)


def _two_party_state() -> dict[str, object]:
    return {
        "position_base_a": 5,
        "position_base_b": -5,
        "collateral_e8_a": 70,
        "collateral_e8_b": 20,
        "fee_pool_e8": 10,
        "net_deposited_e8": 100,
    }


def _three_party_state() -> dict[str, object]:
    return {
        "position_base_a": 5,
        "position_base_b": -5,
        "position_base_c": 0,
        "collateral_e8_a": 50,
        "collateral_e8_b": 30,
        "collateral_e8_c": 10,
        "fee_pool_e8": 10,
        "net_deposited_e8": 100,
    }


def test_two_party_invariants_reject_coerced_state_numerics() -> None:
    state = _two_party_state()
    state["position_base_a"] = "5"

    with pytest.raises(TypeError, match="position_base_a"):
        validate_two_party_clearinghouse_invariants(state)


def test_two_party_invariants_reject_bool_state_numerics() -> None:
    state = _two_party_state()
    state["fee_pool_e8"] = True

    with pytest.raises(TypeError, match="fee_pool_e8"):
        validate_two_party_clearinghouse_invariants(state)


def test_three_party_invariants_reject_coerced_state_numerics() -> None:
    state = _three_party_state()
    state["collateral_e8_c"] = "10"

    with pytest.raises(TypeError, match="collateral_e8_c"):
        validate_three_party_transfer_clearinghouse_invariants(state)


def test_fixed_participant_invariants_accept_valid_plain_ints() -> None:
    validate_two_party_clearinghouse_invariants(_two_party_state())
    validate_three_party_transfer_clearinghouse_invariants(_three_party_state())
