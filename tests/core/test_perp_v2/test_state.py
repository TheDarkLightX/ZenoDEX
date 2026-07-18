"""Tests for src/core/perp_v2/state.py — state construction and serialization."""

import pytest

from src.core.perp_v2.state import (
    STATE_VAR_NAMES,
    initial_state,
    state_from_dict,
    state_to_dict,
)
from src.core.perp_v2.types import EpochPhase, PerpState


class TestInitialState:
    def test_returns_perp_state(self):
        s = initial_state()
        assert type(s) is PerpState

    def test_default_values(self):
        s = initial_state()
        assert s.now_epoch == 0
        assert s.breaker_active is False
        assert s.oracle_seen is False
        assert s.max_oracle_staleness_epochs == 100
        assert s.max_oracle_move_bps == 500
        assert s.initial_margin_bps == 1000
        assert s.maintenance_margin_bps == 500
        assert s.depeg_buffer_bps == 100
        assert s.liquidation_penalty_bps == 50
        assert s.max_position_abs == 1000000
        assert s.funding_cap_bps == 100
        assert s.min_notional_for_bounty == 100_000_000
        assert s.position_base == 0
        assert s.collateral_quote == 0
        assert s.fee_pool_quote == 0
        assert s.insurance_balance == 0

    def test_frozen(self):
        s = initial_state()
        with pytest.raises(AttributeError):
            s.now_epoch = 1  # type: ignore


class TestStateVarNames:
    def test_count(self):
        assert len(STATE_VAR_NAMES) == 31

    def test_no_duplicates(self):
        assert len(set(STATE_VAR_NAMES)) == 31


class TestRoundTrip:
    def test_initial_state_round_trip(self):
        s = initial_state()
        d = state_to_dict(s)
        s2 = state_from_dict(d)
        assert s == s2

    def test_custom_state_round_trip(self):
        s = PerpState(
            now_epoch=42,
            breaker_active=True,
            breaker_last_trigger_epoch=40,
            clearing_price_seen=True,
            clearing_price_epoch=42,
            clearing_price_e8=100_000_000,
            oracle_seen=True,
            oracle_last_update_epoch=42,
            index_price_e8=100_000_000,
            position_base=-500,
            entry_price_e8=100_000_000,
            collateral_quote=50000,
            fee_pool_quote=100,
            funding_rate_bps=50,
            funding_paid_cumulative=-200,
            insurance_balance=100,
            initial_insurance=0,
            fee_income=100,
            claims_paid=0,
        )
        d = state_to_dict(s)
        s2 = state_from_dict(d)
        assert s == s2

    def test_all_fields_present_in_dict(self):
        d = state_to_dict(initial_state())
        for name in STATE_VAR_NAMES:
            assert name in d

    def test_no_extra_fields_in_dict(self):
        d = state_to_dict(initial_state())
        assert set(d.keys()) == set(STATE_VAR_NAMES)


class TestStateFromDict:
    def test_missing_key_rejects_exact_schema(self):
        d = state_to_dict(initial_state())
        del d["now_epoch"]
        with pytest.raises(ValueError, match="fields must match exactly"):
            state_from_dict(d)

    def test_unknown_key_rejects_exact_schema(self):
        d = state_to_dict(initial_state())
        d["future_state_field"] = 0
        with pytest.raises(ValueError, match="fields must match exactly"):
            state_from_dict(d)

    def test_wrong_type_raises(self):
        d = state_to_dict(initial_state())
        d["now_epoch"] = "not_an_int"
        with pytest.raises(TypeError):
            state_from_dict(d)

    def test_epoch_phase_accepts_int_encoding(self):
        d = state_to_dict(initial_state())
        d["epoch_phase"] = 1
        s = state_from_dict(d)
        assert s.epoch_phase == EpochPhase.PRICE_PUBLISHED

    def test_epoch_phase_invalid_int_raises(self):
        d = state_to_dict(initial_state())
        d["epoch_phase"] = 3
        with pytest.raises(ValueError):
            state_from_dict(d)

    def test_epoch_phase_bool_rejected(self):
        d = state_to_dict(initial_state())
        d["epoch_phase"] = True
        with pytest.raises(TypeError):
            state_from_dict(d)
