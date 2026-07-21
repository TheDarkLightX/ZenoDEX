"""Oracle equivalence tests: v3 native adapter vs generated v3 reference.

Uses Hypothesis to fuzz random action sequences and verify that both engines
agree on accept/reject, post-state, and effects for every step.
"""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path
from typing import Any

import pytest

if importlib.util.find_spec("hypothesis") is None:  # pragma: no cover
    pytest.skip("hypothesis not installed", allow_module_level=True)

import hypothesis.strategies as st
from hypothesis import given, settings

from src.core.perp_epoch import (
    PerpStepResult,
    perp_epoch_isolated_v3_native_apply,
    perp_epoch_isolated_v3_native_initial_state,
)
from src.core.perp_v2 import Action, ActionParams

# ---------------------------------------------------------------------------
# Import the generated reference oracle (importlib, no sys.path mutation)
# ---------------------------------------------------------------------------


def _import_generated_ref() -> Any:
    root = Path(__file__).resolve().parents[3]
    ref_path = root / "generated" / "perp_python" / "perp_epoch_isolated_v3_ref.py"
    if not ref_path.exists():
        pytest.skip(f"generated ref not found at {ref_path}", allow_module_level=True)

    module_name = "generated.perp_python.perp_epoch_isolated_v3_ref"
    spec = importlib.util.spec_from_file_location(module_name, ref_path)
    assert spec and spec.loader, f"could not load spec from {ref_path}"
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module


ref = _import_generated_ref()

# ---------------------------------------------------------------------------
# Translation helpers
# ---------------------------------------------------------------------------


def ref_state_to_dict(s) -> dict[str, bool | int]:
    return vars(s)


def params_to_command(params: ActionParams):
    tag = params.action.value
    args: dict[str, bool | int] = {}
    if tag == "advance_epoch":
        args = {"delta": params.delta}
    elif tag == "publish_clearing_price":
        args = {"price_e8": params.price_e8, "auth_ok": params.auth_ok}
    elif tag == "settle_epoch":
        args = {}
    elif tag == "deposit_collateral":
        args = {"amount": params.amount, "auth_ok": params.auth_ok}
    elif tag == "withdraw_collateral":
        args = {"amount": params.amount, "auth_ok": params.auth_ok}
    elif tag == "set_position":
        args = {"new_position_base": params.new_position_base, "auth_ok": params.auth_ok}
    elif tag == "clear_breaker":
        args = {"auth_ok": params.auth_ok}
    elif tag == "apply_funding":
        args = {"new_rate_bps": params.new_rate_bps, "auth_ok": params.auth_ok}
    elif tag == "deposit_insurance":
        args = {"amount": params.amount}
    elif tag == "apply_insurance_claim":
        args = {"claim_amount": params.claim_amount, "auth_ok": params.auth_ok}
    return ref.Command(tag=tag, args=args)


def apply_native(state: dict[str, bool | int], command) -> PerpStepResult:
    return perp_epoch_isolated_v3_native_apply(
        state=state,
        action=command.tag,
        params=command.args,
    )


def assert_result_parity(
    native_result: PerpStepResult,
    ref_result,
    *,
    context: str,
) -> None:
    assert native_result.ok == ref_result.ok, (
        f"{context}: accept/reject mismatch: "
        f"native={native_result.ok} (error={native_result.error}), "
        f"ref={ref_result.ok} (error={ref_result.error})"
    )
    if not native_result.ok:
        assert native_result.state is None
        assert native_result.effects is None
        return

    assert native_result.state is not None
    assert native_result.effects is not None
    assert ref_result.state is not None
    assert ref_result.effects is not None
    assert native_result.state == ref_state_to_dict(ref_result.state), context
    assert native_result.effects == dict(ref_result.effects), context


def oracle_bound_initial_states() -> tuple[dict[str, bool | int], Any]:
    native = {
        **perp_epoch_isolated_v3_native_initial_state(),
        "oracle_seen": True,
        "oracle_last_update_epoch": 0,
        "index_price_e8": 100_000_000,
    }
    generated = ref.State(**native)
    return native, generated


# ---------------------------------------------------------------------------
# Hypothesis strategies: generate action params in YAML domain bounds
# ---------------------------------------------------------------------------


def action_params_strategy() -> st.SearchStrategy[ActionParams]:
    """Generate random ActionParams within YAML domain bounds.

    auth_ok is randomized for auth-gated actions to cover both
    the accepted (True) and guard-rejected (False) paths.
    """
    auth = st.booleans()
    return st.one_of(
        st.builds(
            ActionParams,
            action=st.just(Action.ADVANCE_EPOCH),
            delta=st.integers(min_value=1, max_value=10_000),
        ),
        st.builds(
            ActionParams,
            action=st.just(Action.PUBLISH_CLEARING_PRICE),
            price_e8=st.integers(min_value=1, max_value=1_000_000_000_000),
            auth_ok=auth,
        ),
        st.builds(
            ActionParams,
            action=st.just(Action.SETTLE_EPOCH),
        ),
        st.builds(
            ActionParams,
            action=st.just(Action.DEPOSIT_COLLATERAL),
            amount=st.integers(min_value=1, max_value=1_000_000_000_000),
            auth_ok=auth,
        ),
        st.builds(
            ActionParams,
            action=st.just(Action.WITHDRAW_COLLATERAL),
            amount=st.integers(min_value=1, max_value=1_000_000_000_000),
            auth_ok=auth,
        ),
        st.builds(
            ActionParams,
            action=st.just(Action.SET_POSITION),
            new_position_base=st.integers(min_value=-1_000_000, max_value=1_000_000),
            auth_ok=auth,
        ),
        st.builds(
            ActionParams,
            action=st.just(Action.CLEAR_BREAKER),
            auth_ok=auth,
        ),
        st.builds(
            ActionParams,
            action=st.just(Action.APPLY_FUNDING),
            new_rate_bps=st.integers(min_value=-100, max_value=100),
            auth_ok=auth,
        ),
        st.builds(
            ActionParams,
            action=st.just(Action.DEPOSIT_INSURANCE),
            amount=st.integers(min_value=1, max_value=1_000_000_000_000),
        ),
        st.builds(
            ActionParams,
            action=st.just(Action.APPLY_INSURANCE_CLAIM),
            claim_amount=st.integers(min_value=1, max_value=1_000_000_000_000),
            auth_ok=auth,
        ),
    )


# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------


class TestInitialStateEquivalence:
    def test_initial_states_match(self):
        our = perp_epoch_isolated_v3_native_initial_state()
        theirs = ref_state_to_dict(ref.init_state())
        assert our == theirs


class TestSingleActionEquivalence:
    """Fuzz single actions from the initial state."""

    @given(params=action_params_strategy())
    @settings(max_examples=500, deadline=2000)
    def test_single_step(self, params: ActionParams):
        our_state = perp_epoch_isolated_v3_native_initial_state()
        ref_state = ref.init_state()

        command = params_to_command(params)
        our_result = apply_native(our_state, command)
        ref_result = ref.step(ref_state, command)
        assert_result_parity(
            our_result,
            ref_result,
            context=f"single {params.action.value}",
        )


class TestActionSequenceEquivalence:
    """Fuzz multi-step action sequences."""

    @given(actions=st.lists(action_params_strategy(), min_size=1, max_size=30))
    @settings(max_examples=200, deadline=5000)
    def test_sequence(self, actions: list[ActionParams]):
        our_state = perp_epoch_isolated_v3_native_initial_state()
        ref_state = ref.init_state()

        for i, params in enumerate(actions):
            command = params_to_command(params)
            our_result = apply_native(our_state, command)
            ref_result = ref.step(ref_state, command)
            assert_result_parity(
                our_result,
                ref_result,
                context=f"step {i} ({params.action.value})",
            )

            if our_result.ok:
                assert our_result.state is not None
                assert ref_result.state is not None
                our_state = our_result.state
                ref_state = ref_result.state


class TestLifecycleEquivalence:
    """Deterministic lifecycle: advance -> price -> deposit -> position -> settle."""

    def test_full_lifecycle(self):
        our_s, ref_s = oracle_bound_initial_states()

        actions = [
            ActionParams(action=Action.ADVANCE_EPOCH, delta=1),
            ActionParams(action=Action.DEPOSIT_COLLATERAL, amount=1_000_000, auth_ok=True),
            ActionParams(action=Action.SET_POSITION, new_position_base=100, auth_ok=True),
            ActionParams(action=Action.PUBLISH_CLEARING_PRICE, price_e8=100_000_000, auth_ok=True),
            ActionParams(action=Action.SETTLE_EPOCH),
            ActionParams(action=Action.ADVANCE_EPOCH, delta=1),
            ActionParams(action=Action.PUBLISH_CLEARING_PRICE, price_e8=105_000_000, auth_ok=True),
            ActionParams(action=Action.SETTLE_EPOCH),
            ActionParams(action=Action.APPLY_FUNDING, new_rate_bps=10, auth_ok=True),
            ActionParams(action=Action.DEPOSIT_INSURANCE, amount=500_000),
            ActionParams(action=Action.ADVANCE_EPOCH, delta=1),
            ActionParams(action=Action.PUBLISH_CLEARING_PRICE, price_e8=102_000_000, auth_ok=True),
            ActionParams(action=Action.SETTLE_EPOCH),
        ]

        for i, params in enumerate(actions):
            command = params_to_command(params)
            our_result = apply_native(our_s, command)
            ref_result = ref.step(ref_s, command)
            assert_result_parity(
                our_result,
                ref_result,
                context=f"lifecycle step {i} ({params.action.value})",
            )

            if our_result.ok:
                assert our_result.state is not None
                assert ref_result.state is not None
                our_s = our_result.state
                ref_s = ref_result.state


def test_regression_stale_oracle_settle_epoch_accept_reject_parity() -> None:
    """
    Regression for a ref/native mismatch found by Hypothesis shrinking.

    Scenario:
    1) Settle epoch 1 to establish an oracle snapshot.
    2) Advance by a large delta so the last oracle update is far in the past.
    3) Publish a clearing price and attempt to settle again.

    Expected: accept/reject parity with the generated ref model.
    """
    actions = [
        ActionParams(action=Action.ADVANCE_EPOCH, delta=1),
        ActionParams(action=Action.PUBLISH_CLEARING_PRICE, price_e8=1, auth_ok=True),
        ActionParams(action=Action.SETTLE_EPOCH),
        ActionParams(action=Action.ADVANCE_EPOCH, delta=101),
        ActionParams(action=Action.PUBLISH_CLEARING_PRICE, price_e8=1, auth_ok=True),
        ActionParams(action=Action.SETTLE_EPOCH),
    ]

    our_s, ref_s = oracle_bound_initial_states()
    for i, params in enumerate(actions):
        command = params_to_command(params)
        our_result = apply_native(our_s, command)
        ref_result = ref.step(ref_s, command)
        assert_result_parity(
            our_result,
            ref_result,
            context=f"stale regression step {i} ({params.action.value})",
        )
        if our_result.ok:
            assert our_result.state is not None
            assert ref_result.state is not None
            our_s = our_result.state
            ref_s = ref_result.state
