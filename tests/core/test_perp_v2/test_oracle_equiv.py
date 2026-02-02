"""Oracle equivalence tests: perp_v2 hand-written engine vs ESSO-generated reference.

Uses Hypothesis to fuzz random action sequences and verify that both engines
agree on accept/reject, post-state, and effects for every step.
"""

from __future__ import annotations

import importlib.util
import sys
from dataclasses import fields as dc_fields
from pathlib import Path
from typing import Any

import pytest

if importlib.util.find_spec("hypothesis") is None:  # pragma: no cover
    pytest.skip("hypothesis not installed", allow_module_level=True)

import hypothesis.strategies as st
from hypothesis import given, settings

from src.core.perp_v2 import Action, ActionParams, initial_state, step
from src.core.perp_v2.state import state_to_dict

# ---------------------------------------------------------------------------
# Import the ESSO-generated reference oracle (importlib, no sys.path mutation)
# ---------------------------------------------------------------------------


def _import_generated_ref() -> Any:
    root = Path(__file__).resolve().parents[3]
    ref_path = root / "generated" / "perp_python" / "perp_epoch_isolated_v2_ref.py"
    if not ref_path.exists():
        pytest.skip(f"generated ref not found at {ref_path}", allow_module_level=True)

    module_name = "generated.perp_python.perp_epoch_isolated_v2_ref"
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
    return {f.name: getattr(s, f.name) for f in dc_fields(s)}


def params_to_command(params: ActionParams):
    tag = params.action.value
    args: dict[str, bool | int] = {}
    if tag == "advance_epoch":
        args = {"delta": params.delta}
    elif tag == "publish_clearing_price":
        args = {"price_e8": params.price_e8}
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


def our_effect_to_dict(effect) -> dict[str, bool | int | str]:
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
        our = state_to_dict(initial_state())
        theirs = ref_state_to_dict(ref.init_state())
        assert our == theirs


class TestSingleActionEquivalence:
    """Fuzz single actions from the initial state."""

    @given(params=action_params_strategy())
    @settings(max_examples=500, deadline=2000)
    def test_single_step(self, params: ActionParams):
        our_state = initial_state()
        ref_state = ref.init_state()

        our_result = step(our_state, params)
        ref_result = ref.step(ref_state, params_to_command(params))

        assert our_result.accepted == ref_result.ok, (
            f"accept/reject mismatch on {params.action.value}: "
            f"ours={our_result.accepted} (rejection={our_result.rejection}), "
            f"ref={ref_result.ok} (error={ref_result.error})"
        )

        if our_result.accepted and ref_result.ok:
            our_post = state_to_dict(our_result.state)
            ref_post = ref_state_to_dict(ref_result.state)
            for key in sorted(ref_post):
                assert our_post[key] == ref_post[key], (
                    f"state mismatch on {key}: ours={our_post[key]}, ref={ref_post[key]}"
                )

            our_eff = our_effect_to_dict(our_result.effect)
            ref_eff = dict(ref_result.effects)
            for key in sorted(ref_eff):
                assert our_eff[key] == ref_eff[key], (
                    f"effect mismatch on {key}: ours={our_eff[key]}, ref={ref_eff[key]}"
                )


class TestActionSequenceEquivalence:
    """Fuzz multi-step action sequences."""

    @given(actions=st.lists(action_params_strategy(), min_size=1, max_size=30))
    @settings(max_examples=200, deadline=5000)
    def test_sequence(self, actions: list[ActionParams]):
        our_state = initial_state()
        ref_state = ref.init_state()

        for i, params in enumerate(actions):
            our_result = step(our_state, params)
            ref_result = ref.step(ref_state, params_to_command(params))

            assert our_result.accepted == ref_result.ok, (
                f"step {i} ({params.action.value}): "
                f"accept/reject mismatch: "
                f"ours={our_result.accepted} (rejection={our_result.rejection}), "
                f"ref={ref_result.ok} (error={ref_result.error})"
            )

            if our_result.accepted and ref_result.ok:
                our_post = state_to_dict(our_result.state)
                ref_post = ref_state_to_dict(ref_result.state)
                for key in sorted(ref_post):
                    assert our_post[key] == ref_post[key], (
                        f"step {i} ({params.action.value}): "
                        f"state mismatch on {key}: ours={our_post[key]}, ref={ref_post[key]}"
                    )

                our_eff = our_effect_to_dict(our_result.effect)
                ref_eff = dict(ref_result.effects)
                for key in sorted(ref_eff):
                    assert our_eff[key] == ref_eff[key], (
                        f"step {i} ({params.action.value}): "
                        f"effect mismatch on {key}: ours={our_eff[key]}, ref={ref_eff[key]}"
                    )

                our_state = our_result.state
                ref_state = ref_result.state
            else:
                # Both rejected — state doesn't advance.
                pass


class TestLifecycleEquivalence:
    """Deterministic lifecycle: advance -> price -> deposit -> position -> settle."""

    def test_full_lifecycle(self):
        our_s = initial_state()
        ref_s = ref.init_state()

        actions = [
            ActionParams(action=Action.ADVANCE_EPOCH, delta=1),
            ActionParams(action=Action.PUBLISH_CLEARING_PRICE, price_e8=100_000_000),
            ActionParams(action=Action.DEPOSIT_COLLATERAL, amount=1_000_000, auth_ok=True),
            ActionParams(action=Action.SET_POSITION, new_position_base=100, auth_ok=True),
            ActionParams(action=Action.ADVANCE_EPOCH, delta=1),
            ActionParams(action=Action.PUBLISH_CLEARING_PRICE, price_e8=105_000_000),
            ActionParams(action=Action.SETTLE_EPOCH),
            ActionParams(action=Action.APPLY_FUNDING, new_rate_bps=10, auth_ok=True),
            ActionParams(action=Action.DEPOSIT_INSURANCE, amount=500_000),
            ActionParams(action=Action.ADVANCE_EPOCH, delta=1),
            ActionParams(action=Action.PUBLISH_CLEARING_PRICE, price_e8=102_000_000),
            ActionParams(action=Action.SETTLE_EPOCH),
        ]

        for i, params in enumerate(actions):
            our_result = step(our_s, params)
            ref_result = ref.step(ref_s, params_to_command(params))

            assert our_result.accepted == ref_result.ok, (
                f"step {i} ({params.action.value}): "
                f"ours={our_result.accepted} ({our_result.rejection}), "
                f"ref={ref_result.ok} ({ref_result.error})"
            )

            if our_result.accepted:
                our_post = state_to_dict(our_result.state)
                ref_post = ref_state_to_dict(ref_result.state)
                assert our_post == ref_post, (
                    f"step {i}: state diverged: "
                    + ", ".join(
                        f"{k}: {our_post[k]} vs {ref_post[k]}"
                        for k in sorted(ref_post)
                        if our_post[k] != ref_post[k]
                    )
                )

                our_eff = our_effect_to_dict(our_result.effect)
                ref_eff = dict(ref_result.effects)
                assert our_eff == ref_eff, (
                    f"step {i}: effects diverged: "
                    + ", ".join(
                        f"{k}: {our_eff[k]} vs {ref_eff[k]}"
                        for k in sorted(ref_eff)
                        if our_eff.get(k) != ref_eff.get(k)
                    )
                )

                our_s = our_result.state
                ref_s = ref_result.state
