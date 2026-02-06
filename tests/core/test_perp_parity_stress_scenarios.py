from __future__ import annotations

import pytest
from dataclasses import asdict
from functools import lru_cache
from typing import Callable, Iterable, Mapping


def _strip_auth_ok(params: Mapping[str, object]) -> dict[str, object]:
    out = dict(params)
    out.pop("auth_ok", None)
    return out


def _native_initial_state() -> dict[str, object]:
    from src.core.perp_epoch import perp_epoch_isolated_v2_native_initial_state

    return dict(perp_epoch_isolated_v2_native_initial_state())


def _native_apply(
    *,
    state: Mapping[str, object],
    action: str,
    params: Mapping[str, object],
) -> tuple[bool, dict[str, object] | None, dict[str, object] | None, str | None]:
    from src.core.perp_epoch import perp_epoch_isolated_v2_native_apply

    res = perp_epoch_isolated_v2_native_apply(state=state, action=str(action), params=dict(params))
    if not res.ok or res.state is None:
        return False, None, None, str(res.error or "rejected")
    return True, dict(res.state), dict(res.effects or {}), None


def _state_key(state: Mapping[str, object]) -> tuple[tuple[str, object], ...]:
    return tuple(sorted(((str(k), state[k]) for k in state.keys()), key=lambda kv: kv[0]))


def _params_key(params: Mapping[str, object]) -> tuple[tuple[str, object], ...]:
    return tuple(sorted(((str(k), params[k]) for k in params.keys()), key=lambda kv: kv[0]))


@lru_cache(maxsize=100_000)
def _native_apply_cached(
    state_k: tuple[tuple[str, object], ...],
    action: str,
    params_k: tuple[tuple[str, object], ...],
) -> tuple[bool, dict[str, object] | None, dict[str, object] | None, str | None]:
    return _native_apply(state=dict(state_k), action=action, params=dict(params_k))


def _ref_initial_state() -> dict[str, object]:
    from generated.perp_python import perp_epoch_isolated_v2_ref as ref

    return dict(asdict(ref.init_state()))


def _ref_apply(
    *,
    state: Mapping[str, object],
    action: str,
    params: Mapping[str, object],
) -> tuple[bool, dict[str, object] | None, dict[str, object] | None, str | None]:
    from generated.perp_python import perp_epoch_isolated_v2_ref as ref

    s = ref.State(**dict(state))
    cmd = ref.Command(tag=str(action), args=dict(params))
    res = ref.step(s, cmd)
    if not res.ok or res.state is None:
        return False, None, None, str(res.error or "rejected")
    return True, dict(asdict(res.state)), dict(res.effects or {}), None


@lru_cache(maxsize=100_000)
def _ref_apply_cached(
    state_k: tuple[tuple[str, object], ...],
    action: str,
    params_k: tuple[tuple[str, object], ...],
) -> tuple[bool, dict[str, object] | None, dict[str, object] | None, str | None]:
    return _ref_apply(state=dict(state_k), action=action, params=dict(params_k))


def _yaml_apply(
    *,
    state: Mapping[str, object],
    action: str,
    params: Mapping[str, object],
) -> tuple[bool, dict[str, object] | None, dict[str, object] | None, str | None]:
    from src.core.perp_epoch import perp_epoch_isolated_v2_apply

    res = perp_epoch_isolated_v2_apply(state=state, action=str(action), params=dict(params))
    if not res.ok or res.state is None:
        return False, None, None, str(res.error or "rejected")
    return True, dict(res.state), dict(res.effects or {}), None


def _esso_available() -> bool:
    try:
        import ESSO.kernel.interpreter  # type: ignore  # noqa: F401
    except ModuleNotFoundError:
        return False
    return True


def _find_first_mismatch(
    *,
    steps: Iterable[dict[str, object]],
    apply_a: Callable[..., tuple[bool, dict[str, object] | None, dict[str, object] | None, str | None]],
    apply_b: Callable[..., tuple[bool, dict[str, object] | None, dict[str, object] | None, str | None]],
    init_a: Callable[[], dict[str, object]],
    init_b: Callable[[], dict[str, object]],
    strip_auth_ok_for_b: bool,
) -> str | None:
    st_a: dict[str, object] = init_a()
    st_b: dict[str, object] = init_b()
    for i, step in enumerate(steps):
        action = str(step["action"])
        params = dict(step.get("params") or {})
        ok_a, next_a, eff_a, err_a = apply_a(state=st_a, action=action, params=params)
        params_b = _strip_auth_ok(params) if strip_auth_ok_for_b else params
        ok_b, next_b, eff_b, err_b = apply_b(state=st_b, action=action, params=params_b)
        if ok_a != ok_b:
            return f"step {i}: accept mismatch action={action} a_ok={ok_a} b_ok={ok_b} a_err={err_a!r} b_err={err_b!r}"
        if not ok_a and not ok_b:
            return None
        if next_a != next_b:
            return f"step {i}: state mismatch action={action}"
        if dict(eff_a or {}) != dict(eff_b or {}):
            return f"step {i}: effects mismatch action={action}"
        st_a = dict(next_a or {})
        st_b = dict(next_b or {})
    return None


SCENARIOS: dict[str, list[dict[str, object]]] = {
    "liq_long_shock": [
        {"action": "deposit_collateral", "params": {"amount": 1_000_000_000_000, "auth_ok": True}},
        {"action": "set_position", "params": {"new_position_base": 1_000_000, "auth_ok": True}},
        {"action": "advance_epoch", "params": {"delta": 1}},
        {"action": "publish_clearing_price", "params": {"price_e8": 1}},
        {"action": "settle_epoch", "params": {}},
    ],
    "liq_short_shock": [
        {"action": "deposit_collateral", "params": {"amount": 1_000_000_000_000, "auth_ok": True}},
        {"action": "set_position", "params": {"new_position_base": -1_000_000, "auth_ok": True}},
        {"action": "advance_epoch", "params": {"delta": 1}},
        {"action": "publish_clearing_price", "params": {"price_e8": 1_000_000_000_000}},
        {"action": "settle_epoch", "params": {}},
    ],
    "funding_whipsaw_long": [
        {"action": "set_position", "params": {"new_position_base": 1_000_000, "auth_ok": True}},
        {"action": "apply_funding", "params": {"new_rate_bps": 10000, "auth_ok": True}},
        {"action": "apply_funding", "params": {"new_rate_bps": -10000, "auth_ok": True}},
        {"action": "advance_epoch", "params": {"delta": 1}},
        {"action": "publish_clearing_price", "params": {"price_e8": 200_000_000}},
        {"action": "settle_epoch", "params": {}},
    ],
    "funding_whipsaw_short": [
        {"action": "set_position", "params": {"new_position_base": -1_000_000, "auth_ok": True}},
        {"action": "apply_funding", "params": {"new_rate_bps": -10000, "auth_ok": True}},
        {"action": "apply_funding", "params": {"new_rate_bps": 10000, "auth_ok": True}},
        {"action": "advance_epoch", "params": {"delta": 1}},
        {"action": "publish_clearing_price", "params": {"price_e8": 200_000_000}},
        {"action": "settle_epoch", "params": {}},
    ],
    "breaker_pulse": [
        {"action": "set_position", "params": {"new_position_base": 1_000_000, "auth_ok": True}},
        {"action": "apply_funding", "params": {"new_rate_bps": 10000, "auth_ok": True}},
        {"action": "advance_epoch", "params": {"delta": 1}},
        {"action": "publish_clearing_price", "params": {"price_e8": 1}},
        {"action": "settle_epoch", "params": {}},
        {"action": "clear_breaker", "params": {"auth_ok": True}},
        {"action": "advance_epoch", "params": {"delta": 1}},
        {"action": "publish_clearing_price", "params": {"price_e8": 1_000_000_000_000}},
        {"action": "settle_epoch", "params": {}},
    ],
    "epoch_warp_flip": [
        {"action": "set_position", "params": {"new_position_base": 1_000_000, "auth_ok": True}},
        {"action": "advance_epoch", "params": {"delta": 100}},
        {"action": "publish_clearing_price", "params": {"price_e8": 200_000_000}},
        {"action": "settle_epoch", "params": {}},
        {"action": "set_position", "params": {"new_position_base": -1_000_000, "auth_ok": True}},
        {"action": "advance_epoch", "params": {"delta": 100}},
        {"action": "publish_clearing_price", "params": {"price_e8": 100_000_000}},
        {"action": "settle_epoch", "params": {}},
    ],
    "insurance_oscillation": [
        {"action": "deposit_insurance", "params": {"amount": 1_000_000_000_000}},
        {"action": "apply_insurance_claim", "params": {"claim_amount": 100_000_000, "auth_ok": True}},
        {"action": "deposit_insurance", "params": {"amount": 1}},
        {"action": "apply_insurance_claim", "params": {"claim_amount": 1, "auth_ok": True}},
        {"action": "deposit_insurance", "params": {"amount": 100_000_000}},
    ],
}


@pytest.mark.parametrize(("name", "steps"), sorted(SCENARIOS.items()))
def test_stress_scenarios_native_ref_parity(name: str, steps: list[dict[str, object]]) -> None:
    mismatch = _find_first_mismatch(
        steps=steps,
        apply_a=lambda *, state, action, params: _native_apply_cached(_state_key(state), str(action), _params_key(params)),
        apply_b=lambda *, state, action, params: _ref_apply_cached(_state_key(state), str(action), _params_key(params)),
        init_a=_native_initial_state,
        init_b=_ref_initial_state,
        strip_auth_ok_for_b=False,
    )
    assert mismatch is None, f"{name}: native/ref mismatch: {mismatch}"


@pytest.mark.parametrize(("name", "steps"), sorted(SCENARIOS.items()))
@pytest.mark.skipif(not _esso_available(), reason="ESSO interpreter is not installed")
def test_stress_scenarios_native_yaml_parity(name: str, steps: list[dict[str, object]]) -> None:
    mismatch = _find_first_mismatch(
        steps=steps,
        apply_a=lambda *, state, action, params: _native_apply_cached(_state_key(state), str(action), _params_key(params)),
        apply_b=_yaml_apply,
        init_a=_native_initial_state,
        init_b=_native_initial_state,
        strip_auth_ok_for_b=True,
    )
    assert mismatch is None, f"{name}: native/yaml mismatch: {mismatch}"


@pytest.mark.parametrize(("name", "steps"), sorted(SCENARIOS.items()))
def test_stress_scenarios_native_invariants_hold(name: str, steps: list[dict[str, object]]) -> None:
    from src.core.perp_v2.invariants import check_all
    from src.core.perp_v2.types import PerpState

    state: dict[str, object] = _native_initial_state()
    violations0 = check_all(PerpState(**state))
    assert not violations0, f"{name}: initial invariant violations: {violations0}"
    for idx, step in enumerate(steps):
        action = str(step["action"])
        params = dict(step.get("params") or {})
        ok, next_state, _eff, err = _native_apply(state=state, action=action, params=params)
        if ok and next_state is not None:
            typed = PerpState(**next_state)
            violations = check_all(typed)
            assert not violations, f"{name}: step {idx} invariant violations after action={action}: {violations}"
            state = dict(next_state)
        else:
            typed = PerpState(**state)
            violations = check_all(typed)
            assert not violations, f"{name}: step {idx} invariant violations on rejected action={action}: {violations}"
            assert next_state is None, f"{name}: step {idx} rejected action unexpectedly mutated state"
            assert err is not None, f"{name}: step {idx} rejected action missing error"
