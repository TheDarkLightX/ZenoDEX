from __future__ import annotations

import json
from dataclasses import asdict
from functools import lru_cache
from typing import Any, Callable, Dict, Iterable, Mapping, MutableMapping, TypedDict

from morph.domain import ProblemState
from morph.kernel_v1 import KernelDomain
from morph.proofs import VerifyResult
from morph.runtime import Err, Fail, MorphRuntime, Ok, PrimitiveFn, Solution
from morph.triviality_safe import CheckResult, SatResult


class Step(TypedDict):
    action: str
    params: dict[str, object]


class Witness(TypedDict):
    steps: list[Step]


def _json_dumps(obj: object) -> str:
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def _json_loads(text: str) -> object:
    return json.loads(text)


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
    # Deterministic, hashable key.
    return tuple(sorted(((str(k), state[k]) for k in state.keys()), key=lambda kv: kv[0]))


def _params_key(params: Mapping[str, object]) -> tuple[tuple[str, object], ...]:
    return tuple(sorted(((str(k), params[k]) for k in params.keys()), key=lambda kv: kv[0]))


@lru_cache(maxsize=250_000)
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


@lru_cache(maxsize=250_000)
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


def _find_first_mismatch(
    *,
    steps: Iterable[Step],
    apply_a: Callable[..., tuple[bool, dict[str, object] | None, dict[str, object] | None, str | None]],
    apply_b: Callable[..., tuple[bool, dict[str, object] | None, dict[str, object] | None, str | None]],
    init_a: Callable[[], dict[str, object]],
    init_b: Callable[[], dict[str, object]],
    strip_auth_ok_for_b: bool,
) -> str | None:
    """
    Return a short mismatch summary, or None if fully matched across the whole trace.
    """
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


class PerpsParityDomain(KernelDomain[str]):
    """
    MORPH domain: find a witness where perp_v2 native diverges from the generated reference.

    - Check: native vs generated reference (dependency-free).
    - Check2: native vs YAML spec interpreter (ESSO-backed), stripping any `auth_ok` metadata.
    """

    def normalize(self, state: ProblemState) -> ProblemState:
        try:
            obj = _json_loads(state.representation.text)
        except Exception:
            return state
        return ProblemState.create(
            goal=state.goal.text,
            representation=_json_dumps(obj),
            givens=(g.text for g in state.givens),
            constraints=(c.text for c in state.constraints),
            examples=(e.text for e in state.examples),
            obligations=(o.statement for o in state.obligations),
        )

    def sat(self, state: ProblemState) -> SatResult:
        return SatResult.SAT

    def check(self, state: ProblemState, witness: str) -> CheckResult:
        try:
            obj = _json_loads(str(witness))
            if not isinstance(obj, dict) or "steps" not in obj:
                return CheckResult.FAIL
            steps = obj["steps"]
            if not isinstance(steps, list):
                return CheckResult.FAIL
        except Exception:
            return CheckResult.FAIL

        mismatch = _find_first_mismatch(
            steps=steps,  # type: ignore[arg-type]
            apply_a=lambda *, state, action, params: _native_apply_cached(_state_key(state), str(action), _params_key(params)),
            apply_b=lambda *, state, action, params: _ref_apply_cached(_state_key(state), str(action), _params_key(params)),
            init_a=_native_initial_state,
            init_b=_ref_initial_state,
            strip_auth_ok_for_b=False,
        )
        return CheckResult.PASS if mismatch is not None else CheckResult.FAIL

    def check2(self, state: ProblemState, witness: str) -> CheckResult:
        try:
            obj = _json_loads(str(witness))
            if not isinstance(obj, dict) or "steps" not in obj:
                return CheckResult.FAIL
            steps = obj["steps"]
            if not isinstance(steps, list):
                return CheckResult.FAIL
        except Exception:
            return CheckResult.FAIL

        mismatch = _find_first_mismatch(
            steps=steps,  # type: ignore[arg-type]
            apply_a=lambda *, state, action, params: _native_apply_cached(_state_key(state), str(action), _params_key(params)),
            apply_b=_yaml_apply,
            init_a=_native_initial_state,
            init_b=_native_initial_state,
            strip_auth_ok_for_b=True,
        )
        return CheckResult.PASS if mismatch is not None else CheckResult.FAIL

    def proof_validate(self, state: ProblemState, proof: str) -> CheckResult:
        return CheckResult.FAIL

    def verify_transition(self, parent: ProblemState, transition) -> VerifyResult:
        return VerifyResult.PASS

    def witness_from_solution(self, solution: Solution) -> str:
        return str(solution.artifact)

    def vacuity_reason(self, state: ProblemState, sat: SatResult) -> str | None:
        return None


class _SearchState(TypedDict):
    steps: list[Step]
    native_state: dict[str, object]
    ref_state: dict[str, object]
    diverged: bool
    divergence: str | None


def _parse_search_state(ps: ProblemState) -> _SearchState | Err:
    try:
        obj = _json_loads(ps.representation.text)
        if not isinstance(obj, dict):
            return Fail("representation not an object")
        steps = obj.get("steps")
        native_state = obj.get("native_state")
        ref_state = obj.get("ref_state")
        diverged = obj.get("diverged")
        divergence = obj.get("divergence")
        if not isinstance(steps, list) or not isinstance(native_state, dict) or not isinstance(ref_state, dict):
            return Fail("bad representation schema")
        if not isinstance(diverged, bool):
            return Fail("bad diverged flag")
        if divergence is not None and not isinstance(divergence, str):
            return Fail("bad divergence")
        return _SearchState(
            steps=steps,  # type: ignore[typeddict-item]
            native_state=native_state,  # type: ignore[typeddict-item]
            ref_state=ref_state,  # type: ignore[typeddict-item]
            diverged=diverged,  # type: ignore[typeddict-item]
            divergence=divergence,  # type: ignore[typeddict-item]
        )
    except Exception as exc:
        return Fail(f"bad json: {exc}")


def _mk_problem_state(*, base: ProblemState, rep: _SearchState) -> ProblemState:
    return ProblemState.create(
        goal=base.goal.text,
        representation=_json_dumps(rep),
        givens=(g.text for g in base.givens),
        constraints=(c.text for c in base.constraints),
        examples=(e.text for e in base.examples),
        obligations=(o.statement for o in base.obligations),
    )


def _prim_try_solve(ps: ProblemState, _arg: str | None) -> object:
    st = _parse_search_state(ps)
    if not isinstance(st, dict):
        return st
    if not st["diverged"]:
        return Fail("no divergence")
    wit: Witness = {"steps": list(st["steps"])}
    return Ok(Solution(state=ps, artifact=_json_dumps(wit)))


def _make_step_primitive(*, action: str, params: Mapping[str, object]) -> PrimitiveFn:
    def _prim(ps: ProblemState, _arg: str | None):
        st = _parse_search_state(ps)
        if not isinstance(st, dict):
            return st
        if st["diverged"]:
            return Fail("already diverged")

        ok_n, next_n, eff_n, err_n = _native_apply_cached(_state_key(st["native_state"]), action, _params_key(params))
        ok_r, next_r, eff_r, err_r = _ref_apply_cached(_state_key(st["ref_state"]), action, _params_key(params))

        if not ok_n and not ok_r:
            return Fail("both rejected")

        step: Step = {"action": action, "params": dict(params)}
        steps2 = list(st["steps"]) + [step]
        rep2: _SearchState = {
            "steps": steps2,
            "native_state": dict(next_n or st["native_state"]),
            "ref_state": dict(next_r or st["ref_state"]),
            "diverged": False,
            "divergence": None,
        }

        diverged = False
        reason = None
        if ok_n != ok_r:
            diverged = True
            reason = f"accept mismatch native_ok={ok_n} ref_ok={ok_r} native_err={err_n!r} ref_err={err_r!r}"
        elif ok_n and ok_r:
            if dict(next_n or {}) != dict(next_r or {}):
                diverged = True
                reason = "state mismatch"
            elif dict(eff_n or {}) != dict(eff_r or {}):
                diverged = True
                reason = "effects mismatch"

        if diverged:
            rep2["diverged"] = True
            rep2["divergence"] = reason

        return Ok(_mk_problem_state(base=ps, rep=rep2))

    return _prim


def _make_multi_step_primitive(*, steps: list[Step]) -> PrimitiveFn:
    def _prim(ps: ProblemState, _arg: str | None):
        st = _parse_search_state(ps)
        if not isinstance(st, dict):
            return st
        if st["diverged"]:
            return Fail("already diverged")

        rep = dict(st)
        base = ps
        for step in steps:
            prim = _make_step_primitive(action=str(step["action"]), params=dict(step.get("params") or {}))
            out = prim(base, None)
            if not isinstance(out, Ok):
                return out
            val = out.value
            if not isinstance(val, ProblemState):
                return Fail("unexpected non-state from multi-step primitive")
            base = val
            rep2 = _parse_search_state(base)
            if not isinstance(rep2, dict):
                return rep2
            rep = rep2
            if rep["diverged"]:
                break
        return Ok(base)

    return _prim


def build_runtime() -> MorphRuntime:
    init_native = _native_initial_state()
    init_ref = _ref_initial_state()
    primitives: MutableMapping[str, PrimitiveFn] = {
        "TrySolve": _prim_try_solve,
        # Collateral
        "Deposit1": _make_step_primitive(action="deposit_collateral", params={"amount": 1, "auth_ok": True}),
        "Deposit1e8": _make_step_primitive(action="deposit_collateral", params={"amount": 100_000_000, "auth_ok": True}),
        "Deposit1e12": _make_step_primitive(action="deposit_collateral", params={"amount": 1_000_000_000_000, "auth_ok": True}),
        "Withdraw1": _make_step_primitive(action="withdraw_collateral", params={"amount": 1, "auth_ok": True}),
        "Withdraw1e8": _make_step_primitive(action="withdraw_collateral", params={"amount": 100_000_000, "auth_ok": True}),
        "Withdraw1e12": _make_step_primitive(action="withdraw_collateral", params={"amount": 1_000_000_000_000, "auth_ok": True}),
        # Position
        "SetPos0": _make_step_primitive(action="set_position", params={"new_position_base": 0, "auth_ok": True}),
        "SetPos1": _make_step_primitive(action="set_position", params={"new_position_base": 1, "auth_ok": True}),
        "SetPosN1": _make_step_primitive(action="set_position", params={"new_position_base": -1, "auth_ok": True}),
        "SetPos10": _make_step_primitive(action="set_position", params={"new_position_base": 10, "auth_ok": True}),
        "SetPosN10": _make_step_primitive(action="set_position", params={"new_position_base": -10, "auth_ok": True}),
        "SetPosMax": _make_step_primitive(action="set_position", params={"new_position_base": 1_000_000, "auth_ok": True}),
        "SetPosNMax": _make_step_primitive(action="set_position", params={"new_position_base": -1_000_000, "auth_ok": True}),
        # Epoch / oracle
        "Advance1": _make_step_primitive(action="advance_epoch", params={"delta": 1}),
        "Advance2": _make_step_primitive(action="advance_epoch", params={"delta": 2}),
        "Advance10": _make_step_primitive(action="advance_epoch", params={"delta": 10}),
        "Advance100": _make_step_primitive(action="advance_epoch", params={"delta": 100}),
        "PublishLow": _make_step_primitive(action="publish_clearing_price", params={"price_e8": 1}),
        "Publish1": _make_step_primitive(action="publish_clearing_price", params={"price_e8": 100_000_000}),
        "Publish2": _make_step_primitive(action="publish_clearing_price", params={"price_e8": 200_000_000}),
        "PublishHigh": _make_step_primitive(action="publish_clearing_price", params={"price_e8": 1_000_000_000_000}),
        "Settle": _make_step_primitive(action="settle_epoch", params={}),
        # Funding / breaker
        "FundingP1": _make_step_primitive(action="apply_funding", params={"new_rate_bps": 1, "auth_ok": True}),
        "FundingN1": _make_step_primitive(action="apply_funding", params={"new_rate_bps": -1, "auth_ok": True}),
        "FundingP100": _make_step_primitive(action="apply_funding", params={"new_rate_bps": 100, "auth_ok": True}),
        "FundingN100": _make_step_primitive(action="apply_funding", params={"new_rate_bps": -100, "auth_ok": True}),
        "FundingP10000": _make_step_primitive(action="apply_funding", params={"new_rate_bps": 10000, "auth_ok": True}),
        "FundingN10000": _make_step_primitive(action="apply_funding", params={"new_rate_bps": -10000, "auth_ok": True}),
        "ClearBreaker": _make_step_primitive(action="clear_breaker", params={"auth_ok": True}),
        # Insurance
        "DepositIns1": _make_step_primitive(action="deposit_insurance", params={"amount": 1}),
        "DepositIns1e8": _make_step_primitive(action="deposit_insurance", params={"amount": 100_000_000}),
        "DepositIns1e12": _make_step_primitive(action="deposit_insurance", params={"amount": 1_000_000_000_000}),
        "Claim1": _make_step_primitive(action="apply_insurance_claim", params={"claim_amount": 1, "auth_ok": True}),
        "Claim1e8": _make_step_primitive(action="apply_insurance_claim", params={"claim_amount": 100_000_000, "auth_ok": True}),
        # Scenario helpers (multi-step)
        "Bootstrap": _make_multi_step_primitive(
            steps=[
                {"action": "advance_epoch", "params": {"delta": 1}},
                {"action": "publish_clearing_price", "params": {"price_e8": 100_000_000}},
                {"action": "settle_epoch", "params": {}},
            ]
        ),
        "CycleLow": _make_multi_step_primitive(
            steps=[
                {"action": "advance_epoch", "params": {"delta": 1}},
                {"action": "publish_clearing_price", "params": {"price_e8": 1}},
                {"action": "settle_epoch", "params": {}},
            ]
        ),
        "Cycle2": _make_multi_step_primitive(
            steps=[
                {"action": "advance_epoch", "params": {"delta": 1}},
                {"action": "publish_clearing_price", "params": {"price_e8": 200_000_000}},
                {"action": "settle_epoch", "params": {}},
            ]
        ),
        "CycleHigh": _make_multi_step_primitive(
            steps=[
                {"action": "advance_epoch", "params": {"delta": 1}},
                {"action": "publish_clearing_price", "params": {"price_e8": 1_000_000_000_000}},
                {"action": "settle_epoch", "params": {}},
            ]
        ),
        "LiqLongShock": _make_multi_step_primitive(
            steps=[
                {"action": "deposit_collateral", "params": {"amount": 1_000_000_000_000, "auth_ok": True}},
                {"action": "set_position", "params": {"new_position_base": 1_000_000, "auth_ok": True}},
                {"action": "advance_epoch", "params": {"delta": 1}},
                {"action": "publish_clearing_price", "params": {"price_e8": 1}},
                {"action": "settle_epoch", "params": {}},
            ]
        ),
        "LiqShortShock": _make_multi_step_primitive(
            steps=[
                {"action": "deposit_collateral", "params": {"amount": 1_000_000_000_000, "auth_ok": True}},
                {"action": "set_position", "params": {"new_position_base": -1_000_000, "auth_ok": True}},
                {"action": "advance_epoch", "params": {"delta": 1}},
                {"action": "publish_clearing_price", "params": {"price_e8": 1_000_000_000_000}},
                {"action": "settle_epoch", "params": {}},
            ]
        ),
        "FundingWhipsawLong": _make_multi_step_primitive(
            steps=[
                {"action": "set_position", "params": {"new_position_base": 1_000_000, "auth_ok": True}},
                {"action": "apply_funding", "params": {"new_rate_bps": 10000, "auth_ok": True}},
                {"action": "apply_funding", "params": {"new_rate_bps": -10000, "auth_ok": True}},
                {"action": "advance_epoch", "params": {"delta": 1}},
                {"action": "publish_clearing_price", "params": {"price_e8": 200_000_000}},
                {"action": "settle_epoch", "params": {}},
            ]
        ),
        "FundingWhipsawShort": _make_multi_step_primitive(
            steps=[
                {"action": "set_position", "params": {"new_position_base": -1_000_000, "auth_ok": True}},
                {"action": "apply_funding", "params": {"new_rate_bps": -10000, "auth_ok": True}},
                {"action": "apply_funding", "params": {"new_rate_bps": 10000, "auth_ok": True}},
                {"action": "advance_epoch", "params": {"delta": 1}},
                {"action": "publish_clearing_price", "params": {"price_e8": 200_000_000}},
                {"action": "settle_epoch", "params": {}},
            ]
        ),
        "InsuranceDrain": _make_multi_step_primitive(
            steps=[
                {"action": "deposit_insurance", "params": {"amount": 1}},
                {"action": "apply_insurance_claim", "params": {"claim_amount": 1, "auth_ok": True}},
                {"action": "deposit_insurance", "params": {"amount": 100_000_000}},
                {"action": "apply_insurance_claim", "params": {"claim_amount": 100_000_000, "auth_ok": True}},
            ]
        ),
        "RoundTripCollateral": _make_multi_step_primitive(
            steps=[
                {"action": "deposit_collateral", "params": {"amount": 1_000_000_000_000, "auth_ok": True}},
                {"action": "withdraw_collateral", "params": {"amount": 1_000_000_000_000, "auth_ok": True}},
            ]
        ),
        "BreakerPulse": _make_multi_step_primitive(
            steps=[
                {"action": "set_position", "params": {"new_position_base": 1_000_000, "auth_ok": True}},
                {"action": "apply_funding", "params": {"new_rate_bps": 10000, "auth_ok": True}},
                {"action": "advance_epoch", "params": {"delta": 1}},
                {"action": "publish_clearing_price", "params": {"price_e8": 1}},
                {"action": "settle_epoch", "params": {}},
                {"action": "clear_breaker", "params": {"auth_ok": True}},
                {"action": "advance_epoch", "params": {"delta": 1}},
                {"action": "publish_clearing_price", "params": {"price_e8": 1_000_000_000_000}},
                {"action": "settle_epoch", "params": {}},
            ]
        ),
        "EpochWarpFlip": _make_multi_step_primitive(
            steps=[
                {"action": "set_position", "params": {"new_position_base": 1_000_000, "auth_ok": True}},
                {"action": "advance_epoch", "params": {"delta": 100}},
                {"action": "publish_clearing_price", "params": {"price_e8": 200_000_000}},
                {"action": "settle_epoch", "params": {}},
                {"action": "set_position", "params": {"new_position_base": -1_000_000, "auth_ok": True}},
                {"action": "advance_epoch", "params": {"delta": 100}},
                {"action": "publish_clearing_price", "params": {"price_e8": 100_000_000}},
                {"action": "settle_epoch", "params": {}},
            ]
        ),
        "InsuranceOscillation": _make_multi_step_primitive(
            steps=[
                {"action": "deposit_insurance", "params": {"amount": 1_000_000_000_000}},
                {"action": "apply_insurance_claim", "params": {"claim_amount": 100_000_000, "auth_ok": True}},
                {"action": "deposit_insurance", "params": {"amount": 1}},
                {"action": "apply_insurance_claim", "params": {"claim_amount": 1, "auth_ok": True}},
                {"action": "deposit_insurance", "params": {"amount": 100_000_000}},
            ]
        ),
    }
    rt = MorphRuntime(primitives=dict(primitives))

    # Ensure the default sigma0 representation schema is available even if the caller
    # provides a minimal sigma0.json.
    _ = init_native, init_ref
    return rt
