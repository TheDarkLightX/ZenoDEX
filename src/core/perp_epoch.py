"""
Epoch-based perpetuals: isolated-margin linear perp risk engine (wrapper).

This module provides a stable `initial_state` / `apply` interface for the rest
of the codebase.

Two “sources of truth” coexist:
- A formal YAML state-machine specification (“kernel”) under `src/kernels/dex/`.
- A hand-written Python implementation under `src/core/perp_v2/`.

Backends:
- Spec interpreter (optional): loads and steps the YAML kernel directly using an
  optional private toolchain (vendored under `external/` and git-ignored). The
  toolchain is a deterministic verifier + interpreter + code generator for YAML
  kernels. It is not required at production runtime, but it is used by evidence
  gates.
- Native (default): executes `src/core/perp_v4/`, which is kept equivalent to the
  YAML kernel via parity tests against a generated, dependency-free Python
  reference model committed under `generated/perp_python/`.

Default posture: v4 native. The v3 spec and native entry points remain available
for explicit replay and migration comparison.
"""

from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path
from typing import Any, Mapping

try:
    import yaml  # type: ignore[import-untyped]

    _YAML_AVAILABLE = True
except ImportError:  # pragma: no cover - optional dependency in some environments
    yaml = None
    _YAML_AVAILABLE = False


# Kernel values are JSON-like scalars used by both the spec interpreter backend
# and the generated reference models.
Value = bool | int | str


@dataclass(frozen=True)
class PerpStepResult:
    ok: bool
    state: dict[str, Value] | None = None
    effects: dict[str, Value] | None = None
    error: str | None = None
    code: str | None = None


def _model_path_v1() -> Path:
    # src/core/perp_epoch.py -> src/ -> kernels/dex/perp_epoch_isolated_v1.yaml
    return Path(__file__).resolve().parents[1].joinpath("kernels", "dex", "perp_epoch_isolated_v1.yaml")


def _model_path_v1_1() -> Path:
    # src/core/perp_epoch.py -> src/ -> kernels/dex/perp_epoch_isolated_v1_1.yaml
    return Path(__file__).resolve().parents[1].joinpath("kernels", "dex", "perp_epoch_isolated_v1_1.yaml")


def _model_path_v2() -> Path:
    # src/core/perp_epoch.py -> src/ -> kernels/dex/perp_epoch_isolated_v2.yaml
    return Path(__file__).resolve().parents[1].joinpath("kernels", "dex", "perp_epoch_isolated_v2.yaml")


def _model_path_v3() -> Path:
    # src/core/perp_epoch.py -> src/ -> kernels/dex/perp_epoch_isolated_v3.yaml
    return Path(__file__).resolve().parents[1].joinpath("kernels", "dex", "perp_epoch_isolated_v3.yaml")


def _model_path_v4() -> Path:
    # src/core/perp_epoch.py -> src/ -> kernels/dex/perp_epoch_isolated_v4.yaml
    return Path(__file__).resolve().parents[1].joinpath("kernels", "dex", "perp_epoch_isolated_v4.yaml")


def _load_yaml_model(path: Path):
    if not _YAML_AVAILABLE:
        raise RuntimeError("PyYAML is required to load kernel YAML models (pip install pyyaml)")
    from ESSO.ir.schema import CandidateIR

    obj = yaml.safe_load(path.read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise TypeError("model YAML must be a mapping")
    return CandidateIR.from_json_dict(obj).canonicalized()


@lru_cache(maxsize=1)
def _kernel_ctx_v1():
    from ESSO.evolve import ir_hash
    from ESSO.kernel.interpreter import StepError, prepare_step_context

    path = _model_path_v1()
    ir = _load_yaml_model(path)
    ctx = prepare_step_context(ir)
    if isinstance(ctx, StepError):
        raise RuntimeError(f"perp kernel invalid: {ctx.code}: {ctx.message}")

    # Adapters pin the expected spec hash so regenerated artifacts cannot drift
    # silently from the checked/verified model.
    try:
        from ..kernels.python.perp_epoch_isolated_v1_adapter import IR_HASH as expected_hash

        if isinstance(expected_hash, str) and expected_hash and expected_hash != ir_hash(ir):
            raise RuntimeError(f"perp kernel IR hash mismatch: adapter={expected_hash} model={ir_hash(ir)}")
    except ImportError:
        # Best-effort only; runtime can still operate with the loaded IR.
        pass

    return ir, ctx


def perp_epoch_isolated_v1_initial_state() -> dict[str, Value]:
    from ESSO.kernel.simulate import initial_state

    ir, _ctx = _kernel_ctx_v1()
    return dict(initial_state(ir))


def perp_epoch_isolated_v1_apply(
    *, state: Mapping[str, Value], action: str, params: Mapping[str, Value] | None = None
) -> PerpStepResult:
    from ESSO.kernel.interpreter import Command, StepError, step_ctx

    _ir, ctx = _kernel_ctx_v1()
    cmd = Command(tag=str(action), args=dict(params or {}))
    res = step_ctx(dict(state), cmd, ctx)
    if isinstance(res, StepError):
        return PerpStepResult(ok=False, error=res.message, code=res.code)
    return PerpStepResult(ok=True, state=dict(res.state), effects=dict(res.effects))


def _state_var_int_max(ir, *, var_id: str) -> int:
    for v in ir.state_vars:
        if getattr(v, "id", None) != var_id:
            continue
        t = getattr(v, "type", None)
        if getattr(t, "kind", None) != "int":
            raise TypeError(f"{var_id} is not an int state var")
        mx = getattr(t, "max", None)
        if not isinstance(mx, int) or isinstance(mx, bool):
            raise TypeError(f"{var_id}.max is not an int")
        return int(mx)
    raise KeyError(f"state var not found: {var_id}")


def perp_epoch_isolated_v1_fee_pool_max_quote() -> int:
    ir, _ctx = _kernel_ctx_v1()
    return _state_var_int_max(ir, var_id="fee_pool_quote")


@lru_cache(maxsize=1)
def _kernel_ctx_v1_1():
    from ESSO.evolve import ir_hash
    from ESSO.kernel.interpreter import StepError, prepare_step_context

    path = _model_path_v1_1()
    ir = _load_yaml_model(path)
    ctx = prepare_step_context(ir)
    if isinstance(ctx, StepError):
        raise RuntimeError(f"perp kernel invalid: {ctx.code}: {ctx.message}")

    try:
        from ..kernels.python.perp_epoch_isolated_v1_1_adapter import IR_HASH as expected_hash

        if isinstance(expected_hash, str) and expected_hash and expected_hash != ir_hash(ir):
            raise RuntimeError(f"perp kernel IR hash mismatch: adapter={expected_hash} model={ir_hash(ir)}")
    except ImportError:
        pass

    return ir, ctx


def perp_epoch_isolated_v1_1_initial_state() -> dict[str, Value]:
    from ESSO.kernel.simulate import initial_state

    ir, _ctx = _kernel_ctx_v1_1()
    return dict(initial_state(ir))


def perp_epoch_isolated_v1_1_apply(
    *, state: Mapping[str, Value], action: str, params: Mapping[str, Value] | None = None
) -> PerpStepResult:
    from ESSO.kernel.interpreter import Command, StepError, step_ctx

    _ir, ctx = _kernel_ctx_v1_1()
    cmd = Command(tag=str(action), args=dict(params or {}))
    res = step_ctx(dict(state), cmd, ctx)
    if isinstance(res, StepError):
        return PerpStepResult(ok=False, error=res.message, code=res.code)
    return PerpStepResult(ok=True, state=dict(res.state), effects=dict(res.effects))


def perp_epoch_isolated_v1_1_fee_pool_max_quote() -> int:
    ir, _ctx = _kernel_ctx_v1_1()
    return _state_var_int_max(ir, var_id="fee_pool_quote")


@lru_cache(maxsize=1)
def _kernel_ctx_v2():
    from ESSO.evolve import ir_hash
    from ESSO.kernel.interpreter import StepError, prepare_step_context

    path = _model_path_v2()
    ir = _load_yaml_model(path)
    ctx = prepare_step_context(ir)
    if isinstance(ctx, StepError):
        raise RuntimeError(f"perp kernel invalid: {ctx.code}: {ctx.message}")

    try:
        from ..kernels.python.perp_epoch_isolated_v2_adapter import IR_HASH as expected_hash

        if isinstance(expected_hash, str) and expected_hash and expected_hash != ir_hash(ir):
            raise RuntimeError(f"perp kernel IR hash mismatch: adapter={expected_hash} model={ir_hash(ir)}")
    except ImportError:
        pass

    return ir, ctx


def perp_epoch_isolated_v2_initial_state() -> dict[str, Value]:
    from ESSO.kernel.simulate import initial_state

    ir, _ctx = _kernel_ctx_v2()
    return dict(initial_state(ir))


def perp_epoch_isolated_v2_apply(
    *, state: Mapping[str, Value], action: str, params: Mapping[str, Value] | None = None
) -> PerpStepResult:
    from ESSO.kernel.interpreter import Command, StepError, step_ctx

    _ir, ctx = _kernel_ctx_v2()
    cmd = Command(tag=str(action), args=dict(params or {}))
    res = step_ctx(dict(state), cmd, ctx)
    if isinstance(res, StepError):
        return PerpStepResult(ok=False, error=res.message, code=res.code)
    return PerpStepResult(ok=True, state=dict(res.state), effects=dict(res.effects))


def perp_epoch_isolated_v2_fee_pool_max_quote() -> int:
    ir, _ctx = _kernel_ctx_v2()
    return _state_var_int_max(ir, var_id="fee_pool_quote")


@lru_cache(maxsize=1)
def _kernel_ctx_v3():
    from ESSO.evolve import ir_hash
    from ESSO.kernel.interpreter import StepError, prepare_step_context

    path = _model_path_v3()
    ir = _load_yaml_model(path)
    ctx = prepare_step_context(ir)
    if isinstance(ctx, StepError):
        raise RuntimeError(f"perp kernel invalid: {ctx.code}: {ctx.message}")

    try:
        from ..kernels.python.perp_epoch_isolated_v3_adapter import IR_HASH as expected_hash

        if isinstance(expected_hash, str) and expected_hash and expected_hash != ir_hash(ir):
            raise RuntimeError(f"perp kernel IR hash mismatch: adapter={expected_hash} model={ir_hash(ir)}")
    except ImportError:
        pass

    return ir, ctx


def perp_epoch_isolated_v3_initial_state() -> dict[str, Value]:
    from ESSO.kernel.simulate import initial_state

    ir, _ctx = _kernel_ctx_v3()
    return dict(initial_state(ir))


def perp_epoch_isolated_v3_apply(
    *, state: Mapping[str, Value], action: str, params: Mapping[str, Value] | None = None
) -> PerpStepResult:
    from ESSO.kernel.interpreter import Command, StepError, step_ctx

    _ir, ctx = _kernel_ctx_v3()
    cmd = Command(tag=str(action), args=dict(params or {}))
    res = step_ctx(dict(state), cmd, ctx)
    if isinstance(res, StepError):
        return PerpStepResult(ok=False, error=res.message, code=res.code)
    return PerpStepResult(ok=True, state=dict(res.state), effects=dict(res.effects))


def perp_epoch_isolated_v3_fee_pool_max_quote() -> int:
    ir, _ctx = _kernel_ctx_v3()
    return _state_var_int_max(ir, var_id="fee_pool_quote")


@lru_cache(maxsize=1)
def _kernel_ctx_v4():
    from ESSO.evolve import ir_hash
    from ESSO.kernel.interpreter import StepError, prepare_step_context

    path = _model_path_v4()
    ir = _load_yaml_model(path)
    ctx = prepare_step_context(ir)
    if isinstance(ctx, StepError):
        raise RuntimeError(f"perp kernel invalid: {ctx.code}: {ctx.message}")

    try:
        from ..kernels.python.perp_epoch_isolated_v4_adapter import IR_HASH as expected_hash

        if isinstance(expected_hash, str) and expected_hash and expected_hash != ir_hash(ir):
            raise RuntimeError(f"perp kernel IR hash mismatch: adapter={expected_hash} model={ir_hash(ir)}")
    except ImportError:
        pass

    return ir, ctx


def perp_epoch_isolated_v4_initial_state() -> dict[str, Value]:
    from ESSO.kernel.simulate import initial_state

    ir, _ctx = _kernel_ctx_v4()
    return dict(initial_state(ir))


def perp_epoch_isolated_v4_apply(
    *, state: Mapping[str, Value], action: str, params: Mapping[str, Value] | None = None
) -> PerpStepResult:
    from ESSO.kernel.interpreter import Command, StepError, step_ctx

    _ir, ctx = _kernel_ctx_v4()
    cmd = Command(tag=str(action), args=dict(params or {}))
    res = step_ctx(dict(state), cmd, ctx)
    if isinstance(res, StepError):
        return PerpStepResult(ok=False, error=res.message, code=res.code)
    return PerpStepResult(ok=True, state=dict(res.state), effects=dict(res.effects))


def perp_epoch_isolated_v4_fee_pool_max_quote() -> int:
    ir, _ctx = _kernel_ctx_v4()
    return _state_var_int_max(ir, var_id="fee_pool_quote")


# ---------------------------------------------------------------------------
# v2 native backend: uses hand-written src/core/perp_v2 (no external toolchain dependency)
# ---------------------------------------------------------------------------

_EPOCH_PHASE_STR_TO_INT: dict[str, int] = {
    "Open": 0,
    "PricePublished": 1,
    "Settled": 2,
}


def _normalize_native_state_for_kernel_abi_v3(state: Mapping[str, Value]) -> dict[str, Value]:
    """
    Normalize native state dict to the v3 kernel ABI.

    v3 adds the `epoch_phase` state var, encoded as an int:
      Open=0, PricePublished=1, Settled=2.
    """
    out = dict(state)
    ep = out.get("epoch_phase")
    if isinstance(ep, str):
        mapped = _EPOCH_PHASE_STR_TO_INT.get(ep)
        if mapped is not None:
            out["epoch_phase"] = int(mapped)
    return out


def _normalize_native_state_for_kernel_abi_v2(state: Mapping[str, Value]) -> dict[str, Value]:
    """
    Normalize native state dict to the v2 kernel ABI.

    v2 does not have `epoch_phase`; for parity with v2 kernels/refs, drop it.
    """
    out = dict(state)
    out.pop("epoch_phase", None)
    return out


def _infer_epoch_phase_for_native_input(state: Mapping[str, Value]) -> str:
    """
    Best-effort phase reconstruction for v2-shaped states that omit epoch_phase.
    """
    now = state.get("now_epoch")
    clearing_seen = bool(state.get("clearing_price_seen", False))
    clearing_epoch = state.get("clearing_price_epoch")
    oracle_seen = bool(state.get("oracle_seen", False))
    oracle_last = state.get("oracle_last_update_epoch")
    if (
        clearing_seen
        and isinstance(now, int)
        and not isinstance(now, bool)
        and isinstance(clearing_epoch, int)
        and not isinstance(clearing_epoch, bool)
        and int(clearing_epoch) == int(now)
    ):
        if (
            oracle_seen
            and isinstance(oracle_last, int)
            and not isinstance(oracle_last, bool)
            and int(oracle_last) == int(now)
        ):
            return "Settled"
        return "PricePublished"
    return "Open"


def _state_with_epoch_phase_for_native_input(state: Mapping[str, Value]) -> dict[str, Value]:
    out = dict(state)
    if "epoch_phase" not in out:
        out["epoch_phase"] = _infer_epoch_phase_for_native_input(state)
    return out


def _require_native_int(value: object, *, name: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise TypeError(f"{name} must be an int")
    return int(value)


def _require_native_bool(value: object, *, name: str) -> bool:
    if not isinstance(value, bool):
        raise TypeError(f"{name} must be a bool")
    return bool(value)


def perp_epoch_isolated_v2_native_initial_state() -> dict[str, Value]:
    from .perp_v2 import initial_state
    from .perp_v2.state import state_to_dict

    return _normalize_native_state_for_kernel_abi_v2(state_to_dict(initial_state()))


def perp_epoch_isolated_v3_native_initial_state() -> dict[str, Value]:
    from .perp_v2 import initial_state
    from .perp_v2.state import state_to_dict

    return _normalize_native_state_for_kernel_abi_v3(state_to_dict(initial_state()))


def perp_epoch_isolated_v4_native_initial_state() -> dict[str, Value]:
    from .perp_v4 import initial_state, state_to_dict

    return _normalize_native_state_for_kernel_abi_v3(state_to_dict(initial_state()))


def perp_epoch_isolated_v3_to_v4_migrate(
    state: Mapping[str, Value],
) -> dict[str, Value]:
    """Validate an unchanged-ABI v3 state against the stronger v4 invariants.

    The migration is identity on accepted state bytes. Accounts that depended
    on nested-floor undercollateralization must top up or close under v3 before
    migration; v4 never fabricates collateral or silently liquidates them.
    """
    from .perp_v4 import state_from_dict, state_to_dict
    from .perp_v4.invariants import check_all

    candidate = state_from_dict(_state_with_epoch_phase_for_native_input(state))
    violations = check_all(candidate)
    if violations:
        raise ValueError(f"v4_migration_invariant:{','.join(violations)}")
    return _normalize_native_state_for_kernel_abi_v3(state_to_dict(candidate))


def _action_params_from_dict(action: str, params: Mapping[str, Value] | None):
    """Translate (action_str, params_dict) to a perp_v2 ActionParams.

    This is deliberately strict/fail-closed:
    - unknown actions raise ValueError
    - missing required keys raise KeyError
    - type mismatches raise TypeError/ValueError

    Note: unexpected keys are ignored here because the integration layer
    (`src/integration/perp_engine.py`) rejects unknown fields at the API boundary.
    """
    from .perp_v2.types import Action, ActionParams

    _field_map: dict[Action, list[tuple[str, str]]] = {
        Action.ADVANCE_EPOCH: [("delta", "delta")],
        Action.PUBLISH_CLEARING_PRICE: [("price_e8", "price_e8")],
        Action.SETTLE_EPOCH: [],
        Action.DEPOSIT_COLLATERAL: [("amount", "amount")],
        Action.WITHDRAW_COLLATERAL: [("amount", "amount")],
        Action.SET_POSITION: [("new_position_base", "new_position_base")],
        Action.CLEAR_BREAKER: [],
        Action.APPLY_FUNDING: [("new_rate_bps", "new_rate_bps")],
        Action.DEPOSIT_INSURANCE: [("amount", "amount")],
        Action.APPLY_INSURANCE_CLAIM: [("claim_amount", "claim_amount")],
        Action.PARTIAL_LIQUIDATE: [("fraction_bps", "fraction_bps")],
    }
    _auth_actions = frozenset({
        Action.DEPOSIT_COLLATERAL, Action.WITHDRAW_COLLATERAL,
        Action.SET_POSITION, Action.CLEAR_BREAKER,
        Action.APPLY_FUNDING, Action.APPLY_INSURANCE_CLAIM,
        Action.PARTIAL_LIQUIDATE,
    })

    p = dict(params or {})
    act = Action(action)
    fields = _field_map.get(act)
    if fields is None:
        raise ValueError(f"unknown action: {action}")

    kwargs: dict[str, Any] = {"action": act}
    for field_name, dict_key in fields:
        if act is Action.PARTIAL_LIQUIDATE and dict_key not in p:
            kwargs[field_name] = 0
        else:
            kwargs[field_name] = _require_native_int(p[dict_key], name=dict_key)
    if act in _auth_actions:
        kwargs["auth_ok"] = _require_native_bool(p.get("auth_ok", False), name="auth_ok")
    return ActionParams(**kwargs)


def _effect_to_dict(effect) -> dict[str, Value]:
    """Convert a perp_v2 Effect to a plain dict matching kernel effect keys."""
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


def perp_epoch_isolated_v2_native_apply(
    *, state: Mapping[str, Value], action: str, params: Mapping[str, Value] | None = None
) -> PerpStepResult:
    from .perp_v2 import step
    from .perp_v2.state import state_from_dict, state_to_dict

    def _code_from_rejection(reason: str) -> str | None:
        # Align native rejection classification with ESSO interpreter StepError codes
        # (see external/ESSO/ESSO/kernel/interpreter.py).
        if reason.startswith("unknown_action:"):
            return "UnknownAction"
        if reason.startswith("param_domain:"):
            return "ParamType"
        if reason == "guard":
            return "GuardFalse"
        if reason.startswith("invariant:"):
            return "PostInvariantViolation"
        return None

    try:
        perp_state = state_from_dict(_state_with_epoch_phase_for_native_input(state))
        action_params = _action_params_from_dict(action, params)
    except (KeyError, TypeError, ValueError) as exc:
        # Best-effort classification (fail-closed on ok=false regardless).
        code: str | None = None
        if isinstance(exc, KeyError):
            # Missing required field in state/params.
            code = "ParamShape"
        else:
            msg = str(exc)
            if msg.startswith("unknown action:"):
                code = "UnknownAction"
            else:
                code = "ParamType"
        return PerpStepResult(ok=False, error=str(exc), code=code)

    result = step(perp_state, action_params)
    if not result.accepted:
        reason = str(result.rejection or "")
        return PerpStepResult(ok=False, error=reason, code=_code_from_rejection(reason))

    return PerpStepResult(
        ok=True,
        state=_normalize_native_state_for_kernel_abi_v2(state_to_dict(result.state)),
        effects=_effect_to_dict(result.effect),
    )


def perp_epoch_isolated_v3_native_apply(
    *, state: Mapping[str, Value], action: str, params: Mapping[str, Value] | None = None
) -> PerpStepResult:
    # Same hand-written perp_v2 implementation, but normalized to the v3 ABI.
    from .perp_v2 import step
    from .perp_v2.state import state_from_dict, state_to_dict

    def _code_from_rejection(reason: str) -> str | None:
        # Keep classification aligned with v2 native posture.
        if reason.startswith("unknown_action:"):
            return "UnknownAction"
        if reason.startswith("param_domain:"):
            return "ParamType"
        if reason == "guard":
            return "GuardFalse"
        if reason.startswith("invariant:"):
            return "PostInvariantViolation"
        return None

    try:
        perp_state = state_from_dict(_state_with_epoch_phase_for_native_input(state))
        action_params = _action_params_from_dict(action, params)
    except (KeyError, TypeError, ValueError) as exc:
        code: str | None = None
        if isinstance(exc, KeyError):
            code = "ParamShape"
        else:
            msg = str(exc)
            if msg.startswith("unknown action:"):
                code = "UnknownAction"
            else:
                code = "ParamType"
        return PerpStepResult(ok=False, error=str(exc), code=code)

    result = step(perp_state, action_params)
    if not result.accepted:
        reason = str(result.rejection or "")
        return PerpStepResult(ok=False, error=reason, code=_code_from_rejection(reason))

    return PerpStepResult(
        ok=True,
        state=_normalize_native_state_for_kernel_abi_v3(state_to_dict(result.state)),
        effects=_effect_to_dict(result.effect),
    )


def perp_epoch_isolated_v4_native_apply(
    *, state: Mapping[str, Value], action: str, params: Mapping[str, Value] | None = None
) -> PerpStepResult:
    from .perp_v4 import state_from_dict, state_to_dict, step

    def _code_from_rejection(reason: str) -> str | None:
        if reason.startswith("unknown_action:"):
            return "UnknownAction"
        if reason.startswith("param_domain:"):
            return "ParamType"
        if reason == "guard":
            return "GuardFalse"
        if reason.startswith("invariant:"):
            return "PostInvariantViolation"
        return None

    try:
        perp_state = state_from_dict(_state_with_epoch_phase_for_native_input(state))
        action_params = _action_params_from_dict(action, params)
    except (KeyError, TypeError, ValueError) as exc:
        if isinstance(exc, KeyError):
            code: str | None = "ParamShape"
        elif str(exc).startswith("unknown action:"):
            code = "UnknownAction"
        else:
            code = "ParamType"
        return PerpStepResult(ok=False, error=str(exc), code=code)

    result = step(perp_state, action_params)
    if not result.accepted:
        reason = str(result.rejection or "")
        return PerpStepResult(ok=False, error=reason, code=_code_from_rejection(reason))

    return PerpStepResult(
        ok=True,
        state=_normalize_native_state_for_kernel_abi_v3(state_to_dict(result.state)),
        effects=_effect_to_dict(result.effect),
    )


def perp_epoch_isolated_v2_native_fee_pool_max_quote() -> int:
    from .perp_v2.math import MAX_COLLATERAL

    return MAX_COLLATERAL


# v3 native backend is the same hand-written implementation (perp_v2 package) but
# corresponds to the v3 kernel spec (`perp_epoch_isolated_v3.yaml`).
perp_epoch_isolated_v3_native_fee_pool_max_quote = perp_epoch_isolated_v2_native_fee_pool_max_quote
perp_epoch_isolated_v4_native_fee_pool_max_quote = perp_epoch_isolated_v2_native_fee_pool_max_quote


# Default posture: v4 native. v3 remains explicit for replay and migration tests.
perp_epoch_isolated_default_initial_state = perp_epoch_isolated_v4_native_initial_state
perp_epoch_isolated_default_apply = perp_epoch_isolated_v4_native_apply
perp_epoch_isolated_default_fee_pool_max_quote = perp_epoch_isolated_v4_native_fee_pool_max_quote
