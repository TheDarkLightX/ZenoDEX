"""
Epoch-based perpetuals: isolated-margin linear perp risk engine (wrapper).

This module provides a stable `initial_state` / `apply` interface for the rest
of the codebase.

Two “sources of truth” coexist:
- A formal YAML state-machine specification (“kernel”) under `src/kernels/dex/`.
- A hand-written Python implementation under `src/core/perp_v2/`.

Backends:
- Spec interpreter (optional): uses the `external/ESSO` toolchain to interpret the
  YAML kernel directly. ESSO (“Evolutionary State Space Optimizer”) is the verifier/
  interpreter/codegen tool used in this repo for kernel specs.
- Native (default): executes `src/core/perp_v2/`, which is kept equivalent to the
  YAML spec via parity tests against a generated Python reference model under
  `generated/perp_python/`.

Default posture: v2 native.
"""

from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path
from typing import Any, Mapping


try:
    import yaml  # type: ignore

    _YAML_AVAILABLE = True
except Exception:  # pragma: no cover - optional dependency in some environments
    yaml = None  # type: ignore[assignment]
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
    return Path(__file__).resolve().parents[1] / "kernels" / "dex" / "perp_epoch_isolated_v1.yaml"


def _model_path_v1_1() -> Path:
    # src/core/perp_epoch.py -> src/ -> kernels/dex/perp_epoch_isolated_v1_1.yaml
    return Path(__file__).resolve().parents[1] / "kernels" / "dex" / "perp_epoch_isolated_v1_1.yaml"


def _model_path_v2() -> Path:
    # src/core/perp_epoch.py -> src/ -> kernels/dex/perp_epoch_isolated_v2.yaml
    return Path(__file__).resolve().parents[1] / "kernels" / "dex" / "perp_epoch_isolated_v2.yaml"


def _load_yaml_model(path: Path):
    if not _YAML_AVAILABLE:
        raise RuntimeError("PyYAML is required to load kernel YAML models (pip install pyyaml)")
    from ESSO.ir.schema import CandidateIR  # type: ignore

    obj = yaml.safe_load(path.read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise TypeError("model YAML must be a mapping")
    return CandidateIR.from_json_dict(obj).canonicalized()


@lru_cache(maxsize=1)
def _kernel_ctx_v1():
    from ESSO.evolve import ir_hash  # type: ignore
    from ESSO.kernel.interpreter import StepError, prepare_step_context  # type: ignore

    path = _model_path_v1()
    ir = _load_yaml_model(path)
    ctx = prepare_step_context(ir)
    if isinstance(ctx, StepError):
        raise RuntimeError(f"perp kernel invalid: {ctx.code}: {ctx.message}")

    # Keep adapter IR_HASH binding honest if present.
    try:
        from ..kernels.python.perp_epoch_isolated_v1_adapter import IR_HASH as expected_hash

        if isinstance(expected_hash, str) and expected_hash and expected_hash != ir_hash(ir):
            raise RuntimeError(f"perp kernel IR hash mismatch: adapter={expected_hash} model={ir_hash(ir)}")
    except Exception:
        # Best-effort only; runtime can still operate with the loaded IR.
        pass

    return ir, ctx


def perp_epoch_isolated_v1_initial_state() -> dict[str, Value]:
    from ESSO.kernel.simulate import initial_state  # type: ignore

    ir, _ctx = _kernel_ctx_v1()
    return dict(initial_state(ir))


def perp_epoch_isolated_v1_apply(
    *, state: Mapping[str, Value], action: str, params: Mapping[str, Value] | None = None
) -> PerpStepResult:
    from ESSO.kernel.interpreter import Command, StepError, step_ctx  # type: ignore

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
    from ESSO.evolve import ir_hash  # type: ignore
    from ESSO.kernel.interpreter import StepError, prepare_step_context  # type: ignore

    path = _model_path_v1_1()
    ir = _load_yaml_model(path)
    ctx = prepare_step_context(ir)
    if isinstance(ctx, StepError):
        raise RuntimeError(f"perp kernel invalid: {ctx.code}: {ctx.message}")

    try:
        from ..kernels.python.perp_epoch_isolated_v1_1_adapter import IR_HASH as expected_hash

        if isinstance(expected_hash, str) and expected_hash and expected_hash != ir_hash(ir):
            raise RuntimeError(f"perp kernel IR hash mismatch: adapter={expected_hash} model={ir_hash(ir)}")
    except Exception:
        pass

    return ir, ctx


def perp_epoch_isolated_v1_1_initial_state() -> dict[str, Value]:
    from ESSO.kernel.simulate import initial_state  # type: ignore

    ir, _ctx = _kernel_ctx_v1_1()
    return dict(initial_state(ir))


def perp_epoch_isolated_v1_1_apply(
    *, state: Mapping[str, Value], action: str, params: Mapping[str, Value] | None = None
) -> PerpStepResult:
    from ESSO.kernel.interpreter import Command, StepError, step_ctx  # type: ignore

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
    from ESSO.evolve import ir_hash  # type: ignore
    from ESSO.kernel.interpreter import StepError, prepare_step_context  # type: ignore

    path = _model_path_v2()
    ir = _load_yaml_model(path)
    ctx = prepare_step_context(ir)
    if isinstance(ctx, StepError):
        raise RuntimeError(f"perp kernel invalid: {ctx.code}: {ctx.message}")

    try:
        from ..kernels.python.perp_epoch_isolated_v2_adapter import IR_HASH as expected_hash

        if isinstance(expected_hash, str) and expected_hash and expected_hash != ir_hash(ir):
            raise RuntimeError(f"perp kernel IR hash mismatch: adapter={expected_hash} model={ir_hash(ir)}")
    except Exception:
        pass

    return ir, ctx


def perp_epoch_isolated_v2_initial_state() -> dict[str, Value]:
    from ESSO.kernel.simulate import initial_state  # type: ignore

    ir, _ctx = _kernel_ctx_v2()
    return dict(initial_state(ir))


def perp_epoch_isolated_v2_apply(
    *, state: Mapping[str, Value], action: str, params: Mapping[str, Value] | None = None
) -> PerpStepResult:
    from ESSO.kernel.interpreter import Command, StepError, step_ctx  # type: ignore

    _ir, ctx = _kernel_ctx_v2()
    cmd = Command(tag=str(action), args=dict(params or {}))
    res = step_ctx(dict(state), cmd, ctx)
    if isinstance(res, StepError):
        return PerpStepResult(ok=False, error=res.message, code=res.code)
    return PerpStepResult(ok=True, state=dict(res.state), effects=dict(res.effects))


def perp_epoch_isolated_v2_fee_pool_max_quote() -> int:
    ir, _ctx = _kernel_ctx_v2()
    return _state_var_int_max(ir, var_id="fee_pool_quote")


# ---------------------------------------------------------------------------
# v2 native backend: uses hand-written src/core/perp_v2 (no external toolchain dependency)
# ---------------------------------------------------------------------------

def perp_epoch_isolated_v2_native_initial_state() -> dict[str, Value]:
    from .perp_v2 import initial_state
    from .perp_v2.state import state_to_dict

    return state_to_dict(initial_state())


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
    }
    _auth_actions = frozenset({
        Action.DEPOSIT_COLLATERAL, Action.WITHDRAW_COLLATERAL,
        Action.SET_POSITION, Action.CLEAR_BREAKER,
        Action.APPLY_FUNDING, Action.APPLY_INSURANCE_CLAIM,
    })

    p = dict(params or {})
    act = Action(action)
    fields = _field_map.get(act)
    if fields is None:
        raise ValueError(f"unknown action: {action}")

    kwargs: dict[str, Any] = {"action": act}
    for field_name, dict_key in fields:
        kwargs[field_name] = int(p[dict_key])
    if act in _auth_actions:
        kwargs["auth_ok"] = bool(p.get("auth_ok", False))
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

    try:
        perp_state = state_from_dict(state)
        action_params = _action_params_from_dict(action, params)
    except (KeyError, TypeError, ValueError) as exc:
        return PerpStepResult(ok=False, error=str(exc))

    result = step(perp_state, action_params)
    if not result.accepted:
        return PerpStepResult(ok=False, error=result.rejection)

    return PerpStepResult(
        ok=True,
        state=state_to_dict(result.state),
        effects=_effect_to_dict(result.effect),
    )


def perp_epoch_isolated_v2_native_fee_pool_max_quote() -> int:
    from .perp_v2.math import MAX_COLLATERAL

    return MAX_COLLATERAL


# Default posture: v2 native (oracle-equivalence tested, no external toolchain dependency).
perp_epoch_isolated_default_initial_state = perp_epoch_isolated_v2_native_initial_state
perp_epoch_isolated_default_apply = perp_epoch_isolated_v2_native_apply
perp_epoch_isolated_default_fee_pool_max_quote = perp_epoch_isolated_v2_native_fee_pool_max_quote
