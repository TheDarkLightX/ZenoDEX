"""
Epoch-based perpetuals (v1): isolated-margin linear perp risk engine.

This module is a thin, deterministic wrapper around the ESSO kernel:
`src/kernels/dex/perp_epoch_isolated_v1.yaml` and `src/kernels/dex/perp_epoch_isolated_v1_1.yaml`.

The kernel is the source of truth for guards/invariants; this file provides a
Python-friendly interface and stable loading/caching.
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


# NOTE: ESSO defines Value = bool|int|str for kernel states/effects.
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


def _load_yaml_model(path: Path):
    if not _YAML_AVAILABLE:
        raise RuntimeError("PyYAML is required to load ESSO-IR YAML models (pip install pyyaml)")
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


# Default posture: v1.1 (clamp + breaker).
perp_epoch_isolated_default_initial_state = perp_epoch_isolated_v1_1_initial_state
perp_epoch_isolated_default_apply = perp_epoch_isolated_v1_1_apply
perp_epoch_isolated_default_fee_pool_max_quote = perp_epoch_isolated_v1_1_fee_pool_max_quote
