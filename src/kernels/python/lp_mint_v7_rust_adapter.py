"""Rust-backed ESSO shell adapter for `lp_mint_v7`.

Used with:
  python3 -m ESSO shell-lint src/kernels/dex/lp_mint_v7.yaml --adapter <this>:make_adapter
  python3 -m ESSO verify-shell src/kernels/dex/lp_mint_v7.yaml --adapter <this>:make_adapter

The adapter binds the ESSO LP mint model to the Rust `lp_math_v7` CLI surface.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Mapping

from .lp_math_v7_rust_adapter_common import is_rust_ok, run_rust_lp_math


IR_HASH = "sha256:5f97005645c6b8297186259d76494fd2b66d2da9d760ffcddafacbfc1de22c24"
MIN_LP_LOCK = 1000
MAX_RESERVE = 3_000_000_000
MAX_LP_SUPPLY = 3_000_000_000


def _step_error(code: str, message: str) -> Any:
    from ESSO.kernel.interpreter import StepError  # type: ignore

    return StepError(code=code, message=message)


def _guard_false(action_id: str) -> Any:
    return _step_error("GuardFalse", f"guard false for action '{action_id}'")


def _state_within_model_bounds(state: Mapping[str, Any]) -> bool:
    return (
        0 <= int(state["reserve0_before"]) <= MAX_RESERVE
        and 0 <= int(state["reserve0"]) <= MAX_RESERVE
        and 0 <= int(state["reserve1_before"]) <= MAX_RESERVE
        and 0 <= int(state["reserve1"]) <= MAX_RESERVE
        and 0 <= int(state["lp_supply_before"]) <= MAX_LP_SUPPLY
        and 0 <= int(state["lp_supply"]) <= MAX_LP_SUPPLY
        and int(state["locked_liquidity"]) in {0, MIN_LP_LOCK}
    )


@dataclass
class LpMintV7RustAdapter:
    ir: Any
    _state: dict[str, Any] = field(default_factory=dict)
    _pending_effects: dict[str, Any] = field(default_factory=dict)

    def reset(self, *, state: Mapping[str, Any]) -> None:
        self._state = dict(state)
        self._pending_effects = {}

    def get_state(self) -> Mapping[str, Any]:
        return dict(self._state)

    def apply(self, command: Any) -> Any:
        self._pending_effects = {}
        handler = ACTION_HANDLERS.get(str(getattr(command, "tag", "")))
        if handler is None:
            return _step_error("UnknownAction", "no handler for command.tag")

        res = handler(self, command)
        from ESSO.kernel.interpreter import StepOk  # type: ignore

        if isinstance(res, StepOk):
            self._state = dict(res.state)
            for eff_id, value in res.effects.items():
                eff_handler = EFFECT_HANDLERS.get(str(eff_id))
                if eff_handler is not None:
                    eff_handler(self, str(eff_id), value)
        return res

    def drain_effects(self) -> Mapping[str, Any]:
        out = dict(self._pending_effects)
        self._pending_effects = {}
        return out


def _handle_mint_initial(adapter: LpMintV7RustAdapter, command: Any) -> Any:
    from ESSO.kernel.interpreter import StepOk  # type: ignore

    action_id = "mint_initial"
    state = adapter._state
    args = dict(getattr(command, "args", {}) or {})
    reserve0 = int(state["reserve0"])
    reserve1 = int(state["reserve1"])
    lp_supply = int(state["lp_supply"])
    locked = int(state["locked_liquidity"])
    amount0 = int(args["amount0"])
    amount1 = int(args["amount1"])
    sqrt_product = int(args["sqrt_product"])

    if not (reserve0 == 0 and reserve1 == 0 and lp_supply == 0 and locked == 0):
        return _guard_false(action_id)

    payload = run_rust_lp_math("mint_initial_witness", amount0, amount1, sqrt_product)
    if not is_rust_ok(payload):
        return _guard_false(action_id)
    result = dict(payload["result"])
    minted = int(result["liquidity_minted"])
    total_supply = int(result["total_supply"])
    if total_supply != minted + MIN_LP_LOCK:
        return _guard_false(action_id)

    new_state = dict(state)
    new_state["reserve0_before"] = reserve0
    new_state["reserve1_before"] = reserve1
    new_state["lp_supply_before"] = lp_supply
    new_state["reserve0"] = amount0
    new_state["reserve1"] = amount1
    new_state["lp_supply"] = minted
    new_state["locked_liquidity"] = MIN_LP_LOCK
    if not _state_within_model_bounds(new_state):
        return _guard_false(action_id)

    effects = {
        "liquidity_minted": minted,
        "amount0_used": amount0,
        "amount1_used": amount1,
        "total_supply": total_supply,
        "amount0_refund": 0,
        "amount1_refund": 0,
    }
    return StepOk(state=new_state, effects=effects)


def _handle_mint(adapter: LpMintV7RustAdapter, command: Any) -> Any:
    from ESSO.kernel.interpreter import StepOk  # type: ignore

    action_id = "mint"
    state = adapter._state
    args = dict(getattr(command, "args", {}) or {})
    reserve0 = int(state["reserve0"])
    reserve1 = int(state["reserve1"])
    lp_supply = int(state["lp_supply"])
    locked = int(state["locked_liquidity"])
    amount0 = int(args["amount0"])
    amount1 = int(args["amount1"])
    min_liquidity = int(args["min_liquidity"])

    if not (reserve0 > 0 and reserve1 > 0 and locked == MIN_LP_LOCK):
        return _guard_false(action_id)
    if reserve0 + amount0 > MAX_RESERVE or reserve1 + amount1 > MAX_RESERVE:
        return _guard_false(action_id)

    total_supply_pre = lp_supply + locked
    payload = run_rust_lp_math("mint", reserve0, reserve1, total_supply_pre, amount0, amount1, min_liquidity)
    if not is_rust_ok(payload):
        return _guard_false(action_id)
    result = dict(payload["result"])

    new_total_supply = int(result["new_total_supply"])
    if new_total_supply < locked:
        return _guard_false(action_id)

    new_state = dict(state)
    new_state["reserve0_before"] = reserve0
    new_state["reserve1_before"] = reserve1
    new_state["lp_supply_before"] = lp_supply
    new_state["reserve0"] = int(result["new_reserve0"])
    new_state["reserve1"] = int(result["new_reserve1"])
    new_state["lp_supply"] = new_total_supply - locked
    new_state["locked_liquidity"] = locked
    if not _state_within_model_bounds(new_state):
        return _guard_false(action_id)

    effects = {
        "liquidity_minted": int(result["liquidity_minted"]),
        "amount0_used": int(result["amount0_used"]),
        "amount1_used": int(result["amount1_used"]),
        "total_supply": new_total_supply,
        "amount0_refund": int(result["amount0_refund"]),
        "amount1_refund": int(result["amount1_refund"]),
    }
    return StepOk(state=new_state, effects=effects)


def _commit_effect(adapter: LpMintV7RustAdapter, effect_id: str, value: Any) -> None:
    adapter._pending_effects[str(effect_id)] = value


ACTION_HANDLERS: dict[str, Callable[[LpMintV7RustAdapter, Any], Any]] = {
    "mint_initial": _handle_mint_initial,
    "mint": _handle_mint,
}

EFFECT_HANDLERS: dict[str, Callable[[LpMintV7RustAdapter, str, Any], None]] = {
    "liquidity_minted": _commit_effect,
    "amount0_used": _commit_effect,
    "amount1_used": _commit_effect,
    "total_supply": _commit_effect,
    "amount0_refund": _commit_effect,
    "amount1_refund": _commit_effect,
}


def make_adapter(ir: Any) -> LpMintV7RustAdapter:
    return LpMintV7RustAdapter(ir=ir)
