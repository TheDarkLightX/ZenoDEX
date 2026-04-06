"""Native (non-interpreter) shell adapter for `zusd_oracle_commit_apply_v1`.

Used with:
  python3 -m ESSO shell-lint src/kernels/dex/zusd_oracle_commit_apply_v1.yaml --adapter <this>:make_adapter
  python3 -m ESSO verify-shell src/kernels/dex/zusd_oracle_commit_apply_v1.yaml --adapter <this>:make_adapter
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Mapping


# Derived from:
# `python3 -m ESSO validate src/kernels/dex/zusd_oracle_commit_apply_v1.yaml`.
IR_HASH = "sha256:995cf7af1940f23973233a7665416a0789250e8701e68a62ee17d2713be5bfca"


def _guard_false(action_id: str) -> Any:
    from ESSO.kernel.interpreter import StepError  # type: ignore

    return StepError(code="GuardFalse", message=f"guard false for action '{action_id}'")


@dataclass
class ZUSDOracleCommitApplyV1NativeAdapter:
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
            from ESSO.kernel.interpreter import StepError  # type: ignore

            return StepError(code="UnknownAction", message="no handler for command.tag")

        res = handler(self, command)
        from ESSO.kernel.interpreter import StepOk  # type: ignore

        if isinstance(res, StepOk):
            self._state = dict(res.state)
            for eff_id, value in res.effects.items():
                eff_handler = EFFECT_HANDLERS.get(str(eff_id))
                if eff_handler is None:
                    continue
                eff_handler(self, str(eff_id), value)
        return res

    def drain_effects(self) -> Mapping[str, Any]:
        out = dict(self._pending_effects)
        self._pending_effects = {}
        return out


def _handle_apply_oracle_commit(adapter: ZUSDOracleCommitApplyV1NativeAdapter, command: Any) -> Any:
    from ESSO.kernel.interpreter import StepOk  # type: ignore

    s = adapter._state
    action_id = "apply_oracle_commit"

    now_epoch = int(s["now_epoch"])
    oracle_seen = int(s["oracle_seen"])
    oracle_last_update_epoch = int(s["oracle_last_update_epoch"])
    price_e8 = int(s["price_e8"])
    price_pending_e8 = int(s["price_pending_e8"])
    max_oracle_staleness_epochs = int(s["max_oracle_staleness_epochs"])
    auth_ok = int(s["auth_ok"])
    mcr_ok_at_pending = int(s["mcr_ok_at_pending"])

    pending_le_active = price_pending_e8 <= price_e8
    fresh_ok = (now_epoch - oracle_last_update_epoch) <= max_oracle_staleness_epochs
    env_ok = (oracle_seen == 1) and pending_le_active and fresh_ok
    policy_ok = (auth_ok == 1) and (mcr_ok_at_pending == 1)
    oracle_commit_allowed = env_ok and policy_ok

    if not oracle_commit_allowed:
        return _guard_false(action_id)

    post = dict(s)
    post["price_e8"] = price_pending_e8
    post["oracle_last_update_epoch"] = now_epoch
    effects = {
        "pending_le_active": bool(pending_le_active),
        "fresh_ok": bool(fresh_ok),
        "env_ok": bool(env_ok),
        "policy_ok": bool(policy_ok),
        "oracle_commit_allowed": True,
        "price_after_e8": int(price_pending_e8),
        "oracle_last_update_after": int(now_epoch),
    }
    return StepOk(state=post, effects=effects)


def _commit_effect(adapter: ZUSDOracleCommitApplyV1NativeAdapter, effect_id: str, value: Any) -> None:
    adapter._pending_effects[str(effect_id)] = value


ACTION_HANDLERS: dict[str, Callable[[ZUSDOracleCommitApplyV1NativeAdapter, Any], Any]] = {
    "apply_oracle_commit": _handle_apply_oracle_commit,
}

EFFECT_HANDLERS: dict[str, Callable[[ZUSDOracleCommitApplyV1NativeAdapter, str, Any], None]] = {
    "pending_le_active": _commit_effect,
    "fresh_ok": _commit_effect,
    "env_ok": _commit_effect,
    "policy_ok": _commit_effect,
    "oracle_commit_allowed": _commit_effect,
    "price_after_e8": _commit_effect,
    "oracle_last_update_after": _commit_effect,
}


def make_adapter(ir: Any) -> ZUSDOracleCommitApplyV1NativeAdapter:
    return ZUSDOracleCommitApplyV1NativeAdapter(ir=ir)
