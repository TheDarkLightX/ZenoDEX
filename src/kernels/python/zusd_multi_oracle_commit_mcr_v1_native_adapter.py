"""Native (non-interpreter) shell adapter for `zusd_multi_oracle_commit_mcr_v1`.

Used with:
  python3 -m ESSO shell-lint src/kernels/dex/zusd_multi_oracle_commit_mcr_v1.yaml --adapter <this>:make_adapter
  python3 -m ESSO verify-shell src/kernels/dex/zusd_multi_oracle_commit_mcr_v1.yaml --adapter <this>:make_adapter
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Mapping

from ...core.zusd_multi_oracle_commit_mcr import check_multi_oracle_commit_mcr

# Derived from:
# `python3 -m ESSO validate src/kernels/dex/zusd_multi_oracle_commit_mcr_v1.yaml`.
IR_HASH = "sha256:0327770ad890782df3d346a9ad138e3018befe7892993a5090a6c9c818c86e5c"


def _guard_false(action_id: str) -> Any:
    from ESSO.kernel.interpreter import StepError  # type: ignore

    return StepError(code="GuardFalse", message=f"guard false for action '{action_id}'")


@dataclass
class ZUSDMultiOracleCommitMCRV1NativeAdapter:
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


def _handle_evaluate_multi_oracle_commit_mcr(adapter: ZUSDMultiOracleCommitMCRV1NativeAdapter, command: Any) -> Any:
    from ESSO.kernel.interpreter import StepOk  # type: ignore

    del command
    s = adapter._state
    action_id = "evaluate_multi_oracle_commit_mcr"
    try:
        # REVIEW [B -> A-]: this adapter previously coerced shell state with
        # int(...), which reopened bool/string acceptance after the core MCR
        # checker had been made strict. Pass raw values so the authoritative
        # checker owns all numeric-domain validation.
        outcome = check_multi_oracle_commit_mcr(
            price_pending_e8=s["price_pending_e8"],
            mcr_bps=s["mcr_bps"],
            vault_a_collateral_e8=s["vault_a_collateral_e8"],
            vault_a_debt_e8=s["vault_a_debt_e8"],
            vault_b_collateral_e8=s["vault_b_collateral_e8"],
            vault_b_debt_e8=s["vault_b_debt_e8"],
        )
    except (KeyError, TypeError, ValueError):
        return _guard_false(action_id)

    return StepOk(
        state=dict(s),
        effects={
            "vault_a_mcr_ok": bool(outcome.vault_a_mcr_ok),
            "vault_b_mcr_ok": bool(outcome.vault_b_mcr_ok),
            "mcr_ok_at_pending": bool(outcome.mcr_ok_at_pending),
        },
    )


def _commit_effect(adapter: ZUSDMultiOracleCommitMCRV1NativeAdapter, effect_id: str, value: Any) -> None:
    adapter._pending_effects[str(effect_id)] = value


ACTION_HANDLERS: dict[str, Callable[[ZUSDMultiOracleCommitMCRV1NativeAdapter, Any], Any]] = {
    "evaluate_multi_oracle_commit_mcr": _handle_evaluate_multi_oracle_commit_mcr,
}

EFFECT_HANDLERS: dict[str, Callable[[ZUSDMultiOracleCommitMCRV1NativeAdapter, str, Any], None]] = {
    "vault_a_mcr_ok": _commit_effect,
    "vault_b_mcr_ok": _commit_effect,
    "mcr_ok_at_pending": _commit_effect,
}


def make_adapter(ir: Any) -> ZUSDMultiOracleCommitMCRV1NativeAdapter:
    return ZUSDMultiOracleCommitMCRV1NativeAdapter(ir=ir)
