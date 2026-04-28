"""Native shell adapter for `fire_burn_boost_call_v1`.

Used with:
  python3 -m ESSO shell-lint src/kernels/dex/fire_burn_boost_call_v1.yaml --adapter <this>:make_simulation_adapter
  python3 -m ESSO verify-shell src/kernels/dex/fire_burn_boost_call_v1.yaml --adapter <this>:make_simulation_adapter
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Mapping

from src.fire.runtime.adapter_manifest_gate_v1 import (
    validate_persisted_bundle_command_args,
    validate_persisted_bundle_settlement_receipt,
)
from src.fire.verifier.settlement_v1 import FireSettlementPacket, FireVerifierReceipt
from src.fire.kernel import fire_burn_boost_call_v1_ref as ref


IR_HASH = "sha256:b26b68dbadb3313ef59399eeb2f7f180ea9775bffd3e797c27186a0d5daddc61"


def _state_from_mapping(state: Mapping[str, Any]) -> ref.State:
    return ref.State(
        artifact_lower=int(state["artifact_lower"]),
        artifact_upper=int(state["artifact_upper"]),
        cap_index=int(state["cap_index"]),
        holder_delta=int(state["holder_delta"]),
        holder_posted=int(state["holder_posted"]),
        n_notional=int(state["n_notional"]),
        phase=str(state["phase"]),
        source_upper=int(state["source_upper"]),
        strike_index=int(state["strike_index"]),
        witness_final=int(state["witness_final"]),
        writer_delta=int(state["writer_delta"]),
        writer_posted=int(state["writer_posted"]),
    )


def _step_error(code: str, message: str) -> Any:
    from ESSO.kernel.interpreter import StepError  # type: ignore

    return StepError(code=code, message=message)


def _commit_effect(adapter: "FireBurnBoostCallV1NativeAdapter", effect_id: str, value: Any) -> None:
    adapter._pending_effects[str(effect_id)] = value


def _commit_receipt_effect(adapter: "FireBurnBoostCallV1NativeAdapter", args: Mapping[str, Any]) -> None:
    receipt = args.get("verifier_receipt")
    if args.get("persisted_bundle_dir") is not None and isinstance(receipt, Mapping):
        adapter._pending_effects["verifier_receipt"] = dict(receipt)


def _commit_settlement_packet_effect(adapter: "FireBurnBoostCallV1NativeAdapter", args: Mapping[str, Any]) -> None:
    receipt = args.get("verifier_receipt")
    if args.get("persisted_bundle_dir") is None or not isinstance(receipt, Mapping):
        return
    packet = FireSettlementPacket.build(
        receipt=adapter._pending_effects["verifier_receipt_obj"],
        holder_delta=int(adapter._state.holder_delta),
        writer_delta=int(adapter._state.writer_delta),
        payoff_out=int(adapter._state.holder_delta),
        firev_accept=adapter._pending_effects["firev_accept"],
    )
    adapter._pending_effects["settlement_packet"] = packet.to_dict()


def _run_kernel_step(adapter: "FireBurnBoostCallV1NativeAdapter", tag: str, args: Mapping[str, Any]) -> Any:
    result = ref.step(adapter._state, ref.Command(tag=tag, args=dict(args)))

    if not result.ok or result.state is None:
        message = result.error or "kernel rejected"
        if message.startswith("unknown action"):
            return _step_error("UnknownAction", message)
        if message.startswith("guard failed"):
            return _step_error("GuardFalse", message)
        if message.startswith("invalid param"):
            return _step_error("InvalidParam", message)
        if message.startswith("pre-invariant violated") or message.startswith("post-invariant violated"):
            return _step_error("InvariantViolation", message)
        return _step_error("KernelError", message)

    if adapter.require_settlement_receipt:
        receipt_error = validate_persisted_bundle_settlement_receipt(
            state_after=vars(result.state),
            args=args,
            expected_ir_hash=IR_HASH,
            command_tag=tag,
            witness_inputs={"witness_final": args.get("witness_final_in")},
        )
        if receipt_error is not None:
            return _step_error("GuardFalse", f"receipt gate failed: {receipt_error}")

    from ESSO.kernel.interpreter import StepOk  # type: ignore

    previous_state = adapter._state
    previous_effects = dict(adapter._pending_effects)
    adapter._state = result.state
    adapter._pending_effects = dict()
    try:
        for eff_id, value in dict(result.effects or {}).items():
            eff_handler = EFFECT_HANDLERS.get(str(eff_id))
            if eff_handler is not None:
                eff_handler(adapter, str(eff_id), value)
        _commit_receipt_effect(adapter, args)
        if "verifier_receipt" in adapter._pending_effects:
            adapter._pending_effects["verifier_receipt_obj"] = FireVerifierReceipt.from_dict(
                adapter._pending_effects["verifier_receipt"]
            )
            _commit_settlement_packet_effect(adapter, args)
            del adapter._pending_effects["verifier_receipt_obj"]
    except (KeyError, TypeError, ValueError) as exc:
        adapter._state = previous_state
        adapter._pending_effects = previous_effects
        return _step_error("GuardFalse", f"settlement packet gate failed: {exc}")
    return StepOk(state=vars(result.state), effects=dict(result.effects or {}))


def _handle_compile_burn_boost_call(adapter: "FireBurnBoostCallV1NativeAdapter", command: Any) -> Any:
    return _run_kernel_step(adapter, "compile_burn_boost_call", dict(getattr(command, "args", {}) or {}))


def _handle_firev_accept_and_settle(adapter: "FireBurnBoostCallV1NativeAdapter", command: Any) -> Any:
    args = dict(getattr(command, "args", {}) or {})
    manifest_error = validate_persisted_bundle_command_args(
        state=vars(adapter._state),
        args=args,
        expected_ir_hash=IR_HASH,
    )
    if manifest_error is not None:
        return _step_error("GuardFalse", f"manifest gate failed: {manifest_error}")
    return _run_kernel_step(adapter, "firev_accept_and_settle", args)


@dataclass
class FireBurnBoostCallV1NativeAdapter:
    ir: Any
    require_settlement_receipt: bool = True
    _state: ref.State = field(default_factory=ref.init_state)
    _pending_effects: dict[str, Any] = field(default_factory=dict)

    def reset(self, *, state: Mapping[str, Any]) -> None:
        self._state = _state_from_mapping(state)
        self._pending_effects = {}

    def get_state(self) -> Mapping[str, Any]:
        return vars(self._state)

    def apply(self, command: Any) -> Any:
        self._pending_effects = {}
        tag = str(getattr(command, "tag", ""))
        handler = ACTION_HANDLERS.get(tag)
        if handler is None:
            return _step_error("UnknownAction", "no handler for command.tag")
        return handler(self, command)

    def drain_effects(self) -> Mapping[str, Any]:
        out = dict(self._pending_effects)
        self._pending_effects = {}
        return out


def make_adapter(ir: Any) -> FireBurnBoostCallV1NativeAdapter:
    return FireBurnBoostCallV1NativeAdapter(ir=ir)


def make_simulation_adapter(ir: Any) -> FireBurnBoostCallV1NativeAdapter:
    return FireBurnBoostCallV1NativeAdapter(ir=ir, require_settlement_receipt=False)


ACTION_HANDLERS: dict[str, Callable[[FireBurnBoostCallV1NativeAdapter, Any], Any]] = {
    "compile_burn_boost_call": _handle_compile_burn_boost_call,
    "firev_accept_and_settle": _handle_firev_accept_and_settle,
}


EFFECT_HANDLERS: dict[str, Callable[[FireBurnBoostCallV1NativeAdapter, str, Any], None]] = {
    "compiled_upper": _commit_effect,
    "firev_accept": _commit_effect,
    "payoff_out": _commit_effect,
}


__all__ = [
    "FireBurnBoostCallV1NativeAdapter",
    "IR_HASH",
    "make_adapter",
    "make_simulation_adapter",
]
