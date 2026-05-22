from __future__ import annotations

from contextlib import contextmanager
from dataclasses import dataclass
import hashlib
from pathlib import Path
from types import ModuleType, SimpleNamespace
from typing import Any, Callable, Iterator, Mapping
import sys

from src.fire.compiler.compiler_registry_v1 import FIRE_COMPILER_SPECS, compile_fire_object
from src.fire.compiler.fmos_v1 import build_fmos_manifest
from src.fire.kernel.apply_receipt_v1 import FireApplyReceipt
from src.fire.kernel.ledger_adapter_v1 import (
    FireLedgerBalances,
    apply_verified_fire_settlement_effects,
)
from src.fire.registry.bundle_v1 import verify_fire_registry_bundle
from src.fire.runtime import burn_boost_call_v1 as burn_boost_runtime
from src.fire.runtime import fee_note_v1 as fee_note_runtime
from src.fire.runtime import lp_loss_cover_v1 as lp_loss_cover_runtime
from src.fire.runtime.native_adapter_registry_v1 import get_fire_native_adapter_maker
from src.fire.verifier.settlement_v1 import (
    FireSettlementPacket,
    FireVerifierReceipt,
    fire_witness_binding_hash,
)


@dataclass(frozen=True)
class FirePersistedBundleSettlementEntry:
    object_id: str
    object_name: str
    object_version: str
    object_family: str
    verify_and_settle: Callable[..., Any]
    make_adapter: Callable[[Any], Any]
    required_witness_inputs: tuple[str, ...]
    build_runtime_kwargs: Callable[[Mapping[str, int], int, int], dict[str, int]]
    build_adapter_args: Callable[[Mapping[str, int], int, int], dict[str, int]]


@dataclass(frozen=True)
class FirePersistedBundleSettlementResult:
    object_id: str
    object_name: str
    object_version: str
    object_family: str
    bundle_dir: str
    bundle_hash: str
    bundle_file_sha256: str
    object_hash: str
    instance_hash: str
    cert_sha256: str
    holder_balance_before: int
    writer_balance_before: int
    holder_balance_after: int
    writer_balance_after: int
    holder_delta: int
    writer_delta: int
    payoff_out: int
    verifier_receipt: FireVerifierReceipt
    settlement_packet: FireSettlementPacket
    apply_receipt: FireApplyReceipt

    def to_dict(self) -> dict[str, object]:
        return {
            "object_id": self.object_id,
            "object_name": self.object_name,
            "object_version": self.object_version,
            "object_family": self.object_family,
            "bundle_dir": self.bundle_dir,
            "bundle_hash": self.bundle_hash,
            "bundle_file_sha256": self.bundle_file_sha256,
            "object_hash": self.object_hash,
            "instance_hash": self.instance_hash,
            "cert_sha256": self.cert_sha256,
            "holder_balance_before": self.holder_balance_before,
            "writer_balance_before": self.writer_balance_before,
            "holder_balance_after": self.holder_balance_after,
            "writer_balance_after": self.writer_balance_after,
            "holder_delta": self.holder_delta,
            "writer_delta": self.writer_delta,
            "payoff_out": self.payoff_out,
            "witness_hash": self.verifier_receipt.witness_hash,
            "verifier_receipt": self.verifier_receipt.to_dict(),
            "settlement_packet": self.settlement_packet.to_dict(),
            "apply_receipt": self.apply_receipt.to_dict(),
        }


def _burn_runtime_kwargs(witness_inputs: Mapping[str, int], holder_posted: int, writer_posted: int) -> dict[str, int]:
    return {
        "witness_final": witness_inputs["witness_final"],
        "holder_posted": holder_posted,
        "writer_posted": writer_posted,
    }


def _burn_adapter_args(witness_inputs: Mapping[str, int], holder_posted: int, writer_posted: int) -> dict[str, int]:
    return {
        "witness_final_in": witness_inputs["witness_final"],
        "holder_posted_in": holder_posted,
        "writer_posted_in": writer_posted,
    }


def _fee_runtime_kwargs(witness_inputs: Mapping[str, int], holder_posted: int, writer_posted: int) -> dict[str, int]:
    return {
        "witness_final": witness_inputs["witness_final"],
        "holder_posted": holder_posted,
        "writer_posted": writer_posted,
    }


def _fee_adapter_args(witness_inputs: Mapping[str, int], holder_posted: int, writer_posted: int) -> dict[str, int]:
    return {
        "witness_final_in": witness_inputs["witness_final"],
        "holder_posted_in": holder_posted,
        "writer_posted_in": writer_posted,
    }


def _lp_runtime_kwargs(witness_inputs: Mapping[str, int], holder_posted: int, writer_posted: int) -> dict[str, int]:
    return {
        "witness_hodl_final": witness_inputs["witness_hodl_final"],
        "witness_lpv_final": witness_inputs["witness_lpv_final"],
        "holder_posted": holder_posted,
        "writer_posted": writer_posted,
    }


def _lp_adapter_args(witness_inputs: Mapping[str, int], holder_posted: int, writer_posted: int) -> dict[str, int]:
    return {
        "witness_hodl_final_in": witness_inputs["witness_hodl_final"],
        "witness_lpv_final_in": witness_inputs["witness_lpv_final"],
        "holder_posted_in": holder_posted,
        "writer_posted_in": writer_posted,
    }


_RUNTIME_BEHAVIOR: dict[str, tuple[Callable[..., Any], tuple[str, ...], Callable[[Mapping[str, int], int, int], dict[str, int]], Callable[[Mapping[str, int], int, int], dict[str, int]]]] = {
    "burn_boost_call_v1": (
        burn_boost_runtime.verify_and_settle,
        ("witness_final",),
        _burn_runtime_kwargs,
        _burn_adapter_args,
    ),
    "fee_note_v1": (
        fee_note_runtime.verify_and_settle,
        ("witness_final",),
        _fee_runtime_kwargs,
        _fee_adapter_args,
    ),
    "lp_loss_cover_v1": (
        lp_loss_cover_runtime.verify_and_settle,
        ("witness_hodl_final", "witness_lpv_final"),
        _lp_runtime_kwargs,
        _lp_adapter_args,
    ),
}


def _build_entries() -> tuple[FirePersistedBundleSettlementEntry, ...]:
    entries: list[FirePersistedBundleSettlementEntry] = []
    for spec in FIRE_COMPILER_SPECS:
        behavior = _RUNTIME_BEHAVIOR.get(spec.object_id)
        if behavior is None:
            continue
        verify_and_settle, required_witness_inputs, build_runtime_kwargs, build_adapter_args = behavior
        entries.append(
            FirePersistedBundleSettlementEntry(
                object_id=spec.object_id,
                object_name=spec.object_name,
                object_version=spec.object_version,
                object_family=spec.object_family,
                verify_and_settle=verify_and_settle,
                make_adapter=get_fire_native_adapter_maker(spec.object_id),
                required_witness_inputs=required_witness_inputs,
                build_runtime_kwargs=build_runtime_kwargs,
                build_adapter_args=build_adapter_args,
            )
        )
    return tuple(entries)


_ENTRIES: tuple[FirePersistedBundleSettlementEntry, ...] = _build_entries()


def _sha256_prefixed_bytes(payload: bytes) -> str:
    return "sha256:" + hashlib.sha256(payload).hexdigest()


def _ensure_int_mapping(name: str, payload: Mapping[str, object]) -> dict[str, int]:
    normalized: dict[str, int] = {}
    for key, value in payload.items():
        if not isinstance(key, str) or not key:
            raise TypeError(f"{name} keys must be non-empty strings")
        if not isinstance(value, int) or isinstance(value, bool):
            raise TypeError(f"{name}[{key}] must be an int")
        normalized[key] = int(value)
    return normalized


def _require_int(name: str, value: object) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    return int(value)


def _resolve_entry(object_name: str, object_version: str, object_family: str) -> FirePersistedBundleSettlementEntry:
    matches = [
        entry
        for entry in _ENTRIES
        if entry.object_name == object_name
        and entry.object_version == object_version
        and entry.object_family == object_family
    ]
    if not matches:
        raise KeyError(f"unsupported FIRE settlement family: {object_name}:{object_version}:{object_family}")
    if len(matches) > 1:
        raise RuntimeError(f"ambiguous FIRE settlement family: {object_name}:{object_version}:{object_family}")
    return matches[0]


def _validate_witness_inputs(
    entry: FirePersistedBundleSettlementEntry,
    witness_inputs: Mapping[str, object],
) -> dict[str, int]:
    normalized = _ensure_int_mapping("witness_inputs", witness_inputs)
    missing = [name for name in entry.required_witness_inputs if name not in normalized]
    extras = [name for name in normalized if name not in entry.required_witness_inputs]
    if missing:
        raise ValueError(f"missing witness inputs: {', '.join(sorted(missing))}")
    if extras:
        raise ValueError(f"unexpected witness inputs: {', '.join(sorted(extras))}")
    return normalized


@contextmanager
def _adapter_interpreter_context() -> Iterator[None]:
    try:
        import ESSO.kernel.interpreter  # type: ignore  # noqa: F401
        yield
        return
    except ImportError:
        pass

    backups = {name: sys.modules.get(name) for name in ("ESSO", "ESSO.kernel", "ESSO.kernel.interpreter")}
    esso_mod = ModuleType("ESSO")
    kernel_mod = ModuleType("ESSO.kernel")
    interp_mod = ModuleType("ESSO.kernel.interpreter")

    class StepOk:
        def __init__(self, *, state: Any, effects: Any) -> None:
            self.state = state
            self.effects = effects

    class StepError:
        def __init__(self, *, code: str, message: str) -> None:
            self.code = code
            self.message = message

    interp_mod.StepOk = StepOk
    interp_mod.StepError = StepError
    kernel_mod.interpreter = interp_mod
    esso_mod.kernel = kernel_mod
    sys.modules["ESSO"] = esso_mod
    sys.modules["ESSO.kernel"] = kernel_mod
    sys.modules["ESSO.kernel.interpreter"] = interp_mod
    try:
        yield
    finally:
        for name, module in backups.items():
            if module is None:
                sys.modules.pop(name, None)
            else:
                sys.modules[name] = module


def _apply_with_adapter(
    *,
    entry: FirePersistedBundleSettlementEntry,
    compiled: Any,
    receipt: FireVerifierReceipt,
    bundle_dir: Path,
    bundle_hash: str,
    bundle_file_sha256: str,
    cert_sha256: str,
    holder_posted: int,
    writer_posted: int,
    witness_inputs: Mapping[str, int],
) -> tuple[bool, str | None, Mapping[str, Any] | None]:
    adapter = entry.make_adapter(ir={"schema": "zenodex/fire-adapter-runner/v1"})
    compiled_state = compiled.spec.compile_state(compiled.artifact.terms)
    adapter.reset(state=vars(compiled_state))
    args = entry.build_adapter_args(witness_inputs, holder_posted, writer_posted)
    args.update(
        {
            "persisted_bundle_dir": str(bundle_dir),
            "expected_bundle_hash": bundle_hash,
            "expected_bundle_file_sha256": bundle_file_sha256,
            "expected_cert_sha256": cert_sha256,
            "verifier_receipt": receipt.to_dict(),
        }
    )
    with _adapter_interpreter_context():
        result = adapter.apply(SimpleNamespace(tag="firev_accept_and_settle", args=args))
    if hasattr(result, "code") and hasattr(result, "message"):
        return False, f"adapter_{result.code}:{result.message}", None
    effects = dict(adapter.drain_effects())
    return True, None, effects


def _crosscheck_runtime_and_applied_settlement(
    *,
    verified_settlement: Any,
    apply_result: Any,
) -> str | None:
    runtime_receipt = getattr(verified_settlement, "verifier_receipt", None)
    packet = getattr(apply_result, "packet", None)
    if runtime_receipt is None or packet is None:
        return "crosscheck_payload_missing"
    if packet.receipt.to_dict() != runtime_receipt.to_dict():
        return "crosscheck_receipt_mismatch"
    try:
        runtime_holder_delta = _require_int(
            "verified_settlement.holder_delta",
            getattr(verified_settlement, "holder_delta", None),
        )
        runtime_writer_delta = _require_int(
            "verified_settlement.writer_delta",
            getattr(verified_settlement, "writer_delta", None),
        )
    except TypeError as exc:
        return f"crosscheck_runtime_delta_invalid:{exc}"
    if packet.holder_delta != runtime_holder_delta:
        return "crosscheck_holder_delta_mismatch"
    if packet.writer_delta != runtime_writer_delta:
        return "crosscheck_writer_delta_mismatch"
    if packet.payoff_out != runtime_holder_delta:
        return "crosscheck_payoff_out_mismatch"
    return None


def apply_fire_persisted_bundle_settlement(
    *,
    bundle_dir: str | Path,
    holder_posted: int,
    writer_posted: int,
    holder_balance: int,
    writer_balance: int,
    witness_inputs: Mapping[str, object],
) -> tuple[bool, str | None, FirePersistedBundleSettlementResult | None]:
    bundle_root = Path(bundle_dir)
    try:
        bundle_file_sha256 = _sha256_prefixed_bytes((bundle_root / "bundle_manifest.json").read_bytes())
    except (FileNotFoundError, OSError) as exc:
        return False, f"bundle_manifest_read_failed:{exc}", None
    ok, err, bundle_manifest, object_manifest, object_instance, _object_lock = verify_fire_registry_bundle(bundle_dir)
    if not ok or bundle_manifest is None or object_manifest is None or object_instance is None:
        return False, err or "bundle_invalid", None

    try:
        entry = _resolve_entry(object_manifest.object_name, object_manifest.object_version, object_manifest.object_family)
        normalized_witness_inputs = _validate_witness_inputs(entry, witness_inputs)
        compiled = compile_fire_object(
            entry.object_id,
            {item.name: item.value for item in object_instance.parameters},
        )
    except (KeyError, RuntimeError, TypeError, ValueError) as exc:
        return False, str(exc), None

    derived_manifest = build_fmos_manifest(compiled.spec, compiled.artifact)
    if derived_manifest.manifest_hash != object_manifest.manifest_hash:
        return False, "compiled_manifest_hash_mismatch", None
    if derived_manifest.cert_sha256 != object_manifest.cert_sha256:
        return False, "compiled_cert_sha256_mismatch", None

    try:
        verified_result = entry.verify_and_settle(
            artifact=compiled.artifact,
            persisted_bundle_dir=bundle_dir,
            expected_bundle_hash=bundle_manifest.bundle_hash,
            expected_bundle_file_sha256=bundle_file_sha256,
            **entry.build_runtime_kwargs(normalized_witness_inputs, holder_posted, writer_posted),
        )
    except (RuntimeError, TypeError, ValueError) as exc:
        return False, str(exc), None

    settlement = getattr(verified_result, "settlement", None)
    if not getattr(verified_result, "ok", False) or settlement is None:
        return False, getattr(verified_result, "error", None) or "verified_settlement_rejected", None

    ok, err, effects = _apply_with_adapter(
        entry=entry,
        compiled=compiled,
        receipt=settlement.verifier_receipt,
        bundle_dir=bundle_root,
        bundle_hash=bundle_manifest.bundle_hash,
        bundle_file_sha256=bundle_file_sha256,
        cert_sha256=object_manifest.cert_sha256,
        holder_posted=holder_posted,
        writer_posted=writer_posted,
        witness_inputs=normalized_witness_inputs,
    )
    if not ok or effects is None:
        return False, err or "adapter_rejected", None

    ok, err, apply_result = apply_verified_fire_settlement_effects(
        effects,
        balances=FireLedgerBalances(holder_balance=holder_balance, writer_balance=writer_balance),
        expected_object_hash=object_manifest.manifest_hash,
        expected_instance_hash=object_instance.instance_hash,
        expected_cert_sha256=object_manifest.cert_sha256,
        expected_bundle_hash=bundle_manifest.bundle_hash,
        expected_witness_hash=fire_witness_binding_hash(normalized_witness_inputs),
    )
    if not ok or apply_result is None:
        return False, err or "ledger_apply_rejected", None
    crosscheck_error = _crosscheck_runtime_and_applied_settlement(
        verified_settlement=settlement,
        apply_result=apply_result,
    )
    if crosscheck_error is not None:
        return False, crosscheck_error, None

    return True, None, FirePersistedBundleSettlementResult(
        object_id=entry.object_id,
        object_name=object_manifest.object_name,
        object_version=object_manifest.object_version,
        object_family=object_manifest.object_family,
        bundle_dir=str(bundle_root.resolve()),
        bundle_hash=bundle_manifest.bundle_hash,
        bundle_file_sha256=bundle_file_sha256,
        object_hash=object_manifest.manifest_hash,
        instance_hash=object_instance.instance_hash,
        cert_sha256=object_manifest.cert_sha256,
        holder_balance_before=holder_balance,
        writer_balance_before=writer_balance,
        holder_balance_after=apply_result.balances.holder_balance,
        writer_balance_after=apply_result.balances.writer_balance,
        holder_delta=apply_result.packet.holder_delta,
        writer_delta=apply_result.packet.writer_delta,
        payoff_out=apply_result.packet.payoff_out,
        verifier_receipt=apply_result.packet.receipt,
        settlement_packet=apply_result.packet,
        apply_receipt=apply_result.apply_receipt,
    )


__all__ = [
    "FirePersistedBundleSettlementResult",
    "apply_fire_persisted_bundle_settlement",
]
