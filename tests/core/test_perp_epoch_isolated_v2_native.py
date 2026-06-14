from __future__ import annotations

from dataclasses import asdict

import pytest

from generated.perp_python import perp_epoch_isolated_v2_ref as ref
from src.core import perp_epoch as perp_epoch_module
from src.core.perp_epoch import (
    perp_epoch_isolated_v2_native_apply,
    perp_epoch_isolated_v2_native_initial_state,
    perp_epoch_isolated_v3_native_initial_state,
)


def test_perp_epoch_isolated_v2_native_initial_state_matches_v2_ref_shape() -> None:
    native = dict(perp_epoch_isolated_v2_native_initial_state())
    reference = dict(asdict(ref.init_state()))
    assert "epoch_phase" not in native
    assert native == reference


def test_perp_epoch_isolated_v2_native_deposit_insurance_matches_v2_ref_shape() -> None:
    native_state = dict(perp_epoch_isolated_v2_native_initial_state())
    params = {"amount": 1_000_000_000_000}

    native = perp_epoch_isolated_v2_native_apply(state=native_state, action="deposit_insurance", params=params)
    reference = ref.step(ref.init_state(), ref.Command(tag="deposit_insurance", args=params))

    assert native.ok is True
    assert reference.ok is True
    assert native.state is not None
    assert "epoch_phase" not in native.state
    assert native.state == dict(asdict(reference.state))


def test_perp_epoch_isolated_v3_native_initial_state_keeps_epoch_phase() -> None:
    native = dict(perp_epoch_isolated_v3_native_initial_state())
    # v3 native kernel ABI encodes epoch_phase as an integer enum (Open=0,
    # PricePublished=1, Settled=2); the initial state is Open. The string "Open"
    # is the typed/human form; the native ABI is integer.
    assert native["epoch_phase"] == 0


def test_adapter_hash_pin_allows_missing_optional_adapter(monkeypatch: pytest.MonkeyPatch) -> None:
    def _missing_adapter(module_name: str):
        raise ModuleNotFoundError("adapter absent", name=module_name)

    monkeypatch.setattr(perp_epoch_module.importlib, "import_module", _missing_adapter)

    perp_epoch_module._verify_adapter_ir_hash(
        adapter_module="src.kernels.python.missing_perp_adapter",
        actual_hash="actual",
    )


def test_adapter_hash_pin_rejects_mismatch(monkeypatch: pytest.MonkeyPatch) -> None:
    class _Adapter:
        IR_HASH = "expected"

    monkeypatch.setattr(perp_epoch_module.importlib, "import_module", lambda _module_name: _Adapter)

    with pytest.raises(RuntimeError, match="perp kernel IR hash mismatch"):
        perp_epoch_module._verify_adapter_ir_hash(
            adapter_module="src.kernels.python.perp_epoch_isolated_v2_adapter",
            actual_hash="actual",
        )


def test_adapter_hash_pin_propagates_adapter_import_failure(monkeypatch: pytest.MonkeyPatch) -> None:
    def _broken_adapter(_module_name: str):
        raise ModuleNotFoundError("internal dependency absent", name="missing_dependency")

    monkeypatch.setattr(perp_epoch_module.importlib, "import_module", _broken_adapter)

    with pytest.raises(ModuleNotFoundError, match="internal dependency absent"):
        perp_epoch_module._verify_adapter_ir_hash(
            adapter_module="src.kernels.python.perp_epoch_isolated_v2_adapter",
            actual_hash="actual",
        )
