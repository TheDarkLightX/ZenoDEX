from __future__ import annotations

import sys
from types import ModuleType

import pytest

from src.core.perp_epoch import _assert_expected_ir_hash


def _module(name: str, *, ir_hash: object = "sha256:actual") -> ModuleType:
    module = ModuleType(name)
    module.IR_HASH = ir_hash
    return module


def test_adapter_hash_guard_accepts_matching_declared_hash(monkeypatch: pytest.MonkeyPatch) -> None:
    module_name = "tests.fake_perp_adapter_match"
    monkeypatch.setitem(sys.modules, module_name, _module(module_name))

    _assert_expected_ir_hash(
        {"fake": "ir"},
        adapter_module=module_name,
        ir_hash_fn=lambda _ir: "sha256:actual",
    )


def test_adapter_hash_guard_treats_missing_adapter_as_optional() -> None:
    _assert_expected_ir_hash(
        {"fake": "ir"},
        adapter_module="tests.fake_perp_adapter_missing",
        ir_hash_fn=lambda _ir: "sha256:actual",
    )


def test_adapter_hash_guard_treats_legacy_missing_hash_as_optional(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    module_name = "tests.fake_perp_adapter_legacy"
    module = ModuleType(module_name)
    monkeypatch.setitem(sys.modules, module_name, module)

    _assert_expected_ir_hash(
        {"fake": "ir"},
        adapter_module=module_name,
        ir_hash_fn=lambda _ir: "sha256:actual",
    )


def test_adapter_hash_guard_rejects_declared_hash_mismatch(monkeypatch: pytest.MonkeyPatch) -> None:
    module_name = "tests.fake_perp_adapter_mismatch"
    monkeypatch.setitem(sys.modules, module_name, _module(module_name, ir_hash="sha256:expected"))

    with pytest.raises(RuntimeError, match="perp kernel IR hash mismatch"):
        _assert_expected_ir_hash(
            {"fake": "ir"},
            adapter_module=module_name,
            ir_hash_fn=lambda _ir: "sha256:actual",
        )


def test_adapter_hash_guard_does_not_suppress_nested_import_errors(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    module_name = "tests.fake_perp_adapter_nested_failure"

    real_import_module = __import__("src.core.perp_epoch", fromlist=["import_module"]).import_module

    def fake_import_module(name: str) -> ModuleType:
        if name == module_name:
            raise ModuleNotFoundError("No module named 'missing_nested_dependency'", name="missing_nested_dependency")
        return real_import_module(name)

    monkeypatch.setattr("src.core.perp_epoch.import_module", fake_import_module)

    with pytest.raises(ModuleNotFoundError) as exc_info:
        _assert_expected_ir_hash(
            {"fake": "ir"},
            adapter_module=module_name,
            ir_hash_fn=lambda _ir: "sha256:actual",
        )

    assert exc_info.value.name == "missing_nested_dependency"
