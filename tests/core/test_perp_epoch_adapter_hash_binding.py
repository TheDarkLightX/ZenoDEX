from __future__ import annotations

import sys
from types import ModuleType

import pytest

from src.core.perp_epoch import _assert_adapter_ir_hash_matches


def test_adapter_ir_hash_mismatch_fails_closed(monkeypatch: pytest.MonkeyPatch) -> None:
    adapter = ModuleType("perp_epoch_fake_adapter_mismatch")
    adapter.IR_HASH = "sha256:adapter"
    monkeypatch.setitem(sys.modules, adapter.__name__, adapter)

    with pytest.raises(RuntimeError, match="perp kernel IR hash mismatch"):
        _assert_adapter_ir_hash_matches(
            adapter_module=adapter.__name__,
            actual_ir_hash="sha256:model",
        )


def test_adapter_ir_hash_match_allows_spec_backend(monkeypatch: pytest.MonkeyPatch) -> None:
    adapter = ModuleType("perp_epoch_fake_adapter_match")
    adapter.IR_HASH = "sha256:same"
    monkeypatch.setitem(sys.modules, adapter.__name__, adapter)

    _assert_adapter_ir_hash_matches(
        adapter_module=adapter.__name__,
        actual_ir_hash="sha256:same",
    )


def test_missing_adapter_module_remains_optional() -> None:
    _assert_adapter_ir_hash_matches(
        adapter_module="perp_epoch_missing_adapter_for_legacy_checkout",
        actual_ir_hash="sha256:model",
    )
