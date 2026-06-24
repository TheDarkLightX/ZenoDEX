from __future__ import annotations

import pytest

from src.core.perp_epoch import _check_adapter_ir_hash, _optional_adapter_ir_hash


def test_optional_adapter_ir_hash_treats_absent_adapter_as_optional() -> None:
    assert _optional_adapter_ir_hash("..kernels.python.definitely_missing_perp_adapter_for_test") is None


def test_check_adapter_ir_hash_allows_empty_or_matching_hash() -> None:
    _check_adapter_ir_hash(expected_hash=None, model_hash="abc")
    _check_adapter_ir_hash(expected_hash="", model_hash="abc")
    _check_adapter_ir_hash(expected_hash="abc", model_hash="abc")


def test_check_adapter_ir_hash_rejects_present_mismatch() -> None:
    with pytest.raises(RuntimeError, match="perp kernel IR hash mismatch"):
        _check_adapter_ir_hash(expected_hash="adapter-hash", model_hash="model-hash")
