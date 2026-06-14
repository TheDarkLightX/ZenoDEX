from __future__ import annotations

from types import SimpleNamespace

import pytest

import src.core.perp_epoch as perp_epoch


def test_adapter_ir_hash_check_allows_missing_optional_adapter(monkeypatch: pytest.MonkeyPatch) -> None:
    def missing_adapter(*_args, **_kwargs):
        raise ModuleNotFoundError("adapter missing")

    monkeypatch.setattr(perp_epoch.importlib, "import_module", missing_adapter)

    perp_epoch._check_adapter_ir_hash("missing_adapter", object(), lambda _ir: "sha256:model")


def test_adapter_ir_hash_check_rejects_present_adapter_drift(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(
        perp_epoch.importlib,
        "import_module",
        lambda *_args, **_kwargs: SimpleNamespace(IR_HASH="sha256:adapter"),
    )

    with pytest.raises(RuntimeError, match="perp kernel IR hash mismatch"):
        perp_epoch._check_adapter_ir_hash("present_adapter", object(), lambda _ir: "sha256:model")


def test_adapter_ir_hash_check_accepts_matching_adapter(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(
        perp_epoch.importlib,
        "import_module",
        lambda *_args, **_kwargs: SimpleNamespace(IR_HASH="sha256:model"),
    )

    perp_epoch._check_adapter_ir_hash("present_adapter", object(), lambda _ir: "sha256:model")
