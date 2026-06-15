from __future__ import annotations

from types import ModuleType

import pytest

from src.core import perp_epoch


class _FakeStepError:
    code = "FakeStepError"
    message = "fake step error"


def _install_fake_esso(monkeypatch: pytest.MonkeyPatch, *, digest: str) -> None:
    esso = ModuleType("ESSO")
    evolve = ModuleType("ESSO.evolve")
    kernel = ModuleType("ESSO.kernel")
    interpreter = ModuleType("ESSO.kernel.interpreter")

    def ir_hash(_ir: object) -> str:
        return digest

    def prepare_step_context(_ir: object) -> object:
        return object()

    evolve.ir_hash = ir_hash  # type: ignore[attr-defined]
    interpreter.StepError = _FakeStepError  # type: ignore[attr-defined]
    interpreter.prepare_step_context = prepare_step_context  # type: ignore[attr-defined]

    monkeypatch.setitem(__import__("sys").modules, "ESSO", esso)
    monkeypatch.setitem(__import__("sys").modules, "ESSO.evolve", evolve)
    monkeypatch.setitem(__import__("sys").modules, "ESSO.kernel", kernel)
    monkeypatch.setitem(__import__("sys").modules, "ESSO.kernel.interpreter", interpreter)


def test_kernel_ctx_hash_mismatch_fails_closed(monkeypatch: pytest.MonkeyPatch) -> None:
    perp_epoch._kernel_ctx_v1.cache_clear()
    monkeypatch.setattr(perp_epoch, "_load_yaml_model", lambda _path: object())
    _install_fake_esso(monkeypatch, digest="sha256:different")

    with pytest.raises(RuntimeError, match="perp kernel IR hash mismatch"):
        perp_epoch._kernel_ctx_v1()

    perp_epoch._kernel_ctx_v1.cache_clear()


def test_kernel_ctx_matching_hash_still_loads(monkeypatch: pytest.MonkeyPatch) -> None:
    perp_epoch._kernel_ctx_v1.cache_clear()
    ir = object()
    monkeypatch.setattr(perp_epoch, "_load_yaml_model", lambda _path: ir)
    _install_fake_esso(
        monkeypatch,
        digest="sha256:6782fec89f2979132ba6e326de34597889980a352d6e3db6deceec8cc3cbf437",
    )

    loaded_ir, ctx = perp_epoch._kernel_ctx_v1()

    assert loaded_ir is ir
    assert ctx is not None
    perp_epoch._kernel_ctx_v1.cache_clear()
