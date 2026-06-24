from __future__ import annotations

import pytest

import src.core.vault as vault_module
from src.core.vault import VaultCommand, VaultStepResult, init_vault_state, step


def test_vault_step_rejects_unknown_action() -> None:
    result = step(init_vault_state(), VaultCommand(tag="unknown", args={}))

    assert result == VaultStepResult(ok=False, error="unknown action: unknown")


def test_vault_step_converts_expected_value_error(monkeypatch) -> None:
    def fail_with_value_error(_state: object, _args: object) -> VaultStepResult:
        raise ValueError("post-invariant violated")

    monkeypatch.setattr(vault_module, "_stake", fail_with_value_error)

    result = step(init_vault_state(), VaultCommand(tag="stake", args={"amount": 1}))

    assert result == VaultStepResult(ok=False, error="post-invariant violated")


def test_vault_step_surfaces_unexpected_internal_fault(monkeypatch) -> None:
    def fail_with_runtime_error(_state: object, _args: object) -> VaultStepResult:
        raise RuntimeError("vault implementation bug")

    monkeypatch.setattr(vault_module, "_stake", fail_with_runtime_error)

    with pytest.raises(RuntimeError, match="vault implementation bug"):
        step(init_vault_state(), VaultCommand(tag="stake", args={"amount": 1}))
