from __future__ import annotations

import pytest

from src.core import vault
from src.core.vault import VaultCommand, VaultStepResult, init_vault_state


def test_vault_step_returns_domain_errors_as_rejects(monkeypatch: pytest.MonkeyPatch) -> None:
    def reject_harvest(_state: object, _args: object) -> object:
        raise ValueError("domain reject")

    monkeypatch.setattr(vault, "_harvest", reject_harvest)

    result = vault.step(init_vault_state(), VaultCommand(tag="harvest", args={"entry_acc": 0}))

    assert result.ok is False
    assert result.error == "domain reject"


def test_vault_step_does_not_swallow_helper_bugs(monkeypatch: pytest.MonkeyPatch) -> None:
    def broken_harvest(_state: object, _args: object) -> object:
        raise RuntimeError("vault helper bug")

    monkeypatch.setattr(vault, "_harvest", broken_harvest)

    with pytest.raises(RuntimeError, match="vault helper bug"):
        vault.step(init_vault_state(), VaultCommand(tag="harvest", args={"entry_acc": 0}))


def test_vault_step_result_ok_flag_must_be_bool() -> None:
    with pytest.raises(ValueError, match="ok must be bool"):
        VaultStepResult(ok=1, state=init_vault_state(), effects={})  # type: ignore[arg-type]


def test_vault_step_result_accept_requires_state_and_effects() -> None:
    with pytest.raises(ValueError, match="state and effects"):
        VaultStepResult(ok=True, state=init_vault_state())

    with pytest.raises(ValueError, match="state and effects"):
        VaultStepResult(ok=True, effects={})


def test_vault_step_result_accept_rejects_error() -> None:
    with pytest.raises(ValueError, match="cannot include error"):
        VaultStepResult(
            ok=True,
            state=init_vault_state(),
            effects={},
            error="guard",
        )


def test_vault_step_result_reject_requires_error_and_no_post_artifacts() -> None:
    with pytest.raises(ValueError, match="error reason"):
        VaultStepResult(ok=False)

    with pytest.raises(ValueError, match="state or effects"):
        VaultStepResult(ok=False, state=init_vault_state(), error="guard")

    with pytest.raises(ValueError, match="state or effects"):
        VaultStepResult(ok=False, effects={}, error="guard")
