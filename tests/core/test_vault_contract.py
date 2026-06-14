from __future__ import annotations

import pytest

import src.core.vault as vault


def test_step_rejects_malformed_command_args_without_broad_exception() -> None:
    state = vault.init_vault_state()
    cmd = vault.VaultCommand(tag="stake", args=None)  # type: ignore[arg-type]

    result = vault.step(state, cmd)

    assert not result.ok
    assert result.error == "invalid command args"


def test_step_propagates_unexpected_helper_fault(monkeypatch: pytest.MonkeyPatch) -> None:
    state = vault.init_vault_state()
    cmd = vault.VaultCommand(tag="stake", args={"amount": 1})

    def broken_stake(_state: vault.VaultState, _args: object) -> vault.VaultStepResult:
        raise RuntimeError("unexpected helper fault")

    monkeypatch.setattr(vault, "_stake", broken_stake)

    with pytest.raises(RuntimeError, match="unexpected helper fault"):
        vault.step(state, cmd)
