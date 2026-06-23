from __future__ import annotations

from src.kernels.python.strategy_signer_binding_guard_v1_adapter import (
    check_strategy_signer_binding,
)


def test_strategy_signer_binding_guard_accepts_matching_canonical_pubkeys() -> None:
    pubkey = "0x" + ("12" * 48)
    result = check_strategy_signer_binding(
        signer_pubkey=pubkey,
        owner_pubkey=pubkey,
    )
    assert result.ok is True
    assert result.binding_ok is True
    assert result.error is None
    assert result.signer_pubkey == pubkey
    assert result.owner_pubkey == pubkey


def test_strategy_signer_binding_guard_rejects_mismatch_and_invalid_inputs() -> None:
    mismatch = check_strategy_signer_binding(
        signer_pubkey="0x" + ("12" * 48),
        owner_pubkey="0x" + ("34" * 48),
    )
    assert mismatch.ok is False
    assert mismatch.error == "signer_pubkey_mismatch"

    invalid_signer = check_strategy_signer_binding(
        signer_pubkey="bad",
        owner_pubkey="0x" + ("34" * 48),
    )
    assert invalid_signer.ok is False
    assert invalid_signer.error == "signer_pubkey_invalid"

    invalid_owner = check_strategy_signer_binding(
        signer_pubkey="0x" + ("12" * 48),
        owner_pubkey="bad",
    )
    assert invalid_owner.ok is False
    assert invalid_owner.error == "owner_pubkey_invalid"

    non_string_signer = check_strategy_signer_binding(
        signer_pubkey=123,
        owner_pubkey="0x" + ("12" * 48),
    )
    assert non_string_signer.ok is False
    assert non_string_signer.error == "signer_pubkey_invalid"
