from __future__ import annotations

import pytest

from src.integration import zeno_ledger_tokenomics


def test_canonical_hex_predicate_rejects_malformed_hex() -> None:
    assert zeno_ledger_tokenomics._is_canonical_hex_v0("0xzz", nbytes=32) is False


def test_canonical_hex_predicate_does_not_hide_unexpected_canonicalizer_fault(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def faulting_canonicalizer(_value: str, *, nbytes: int, name: str) -> str:
        raise RuntimeError(f"canonicalizer bug: {nbytes}:{name}")

    monkeypatch.setattr(
        zeno_ledger_tokenomics,
        "canonical_hex_fixed_allow_0x",
        faulting_canonicalizer,
    )

    with pytest.raises(RuntimeError, match="canonicalizer bug"):
        zeno_ledger_tokenomics._is_canonical_hex_v0("0x" + "00" * 32, nbytes=32)
