from __future__ import annotations

import pytest

import src.integration.zeno_ledger_signature as sig
from src.integration.zeno_ledger_signature import bls_public_key_hex_from_private_key_v0


def test_bls_backend_absent_rejects_before_attribute_access(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(sig, "_BLS_AVAILABLE", True)
    monkeypatch.setattr(sig, "G2Basic", None)

    with pytest.raises(RuntimeError, match="py_ecc.bls is required"):
        bls_public_key_hex_from_private_key_v0("0x" + ("01" * 32))
