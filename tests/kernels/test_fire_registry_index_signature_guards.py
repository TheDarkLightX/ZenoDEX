from __future__ import annotations

import pytest

import src.fire.registry.index_v1 as index_v1
from src.fire.registry.index_v1 import (
    FireRegistryIndex,
    sign_fire_registry_index,
    verify_fire_registry_index_signature,
)


def test_fire_registry_index_signature_rejects_invalid_signature_hex() -> None:
    index = sign_fire_registry_index(FireRegistryIndex.build(()), privkey=73)
    broken = FireRegistryIndex(
        entries=index.entries,
        index_hash=index.index_hash,
        instance_gate_summary=index.instance_gate_summary,
        certificate_instance_gate_summary=index.certificate_instance_gate_summary,
        contract_receipts=index.contract_receipts,
        signature="0x" + ("12" * 96),
        signer_pubkey=index.signer_pubkey,
    )

    assert verify_fire_registry_index_signature(broken) is False


def test_fire_registry_index_signature_propagates_unexpected_bls_backend_failure(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    class ExplodingBLS:
        @staticmethod
        def Verify(*_args: object) -> bool:
            raise RuntimeError("backend invariant failure")

    index = sign_fire_registry_index(FireRegistryIndex.build(()), privkey=73)
    monkeypatch.setattr(index_v1, "G2Basic", ExplodingBLS)

    with pytest.raises(RuntimeError, match="backend invariant failure"):
        verify_fire_registry_index_signature(index)
