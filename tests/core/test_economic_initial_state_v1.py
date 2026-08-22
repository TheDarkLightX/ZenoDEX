from __future__ import annotations

import hashlib
from dataclasses import replace

import pytest

from src.core.economic_initial_state_v1 import (
    EconomicInitialStateCertificateV1,
    EconomicInitialStateKindV1,
)
from src.core.global_economic_proof_v1 import ReceiptKindV1
from src.core.global_settlement_types_v1 import ZERO_ROOT_V1


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _genesis_certificate() -> EconomicInitialStateCertificateV1:
    receipt_bytes = b"initial-golden"
    certificate = EconomicInitialStateCertificateV1(
        kind=EconomicInitialStateKindV1.GENESIS,
        chain_id="tau-test",
        deployment_root=_root(1),
        profile_root=_root(2),
        writer_epoch=7,
        height=0,
        state_root=_root(3),
        source_profile_root=ZERO_ROOT_V1,
        source_state_root=ZERO_ROOT_V1,
        source_writer_epoch=0,
        source_height=0,
        state_atom_coverage_root=_root(4),
        lane_object_coverage_root=_root(5),
        replay_continuity_root=_root(6),
        terminal_continuity_root=_root(7),
        outbox_continuity_root=_root(8),
        source_manifest_root=_root(9),
        toolchain_manifest_root=_root(10),
        root_image_id=_root(11),
        receipt_root="0x" + hashlib.sha256(receipt_bytes).hexdigest(),
        receipt_kind=ReceiptKindV1.SUCCINCT,
        journal_bytes=1,
        cycle_budget=1_000_000,
    )
    return replace(
        certificate,
        journal_bytes=len(certificate.canonical_journal_bytes),
    )


def test_initial_state_certificate_has_stable_python_rust_golden_roots() -> None:
    certificate = _genesis_certificate()

    assert certificate.journal_bytes == 1_336
    assert hashlib.sha256(certificate.canonical_journal_bytes).hexdigest() == (
        "eaa2444864e429f494f61220afecb9610e0d6195aa1d4cb59f34b9193ca5dd88"
    )
    assert certificate.certificate_root == (
        "0xaad3f289eaa13fc2e96451aa051437c6a91955bd6d026ee3d15517b392c9d809"
    )


def test_initial_state_certificate_rejects_noncanonical_genesis_coordinates() -> None:
    certificate = _genesis_certificate()

    with pytest.raises(ValueError, match="must not declare a predecessor"):
        replace(certificate, source_state_root=_root(12))
    with pytest.raises(TypeError, match="writer_epoch must be an exact integer"):
        replace(certificate, writer_epoch=True)  # type: ignore[arg-type]
