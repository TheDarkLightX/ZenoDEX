from __future__ import annotations

from pathlib import Path

from src.fire.compiler.compiler_registry_v1 import compile_fire_object
from src.fire.compiler.fmos_v1 import build_fmos_manifest, render_fmos_object_card
from src.fire.kernel.settlement_v1 import (
    FireLedgerBalances,
    apply_fire_object_package_settlement,
    apply_fire_persisted_bundle_settlement,
    apply_verified_fire_settlement_packet,
)
from src.fire.registry.bundle_v1 import write_fire_registry_bundle
from src.fire.verifier.settlement_v1 import FireSettlementPacket, FireVerifierReceipt, fire_witness_binding_hash


def _write_bundle(tmp_path: Path, object_id: str, raw_terms: dict[str, int]) -> Path:
    compiled = compile_fire_object(object_id, raw_terms)
    bundle_dir = tmp_path / object_id
    write_fire_registry_bundle(
        bundle_dir,
        artifact=compiled.artifact,
        build_manifest=lambda artifact: build_fmos_manifest(compiled.spec, artifact),
        render_object_card=lambda artifact: render_fmos_object_card(compiled.spec, artifact),
    )
    return bundle_dir


def test_apply_fire_object_package_settlement_burn_end_to_end(tmp_path: Path) -> None:
    bundle_dir = _write_bundle(
        tmp_path,
        "burn_boost_call_v1",
        {
            "n_notional": 10,
            "strike_index": 4,
            "cap_index": 3,
            "source_upper": 9,
        },
    )
    ok, err, result = apply_fire_object_package_settlement(
        bundle_dir=str(bundle_dir),
        holder_posted=0,
        writer_posted=30,
        holder_balance=100,
        writer_balance=250,
        witness_inputs={"witness_final": 7},
    )
    assert ok is True
    assert err is None
    assert result is not None
    assert result.object_id == "burn_boost_call_v1"
    assert result.holder_balance_after == 130
    assert result.writer_balance_after == 220


def test_apply_fire_persisted_bundle_settlement_fee_end_to_end(tmp_path: Path) -> None:
    bundle_dir = _write_bundle(
        tmp_path,
        "fee_note_v1",
        {
            "n_notional": 10,
            "cap_index": 7,
            "source_upper": 2,
        },
    )
    ok, err, result = apply_fire_persisted_bundle_settlement(
        bundle_dir=str(bundle_dir),
        holder_posted=0,
        writer_posted=20,
        holder_balance=40,
        writer_balance=90,
        witness_inputs={"witness_final": 2},
    )
    assert ok is True
    assert err is None
    assert result is not None
    assert result.object_id == "fee_note_v1"
    assert result.holder_balance_after == 60
    assert result.writer_balance_after == 70


def test_apply_verified_fire_settlement_packet_updates_balances_from_fire_kernel_surface() -> None:
    witness_hash = fire_witness_binding_hash({"witness_final": 30})
    receipt = FireVerifierReceipt.build(
        object_hash="sha256:" + "1" * 64,
        instance_hash="sha256:" + "2" * 64,
        cert_sha256="sha256:" + "3" * 64,
        holder_delta=30,
        writer_delta=-30,
        command_tag="firev_accept_and_settle",
        object_name="BurnBoostCall",
        object_version="1.0.0",
        bundle_hash="sha256:" + "4" * 64,
        witness_hash=witness_hash,
    )
    packet = FireSettlementPacket.build(
        receipt=receipt,
        holder_delta=30,
        writer_delta=-30,
        payoff_out=30,
        firev_accept=True,
    )
    ok, err, result = apply_verified_fire_settlement_packet(
        packet,
        balances=FireLedgerBalances(holder_balance=100, writer_balance=250),
        expected_bundle_hash=receipt.bundle_hash,
        expected_witness_hash=witness_hash,
    )
    assert ok is True
    assert err is None
    assert result is not None
    assert result.balances.holder_balance == 130
    assert result.balances.writer_balance == 220
