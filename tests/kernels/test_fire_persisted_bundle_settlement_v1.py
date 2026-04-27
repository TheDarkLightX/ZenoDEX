from __future__ import annotations

from pathlib import Path

from src.fire.compiler.compiler_registry_v1 import compile_fire_object
from src.fire.compiler.fmos_v1 import build_fmos_manifest, render_fmos_object_card
from src.fire.kernel.persisted_bundle_settlement_v1 import apply_fire_persisted_bundle_settlement
from src.fire.registry.bundle_v1 import write_fire_registry_bundle
from src.fire.verifier.settlement_v1 import FireSettlementPacket, fire_witness_binding_hash


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


def test_apply_fire_persisted_bundle_settlement_burn_end_to_end(tmp_path: Path) -> None:
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
    ok, err, result = apply_fire_persisted_bundle_settlement(
        bundle_dir=bundle_dir,
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
    assert result.holder_delta == 30
    assert result.writer_delta == -30
    assert result.holder_balance_after == 130
    assert result.writer_balance_after == 220
    assert result.verifier_receipt.bundle_hash == result.bundle_hash
    assert result.verifier_receipt.witness_hash == fire_witness_binding_hash({"witness_final": 7})
    assert result.settlement_packet.receipt.instance_hash == result.instance_hash
    assert result.apply_receipt.packet_hash == result.settlement_packet.packet_hash
    assert result.apply_receipt.holder_balance_before == 100
    assert result.apply_receipt.holder_balance_after == 130


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
        bundle_dir=bundle_dir,
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
    assert result.holder_delta == 20
    assert result.writer_delta == -20
    assert result.verifier_receipt.witness_hash == fire_witness_binding_hash({"witness_final": 2})
    assert result.holder_balance_after == 60
    assert result.writer_balance_after == 70
    assert result.apply_receipt.writer_balance_before == 90
    assert result.apply_receipt.writer_balance_after == 70


def test_apply_fire_persisted_bundle_settlement_lp_end_to_end(tmp_path: Path) -> None:
    bundle_dir = _write_bundle(
        tmp_path,
        "lp_loss_cover_v1",
        {
            "n_notional": 10,
            "deductible": 2,
            "cap_amount": 5,
            "hodl_lower": 10,
            "hodl_upper": 20,
            "lpv_lower": 7,
            "lpv_upper": 12,
        },
    )
    ok, err, result = apply_fire_persisted_bundle_settlement(
        bundle_dir=bundle_dir,
        holder_posted=0,
        writer_posted=50,
        holder_balance=80,
        writer_balance=200,
        witness_inputs={"witness_hodl_final": 20, "witness_lpv_final": 7},
    )
    assert ok is True
    assert err is None
    assert result is not None
    assert result.object_id == "lp_loss_cover_v1"
    assert result.holder_delta == 50
    assert result.writer_delta == -50
    assert result.verifier_receipt.witness_hash == fire_witness_binding_hash(
        {"witness_hodl_final": 20, "witness_lpv_final": 7}
    )
    assert result.holder_balance_after == 130
    assert result.writer_balance_after == 150
    assert result.apply_receipt.packet_hash == result.settlement_packet.packet_hash


def test_apply_fire_persisted_bundle_settlement_rejects_wrong_witness_shape(tmp_path: Path) -> None:
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
    ok, err, result = apply_fire_persisted_bundle_settlement(
        bundle_dir=bundle_dir,
        holder_posted=0,
        writer_posted=30,
        holder_balance=100,
        writer_balance=250,
        witness_inputs={"witness_hodl_final": 7},
    )
    assert ok is False
    assert err == "missing witness inputs: witness_final"
    assert result is None


def test_apply_fire_persisted_bundle_settlement_rejects_runtime_adapter_divergence(
    monkeypatch, tmp_path: Path
) -> None:
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
    import src.fire.kernel.persisted_bundle_settlement_v1 as settlement_mod

    original_apply = settlement_mod.apply_verified_fire_settlement_effects

    def _tampered_apply(*args, **kwargs):
        ok, err, result = original_apply(*args, **kwargs)
        if not ok or result is None:
            return ok, err, result
        packet = FireSettlementPacket.build(
            receipt=result.packet.receipt,
            holder_delta=result.packet.holder_delta + 1,
            writer_delta=result.packet.writer_delta - 1,
            payoff_out=result.packet.payoff_out + 1,
            firev_accept=result.packet.firev_accept,
        )
        return True, None, type(result)(
            balances=result.balances,
            packet=packet,
            apply_receipt=result.apply_receipt,
        )

    monkeypatch.setattr(settlement_mod, "apply_verified_fire_settlement_effects", _tampered_apply)

    ok, err, result = apply_fire_persisted_bundle_settlement(
        bundle_dir=bundle_dir,
        holder_posted=0,
        writer_posted=30,
        holder_balance=100,
        writer_balance=250,
        witness_inputs={"witness_final": 7},
    )
    assert ok is False
    assert err == "crosscheck_holder_delta_mismatch"
    assert result is None
