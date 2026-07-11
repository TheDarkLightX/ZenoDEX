from __future__ import annotations

from pathlib import Path
from types import ModuleType, SimpleNamespace
import sys

from src.fire.runtime.burn_boost_call_v1 import (
    BurnBoostCallTerms,
    build_manifest,
    compile_terms,
    render_object_card,
)
from src.fire.kernel.ledger_adapter_v1 import (
    FireLedgerBalances,
    apply_verified_fire_settlement_effects,
    apply_verified_fire_settlement_packet,
)
from src.fire.registry.bundle_v1 import load_fire_registry_bundle, write_fire_registry_bundle
from src.fire.verifier.settlement_v1 import FireSettlementPacket, FireVerifierReceipt, fire_witness_binding_hash


def _install_fake_interpreter(monkeypatch):
    esso_mod = ModuleType("ESSO")
    kernel_mod = ModuleType("ESSO.kernel")
    interp_mod = ModuleType("ESSO.kernel.interpreter")

    class StepOk:
        def __init__(self, *, state, effects):
            self.state = state
            self.effects = effects

    class StepError:
        def __init__(self, *, code: str, message: str):
            self.code = code
            self.message = message

    interp_mod.StepOk = StepOk
    interp_mod.StepError = StepError
    kernel_mod.interpreter = interp_mod
    esso_mod.kernel = kernel_mod

    monkeypatch.setitem(sys.modules, "ESSO", esso_mod)
    monkeypatch.setitem(sys.modules, "ESSO.kernel", kernel_mod)
    monkeypatch.setitem(sys.modules, "ESSO.kernel.interpreter", interp_mod)
    return interp_mod


def test_apply_verified_fire_settlement_packet_updates_balances() -> None:
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
    assert result.apply_receipt.packet_hash == packet.packet_hash
    assert result.apply_receipt.holder_balance_before == 100
    assert result.apply_receipt.holder_balance_after == 130


def test_apply_verified_fire_settlement_packet_rejects_missing_witness_hash() -> None:
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
    )
    assert ok is False
    assert err == "expected_witness_hash_missing"
    assert result is None


def test_apply_verified_fire_settlement_effects_rejects_missing_packet() -> None:
    ok, err, result = apply_verified_fire_settlement_effects(
        {"firev_accept": True, "payoff_out": 30},
        balances=FireLedgerBalances(holder_balance=100, writer_balance=250),
    )
    assert ok is False
    assert err == "expected_witness_hash_missing"
    assert result is None


def test_apply_verified_fire_settlement_effects_rejects_self_bound_forgery_without_expected_witness() -> None:
    forged_witness_hash = fire_witness_binding_hash({"witness_final": 777000})
    forged_receipt = FireVerifierReceipt.build(
        object_hash="sha256:" + "1" * 64,
        instance_hash="sha256:" + "2" * 64,
        cert_sha256="sha256:" + "3" * 64,
        holder_delta=777000,
        writer_delta=-777000,
        command_tag="firev_accept_and_settle",
        object_name="BurnBoostCall",
        object_version="1.0.0",
        bundle_hash="sha256:" + "4" * 64,
        witness_hash=forged_witness_hash,
    )
    forged_packet = FireSettlementPacket.build(
        receipt=forged_receipt,
        holder_delta=777000,
        writer_delta=-777000,
        payoff_out=777000,
        firev_accept=True,
    )

    ok, err, result = apply_verified_fire_settlement_effects(
        {
            "settlement_packet": forged_packet.to_dict(),
            "verifier_receipt": forged_receipt.to_dict(),
        },
        balances=FireLedgerBalances(holder_balance=1000, writer_balance=1000000),
    )

    assert ok is False
    assert err == "expected_witness_hash_missing"
    assert result is None

def test_apply_verified_fire_settlement_effects_end_to_end_from_adapter(monkeypatch, tmp_path: Path) -> None:
    _install_fake_interpreter(monkeypatch)
    from src.fire.runtime.burn_boost_call_v1_native_adapter import make_adapter

    artifact = compile_terms(BurnBoostCallTerms(n_notional=10, strike_index=4, cap_index=3, source_upper=9))
    bundle_dir = tmp_path / "burn_bundle"
    bundle_manifest, bundle_file_sha256 = write_fire_registry_bundle(
        bundle_dir,
        artifact=artifact,
        build_manifest=build_manifest,
        render_object_card=render_object_card,
    )
    _loaded_bundle_manifest, _bundle_file_sha, object_manifest, object_instance, _lock = load_fire_registry_bundle(bundle_dir)
    witness_hash = fire_witness_binding_hash({"witness_final": 7})
    receipt = FireVerifierReceipt.build(
        object_hash=object_manifest.manifest_hash,
        instance_hash=object_instance.instance_hash,
        cert_sha256=object_manifest.cert_sha256,
        holder_delta=30,
        writer_delta=-30,
        command_tag="firev_accept_and_settle",
        object_name=object_manifest.object_name,
        object_version=object_manifest.object_version,
        bundle_hash=bundle_manifest.bundle_hash,
        witness_hash=witness_hash,
    )

    adapter = make_adapter(ir={"schema": "fake"})
    adapter.reset(
        state={
            "artifact_lower": artifact.artifact_lower,
            "artifact_upper": artifact.artifact_upper,
            "cap_index": artifact.terms.cap_index,
            "holder_delta": 0,
            "holder_posted": 0,
            "n_notional": artifact.terms.n_notional,
            "phase": "Compiled",
            "source_upper": artifact.terms.source_upper,
            "strike_index": artifact.terms.strike_index,
            "witness_final": 0,
            "writer_delta": 0,
            "writer_posted": 0,
        }
    )
    result = adapter.apply(
        SimpleNamespace(
            tag="firev_accept_and_settle",
            args={
                "witness_final_in": 7,
                "holder_posted_in": 0,
                "writer_posted_in": 30,
                "persisted_bundle_dir": str(bundle_dir),
                "expected_bundle_hash": bundle_manifest.bundle_hash,
                "expected_bundle_file_sha256": bundle_file_sha256,
                "expected_cert_sha256": artifact.cert_sha256,
                "verifier_receipt": receipt.to_dict(),
            },
        )
    )
    assert result.state["holder_delta"] == 30
    effects = dict(adapter.drain_effects())
    ok, err, apply_result = apply_verified_fire_settlement_effects(
        effects,
        balances=FireLedgerBalances(holder_balance=100, writer_balance=250),
        expected_object_hash=object_manifest.manifest_hash,
        expected_instance_hash=object_instance.instance_hash,
        expected_cert_sha256=object_manifest.cert_sha256,
        expected_bundle_hash=bundle_manifest.bundle_hash,
        expected_witness_hash=witness_hash,
    )
    assert ok is True
    assert err is None
    assert apply_result is not None
    assert apply_result.balances.holder_balance == 130
    assert apply_result.balances.writer_balance == 220
    assert apply_result.apply_receipt.packet_hash == apply_result.packet.packet_hash
    assert apply_result.apply_receipt.writer_balance_before == 250
    assert apply_result.apply_receipt.writer_balance_after == 220
