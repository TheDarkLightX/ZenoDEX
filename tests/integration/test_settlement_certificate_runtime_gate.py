from __future__ import annotations

from src.core.batch_clearing import compute_settlement
from src.core.dex import DexState
from src.core.liquidity import create_pool
from src.integration.dex_engine import DexEngineConfig, apply_ops
from src.integration.operations import parse_intents
from src.integration.settlement_end_to_end_certificate_packet import (
    SettlementEndToEndCertificateInputs,
)
from src.integration.settlement_feature_extension_packet import SettlementFeatureExtensionInputs
from src.integration.settlement_price_attestation import (
    SettlementSpotPriceAttestation,
    build_settlement_spot_price_attestation,
)
from src.integration.settlement_price_provenance import (
    SettlementSpotPriceEntry,
    SettlementSpotPricePacket,
    build_settlement_spot_price_packet,
)
from src.integration.settlement_strong_certificate import SettlementProofFlags
from src.integration.validation import validate_operations
from src.state import BalanceTable, LPTable


def _four_swap_intent_dicts() -> tuple[list[dict], BalanceTable, dict[str, object], str, str, str]:
    sender = "0x" + "aa" * 48
    asset0 = "0x" + "11" * 32
    asset1 = "0x" + "22" * 32
    pool_id, pool, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=sender,
    )
    balances = BalanceTable()
    balances.set(sender, asset0, 100_000)
    balances.set(sender, asset1, 0)
    intents = []
    for idx in range(4):
        intents.append(
            {
                "module": "TauSwap",
                "version": "0.1",
                "kind": "SWAP_EXACT_IN",
                "intent_id": "0x" + f"{idx + 1:064x}",
                "sender_pubkey": sender,
                "deadline": 9_999_999_999,
                "nonce": idx + 1,
                "pool_id": pool_id,
                "asset_in": asset0,
                "asset_out": asset1,
                "amount_in": 100,
                "min_amount_out": 1,
            }
        )
    return intents, balances, {pool_id: pool}, sender, asset0, asset1


def _spot_price_packet(asset0: str, asset1: str):
    return build_settlement_spot_price_packet(
        entries=(
            SettlementSpotPriceEntry(asset=asset0, price=100, observed_epoch=95, age_epochs=5, source_id="oracle:a"),
            SettlementSpotPriceEntry(asset=asset1, price=120, observed_epoch=97, age_epochs=3, source_id="oracle:b"),
        ),
        now_epoch=100,
        max_staleness_epochs=10,
    )


def _feature_extension_inputs() -> SettlementFeatureExtensionInputs:
    return SettlementFeatureExtensionInputs(
        trade_amount=100,
        fee_charged=1,
        buyback_amount=1,
        burned_amount=1,
        supply_before=1_000,
        supply_after=999,
        supply_floor=500,
        unit_scale=1,
        rebate_rate_bps=500,
        rebate_amount=1,
        rebate_cap=1,
        lock_days=60,
        stake_amount=50,
        tier1_days=30,
        tier2_days=90,
        weight_t1=1,
        weight_t2=2,
        weight_t3=3,
        weight_claimed=2,
        weighted_stake=100,
    )


def test_validate_operations_accepts_when_replay_bound_certificate_required() -> None:
    intent_dicts, balances, pools, _sender, asset0, asset1 = _four_swap_intent_dicts()
    intents = parse_intents({"2": intent_dicts})
    settlement = compute_settlement(intents=intents, pools=pools, balances=balances, lp_balances=LPTable())

    ok, err = validate_operations(
        intents=intents,
        settlement=settlement,
        balances=balances,
        pools=pools,
        lp_balances=LPTable(),
        block_timestamp=0,
        settlement_validation="strong_replay",
        require_settlement_certificate=True,
        settlement_end_to_end_certificate_inputs=SettlementEndToEndCertificateInputs(
            proof_flags=SettlementProofFlags.all_true(),
            price_history=(100, 110, 120),
            feature_extension_inputs=_feature_extension_inputs(),
            price_packet=_spot_price_packet(asset0, asset1),
        ),
    )
    assert ok is True
    assert err is None



def test_validate_operations_rejects_when_certificate_required_but_inputs_missing() -> None:
    intent_dicts, balances, pools, _sender, _asset0, _asset1 = _four_swap_intent_dicts()
    intents = parse_intents({"2": intent_dicts})
    settlement = compute_settlement(intents=intents, pools=pools, balances=balances, lp_balances=LPTable())

    ok, err = validate_operations(
        intents=intents,
        settlement=settlement,
        balances=balances,
        pools=pools,
        lp_balances=LPTable(),
        block_timestamp=0,
        settlement_validation="strong_replay",
        require_settlement_certificate=True,
        settlement_end_to_end_certificate_inputs=None,
    )
    assert ok is False
    assert err == "settlement certificate required but settlement_end_to_end_certificate_inputs missing"


def test_validate_operations_internalizes_feature_extension_flags_from_packet() -> None:
    intent_dicts, balances, pools, _sender, asset0, asset1 = _four_swap_intent_dicts()
    intents = parse_intents({"2": intent_dicts})
    settlement = compute_settlement(intents=intents, pools=pools, balances=balances, lp_balances=LPTable())

    ok, err = validate_operations(
        intents=intents,
        settlement=settlement,
        balances=balances,
        pools=pools,
        lp_balances=LPTable(),
        block_timestamp=0,
        settlement_validation="strong_replay",
        require_settlement_certificate=True,
        settlement_end_to_end_certificate_inputs=SettlementEndToEndCertificateInputs(
            proof_flags=SettlementProofFlags(
                cpmm_ok=0,
                balance_ok=0,
                token_ok=0,
                buyback_floor_ok=0,
                buyback_floor_fixedpoint_ok=0,
                rebate_ok=0,
                lock_weight_ok=0,
                proof_ok=1,
                binding_ok=1,
            ),
            price_history=(100, 110, 120),
            feature_extension_inputs=_feature_extension_inputs(),
            price_packet=_spot_price_packet(asset0, asset1),
        ),
    )
    assert ok is True
    assert err is None


def test_validate_operations_rejects_when_full_price_rails_fail() -> None:
    intent_dicts, balances, pools, _sender, asset0, asset1 = _four_swap_intent_dicts()
    intents = parse_intents({"2": intent_dicts})
    settlement = compute_settlement(intents=intents, pools=pools, balances=balances, lp_balances=LPTable())

    ok, err = validate_operations(
        intents=intents,
        settlement=settlement,
        balances=balances,
        pools=pools,
        lp_balances=LPTable(),
        block_timestamp=0,
        settlement_validation="strong_replay",
        require_settlement_certificate=True,
        settlement_end_to_end_certificate_inputs=SettlementEndToEndCertificateInputs(
            proof_flags=SettlementProofFlags.all_true(),
            price_history=(0, 60, 70),
            feature_extension_inputs=_feature_extension_inputs(),
            price_packet=_spot_price_packet(asset0, asset1),
        ),
    )
    assert ok is False
    assert err == "settlement end-to-end certificate full price rails rejected"


def test_validate_operations_accepts_when_end_to_end_certificate_required_from_price_packet() -> None:
    intent_dicts, balances, pools, _sender, asset0, asset1 = _four_swap_intent_dicts()
    intents = parse_intents({"2": intent_dicts})
    settlement = compute_settlement(intents=intents, pools=pools, balances=balances, lp_balances=LPTable())

    ok, err = validate_operations(
        intents=intents,
        settlement=settlement,
        balances=balances,
        pools=pools,
        lp_balances=LPTable(),
        block_timestamp=0,
        settlement_validation="strong_replay",
        require_settlement_end_to_end_certificate=True,
        settlement_end_to_end_certificate_inputs=SettlementEndToEndCertificateInputs(
            proof_flags=SettlementProofFlags.all_true(),
            price_history=(100, 110, 120),
            feature_extension_inputs=_feature_extension_inputs(),
            price_packet=_spot_price_packet(asset0, asset1),
        ),
    )
    assert ok is True
    assert err is None


def test_validate_operations_accepts_when_end_to_end_certificate_required_from_attestation() -> None:
    intent_dicts, balances, pools, _sender, asset0, asset1 = _four_swap_intent_dicts()
    intents = parse_intents({"2": intent_dicts})
    settlement = compute_settlement(intents=intents, pools=pools, balances=balances, lp_balances=LPTable())
    attestation = build_settlement_spot_price_attestation(packet=_spot_price_packet(asset0, asset1), signer_privkey=7)

    ok, err = validate_operations(
        intents=intents,
        settlement=settlement,
        balances=balances,
        pools=pools,
        lp_balances=LPTable(),
        block_timestamp=0,
        settlement_validation="strong_replay",
        require_settlement_end_to_end_certificate=True,
        settlement_end_to_end_certificate_inputs=SettlementEndToEndCertificateInputs(
            proof_flags=SettlementProofFlags.all_true(),
            price_history=(100, 110, 120),
            feature_extension_inputs=_feature_extension_inputs(),
            price_attestation=attestation,
            consumer_now_epoch=103,
            max_attestation_age_epochs=5,
            allowed_signers={attestation.signer_pubkey: ["oracle:a", "oracle:b"]},
        ),
    )
    assert ok is True
    assert err is None


def test_validate_operations_rejects_attested_certificate_with_packet_hash_snapshot_mismatch() -> None:
    intent_dicts, balances, pools, _sender, asset0, asset1 = _four_swap_intent_dicts()
    intents = parse_intents({"2": intent_dicts})
    settlement = compute_settlement(intents=intents, pools=pools, balances=balances, lp_balances=LPTable())
    built = build_settlement_spot_price_attestation(packet=_spot_price_packet(asset0, asset1), signer_privkey=7)
    attestation = SettlementSpotPriceAttestation(
        packet=built.packet,
        signer_pubkey=built.signer_pubkey,
        signed_at_epoch=built.signed_at_epoch,
        packet_hash="0x" + "00" * 32,
        signature=built.signature,
    )

    ok, err = validate_operations(
        intents=intents,
        settlement=settlement,
        balances=balances,
        pools=pools,
        lp_balances=LPTable(),
        block_timestamp=0,
        settlement_validation="strong_replay",
        require_settlement_end_to_end_certificate=True,
        settlement_end_to_end_certificate_inputs=SettlementEndToEndCertificateInputs(
            proof_flags=SettlementProofFlags.all_true(),
            price_history=(100, 110, 120),
            feature_extension_inputs=_feature_extension_inputs(),
            price_attestation=attestation,
            consumer_now_epoch=103,
            max_attestation_age_epochs=5,
            allowed_signers={attestation.signer_pubkey: ["oracle:a", "oracle:b"]},
        ),
    )
    assert ok is False
    assert err == "invalid settlement spot price attestation: packet_hash mismatch"


def test_validate_operations_rejects_attestation_with_reordered_price_packet_entries() -> None:
    intent_dicts, balances, pools, _sender, asset0, asset1 = _four_swap_intent_dicts()
    intents = parse_intents({"2": intent_dicts})
    settlement = compute_settlement(intents=intents, pools=pools, balances=balances, lp_balances=LPTable())
    built = build_settlement_spot_price_attestation(packet=_spot_price_packet(asset0, asset1), signer_privkey=7)
    packet = built.packet
    reordered_packet = SettlementSpotPricePacket(
        entries=tuple(reversed(packet.entries)),
        now_epoch=packet.now_epoch,
        max_staleness_epochs=packet.max_staleness_epochs,
        cross_module_sync_required=packet.cross_module_sync_required,
        cross_module_sync_ok=packet.cross_module_sync_ok,
        price_vector_sha256=packet.price_vector_sha256,
        provenance_vector_sha256=packet.provenance_vector_sha256,
        unique_assets=packet.unique_assets,
        all_positive=packet.all_positive,
        all_fresh=packet.all_fresh,
        provenance_ok=packet.provenance_ok,
        cross_module_sync_contract=packet.cross_module_sync_contract,
    )
    attestation = SettlementSpotPriceAttestation(
        packet=reordered_packet,
        signer_pubkey=built.signer_pubkey,
        signed_at_epoch=built.signed_at_epoch,
        packet_hash=built.packet_hash,
        signature=built.signature,
    )

    ok, err = validate_operations(
        intents=intents,
        settlement=settlement,
        balances=balances,
        pools=pools,
        lp_balances=LPTable(),
        block_timestamp=0,
        settlement_validation="strong_replay",
        require_settlement_end_to_end_certificate=True,
        settlement_end_to_end_certificate_inputs=SettlementEndToEndCertificateInputs(
            proof_flags=SettlementProofFlags.all_true(),
            price_history=(100, 110, 120),
            feature_extension_inputs=_feature_extension_inputs(),
            price_attestation=attestation,
            consumer_now_epoch=103,
            max_attestation_age_epochs=5,
            allowed_signers={attestation.signer_pubkey: ["oracle:a", "oracle:b"]},
        ),
    )
    assert ok is False
    assert err == (
        "invalid settlement spot price attestation: invalid settlement spot price packet: "
        "settlement spot price packet mismatch"
    )


def test_validate_operations_rejects_attested_certificate_with_source_allowlist_gap() -> None:
    intent_dicts, balances, pools, _sender, asset0, asset1 = _four_swap_intent_dicts()
    intents = parse_intents({"2": intent_dicts})
    settlement = compute_settlement(intents=intents, pools=pools, balances=balances, lp_balances=LPTable())
    attestation = build_settlement_spot_price_attestation(packet=_spot_price_packet(asset0, asset1), signer_privkey=7)

    ok, err = validate_operations(
        intents=intents,
        settlement=settlement,
        balances=balances,
        pools=pools,
        lp_balances=LPTable(),
        block_timestamp=0,
        settlement_validation="strong_replay",
        require_settlement_end_to_end_certificate=True,
        settlement_end_to_end_certificate_inputs=SettlementEndToEndCertificateInputs(
            proof_flags=SettlementProofFlags.all_true(),
            price_history=(100, 110, 120),
            feature_extension_inputs=_feature_extension_inputs(),
            price_attestation=attestation,
            consumer_now_epoch=103,
            max_attestation_age_epochs=5,
            allowed_signers={attestation.signer_pubkey: ["oracle:a"]},
        ),
    )
    assert ok is False
    assert err == "invalid settlement spot price attestation: source_id not allowlisted for signer: oracle:b"


def test_validate_operations_rejects_stale_attested_certificate_at_runtime_gate() -> None:
    intent_dicts, balances, pools, _sender, asset0, asset1 = _four_swap_intent_dicts()
    intents = parse_intents({"2": intent_dicts})
    settlement = compute_settlement(intents=intents, pools=pools, balances=balances, lp_balances=LPTable())
    attestation = build_settlement_spot_price_attestation(packet=_spot_price_packet(asset0, asset1), signer_privkey=7)

    ok, err = validate_operations(
        intents=intents,
        settlement=settlement,
        balances=balances,
        pools=pools,
        lp_balances=LPTable(),
        block_timestamp=0,
        settlement_validation="strong_replay",
        require_settlement_end_to_end_certificate=True,
        settlement_end_to_end_certificate_inputs=SettlementEndToEndCertificateInputs(
            proof_flags=SettlementProofFlags.all_true(),
            price_history=(100, 110, 120),
            feature_extension_inputs=_feature_extension_inputs(),
            price_attestation=attestation,
            consumer_now_epoch=107,
            max_attestation_age_epochs=5,
            allowed_signers={attestation.signer_pubkey: ["oracle:a", "oracle:b"]},
        ),
    )
    assert ok is False
    assert err == "invalid settlement spot price attestation: settlement spot price attestation is stale"


def test_validate_operations_rejects_future_attestation_epoch_at_runtime_gate() -> None:
    intent_dicts, balances, pools, _sender, asset0, asset1 = _four_swap_intent_dicts()
    intents = parse_intents({"2": intent_dicts})
    settlement = compute_settlement(intents=intents, pools=pools, balances=balances, lp_balances=LPTable())
    attestation = build_settlement_spot_price_attestation(packet=_spot_price_packet(asset0, asset1), signer_privkey=7)

    ok, err = validate_operations(
        intents=intents,
        settlement=settlement,
        balances=balances,
        pools=pools,
        lp_balances=LPTable(),
        block_timestamp=0,
        settlement_validation="strong_replay",
        require_settlement_end_to_end_certificate=True,
        settlement_end_to_end_certificate_inputs=SettlementEndToEndCertificateInputs(
            proof_flags=SettlementProofFlags.all_true(),
            price_history=(100, 110, 120),
            feature_extension_inputs=_feature_extension_inputs(),
            price_attestation=attestation,
            consumer_now_epoch=99,
            max_attestation_age_epochs=5,
            allowed_signers={attestation.signer_pubkey: ["oracle:a", "oracle:b"]},
        ),
    )
    assert ok is False
    assert err == "invalid settlement spot price attestation: attestation signed_at_epoch is in the future"


def test_validate_operations_rejects_when_end_to_end_certificate_required_but_inputs_missing() -> None:
    intent_dicts, balances, pools, _sender, _asset0, _asset1 = _four_swap_intent_dicts()
    intents = parse_intents({"2": intent_dicts})
    settlement = compute_settlement(intents=intents, pools=pools, balances=balances, lp_balances=LPTable())

    ok, err = validate_operations(
        intents=intents,
        settlement=settlement,
        balances=balances,
        pools=pools,
        lp_balances=LPTable(),
        block_timestamp=0,
        settlement_validation="strong_replay",
        require_settlement_end_to_end_certificate=True,
        settlement_end_to_end_certificate_inputs=None,
    )
    assert ok is False
    assert err == "settlement certificate required but settlement_end_to_end_certificate_inputs missing"


def test_validate_operations_rejects_when_end_to_end_full_price_rails_fail() -> None:
    intent_dicts, balances, pools, _sender, asset0, asset1 = _four_swap_intent_dicts()
    intents = parse_intents({"2": intent_dicts})
    settlement = compute_settlement(intents=intents, pools=pools, balances=balances, lp_balances=LPTable())

    ok, err = validate_operations(
        intents=intents,
        settlement=settlement,
        balances=balances,
        pools=pools,
        lp_balances=LPTable(),
        block_timestamp=0,
        settlement_validation="strong_replay",
        require_settlement_end_to_end_certificate=True,
        settlement_end_to_end_certificate_inputs=SettlementEndToEndCertificateInputs(
            proof_flags=SettlementProofFlags.all_true(),
            price_history=(0, 60, 70),
            feature_extension_inputs=_feature_extension_inputs(),
            price_packet=_spot_price_packet(asset0, asset1),
        ),
    )
    assert ok is False
    assert err == "settlement end-to-end certificate full price rails rejected"


def test_validate_operations_existing_certificate_mode_prefers_end_to_end_inputs() -> None:
    intent_dicts, balances, pools, _sender, asset0, asset1 = _four_swap_intent_dicts()
    intents = parse_intents({"2": intent_dicts})
    settlement = compute_settlement(intents=intents, pools=pools, balances=balances, lp_balances=LPTable())

    ok, err = validate_operations(
        intents=intents,
        settlement=settlement,
        balances=balances,
        pools=pools,
        lp_balances=LPTable(),
        block_timestamp=0,
        settlement_validation="strong_replay",
        require_settlement_certificate=True,
        settlement_end_to_end_certificate_inputs=SettlementEndToEndCertificateInputs(
            proof_flags=SettlementProofFlags.all_true(),
            price_history=(100, 110, 120),
            feature_extension_inputs=_feature_extension_inputs(),
            price_packet=_spot_price_packet(asset0, asset1),
        ),
    )
    assert ok is True
    assert err is None


def test_apply_ops_accepts_when_engine_requires_replay_bound_certificate() -> None:
    intent_dicts, balances, pools, sender, asset0, asset1 = _four_swap_intent_dicts()
    state = DexState(balances=balances, pools=pools, lp_balances=LPTable())

    res = apply_ops(
        config=DexEngineConfig(
            allow_missing_settlement=True,
            require_intent_signatures=False,
            require_settlement_certificate=True,
            settlement_end_to_end_certificate_inputs=SettlementEndToEndCertificateInputs(
                proof_flags=SettlementProofFlags.all_true(),
                price_history=(100, 110, 120),
                feature_extension_inputs=_feature_extension_inputs(),
                price_packet=_spot_price_packet(asset0, asset1),
            ),
        ),
        state=state,
        operations={"2": intent_dicts},
        block_timestamp=0,
        tx_sender_pubkey=sender,
    )
    assert res.ok, res.error
    assert res.state is not None


def test_apply_ops_accepts_when_engine_requires_end_to_end_certificate() -> None:
    intent_dicts, balances, pools, sender, asset0, asset1 = _four_swap_intent_dicts()
    state = DexState(balances=balances, pools=pools, lp_balances=LPTable())

    res = apply_ops(
        config=DexEngineConfig(
            allow_missing_settlement=True,
            require_intent_signatures=False,
            require_settlement_end_to_end_certificate=True,
            settlement_end_to_end_certificate_inputs=SettlementEndToEndCertificateInputs(
                proof_flags=SettlementProofFlags.all_true(),
                price_history=(100, 110, 120),
                feature_extension_inputs=_feature_extension_inputs(),
                price_packet=_spot_price_packet(asset0, asset1),
            ),
        ),
        state=state,
        operations={"2": intent_dicts},
        block_timestamp=0,
        tx_sender_pubkey=sender,
    )
    assert res.ok, res.error
    assert res.state is not None


def test_apply_ops_rejects_when_engine_end_to_end_full_price_rails_fail() -> None:
    intent_dicts, balances, pools, sender, asset0, asset1 = _four_swap_intent_dicts()
    state = DexState(balances=balances, pools=pools, lp_balances=LPTable())

    res = apply_ops(
        config=DexEngineConfig(
            allow_missing_settlement=True,
            require_intent_signatures=False,
            require_settlement_end_to_end_certificate=True,
            settlement_end_to_end_certificate_inputs=SettlementEndToEndCertificateInputs(
                proof_flags=SettlementProofFlags.all_true(),
                price_history=(0, 60, 70),
                feature_extension_inputs=_feature_extension_inputs(),
                price_packet=_spot_price_packet(asset0, asset1),
            ),
        ),
        state=state,
        operations={"2": intent_dicts},
        block_timestamp=0,
        tx_sender_pubkey=sender,
    )
    assert res.ok is False
    assert res.error == "settlement end-to-end certificate full price rails rejected"


def test_apply_ops_existing_certificate_mode_prefers_end_to_end_inputs() -> None:
    intent_dicts, balances, pools, sender, asset0, asset1 = _four_swap_intent_dicts()
    state = DexState(balances=balances, pools=pools, lp_balances=LPTable())

    res = apply_ops(
        config=DexEngineConfig(
            allow_missing_settlement=True,
            require_intent_signatures=False,
            require_settlement_certificate=True,
            settlement_end_to_end_certificate_inputs=SettlementEndToEndCertificateInputs(
                proof_flags=SettlementProofFlags.all_true(),
                price_history=(100, 110, 120),
                feature_extension_inputs=_feature_extension_inputs(),
                price_packet=_spot_price_packet(asset0, asset1),
            ),
        ),
        state=state,
        operations={"2": intent_dicts},
        block_timestamp=0,
        tx_sender_pubkey=sender,
    )
    assert res.ok, res.error
    assert res.state is not None


def test_apply_ops_rejects_when_engine_requires_full_price_rails_and_history_fails() -> None:
    intent_dicts, balances, pools, sender, asset0, asset1 = _four_swap_intent_dicts()
    state = DexState(balances=balances, pools=pools, lp_balances=LPTable())

    res = apply_ops(
        config=DexEngineConfig(
            allow_missing_settlement=True,
            require_intent_signatures=False,
            require_settlement_certificate=True,
            settlement_end_to_end_certificate_inputs=SettlementEndToEndCertificateInputs(
                proof_flags=SettlementProofFlags.all_true(),
                price_history=(0, 60, 70),
                feature_extension_inputs=_feature_extension_inputs(),
                price_packet=_spot_price_packet(asset0, asset1),
            ),
        ),
        state=state,
        operations={"2": intent_dicts},
        block_timestamp=0,
        tx_sender_pubkey=sender,
    )
    assert res.ok is False
    assert res.error == "settlement end-to-end certificate full price rails rejected"


def test_end_to_end_certificate_gate_preserves_protocol_fee_policy() -> None:
    intent_dicts, balances, pools, _sender, asset0, asset1 = _four_swap_intent_dicts()
    intents = parse_intents({"2": intent_dicts})
    protocol_recipient = "0x" + "ff" * 48
    settlement = compute_settlement(
        intents=intents,
        pools=pools,
        balances=balances,
        lp_balances=LPTable(),
        protocol_fee_share_bps=10_000,
        protocol_fee_recipient_pubkey=protocol_recipient,
    )
    assert sum(fill.protocol_fee_paid for fill in settlement.fills) > 0

    ok, err = validate_operations(
        intents=intents,
        settlement=settlement,
        balances=balances,
        pools=pools,
        lp_balances=LPTable(),
        block_timestamp=0,
        settlement_validation="strong_replay",
        require_settlement_end_to_end_certificate=True,
        settlement_end_to_end_certificate_inputs=SettlementEndToEndCertificateInputs(
            proof_flags=SettlementProofFlags.all_true(),
            price_history=(100, 110, 120),
            feature_extension_inputs=_feature_extension_inputs(),
            price_packet=_spot_price_packet(asset0, asset1),
        ),
        protocol_fee_share_bps=10_000,
        protocol_fee_recipient_pubkey=protocol_recipient,
    )

    assert ok is True
    assert err is None
