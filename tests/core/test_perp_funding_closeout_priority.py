from __future__ import annotations

from src.core.perp_funding_closeout_liability_certificate import (
    ClosedFundingSourceRow,
    PositionAccount,
    build_funding_closeout_source_portfolio_bound_rationed_allocation_receipt,
)
from src.core.perp_funding_closeout_policy_ledger import (
    HAIRCUT_POLICY_RECOVERABLE_CLAIM,
    build_funding_closeout_policy_ledger,
    funding_closeout_policy_ledger_hash,
)
from src.core.perp_funding_closeout_priority import (
    RECEIVER_DISTRIBUTION_LARGEST_REMAINDER,
    RECOVERY_PRIORITY_RECEIVER_FIRST,
    RECOVERY_PRIORITY_SINK_FIRST,
    RecoveryPriorityVerdict,
    build_funding_closeout_receiver_recovery_distribution_certificate,
    build_funding_closeout_recovery_collection_receipt,
    build_funding_closeout_recovery_priority_certificate,
    build_funding_closeout_recovery_source_authority,
    build_funding_closeout_recovery_source_authority_binding,
    build_funding_closeout_sink_recovery_distribution_certificate,
    compute_receiver_largest_remainder_distribution,
    compute_sink_largest_remainder_distribution,
    funding_closeout_receiver_recovery_distribution_certificate_hash,
    funding_closeout_receiver_recovery_distribution_certificate_to_payload,
    funding_closeout_recovery_collection_receipt_hash,
    funding_closeout_recovery_collection_receipt_to_payload,
    funding_closeout_recovery_priority_certificate_hash,
    funding_closeout_recovery_priority_certificate_to_payload,
    funding_closeout_recovery_source_authority_binding_to_payload,
    funding_closeout_recovery_source_authority_hash,
    funding_closeout_recovery_source_authority_to_payload,
    funding_closeout_sink_recovery_distribution_certificate_hash,
    funding_closeout_sink_recovery_distribution_certificate_to_payload,
    verify_funding_closeout_receiver_recovery_distribution_payload,
    verify_funding_closeout_recovery_collection_receipt_payload,
    verify_funding_closeout_recovery_priority_certificate_payload,
    verify_funding_closeout_recovery_source_authority_binding_payload,
    verify_funding_closeout_recovery_source_authority_payload,
    verify_funding_closeout_sink_recovery_distribution_payload,
)
from src.core.perp_v2.math import PRICE_SCALE

MARKET_ID = "perp:funding-closeout-priority"
EPOCH = 3
PRICE_E8 = 100 * PRICE_SCALE
PAYER_A = "aa" * 48
RECEIVER_A = "bb" * 48
RECEIVER_B = "cc" * 48
PAYER_B = "dd" * 48
AUTHORITY_STATE_ROOT_HASH = "sha256:" + "44" * 32
AUTHORITY_POLICY_HASH = "sha256:" + "55" * 32


def _pre_accounts() -> tuple[PositionAccount, ...]:
    return (
        PositionAccount(PAYER_A, 100_000),
        PositionAccount(RECEIVER_A, -90_000),
        PositionAccount(RECEIVER_B, -60_000),
        PositionAccount(PAYER_B, 50_000),
    )


def _post_accounts() -> tuple[PositionAccount, ...]:
    return (
        PositionAccount(PAYER_A, 0),
        PositionAccount(RECEIVER_A, -90_000),
        PositionAccount(RECEIVER_B, -60_000),
        PositionAccount(PAYER_B, 0),
    )


def _emitted_source_rows() -> tuple[ClosedFundingSourceRow, ...]:
    return (
        ClosedFundingSourceRow(PAYER_A, EPOCH, 0, 145_000),
        ClosedFundingSourceRow(PAYER_B, EPOCH, 0, 150_000),
    )


def _policy_ledger():
    receipt = build_funding_closeout_source_portfolio_bound_rationed_allocation_receipt(
        _pre_accounts(),
        _post_accounts(),
        market_id=MARKET_ID,
        epoch=EPOCH,
        price_e8=PRICE_E8,
        funding_rate_bps=100,
        emitted_source_availability_rows=_emitted_source_rows(),
        aggregate_sink_capacity_quote=70_000,
        sink_capacity_by_account={PAYER_A: 40_000, PAYER_B: 30_000},
    )
    return build_funding_closeout_policy_ledger(
        receipt,
        haircut_policy=HAIRCUT_POLICY_RECOVERABLE_CLAIM,
    )


def _source_authority():
    return build_funding_closeout_recovery_source_authority(
        market_id=MARKET_ID,
        valid_from_epoch=EPOCH,
        valid_until_epoch=EPOCH,
        authorized_source_ids=("source:closed-payer-recovery",),
    )


def _source_authority_binding_payload(
    *,
    authority=None,
    state_root_hash: str = AUTHORITY_STATE_ROOT_HASH,
    policy_hash: str = AUTHORITY_POLICY_HASH,
    signer_privkey: int = 1,
) -> dict[str, object]:
    authority = authority or _source_authority()
    return funding_closeout_recovery_source_authority_binding_to_payload(
        build_funding_closeout_recovery_source_authority_binding(
            market_id=MARKET_ID,
            valid_from_epoch=EPOCH,
            valid_until_epoch=EPOCH,
            authority_hash=funding_closeout_recovery_source_authority_hash(
                authority
            ),
            authority_state_root_hash=state_root_hash,
            policy_hash=policy_hash,
            signer_privkey=signer_privkey,
        )
    )


def test_receiver_first_priority_allocates_remainder_to_sink() -> None:
    ledger = _policy_ledger()
    cert = build_funding_closeout_recovery_priority_certificate(
        ledger,
        priority_policy=RECOVERY_PRIORITY_RECEIVER_FIRST,
        source_capacity_quote=100_000,
    )
    assert cert.total_recoverable_claim_quote == 80_000
    assert cert.total_subrogated_claim_quote == 70_000
    assert cert.receiver_recovery_quote == 80_000
    assert cert.sink_recovery_quote == 20_000
    assert cert.policy_ledger_hash == funding_closeout_policy_ledger_hash(ledger)
    assert verify_funding_closeout_recovery_priority_certificate_payload(
        funding_closeout_recovery_priority_certificate_to_payload(cert),
        policy_ledger=ledger,
    ) == RecoveryPriorityVerdict(True, None)
    assert funding_closeout_recovery_priority_certificate_hash(cert).startswith(
        "sha256:"
    )


def test_sink_first_priority_allocates_remainder_to_receiver() -> None:
    ledger = _policy_ledger()
    cert = build_funding_closeout_recovery_priority_certificate(
        ledger,
        priority_policy=RECOVERY_PRIORITY_SINK_FIRST,
        source_capacity_quote=100_000,
    )
    assert cert.receiver_recovery_quote == 30_000
    assert cert.sink_recovery_quote == 70_000
    assert verify_funding_closeout_recovery_priority_certificate_payload(
        funding_closeout_recovery_priority_certificate_to_payload(cert),
        policy_ledger=ledger,
    ) == RecoveryPriorityVerdict(True, None)


def test_double_recovery_against_same_source_rejects() -> None:
    ledger = _policy_ledger()
    cert = build_funding_closeout_recovery_priority_certificate(
        ledger,
        priority_policy=RECOVERY_PRIORITY_RECEIVER_FIRST,
        source_capacity_quote=100_000,
    )
    payload = funding_closeout_recovery_priority_certificate_to_payload(cert)
    payload["receiver_recovery_quote"] = 80_000
    payload["sink_recovery_quote"] = 70_000
    assert verify_funding_closeout_recovery_priority_certificate_payload(payload) == (
        RecoveryPriorityVerdict(False, "recovery allocation exceeds source capacity")
    )


def test_priority_inversion_rejects_even_when_capacity_is_respected() -> None:
    ledger = _policy_ledger()
    cert = build_funding_closeout_recovery_priority_certificate(
        ledger,
        priority_policy=RECOVERY_PRIORITY_RECEIVER_FIRST,
        source_capacity_quote=100_000,
    )
    payload = funding_closeout_recovery_priority_certificate_to_payload(cert)
    payload["receiver_recovery_quote"] = 30_000
    payload["sink_recovery_quote"] = 70_000
    assert verify_funding_closeout_recovery_priority_certificate_payload(payload) == (
        RecoveryPriorityVerdict(False, "receiver_first receiver recovery mismatch")
    )


def test_policy_ledger_hash_mismatch_rejects() -> None:
    ledger = _policy_ledger()
    cert = build_funding_closeout_recovery_priority_certificate(
        ledger,
        priority_policy=RECOVERY_PRIORITY_RECEIVER_FIRST,
        source_capacity_quote=100_000,
    )
    payload = funding_closeout_recovery_priority_certificate_to_payload(cert)
    payload["policy_ledger_hash"] = "sha256:" + "88" * 32
    assert verify_funding_closeout_recovery_priority_certificate_payload(
        payload,
        policy_ledger=ledger,
    ) == RecoveryPriorityVerdict(
        False,
        "recovery priority policy ledger hash mismatch",
    )


def test_receiver_distribution_splits_recovery_by_largest_remainder() -> None:
    ledger = _policy_ledger()
    priority = build_funding_closeout_recovery_priority_certificate(
        ledger,
        priority_policy=RECOVERY_PRIORITY_RECEIVER_FIRST,
        source_capacity_quote=50_000,
    )
    distribution = build_funding_closeout_receiver_recovery_distribution_certificate(
        ledger,
        priority,
    )
    assert distribution.distribution_policy == RECEIVER_DISTRIBUTION_LARGEST_REMAINDER
    assert distribution.total_receiver_recovery_quote == 50_000
    assert [
        (row.account_pubkey, row.recoverable_claim_quote, row.recovery_quote)
        for row in distribution.receiver_rows
    ] == [
        (RECEIVER_A, 48_000, 30_000),
        (RECEIVER_B, 32_000, 20_000),
    ]
    assert verify_funding_closeout_receiver_recovery_distribution_payload(
        funding_closeout_receiver_recovery_distribution_certificate_to_payload(
            distribution
        ),
        policy_ledger=ledger,
        priority_certificate=priority,
    ) == RecoveryPriorityVerdict(True, None)
    assert funding_closeout_receiver_recovery_distribution_certificate_hash(
        distribution
    ).startswith("sha256:")


def test_receiver_distribution_allocates_floor_dust_deterministically() -> None:
    rows = compute_receiver_largest_remainder_distribution(
        ((RECEIVER_A, 48_000), (RECEIVER_B, 32_000)),
        total_receiver_recovery_quote=1,
    )
    assert [(row.account_pubkey, row.recovery_quote) for row in rows] == [
        (RECEIVER_A, 1),
        (RECEIVER_B, 0),
    ]


def test_receiver_distribution_rejects_row_cap_preserving_skip() -> None:
    ledger = _policy_ledger()
    priority = build_funding_closeout_recovery_priority_certificate(
        ledger,
        priority_policy=RECOVERY_PRIORITY_RECEIVER_FIRST,
        source_capacity_quote=50_000,
    )
    distribution = build_funding_closeout_receiver_recovery_distribution_certificate(
        ledger,
        priority,
    )
    payload = funding_closeout_receiver_recovery_distribution_certificate_to_payload(
        distribution
    )
    rows = list(payload["receiver_rows"])
    rows[0] = {**rows[0], "recovery_quote": 18_000}
    rows[1] = {**rows[1], "recovery_quote": 32_000}
    payload["receiver_rows"] = rows
    assert verify_funding_closeout_receiver_recovery_distribution_payload(
        payload,
        policy_ledger=ledger,
        priority_certificate=priority,
    ) == RecoveryPriorityVerdict(
        False,
        "receiver largest-remainder distribution mismatch",
    )


def test_receiver_distribution_rejects_priority_hash_mismatch() -> None:
    ledger = _policy_ledger()
    priority = build_funding_closeout_recovery_priority_certificate(
        ledger,
        priority_policy=RECOVERY_PRIORITY_RECEIVER_FIRST,
        source_capacity_quote=50_000,
    )
    distribution = build_funding_closeout_receiver_recovery_distribution_certificate(
        ledger,
        priority,
    )
    payload = funding_closeout_receiver_recovery_distribution_certificate_to_payload(
        distribution
    )
    payload["priority_certificate_hash"] = "sha256:" + "99" * 32
    assert verify_funding_closeout_receiver_recovery_distribution_payload(
        payload,
        policy_ledger=ledger,
        priority_certificate=priority,
    ) == RecoveryPriorityVerdict(
        False,
        "receiver distribution priority certificate hash mismatch",
    )


def test_sink_distribution_splits_recovery_by_largest_remainder() -> None:
    ledger = _policy_ledger()
    priority = build_funding_closeout_recovery_priority_certificate(
        ledger,
        priority_policy=RECOVERY_PRIORITY_RECEIVER_FIRST,
        source_capacity_quote=100_000,
    )
    distribution = build_funding_closeout_sink_recovery_distribution_certificate(
        ledger,
        priority,
    )
    assert distribution.total_sink_recovery_quote == 20_000
    assert distribution.total_subrogated_claim_quote == 70_000
    assert [
        (
            row.account_pubkey,
            row.claimant,
            row.subrogated_claim_quote,
            row.recovery_quote,
        )
        for row in distribution.sink_rows
    ] == [
        (PAYER_A, "protocol_sink", 40_000, 11_429),
        (PAYER_B, "protocol_sink", 30_000, 8_571),
    ]
    assert verify_funding_closeout_sink_recovery_distribution_payload(
        funding_closeout_sink_recovery_distribution_certificate_to_payload(
            distribution
        ),
        policy_ledger=ledger,
        priority_certificate=priority,
    ) == RecoveryPriorityVerdict(True, None)
    assert funding_closeout_sink_recovery_distribution_certificate_hash(
        distribution
    ).startswith("sha256:")


def test_sink_distribution_allocates_floor_dust_deterministically() -> None:
    rows = compute_sink_largest_remainder_distribution(
        ((PAYER_A, "protocol_sink", 40_000), (PAYER_B, "protocol_sink", 30_000)),
        total_sink_recovery_quote=1,
    )
    assert [
        (row.account_pubkey, row.claimant, row.recovery_quote) for row in rows
    ] == [
        (PAYER_A, "protocol_sink", 1),
        (PAYER_B, "protocol_sink", 0),
    ]


def test_sink_distribution_rejects_row_cap_preserving_skip() -> None:
    ledger = _policy_ledger()
    priority = build_funding_closeout_recovery_priority_certificate(
        ledger,
        priority_policy=RECOVERY_PRIORITY_RECEIVER_FIRST,
        source_capacity_quote=100_000,
    )
    distribution = build_funding_closeout_sink_recovery_distribution_certificate(
        ledger,
        priority,
    )
    payload = funding_closeout_sink_recovery_distribution_certificate_to_payload(
        distribution
    )
    rows = list(payload["sink_rows"])
    rows[0] = {**rows[0], "recovery_quote": 0}
    rows[1] = {**rows[1], "recovery_quote": 20_000}
    payload["sink_rows"] = rows
    assert verify_funding_closeout_sink_recovery_distribution_payload(
        payload,
        policy_ledger=ledger,
        priority_certificate=priority,
    ) == RecoveryPriorityVerdict(
        False,
        "sink largest-remainder distribution mismatch",
    )


def test_sink_distribution_rejects_wrong_claimant() -> None:
    ledger = _policy_ledger()
    priority = build_funding_closeout_recovery_priority_certificate(
        ledger,
        priority_policy=RECOVERY_PRIORITY_RECEIVER_FIRST,
        source_capacity_quote=100_000,
    )
    distribution = build_funding_closeout_sink_recovery_distribution_certificate(
        ledger,
        priority,
    )
    payload = funding_closeout_sink_recovery_distribution_certificate_to_payload(
        distribution
    )
    rows = list(payload["sink_rows"])
    rows[0] = {**rows[0], "claimant": "attacker_sink"}
    payload["sink_rows"] = sorted(
        rows,
        key=lambda row: (str(row["account_pubkey"]), str(row["claimant"])),
    )
    assert verify_funding_closeout_sink_recovery_distribution_payload(
        payload,
        policy_ledger=ledger,
        priority_certificate=priority,
    ) == RecoveryPriorityVerdict(
        False,
        "sink distribution rows mismatch",
    )


def test_sink_distribution_rejects_priority_hash_mismatch() -> None:
    ledger = _policy_ledger()
    priority = build_funding_closeout_recovery_priority_certificate(
        ledger,
        priority_policy=RECOVERY_PRIORITY_RECEIVER_FIRST,
        source_capacity_quote=100_000,
    )
    distribution = build_funding_closeout_sink_recovery_distribution_certificate(
        ledger,
        priority,
    )
    payload = funding_closeout_sink_recovery_distribution_certificate_to_payload(
        distribution
    )
    payload["priority_certificate_hash"] = "sha256:" + "66" * 32
    assert verify_funding_closeout_sink_recovery_distribution_payload(
        payload,
        policy_ledger=ledger,
        priority_certificate=priority,
    ) == RecoveryPriorityVerdict(
        False,
        "sink distribution priority certificate hash mismatch",
    )


def test_recovery_collection_receipt_binds_collected_source_amount() -> None:
    ledger = _policy_ledger()
    priority = build_funding_closeout_recovery_priority_certificate(
        ledger,
        priority_policy=RECOVERY_PRIORITY_RECEIVER_FIRST,
        source_capacity_quote=100_000,
    )
    receipt = build_funding_closeout_recovery_collection_receipt(
        ledger,
        priority,
        source_id="source:closed-payer-recovery",
        collection_nonce=7,
    )
    assert receipt.source_capacity_quote == 100_000
    assert receipt.collected_source_quote == 100_000
    assert verify_funding_closeout_recovery_collection_receipt_payload(
        funding_closeout_recovery_collection_receipt_to_payload(receipt),
        policy_ledger=ledger,
        priority_certificate=priority,
    ) == RecoveryPriorityVerdict(True, None)
    assert funding_closeout_recovery_collection_receipt_hash(receipt).startswith(
        "sha256:"
    )


def test_recovery_collection_receipt_rejects_wrong_collected_amount() -> None:
    ledger = _policy_ledger()
    priority = build_funding_closeout_recovery_priority_certificate(
        ledger,
        priority_policy=RECOVERY_PRIORITY_RECEIVER_FIRST,
        source_capacity_quote=100_000,
    )
    receipt = build_funding_closeout_recovery_collection_receipt(
        ledger,
        priority,
        source_id="source:closed-payer-recovery",
        collection_nonce=7,
    )
    payload = funding_closeout_recovery_collection_receipt_to_payload(receipt)
    payload["collected_source_quote"] = 99_999
    assert verify_funding_closeout_recovery_collection_receipt_payload(
        payload,
        policy_ledger=ledger,
        priority_certificate=priority,
    ) == RecoveryPriorityVerdict(
        False,
        "recovery collection credited amount mismatch",
    )


def test_recovery_collection_receipt_rejects_wrong_source_capacity() -> None:
    ledger = _policy_ledger()
    priority = build_funding_closeout_recovery_priority_certificate(
        ledger,
        priority_policy=RECOVERY_PRIORITY_RECEIVER_FIRST,
        source_capacity_quote=100_000,
    )
    receipt = build_funding_closeout_recovery_collection_receipt(
        ledger,
        priority,
        source_id="source:closed-payer-recovery",
        collection_nonce=7,
    )
    payload = funding_closeout_recovery_collection_receipt_to_payload(receipt)
    payload["source_capacity_quote"] = 100_001
    assert verify_funding_closeout_recovery_collection_receipt_payload(
        payload,
        policy_ledger=ledger,
        priority_certificate=priority,
    ) == RecoveryPriorityVerdict(
        False,
        "recovery collection source capacity mismatch",
    )


def test_recovery_collection_receipt_rejects_priority_hash_mismatch() -> None:
    ledger = _policy_ledger()
    priority = build_funding_closeout_recovery_priority_certificate(
        ledger,
        priority_policy=RECOVERY_PRIORITY_RECEIVER_FIRST,
        source_capacity_quote=100_000,
    )
    receipt = build_funding_closeout_recovery_collection_receipt(
        ledger,
        priority,
        source_id="source:closed-payer-recovery",
        collection_nonce=7,
    )
    payload = funding_closeout_recovery_collection_receipt_to_payload(receipt)
    payload["priority_certificate_hash"] = "sha256:" + "77" * 32
    assert verify_funding_closeout_recovery_collection_receipt_payload(
        payload,
        policy_ledger=ledger,
        priority_certificate=priority,
    ) == RecoveryPriorityVerdict(
        False,
        "recovery collection priority certificate hash mismatch",
    )


def test_recovery_source_authority_accepts_authorized_collection_source() -> None:
    authority = build_funding_closeout_recovery_source_authority(
        market_id=MARKET_ID,
        valid_from_epoch=EPOCH,
        valid_until_epoch=EPOCH,
        authorized_source_ids=("source:closed-payer-recovery",),
    )
    verdict = verify_funding_closeout_recovery_source_authority_payload(
        funding_closeout_recovery_source_authority_to_payload(authority),
        expected_market_id=MARKET_ID,
        now_epoch=EPOCH,
        required_source_ids=("source:closed-payer-recovery",),
    )
    assert verdict.ok is True
    assert verdict.error is None
    assert verdict.authority == authority


def test_recovery_source_authority_rejects_unauthorized_collection_source() -> None:
    authority = build_funding_closeout_recovery_source_authority(
        market_id=MARKET_ID,
        valid_from_epoch=EPOCH,
        valid_until_epoch=EPOCH,
        authorized_source_ids=("source:other-recovery",),
    )
    verdict = verify_funding_closeout_recovery_source_authority_payload(
        funding_closeout_recovery_source_authority_to_payload(authority),
        expected_market_id=MARKET_ID,
        now_epoch=EPOCH,
        required_source_ids=("source:closed-payer-recovery",),
    )
    assert verdict.ok is False
    assert verdict.error == (
        "recovery source_id not authorized: source:closed-payer-recovery"
    )


def test_recovery_source_authority_rejects_cross_market_replay() -> None:
    authority = build_funding_closeout_recovery_source_authority(
        market_id="perp:other-market",
        valid_from_epoch=EPOCH,
        valid_until_epoch=EPOCH,
        authorized_source_ids=("source:closed-payer-recovery",),
    )
    verdict = verify_funding_closeout_recovery_source_authority_payload(
        funding_closeout_recovery_source_authority_to_payload(authority),
        expected_market_id=MARKET_ID,
        now_epoch=EPOCH,
        required_source_ids=("source:closed-payer-recovery",),
    )
    assert verdict.ok is False
    assert verdict.error == "recovery source authority market_id mismatch"


def test_recovery_source_authority_rejects_stale_epoch() -> None:
    authority = build_funding_closeout_recovery_source_authority(
        market_id=MARKET_ID,
        valid_from_epoch=EPOCH - 2,
        valid_until_epoch=EPOCH - 1,
        authorized_source_ids=("source:closed-payer-recovery",),
    )
    verdict = verify_funding_closeout_recovery_source_authority_payload(
        funding_closeout_recovery_source_authority_to_payload(authority),
        expected_market_id=MARKET_ID,
        now_epoch=EPOCH,
        required_source_ids=("source:closed-payer-recovery",),
    )
    assert verdict.ok is False
    assert verdict.error == "recovery source authority epoch out of range"


def test_recovery_source_authority_rejects_canonical_tamper() -> None:
    authority = build_funding_closeout_recovery_source_authority(
        market_id=MARKET_ID,
        valid_from_epoch=EPOCH,
        valid_until_epoch=EPOCH,
        authorized_source_ids=("source:closed-payer-recovery",),
    )
    payload = funding_closeout_recovery_source_authority_to_payload(authority)
    payload["authorized_source_ids"] = [
        "source:closed-payer-recovery",
        "source:other-recovery",
    ]
    verdict = verify_funding_closeout_recovery_source_authority_payload(
        payload,
        expected_market_id=MARKET_ID,
        now_epoch=EPOCH,
        required_source_ids=("source:closed-payer-recovery",),
    )
    assert verdict.ok is False
    assert verdict.error == "canonical_sha256 mismatch"


def test_recovery_source_authority_binding_accepts_signed_root_and_policy() -> None:
    authority = _source_authority()
    payload = _source_authority_binding_payload(authority=authority)
    verdict = verify_funding_closeout_recovery_source_authority_binding_payload(
        payload,
        authority=authority,
        expected_market_id=MARKET_ID,
        now_epoch=EPOCH,
        expected_authority_state_root_hash=AUTHORITY_STATE_ROOT_HASH,
        expected_policy_hash=AUTHORITY_POLICY_HASH,
        allowed_signer_pubkeys=(str(payload["signer_pubkey"]),),
    )
    assert verdict.ok is True
    assert verdict.error is None
    assert verdict.binding is not None


def test_recovery_source_authority_binding_rejects_wrong_root() -> None:
    authority = _source_authority()
    payload = _source_authority_binding_payload(authority=authority)
    verdict = verify_funding_closeout_recovery_source_authority_binding_payload(
        payload,
        authority=authority,
        expected_market_id=MARKET_ID,
        now_epoch=EPOCH,
        expected_authority_state_root_hash="sha256:" + "45" * 32,
        expected_policy_hash=AUTHORITY_POLICY_HASH,
        allowed_signer_pubkeys=(str(payload["signer_pubkey"]),),
    )
    assert verdict.ok is False
    assert (
        verdict.error
        == "recovery source authority binding state_root_hash mismatch"
    )


def test_recovery_source_authority_binding_rejects_wrong_policy_hash() -> None:
    authority = _source_authority()
    payload = _source_authority_binding_payload(authority=authority)
    verdict = verify_funding_closeout_recovery_source_authority_binding_payload(
        payload,
        authority=authority,
        expected_market_id=MARKET_ID,
        now_epoch=EPOCH,
        expected_authority_state_root_hash=AUTHORITY_STATE_ROOT_HASH,
        expected_policy_hash="sha256:" + "56" * 32,
        allowed_signer_pubkeys=(str(payload["signer_pubkey"]),),
    )
    assert verdict.ok is False
    assert verdict.error == "recovery source authority binding policy_hash mismatch"


def test_recovery_source_authority_binding_rejects_unregistered_signer() -> None:
    authority = _source_authority()
    payload = _source_authority_binding_payload(authority=authority)
    other_payload = _source_authority_binding_payload(
        authority=authority,
        signer_privkey=2,
    )
    verdict = verify_funding_closeout_recovery_source_authority_binding_payload(
        payload,
        authority=authority,
        expected_market_id=MARKET_ID,
        now_epoch=EPOCH,
        expected_authority_state_root_hash=AUTHORITY_STATE_ROOT_HASH,
        expected_policy_hash=AUTHORITY_POLICY_HASH,
        allowed_signer_pubkeys=(str(other_payload["signer_pubkey"]),),
    )
    assert verdict.ok is False
    assert verdict.error == "recovery source authority binding signer not allowed"


def test_recovery_source_authority_binding_rejects_signature_tamper() -> None:
    authority = _source_authority()
    payload = _source_authority_binding_payload(authority=authority)
    payload["signature"] = "0x" + "00" * 96
    verdict = verify_funding_closeout_recovery_source_authority_binding_payload(
        payload,
        authority=authority,
        expected_market_id=MARKET_ID,
        now_epoch=EPOCH,
        expected_authority_state_root_hash=AUTHORITY_STATE_ROOT_HASH,
        expected_policy_hash=AUTHORITY_POLICY_HASH,
        allowed_signer_pubkeys=(str(payload["signer_pubkey"]),),
    )
    assert verdict.ok is False
    assert verdict.error == "recovery source authority binding signature invalid"


def test_recovery_source_authority_binding_rejects_authority_hash_mismatch() -> None:
    authority = _source_authority()
    other_authority = build_funding_closeout_recovery_source_authority(
        market_id=MARKET_ID,
        valid_from_epoch=EPOCH,
        valid_until_epoch=EPOCH,
        authorized_source_ids=("source:other-recovery",),
    )
    payload = _source_authority_binding_payload(authority=other_authority)
    verdict = verify_funding_closeout_recovery_source_authority_binding_payload(
        payload,
        authority=authority,
        expected_market_id=MARKET_ID,
        now_epoch=EPOCH,
        expected_authority_state_root_hash=AUTHORITY_STATE_ROOT_HASH,
        expected_policy_hash=AUTHORITY_POLICY_HASH,
        allowed_signer_pubkeys=(str(payload["signer_pubkey"]),),
    )
    assert verdict.ok is False
    assert (
        verdict.error
        == "recovery source authority binding authority_hash mismatch"
    )


def test_recovery_source_authority_binding_rejects_stale_epoch() -> None:
    authority = _source_authority()
    payload = funding_closeout_recovery_source_authority_binding_to_payload(
        build_funding_closeout_recovery_source_authority_binding(
            market_id=MARKET_ID,
            valid_from_epoch=EPOCH - 2,
            valid_until_epoch=EPOCH - 1,
            authority_hash=funding_closeout_recovery_source_authority_hash(
                authority
            ),
            authority_state_root_hash=AUTHORITY_STATE_ROOT_HASH,
            policy_hash=AUTHORITY_POLICY_HASH,
            signer_privkey=1,
        )
    )
    verdict = verify_funding_closeout_recovery_source_authority_binding_payload(
        payload,
        authority=authority,
        expected_market_id=MARKET_ID,
        now_epoch=EPOCH,
        expected_authority_state_root_hash=AUTHORITY_STATE_ROOT_HASH,
        expected_policy_hash=AUTHORITY_POLICY_HASH,
        allowed_signer_pubkeys=(str(payload["signer_pubkey"]),),
    )
    assert verdict.ok is False
    assert verdict.error == "recovery source authority binding epoch out of range"


def test_exact_count() -> None:
    tests = [
        name
        for name, value in globals().items()
        if name.startswith("test_") and callable(value) and name != "test_exact_count"
    ]
    assert len(tests) == 30
