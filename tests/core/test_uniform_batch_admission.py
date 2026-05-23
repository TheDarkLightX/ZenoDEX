from __future__ import annotations

import pytest

from src.core.uniform_batch_admission import (
    UNIFORM_BATCH_ADMISSION_CERTIFICATE_SCHEMA_V1,
    UNIFORM_BATCH_ADMISSION_POLICY_V1_ID,
    build_uniform_batch_admission_certificate_v1,
    select_uniform_batch_admitted_intents_v1,
    uniform_batch_admission_certificate_hash,
    uniform_batch_admission_intent_set_hash_v1,
    verify_uniform_batch_admission_certificate_v1,
)
from src.core.uniform_batch_clearing import uniform_batch_intent_set_hash
from src.state.intents import Intent, IntentKind


def _intent(
    index: int,
    *,
    pool_id: str = "pool-ab",
    kind: IntentKind = IntentKind.SWAP_EXACT_IN,
    amount_in: int = 100,
    min_amount_out: int = 90,
    asset_in: str = "A",
    asset_out: str = "B",
) -> Intent:
    return Intent(
        module="TauSwap",
        version="0.1",
        kind=kind,
        intent_id=f"0x{index:064x}",
        sender_pubkey=f"trader-{index}",
        deadline=100,
        salt=f"salt-{index}",
        fields={
            "pool_id": pool_id,
            "asset_in": asset_in,
            "asset_out": asset_out,
            "amount_in": amount_in,
            "min_amount_out": min_amount_out,
            "recipient": f"recipient-{index}",
        },
    )


def _exact_out_intent(
    index: int,
    *,
    pool_id: str = "pool-ab",
    amount_out: int = 100,
    max_amount_in: int = 110,
    asset_in: str = "A",
    asset_out: str = "B",
) -> Intent:
    return Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_OUT,
        intent_id=f"0x{index:064x}",
        sender_pubkey=f"trader-{index}",
        deadline=100,
        salt=f"salt-{index}",
        fields={
            "pool_id": pool_id,
            "asset_in": asset_in,
            "asset_out": asset_out,
            "amount_out": amount_out,
            "max_amount_in": max_amount_in,
            "recipient": f"recipient-{index}",
        },
    )


def test_uniform_batch_admission_selects_canonical_intent_id_prefix() -> None:
    eligible = (_intent(3), _intent(1), _intent(2))

    selection = select_uniform_batch_admitted_intents_v1(
        eligible_intents=eligible,
        pool_id="pool-ab",
        max_admitted=2,
    )

    assert [intent.intent_id for intent in selection.admitted] == [
        f"0x{1:064x}",
        f"0x{2:064x}",
    ]
    assert [intent.intent_id for intent in selection.overflow] == [f"0x{3:064x}"]


def test_uniform_batch_admission_certificate_accepts_matching_selection() -> None:
    eligible = (_intent(3), _intent(1), _intent(2))
    selection = select_uniform_batch_admitted_intents_v1(
        eligible_intents=eligible,
        pool_id="pool-ab",
        max_admitted=2,
    )

    certificate = build_uniform_batch_admission_certificate_v1(
        eligible_intents=eligible,
        pool_id="pool-ab",
        max_admitted=2,
    )
    result = verify_uniform_batch_admission_certificate_v1(
        eligible_intents=eligible,
        admitted_intents=tuple(reversed(selection.admitted)),
        certificate=certificate,
    )

    assert result.ok is True
    assert result.error is None
    assert result.admitted == selection.admitted
    assert result.overflow == selection.overflow
    assert result.certificate_hash == certificate.hash()
    assert result.certificate_hash == uniform_batch_admission_certificate_hash(certificate)
    assert certificate.schema == UNIFORM_BATCH_ADMISSION_CERTIFICATE_SCHEMA_V1
    assert certificate.policy_id == UNIFORM_BATCH_ADMISSION_POLICY_V1_ID
    assert certificate.eligible_intent_set_hash == uniform_batch_admission_intent_set_hash_v1(eligible)
    assert certificate.admitted_intent_set_hash == uniform_batch_intent_set_hash(selection.admitted)


def test_uniform_batch_admission_is_input_order_invariant() -> None:
    eligible_a = (_intent(5), _intent(4), _intent(6))
    eligible_b = tuple(reversed(eligible_a))

    certificate_a = build_uniform_batch_admission_certificate_v1(
        eligible_intents=eligible_a,
        pool_id="pool-ab",
        max_admitted=2,
    )
    certificate_b = build_uniform_batch_admission_certificate_v1(
        eligible_intents=eligible_b,
        pool_id="pool-ab",
        max_admitted=2,
    )

    assert certificate_a == certificate_b
    assert certificate_a.hash() == certificate_b.hash()


def test_uniform_batch_admission_accepts_exact_out_selection() -> None:
    eligible = (_exact_out_intent(3), _exact_out_intent(1), _exact_out_intent(2))
    selection = select_uniform_batch_admitted_intents_v1(
        eligible_intents=eligible,
        pool_id="pool-ab",
        max_admitted=2,
    )

    certificate = build_uniform_batch_admission_certificate_v1(
        eligible_intents=eligible,
        pool_id="pool-ab",
        max_admitted=2,
    )
    result = verify_uniform_batch_admission_certificate_v1(
        eligible_intents=eligible,
        admitted_intents=selection.admitted,
        certificate=certificate,
    )

    assert result.ok is True
    assert [intent.intent_id for intent in result.admitted] == [
        f"0x{1:064x}",
        f"0x{2:064x}",
    ]
    assert certificate.admitted_intent_set_hash == uniform_batch_intent_set_hash(selection.admitted)


def test_uniform_batch_admission_rejects_omitted_lower_intent_id() -> None:
    eligible = (_intent(1), _intent(2), _intent(3))
    certificate = build_uniform_batch_admission_certificate_v1(
        eligible_intents=eligible,
        pool_id="pool-ab",
        max_admitted=2,
    )

    result = verify_uniform_batch_admission_certificate_v1(
        eligible_intents=eligible,
        admitted_intents=(_intent(2), _intent(3)),
        certificate=certificate,
    )

    assert result.ok is False
    assert result.error == "admission certificate admitted intent set mismatch"


def test_uniform_batch_admission_rejects_mutated_admitted_intent_object() -> None:
    eligible = (_intent(1), _intent(2), _intent(3))
    selection = select_uniform_batch_admitted_intents_v1(
        eligible_intents=eligible,
        pool_id="pool-ab",
        max_admitted=2,
    )
    mutated_first = _intent(1, amount_in=101)
    certificate = build_uniform_batch_admission_certificate_v1(
        eligible_intents=eligible,
        pool_id="pool-ab",
        max_admitted=2,
    )

    result = verify_uniform_batch_admission_certificate_v1(
        eligible_intents=eligible,
        admitted_intents=(mutated_first, selection.admitted[1]),
        certificate=certificate,
    )

    assert result.ok is False
    assert result.error == "admission certificate provided admitted_intent_set_hash mismatch"


def test_uniform_batch_admission_rejects_tampered_count() -> None:
    eligible = (_intent(1), _intent(2), _intent(3))
    selection = select_uniform_batch_admitted_intents_v1(
        eligible_intents=eligible,
        pool_id="pool-ab",
        max_admitted=2,
    )
    certificate = build_uniform_batch_admission_certificate_v1(
        eligible_intents=eligible,
        pool_id="pool-ab",
        max_admitted=2,
    ).to_dict()
    certificate["eligible_count"] = 4

    result = verify_uniform_batch_admission_certificate_v1(
        eligible_intents=eligible,
        admitted_intents=selection.admitted,
        certificate=certificate,
    )

    assert result.ok is False
    assert result.error == "admission certificate counts do not add up"


def test_uniform_batch_admission_rejects_duplicate_eligible_ids() -> None:
    eligible = (_intent(1), _intent(1))

    with pytest.raises(ValueError, match="duplicate admission intent_id"):
        select_uniform_batch_admitted_intents_v1(
            eligible_intents=eligible,
            pool_id="pool-ab",
            max_admitted=2,
        )


def test_uniform_batch_admission_rejects_unsupported_kind() -> None:
    eligible = (_intent(1, kind=IntentKind.ADD_LIQUIDITY),)

    with pytest.raises(ValueError, match="SWAP_EXACT_IN or SWAP_EXACT_OUT only"):
        select_uniform_batch_admitted_intents_v1(
            eligible_intents=eligible,
            pool_id="pool-ab",
            max_admitted=1,
        )


def test_uniform_batch_admission_rejects_mixed_swap_kind() -> None:
    eligible = (_intent(1), _exact_out_intent(2))

    with pytest.raises(ValueError, match="homogeneous swap kind"):
        select_uniform_batch_admitted_intents_v1(
            eligible_intents=eligible,
            pool_id="pool-ab",
            max_admitted=2,
        )


def test_uniform_batch_admission_rejects_mixed_asset_pair() -> None:
    eligible = (_intent(1), _intent(2, asset_in="A", asset_out="C"))

    with pytest.raises(ValueError, match="one asset pair"):
        select_uniform_batch_admitted_intents_v1(
            eligible_intents=eligible,
            pool_id="pool-ab",
            max_admitted=2,
        )


def test_uniform_batch_admission_rejects_mixed_pool() -> None:
    eligible = (_intent(1), _intent(2, pool_id="other-pool"))

    with pytest.raises(ValueError, match="pool_id mismatch"):
        select_uniform_batch_admitted_intents_v1(
            eligible_intents=eligible,
            pool_id="pool-ab",
            max_admitted=2,
        )


def test_uniform_batch_admission_rejects_zero_max_admitted() -> None:
    eligible = (_intent(1),)

    with pytest.raises(ValueError, match="max_admitted must be positive"):
        select_uniform_batch_admitted_intents_v1(
            eligible_intents=eligible,
            pool_id="pool-ab",
            max_admitted=0,
        )
