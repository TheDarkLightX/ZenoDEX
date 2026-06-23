"""Bounded lattices for UPBA admission certificates.

These tests pin the local admission policy directly: eligible intents are sorted
by canonical intent_id, the admitted set is the prefix up to max_admitted, and
the certificate binds eligible/admitted/overflow counts and hashes.
"""

from __future__ import annotations

import itertools

import pytest

from src.core.uniform_batch_admission import (
    build_uniform_batch_admission_certificate_v1,
    select_uniform_batch_admitted_intents_v1,
    verify_uniform_batch_admission_certificate_v1,
)
from src.state.intents import Intent, IntentKind


SENDER = "0x" + "ab" * 48
POOL_ID = "pool_ab"


def _intent(
    rank: int,
    *,
    kind: IntentKind = IntentKind.SWAP_EXACT_IN,
    pool_id: str = POOL_ID,
    asset_in: str = "A",
    asset_out: str = "B",
    amount: int = 100,
) -> Intent:
    fields: dict[str, object] = {
        "nonce": rank,
        "pool_id": pool_id,
        "asset_in": asset_in,
        "asset_out": asset_out,
    }
    if kind == IntentKind.SWAP_EXACT_IN:
        fields.update({"amount_in": amount, "min_amount_out": 0})
    else:
        fields.update({"amount_out": amount, "max_amount_in": amount + 10})
    return Intent(
        module="TauSwap",
        version="0.1",
        kind=kind,
        intent_id="0x" + f"{rank:064x}",
        sender_pubkey=SENDER,
        deadline=999_999_999,
        salt=f"salt-{rank}",
        fields=fields,
    )


def _ids(intents) -> list[str]:
    return [intent.intent_id for intent in intents]


def test_exhaustive_uniform_batch_admission_prefix_lattice():
    """Complete over all subsets/permutations of four intents x max_admitted.

    This proves input-order independence over the declared bound while checking
    the exact canonical-prefix admitted set, overflow set, and certificate hash.
    """
    base = tuple(_intent(rank) for rank in (3, 1, 4, 2))
    certificate_hash_by_key: dict[tuple[frozenset[str], int], str] = {}
    checked = 0

    for size in range(len(base) + 1):
        for subset in itertools.combinations(base, size):
            for permuted in itertools.permutations(subset):
                for max_admitted in (1, 2, 3, 4):
                    selection = select_uniform_batch_admitted_intents_v1(
                        eligible_intents=permuted,
                        pool_id=POOL_ID,
                        max_admitted=max_admitted,
                    )
                    sorted_ids = sorted(_ids(permuted))
                    assert _ids(selection.admitted) == sorted_ids[:max_admitted]
                    assert _ids(selection.overflow) == sorted_ids[max_admitted:]

                    certificate = build_uniform_batch_admission_certificate_v1(
                        eligible_intents=permuted,
                        pool_id=POOL_ID,
                        max_admitted=max_admitted,
                    )
                    result = verify_uniform_batch_admission_certificate_v1(
                        eligible_intents=permuted,
                        admitted_intents=tuple(reversed(selection.admitted)),
                        certificate=certificate,
                    )
                    assert result.ok, result.error
                    assert _ids(result.admitted) == sorted_ids[:max_admitted]
                    assert _ids(result.overflow) == sorted_ids[max_admitted:]
                    assert result.certificate_hash == certificate.hash()

                    key = (frozenset(sorted_ids), max_admitted)
                    prior_hash = certificate_hash_by_key.setdefault(key, certificate.hash())
                    assert prior_hash == certificate.hash()
                    checked += 1

    assert checked == 260


def test_uniform_batch_admission_boundary_mutations_fail_closed():
    valid = tuple(_intent(rank) for rank in (1, 2, 3))
    certificate = build_uniform_batch_admission_certificate_v1(
        eligible_intents=valid,
        pool_id=POOL_ID,
        max_admitted=2,
    )
    selection = select_uniform_batch_admitted_intents_v1(
        eligible_intents=valid,
        pool_id=POOL_ID,
        max_admitted=2,
    )

    with pytest.raises(ValueError, match="duplicate admission intent_id"):
        build_uniform_batch_admission_certificate_v1(
            eligible_intents=(_intent(1), _intent(1)),
            pool_id=POOL_ID,
            max_admitted=2,
        )

    mixed_pool = verify_uniform_batch_admission_certificate_v1(
        eligible_intents=(_intent(1, pool_id="other_pool"),),
        admitted_intents=(),
        certificate=certificate,
    )
    assert not mixed_pool.ok
    assert "pool_id mismatch" in str(mixed_pool.error)

    with pytest.raises(ValueError, match="homogeneous swap kind"):
        select_uniform_batch_admitted_intents_v1(
            eligible_intents=(
                _intent(1, kind=IntentKind.SWAP_EXACT_IN),
                _intent(2, kind=IntentKind.SWAP_EXACT_OUT),
            ),
            pool_id=POOL_ID,
            max_admitted=2,
        )

    with pytest.raises(ValueError, match="assets must differ"):
        select_uniform_batch_admitted_intents_v1(
            eligible_intents=(_intent(1, asset_in="A", asset_out="A"),),
            pool_id=POOL_ID,
            max_admitted=1,
        )

    with pytest.raises(ValueError, match="amount_in must be positive"):
        select_uniform_batch_admitted_intents_v1(
            eligible_intents=(_intent(1, amount=0),),
            pool_id=POOL_ID,
            max_admitted=1,
        )

    wrong_member = verify_uniform_batch_admission_certificate_v1(
        eligible_intents=valid,
        admitted_intents=(selection.admitted[0], selection.overflow[0]),
        certificate=certificate,
    )
    assert not wrong_member.ok
    assert "admitted intent set mismatch" in str(wrong_member.error)

    bad_counts = certificate.to_dict()
    bad_counts["eligible_count"] += 1
    count_mismatch = verify_uniform_batch_admission_certificate_v1(
        eligible_intents=valid,
        admitted_intents=selection.admitted,
        certificate=bad_counts,
    )
    assert not count_mismatch.ok
    assert "counts do not add up" in str(count_mismatch.error)
