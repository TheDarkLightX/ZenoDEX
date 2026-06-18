from __future__ import annotations

import pytest

from src.core.aequitas_vrf_tiebreak import (
    AequitasSccBatch,
    ExternallyVerifiedVrfReceipt,
    order_aequitas_batches_with_vrf_tiebreak,
    order_aequitas_scc_batches,
    order_members_by_verified_vrf,
)


def _hex(byte: int) -> str:
    return f"{byte:02x}" * 32


def _receipt(subject_id: str, output_byte: int, *, seed_id: str = "seed:epoch:7") -> ExternallyVerifiedVrfReceipt:
    return ExternallyVerifiedVrfReceipt(
        subject_id=subject_id,
        seed_id=seed_id,
        output_hash=_hex(output_byte),
        proof_hash=_hex(200 + output_byte),
    )


def test_order_members_by_verified_vrf_is_deterministic_under_input_reordering() -> None:
    receipts = {
        "alice": _receipt("alice", 30),
        "bob": _receipt("bob", 10),
        "carol": _receipt("carol", 20),
    }

    forward = order_members_by_verified_vrf(
        ("alice", "bob", "carol"),
        receipts_by_subject_id=receipts,
        expected_seed_id="seed:epoch:7",
    )
    reversed_input = order_members_by_verified_vrf(
        ("carol", "bob", "alice"),
        receipts_by_subject_id=receipts,
        expected_seed_id="seed:epoch:7",
    )

    assert forward == ("bob", "carol", "alice")
    assert reversed_input == forward


def test_order_members_by_verified_vrf_uses_subject_id_for_hash_collision_ties() -> None:
    receipts = {
        "bob": _receipt("bob", 10),
        "alice": _receipt("alice", 10),
    }

    got = order_members_by_verified_vrf(
        ("bob", "alice"),
        receipts_by_subject_id=receipts,
        expected_seed_id="seed:epoch:7",
    )

    assert got == ("alice", "bob")


def test_order_members_by_verified_vrf_rejects_seed_mismatch() -> None:
    receipts = {"alice": _receipt("alice", 10, seed_id="seed:other")}

    with pytest.raises(ValueError, match="receipt seed_id mismatch"):
        order_members_by_verified_vrf(
            ("alice",),
            receipts_by_subject_id=receipts,
            expected_seed_id="seed:epoch:7",
        )


def test_order_members_by_verified_vrf_rejects_missing_and_extra_receipts() -> None:
    receipts = {
        "alice": _receipt("alice", 10),
        "carol": _receipt("carol", 20),
    }

    with pytest.raises(ValueError, match="receipts must match member_ids exactly"):
        order_members_by_verified_vrf(
            ("alice", "bob"),
            receipts_by_subject_id=receipts,
            expected_seed_id="seed:epoch:7",
        )


def test_order_members_by_verified_vrf_rejects_subject_mismatch() -> None:
    receipts = {"alice": _receipt("bob", 10)}

    with pytest.raises(ValueError, match="receipt subject_id mismatch"):
        order_members_by_verified_vrf(
            ("alice",),
            receipts_by_subject_id=receipts,
            expected_seed_id="seed:epoch:7",
        )


def test_order_members_by_verified_vrf_rejects_malformed_hashes() -> None:
    receipts = {
        "alice": ExternallyVerifiedVrfReceipt(
            subject_id="alice",
            seed_id="seed:epoch:7",
            output_hash="A" * 64,
            proof_hash=_hex(10),
        )
    }

    with pytest.raises(ValueError, match="receipt.output_hash"):
        order_members_by_verified_vrf(
            ("alice",),
            receipts_by_subject_id=receipts,
            expected_seed_id="seed:epoch:7",
        )


def test_commitment_like_strings_do_not_enter_vrf_ordering_key() -> None:
    receipts = {
        "alice": _receipt("alice", 30),
        "bob": _receipt("bob", 10),
    }
    high_commitment = {"alice": "zzzz", "bob": "0000"}
    low_commitment = {"alice": "0000", "bob": "zzzz"}

    assert tuple(high_commitment) == tuple(low_commitment)
    assert order_members_by_verified_vrf(
        tuple(high_commitment),
        receipts_by_subject_id=receipts,
        expected_seed_id="seed:epoch:7",
    ) == order_members_by_verified_vrf(
        tuple(low_commitment),
        receipts_by_subject_id=receipts,
        expected_seed_id="seed:epoch:7",
    )


def test_order_aequitas_scc_batches_respects_condensation_dependencies() -> None:
    batches = (
        AequitasSccBatch("settle", ("carol",), ("commit", "reveal")),
        AequitasSccBatch("commit", ("alice",)),
        AequitasSccBatch("reveal", ("bob",), ("commit",)),
    )

    got = order_aequitas_scc_batches(reversed(batches))

    assert tuple(batch.batch_id for batch in got) == ("commit", "reveal", "settle")


def test_order_aequitas_scc_batches_rejects_cycles() -> None:
    batches = (
        AequitasSccBatch("a", ("alice",), ("b",)),
        AequitasSccBatch("b", ("bob",), ("a",)),
    )

    with pytest.raises(ValueError, match="acyclic"):
        order_aequitas_scc_batches(batches)


def test_order_aequitas_scc_batches_rejects_member_reuse_across_sccs() -> None:
    batches = (
        AequitasSccBatch("a", ("alice",)),
        AequitasSccBatch("b", ("alice",)),
    )

    with pytest.raises(ValueError, match="globally unique"):
        order_aequitas_scc_batches(batches)


def test_order_aequitas_batches_with_vrf_tiebreak_flattens_batches() -> None:
    batches = (
        AequitasSccBatch("later", ("carol",), ("now",)),
        AequitasSccBatch("now", ("alice", "bob")),
    )
    receipts = {
        "alice": _receipt("alice", 30),
        "bob": _receipt("bob", 10),
        "carol": _receipt("carol", 20),
    }

    got = order_aequitas_batches_with_vrf_tiebreak(
        batches,
        receipts_by_subject_id=receipts,
        expected_seed_id="seed:epoch:7",
    )

    assert got.batch_order == ("now", "later")
    assert got.member_order_by_batch == (
        ("now", ("bob", "alice")),
        ("later", ("carol",)),
    )
    assert got.flattened_member_order == ("bob", "alice", "carol")


def test_ordering_rejects_bool_member_id() -> None:
    with pytest.raises(ValueError, match="member_ids"):
        order_members_by_verified_vrf(
            (True,),
            receipts_by_subject_id={},
            expected_seed_id="seed:epoch:7",
        )
