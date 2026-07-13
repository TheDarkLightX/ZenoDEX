from __future__ import annotations

import copy
import pickle
from collections.abc import Callable
from dataclasses import replace

import pytest

import src.core.recursive_stark_admission as recursive_stark_admission
from src.core.recursive_stark_admission import (
    MAX_CHILD_VERIFICATION_CLAIMS_PER_ROOT,
    RecursiveStarkAdmissionRejectReason,
    RecursiveStarkAdmissionResult,
    RecursiveStarkAdmissionSlot,
    RecursiveStarkAdmissionState,
    RecursiveStarkRootFacts,
    TrustedRecursiveStarkAdmissionPolicy,
    _admit_authenticated_recursive_stark_root,
    _AuthenticatedRecursiveStarkRootFacts,
    _mint_recursive_stark_root_facts_after_verification,
    _RecursiveStarkVerificationProvenance,
    recursive_child_verification_claims_root_v1,
    recursive_message_ids_root_v1,
    recursive_receipt_ids_root_v1,
)


def _hash(index: int) -> str:
    assert index > 0
    return f"0x{index:064x}"


def _facts(**overrides: object) -> RecursiveStarkRootFacts:
    child_claims = (_hash(4), _hash(5))
    receipt_ids = (_hash(6), _hash(7))
    message_ids = (_hash(8), _hash(9))
    values: dict[str, object] = {
        "chain_id": "zenodex-devnet",
        "epoch_id": 7,
        "proof_profile": "recursive_epoch_v1",
        "root_journal_hash": _hash(1),
        "verifier_set_root": _hash(2),
        "public_policy_hash": _hash(3),
        "child_verification_claim_hashes": child_claims,
        "child_verification_claims_root": recursive_child_verification_claims_root_v1(child_claims),
        "accepted_receipt_ids": receipt_ids,
        "accepted_receipts_root": recursive_receipt_ids_root_v1(receipt_ids),
        "cross_shard_message_ids": message_ids,
        "cross_shard_message_ids_root": recursive_message_ids_root_v1(message_ids),
    }
    values.update(overrides)
    if (
        "child_verification_claim_hashes" in overrides
        and "child_verification_claims_root" not in overrides
    ):
        values["child_verification_claims_root"] = recursive_child_verification_claims_root_v1(
            values["child_verification_claim_hashes"]  # type: ignore[arg-type]
        )
    if "accepted_receipt_ids" in overrides and "accepted_receipts_root" not in overrides:
        values["accepted_receipts_root"] = recursive_receipt_ids_root_v1(
            values["accepted_receipt_ids"]  # type: ignore[arg-type]
        )
    if "cross_shard_message_ids" in overrides and "cross_shard_message_ids_root" not in overrides:
        values["cross_shard_message_ids_root"] = recursive_message_ids_root_v1(
            values["cross_shard_message_ids"]  # type: ignore[arg-type]
        )
    return RecursiveStarkRootFacts(**values)  # type: ignore[arg-type]


def _policy(**overrides: object) -> TrustedRecursiveStarkAdmissionPolicy:
    values: dict[str, object] = {
        "expected_chain_id": "zenodex-devnet",
        "expected_epoch_id": 7,
        "expected_proof_profile": "recursive_epoch_v1",
        "expected_verifier_set_root": _hash(2),
        "expected_public_policy_hash": _hash(3),
    }
    values.update(overrides)
    return TrustedRecursiveStarkAdmissionPolicy(**values)  # type: ignore[arg-type]


def _provenance() -> _RecursiveStarkVerificationProvenance:
    return _RecursiveStarkVerificationProvenance(
        authority_manifest_sha256="11" * 32,
        verifier_executable_sha256="22" * 32,
        verification_request_sha256="33" * 32,
    )


def _authenticated(
    facts: RecursiveStarkRootFacts,
    policy: TrustedRecursiveStarkAdmissionPolicy,
) -> _AuthenticatedRecursiveStarkRootFacts:
    return _mint_recursive_stark_root_facts_after_verification(
        facts,
        policy,
        _provenance(),
    )


def _accept(
    state: RecursiveStarkAdmissionState,
    facts: RecursiveStarkRootFacts,
    policy: TrustedRecursiveStarkAdmissionPolicy,
) -> RecursiveStarkAdmissionState:
    result = _admit(state, facts, policy)
    assert result.accepted is True
    assert result.reject_reason is None
    return result.state


def _assert_rejected_unchanged(
    state: RecursiveStarkAdmissionState,
    facts: RecursiveStarkRootFacts,
    policy: TrustedRecursiveStarkAdmissionPolicy,
    expected_reason: RecursiveStarkAdmissionRejectReason,
) -> None:
    result = _admit(state, facts, policy)

    assert result.accepted is False
    assert result.reject_reason is expected_reason
    assert result.state is state


def _admit(
    state: RecursiveStarkAdmissionState,
    facts: RecursiveStarkRootFacts,
    policy: TrustedRecursiveStarkAdmissionPolicy,
) -> RecursiveStarkAdmissionResult:
    authenticated = _authenticated(facts, policy)
    return _admit_authenticated_recursive_stark_root(state, authenticated)


def test_given_authenticated_root_when_first_admitted_then_all_exact_once_indexes_commit() -> None:
    facts = _facts()
    pre_state = RecursiveStarkAdmissionState()

    post_state = _accept(pre_state, facts, _policy())

    assert post_state is not pre_state
    assert post_state.chain_id == facts.chain_id
    assert post_state.accepted_root_journal_hashes == (facts.root_journal_hash,)
    assert post_state.accepted_slots == (facts.slot,)
    assert (
        post_state.accepted_child_verification_claim_hashes == facts.child_verification_claim_hashes
    )
    assert post_state.accepted_receipt_ids == facts.accepted_receipt_ids
    assert post_state.accepted_cross_shard_message_ids == facts.cross_shard_message_ids


def test_given_accepted_root_when_same_root_replayed_then_root_reject_is_no_op() -> None:
    facts = _facts()
    accepted_state = _accept(RecursiveStarkAdmissionState(), facts, _policy())

    _assert_rejected_unchanged(
        accepted_state,
        facts,
        _policy(),
        RecursiveStarkAdmissionRejectReason.DUPLICATE_ROOT_JOURNAL,
    )


def test_given_occupied_slot_when_different_root_targets_slot_then_slot_reject_is_no_op() -> None:
    accepted_state = _accept(RecursiveStarkAdmissionState(), _facts(), _policy())
    different_root = _facts(
        root_journal_hash=_hash(20),
        child_verification_claim_hashes=(_hash(21),),
        accepted_receipt_ids=(_hash(22),),
        cross_shard_message_ids=(_hash(23),),
    )

    _assert_rejected_unchanged(
        accepted_state,
        different_root,
        _policy(),
        RecursiveStarkAdmissionRejectReason.DUPLICATE_ADMISSION_SLOT,
    )


def test_given_accepted_child_when_new_root_reuses_child_then_child_reject_is_no_op() -> None:
    accepted_state = _accept(RecursiveStarkAdmissionState(), _facts(), _policy())
    second_root = _facts(
        epoch_id=8,
        root_journal_hash=_hash(20),
        child_verification_claim_hashes=(_hash(4), _hash(21)),
        accepted_receipt_ids=(_hash(22),),
        cross_shard_message_ids=(_hash(23),),
    )

    _assert_rejected_unchanged(
        accepted_state,
        second_root,
        _policy(expected_epoch_id=8),
        RecursiveStarkAdmissionRejectReason.DUPLICATE_CHILD_VERIFICATION_CLAIM,
    )


def test_given_accepted_receipt_when_new_root_reuses_receipt_then_reject_is_no_op() -> None:
    accepted_state = _accept(RecursiveStarkAdmissionState(), _facts(), _policy())
    second_root = _facts(
        epoch_id=8,
        root_journal_hash=_hash(20),
        child_verification_claim_hashes=(_hash(21),),
        accepted_receipt_ids=(_hash(6), _hash(22)),
        cross_shard_message_ids=(_hash(23),),
    )

    _assert_rejected_unchanged(
        accepted_state,
        second_root,
        _policy(expected_epoch_id=8),
        RecursiveStarkAdmissionRejectReason.DUPLICATE_ACCEPTED_RECEIPT,
    )


def test_given_accepted_message_when_new_root_reuses_message_then_reject_is_no_op() -> None:
    accepted_state = _accept(RecursiveStarkAdmissionState(), _facts(), _policy())
    second_root = _facts(
        epoch_id=8,
        root_journal_hash=_hash(20),
        child_verification_claim_hashes=(_hash(21),),
        accepted_receipt_ids=(_hash(22),),
        cross_shard_message_ids=(_hash(8), _hash(23)),
    )

    _assert_rejected_unchanged(
        accepted_state,
        second_root,
        _policy(expected_epoch_id=8),
        RecursiveStarkAdmissionRejectReason.DUPLICATE_CROSS_SHARD_MESSAGE,
    )


@pytest.mark.parametrize(
    ("facts", "policy", "reason"),
    (
        (
            _facts(chain_id="zenodex-relabelled"),
            _policy(),
            RecursiveStarkAdmissionRejectReason.CHAIN_ID_MISMATCH,
        ),
        (
            _facts(epoch_id=6),
            _policy(),
            RecursiveStarkAdmissionRejectReason.EPOCH_ID_MISMATCH,
        ),
        (
            _facts(proof_profile="recursive_epoch_v2"),
            _policy(),
            RecursiveStarkAdmissionRejectReason.PROOF_PROFILE_MISMATCH,
        ),
        (
            _facts(),
            _policy(expected_verifier_set_root=_hash(30)),
            RecursiveStarkAdmissionRejectReason.VERIFIER_SET_ROOT_MISMATCH,
        ),
        (
            _facts(),
            _policy(expected_public_policy_hash=_hash(31)),
            RecursiveStarkAdmissionRejectReason.PUBLIC_POLICY_HASH_MISMATCH,
        ),
    ),
    ids=(
        "chain-relabel",
        "wrong-epoch",
        "wrong-profile",
        "stale-verifier-set",
        "stale-public-policy",
    ),
)
def test_given_trusted_policy_when_verified_facts_mismatch_then_reject_is_no_op(
    facts: RecursiveStarkRootFacts,
    policy: TrustedRecursiveStarkAdmissionPolicy,
    reason: RecursiveStarkAdmissionRejectReason,
) -> None:
    state = RecursiveStarkAdmissionState()

    _assert_rejected_unchanged(state, facts, policy, reason)


def test_given_partial_replay_overlap_when_rejected_then_no_new_indexes_are_staged() -> None:
    accepted_state = _accept(RecursiveStarkAdmissionState(), _facts(), _policy())
    partially_new_root = _facts(
        epoch_id=8,
        root_journal_hash=_hash(20),
        child_verification_claim_hashes=(_hash(4), _hash(21)),
        accepted_receipt_ids=(_hash(22),),
        cross_shard_message_ids=(_hash(23),),
    )

    result = _admit(
        accepted_state,
        partially_new_root,
        _policy(expected_epoch_id=8),
    )

    assert result.reject_reason is (
        RecursiveStarkAdmissionRejectReason.DUPLICATE_CHILD_VERIFICATION_CLAIM
    )
    assert result.state is accepted_state
    assert _hash(20) not in result.state.accepted_root_journal_hashes
    assert _hash(21) not in result.state.accepted_child_verification_claim_hashes
    assert _hash(22) not in result.state.accepted_receipt_ids
    assert _hash(23) not in result.state.accepted_cross_shard_message_ids


def test_given_disjoint_roots_when_admitted_in_either_order_then_state_is_canonical() -> None:
    first_root = _facts()
    second_root = _facts(
        epoch_id=8,
        root_journal_hash=_hash(20),
        child_verification_claim_hashes=(_hash(21),),
        accepted_receipt_ids=(_hash(22),),
        cross_shard_message_ids=(_hash(23),),
    )
    first_policy = _policy()
    second_policy = _policy(expected_epoch_id=8)

    first_then_second = _accept(
        _accept(RecursiveStarkAdmissionState(), first_root, first_policy),
        second_root,
        second_policy,
    )
    second_then_first = _accept(
        _accept(RecursiveStarkAdmissionState(), second_root, second_policy),
        first_root,
        first_policy,
    )

    assert first_then_second == second_then_first


def test_given_chain_scoped_state_when_other_chain_arrives_then_reject_is_no_op() -> None:
    accepted_state = _accept(RecursiveStarkAdmissionState(), _facts(), _policy())
    other_chain = _facts(
        chain_id="zenodex-other",
        epoch_id=8,
        root_journal_hash=_hash(20),
        child_verification_claim_hashes=(_hash(21),),
        accepted_receipt_ids=(_hash(22),),
        cross_shard_message_ids=(_hash(23),),
    )
    other_policy = _policy(
        expected_chain_id="zenodex-other",
        expected_epoch_id=8,
    )

    _assert_rejected_unchanged(
        accepted_state,
        other_chain,
        other_policy,
        RecursiveStarkAdmissionRejectReason.STATE_CHAIN_ID_MISMATCH,
    )


def test_given_full_replay_index_when_new_root_arrives_then_capacity_reject_is_no_op(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(recursive_stark_admission, "MAX_ADMISSION_INDEX_ENTRIES", 2)
    accepted_state = _accept(RecursiveStarkAdmissionState(), _facts(), _policy())
    second_root = _facts(
        epoch_id=8,
        root_journal_hash=_hash(20),
        child_verification_claim_hashes=(_hash(21),),
        accepted_receipt_ids=(),
        cross_shard_message_ids=(),
    )

    _assert_rejected_unchanged(
        accepted_state,
        second_root,
        _policy(expected_epoch_id=8),
        RecursiveStarkAdmissionRejectReason.ADMISSION_INDEX_CAPACITY_EXCEEDED,
    )


@pytest.mark.parametrize(
    ("field", "value", "error"),
    (
        ("root_journal_hash", "0x" + "00" * 32, "must be nonzero"),
        ("root_journal_hash", "0x" + "AA" * 32, "must be canonical lowercase"),
        (
            "child_verification_claim_hashes",
            (_hash(4), _hash(4)),
            "must be unique",
        ),
        (
            "accepted_receipt_ids",
            (_hash(6), _hash(6)),
            "must be strictly sorted and unique",
        ),
        (
            "cross_shard_message_ids",
            [_hash(8)],
            "must be a tuple",
        ),
    ),
)
def test_given_noncanonical_verified_facts_when_constructed_then_fail_closed(
    field: str,
    value: object,
    error: str,
) -> None:
    with pytest.raises((TypeError, ValueError), match=error):
        _facts(**{field: value})


def test_given_oversized_child_claim_list_when_constructed_then_fail_closed() -> None:
    oversized = tuple(
        _hash(index) for index in range(100, 100 + MAX_CHILD_VERIFICATION_CLAIMS_PER_ROOT + 1)
    )

    with pytest.raises(ValueError, match="child_verification_claim_hashes exceeds"):
        _facts(child_verification_claim_hashes=oversized)


@pytest.mark.parametrize(
    "field",
    (
        "child_verification_claims_root",
        "accepted_receipts_root",
        "cross_shard_message_ids_root",
    ),
)
def test_given_identifier_witness_root_mismatch_when_constructed_then_fail_closed(
    field: str,
) -> None:
    with pytest.raises(ValueError, match=rf"facts\.{field} mismatch"):
        _facts(**{field: _hash(99)})


def test_child_claim_root_preserves_authenticated_lane_order() -> None:
    forward = (_hash(4), _hash(5))
    reverse = tuple(reversed(forward))

    assert recursive_child_verification_claims_root_v1(forward) != (
        recursive_child_verification_claims_root_v1(reverse)
    )
    facts = _facts(child_verification_claim_hashes=reverse)
    assert facts.child_verification_claim_hashes == reverse


def test_identifier_roots_match_rust_parity_fixtures() -> None:
    assert recursive_child_verification_claims_root_v1((_hash(4), _hash(5))) == (
        "0xe071bc014dcfb44a7819e0e53f38b6fe71c2250f67273a167add7e292a615a15"
    )
    assert recursive_receipt_ids_root_v1((_hash(6), _hash(7))) == (
        "0x2c581962ecb7afea608928ad1b359507cad3b5b9f63c9e390367f5d83de6fb52"
    )
    assert recursive_message_ids_root_v1((_hash(8), _hash(9))) == (
        "0x7ab192d52f173c9c4b88581aebbf98d4272e45de319a48c48cb2ac8bb2a46799"
    )


def test_given_noncanonical_state_indexes_when_constructed_then_fail_closed() -> None:
    slot = RecursiveStarkAdmissionSlot(
        chain_id="zenodex-devnet",
        epoch_id=7,
        proof_profile="recursive_epoch_v1",
    )

    with pytest.raises(ValueError, match="root and admission slot counts must match"):
        RecursiveStarkAdmissionState(accepted_slots=(slot,))
    with pytest.raises(ValueError, match="strictly sorted and unique"):
        RecursiveStarkAdmissionState(
            accepted_root_journal_hashes=(_hash(2), _hash(1)),
            accepted_slots=(slot, replace(slot, epoch_id=8)),
        )


def test_given_untrusted_mapping_when_authenticated_then_boundary_raises_type_error() -> None:
    with pytest.raises(TypeError, match="facts must be exactly RecursiveStarkRootFacts"):
        _mint_recursive_stark_root_facts_after_verification(
            {"proof": "unverified"},  # type: ignore[arg-type]
            _policy(),
            _provenance(),
        )


def test_subclassed_shaped_facts_cannot_cross_the_authentication_boundary() -> None:
    class _SubclassedFacts(RecursiveStarkRootFacts):
        pass

    subclassed = _SubclassedFacts(**vars(_facts()))

    with pytest.raises(TypeError, match="facts must be exactly RecursiveStarkRootFacts"):
        _mint_recursive_stark_root_facts_after_verification(
            subclassed,
            _policy(),
            _provenance(),
        )


def test_subclassed_policy_cannot_cross_the_authentication_boundary() -> None:
    class _SubclassedPolicy(TrustedRecursiveStarkAdmissionPolicy):
        pass

    subclassed = _SubclassedPolicy(**vars(_policy()))

    with pytest.raises(
        TypeError,
        match="trusted_policy must be exactly TrustedRecursiveStarkAdmissionPolicy",
    ):
        _mint_recursive_stark_root_facts_after_verification(
            _facts(),
            subclassed,
            _provenance(),
        )


def test_shaped_facts_cannot_enter_authenticated_admission_directly() -> None:
    with pytest.raises(
        TypeError,
        match="authenticated_root must be _AuthenticatedRecursiveStarkRootFacts",
    ):
        _admit_authenticated_recursive_stark_root(
            RecursiveStarkAdmissionState(),
            _facts(),  # type: ignore[arg-type]
        )


def test_authenticated_facts_constructor_rejects_a_caller_supplied_seal() -> None:
    with pytest.raises(TypeError, match="require the private seal"):
        _AuthenticatedRecursiveStarkRootFacts(
            _facts(),
            _policy(),
            _provenance(),
            seal=object(),
        )


def test_object_new_capability_without_private_seal_rejects_before_staging() -> None:
    forged = object.__new__(_AuthenticatedRecursiveStarkRootFacts)
    object.__setattr__(forged, "_facts", _facts())
    object.__setattr__(forged, "_trusted_policy", _policy())
    state = RecursiveStarkAdmissionState()

    with pytest.raises(TypeError, match="authenticated_root lacks the private seal"):
        _admit_authenticated_recursive_stark_root(state, forged)

    assert state == RecursiveStarkAdmissionState()


def test_authenticated_facts_reject_subclass_construction() -> None:
    with pytest.raises(TypeError, match="cannot be subclassed"):

        class _ForgedAuthenticatedFacts(  # type: ignore[misc]
            _AuthenticatedRecursiveStarkRootFacts
        ):
            pass


def _pickle_round_trip(value: object) -> object:
    return pickle.loads(pickle.dumps(value))


@pytest.mark.parametrize(
    "operation",
    (copy.copy, copy.deepcopy, _pickle_round_trip),
)
def test_authenticated_facts_reject_copy_and_serialization(
    operation: Callable[[object], object],
) -> None:
    authenticated = _authenticated(_facts(), _policy())

    with pytest.raises(TypeError, match="cannot be (copied|serialized)"):
        operation(authenticated)


def test_authenticated_facts_reject_dataclass_replace() -> None:
    authenticated = _authenticated(_facts(), _policy())

    with pytest.raises(TypeError, match="dataclass instance"):
        replace(authenticated)  # type: ignore[type-var]


def test_authenticated_facts_bind_policy_before_admission() -> None:
    policy = _policy()
    authenticated = _authenticated(_facts(), policy)

    assert authenticated.trusted_policy is policy
    with pytest.raises(AttributeError, match="authenticated recursive facts are immutable"):
        authenticated.trusted_policy = _policy(expected_epoch_id=8)  # type: ignore[misc]
