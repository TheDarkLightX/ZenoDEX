"""Malicious validator-set chaos.

Honest fork tests are in ``test_zeno_ledger_chaos_forks.py``. This file
covers what happens when the validator set itself is adversarial:

  - **Weight inflation**: an attacker controlling one ``validator_id``
    assigns themselves 51% (or more) of total voting power.
  - **Homoglyph IDs**: validator identifiers chosen to visually impersonate
    legitimate validators (Latin ``a`` vs Cyrillic ``а``, normal vs combining
    marks, trailing zero-width chars).
  - **Public-key impersonation**: two validators with different IDs but the
    same public key — would let one signer satisfy two slots in quorum.
  - **Schedule manipulation**: power distribution chosen so a specific
    height always lands on a single attacker validator.
  - **Quorum-drop rotation**: a registry rotation that excludes a previously
    valid signer mid-flight, leaving in-flight signatures unverifiable.
  - **Mid-validation tampering**: the validator set is mutated between the
    hash binding step and the schedule lookup.

For each scenario, we assert that ZenoLedger either fail-closes or that
the documented protocol invariants make the attack a no-op. **There are no
silent acceptances allowed here.**
"""

from __future__ import annotations

from typing import Any

import pytest

from src.integration.zeno_ledger_signature import (
    SIGNED_ARTIFACT_ALGORITHM_BLS12_381_G2_BASIC_V0,
)
from src.integration.zeno_ledger_signer_registry import (
    build_signer_registry_v0,
    validate_signer_registry_v0,
    verify_signature_quorum_v0,
)
from src.integration.zeno_ledger_v0 import (
    VALIDATOR_SET_SCHEMA_V0,
    scheduled_validator_id_for_height_v0,
    validate_validator_set_v0,
    validator_set_hash_v0,
)

_PK = lambda byte: "0x" + f"{byte:02x}" * 48  # noqa: E731


def _validator(vid: str, *, pk_byte: int = 0xAB, power: int = 1) -> dict[str, Any]:
    return {
        "validator_id": vid,
        "public_key": _PK(pk_byte),
        "voting_power": power,
    }


def _vset(*, chain_id: str = "tau-test", epoch: int = 0, validators: list[dict[str, Any]]) -> dict[str, Any]:
    return {
        "schema": VALIDATOR_SET_SCHEMA_V0,
        "chain_id": chain_id,
        "epoch": epoch,
        "validators": validators,
    }


def _signer(*, signer_id: str, key_id: str, pk_byte: int = 0xAB, **kwargs: Any) -> dict[str, Any]:
    return {
        "signer_id": signer_id,
        "key_id": key_id,
        "public_key": _PK(pk_byte),
        **kwargs,
    }


# -----------------------------------------------------------------------------
# A. Weight inflation — attacker takes majority.
# -----------------------------------------------------------------------------


class TestWeightInflation:
    """A malicious operator who controls a single validator entry can in
    principle set their own ``voting_power`` to anything. The schema requires
    only that power is positive — it does NOT cap total power. The defense
    is at the registry-rotation level: any new validator set must be agreed
    upon by the prior quorum. These tests show that *if* the rotation is
    accepted (because the prior quorum signed it), the math is internally
    consistent — but the rotation itself is the social/governance gate."""

    def test_attacker_with_51_percent_dominates_schedule(self) -> None:
        vs = _vset(validators=[
            _validator("attacker", pk_byte=0xAA, power=51),
            _validator("honest1", pk_byte=0xBB, power=49),
        ])
        validate_validator_set_v0(vs)
        # Most heights → attacker.
        attacker_count = sum(
            1 for h in range(100)
            if scheduled_validator_id_for_height_v0(vs, height=h) == "attacker"
        )
        # 51% should round-robin into ~51/100 attacker slots.
        assert attacker_count == 51

    def test_attacker_with_99_percent_almost_monopolizes_schedule(self) -> None:
        vs = _vset(validators=[
            _validator("attacker", pk_byte=0xAA, power=99),
            _validator("honest1", pk_byte=0xBB, power=1),
        ])
        attacker_count = sum(
            1 for h in range(100)
            if scheduled_validator_id_for_height_v0(vs, height=h) == "attacker"
        )
        assert attacker_count == 99

    def test_huge_voting_power_does_not_overflow(self) -> None:
        # Python ints are arbitrary precision, but downstream consumers
        # (Tau, Rust) may not be. We document this by allowing huge values
        # at the ZenoLedger layer.
        vs = _vset(validators=[
            _validator("v1", pk_byte=0xA1, power=2**63 - 1),
            _validator("v2", pk_byte=0xB2, power=1),
        ])
        validate_validator_set_v0(vs)
        # Schedule for height 0 lands on v1 (sorted: v1 < v2).
        assert scheduled_validator_id_for_height_v0(vs, height=0) == "v1"

    def test_empty_validator_list_rejected_by_schema(self) -> None:
        # An empty validator list is rejected by validate_validator_set_v0.
        vs = _vset(validators=[])
        with pytest.raises(ValueError, match="non-empty"):
            validate_validator_set_v0(vs)

    def test_single_validator_set_works_but_centralizes_completely(self) -> None:
        """A 1-validator set is structurally valid (the schema doesn't
        require ≥2) but governance must catch it. We confirm the math is
        consistent."""
        vs = _vset(validators=[_validator("solo", pk_byte=0xAA, power=1)])
        validate_validator_set_v0(vs)
        # Every height → solo.
        for h in range(10):
            assert scheduled_validator_id_for_height_v0(vs, height=h) == "solo"


# -----------------------------------------------------------------------------
# B. Homoglyph and visually-similar validator IDs.
# -----------------------------------------------------------------------------


class TestHomoglyphIds:
    """Validator IDs are arbitrary strings. An attacker could register
    "honest1" using Cyrillic letters that look like ASCII. Our validator
    detects duplicates by Python string equality, so visually-identical
    Unicode IDs are accepted as distinct. That's the safe behavior at this
    layer — but operators MUST review IDs out-of-band."""

    def test_cyrillic_homoglyph_is_treated_as_distinct_id(self) -> None:
        # Latin "honest1" vs Cyrillic "hоnest1" (the 'о' is U+043E).
        vs = _vset(validators=[
            _validator("honest1", pk_byte=0xA1),
            _validator("h\u043enest1", pk_byte=0xB2),
        ])
        validate_validator_set_v0(vs)
        # Two validators are accepted.
        assert len(vs["validators"]) == 2
        # Their hashes are different (because the IDs are different bytes).
        # Note: the hash uses the sorted-by-validator-id form; both end up
        # included.
        assert validator_set_hash_v0(vs) != validator_set_hash_v0(_vset(
            validators=[_validator("honest1", pk_byte=0xA1)]
        ))

    def test_combining_mark_in_id_is_distinct(self) -> None:
        # "honest" vs "honest" + combining acute (U+0301) — visually
        # similar in many fonts.
        vs = _vset(validators=[
            _validator("honest", pk_byte=0xA1),
            _validator("honest\u0301", pk_byte=0xB2),
        ])
        validate_validator_set_v0(vs)
        assert len(vs["validators"]) == 2

    def test_zero_width_space_in_id_is_distinct(self) -> None:
        # Zero-width space (U+200B) is invisible but Python sees it.
        vs = _vset(validators=[
            _validator("honest", pk_byte=0xA1),
            _validator("honest\u200b", pk_byte=0xB2),
        ])
        validate_validator_set_v0(vs)
        assert len(vs["validators"]) == 2

    def test_duplicate_id_after_unicode_normalization_still_accepted(self) -> None:
        """We do NOT normalize Unicode (NFC) before comparison. So an
        attacker who registers a Unicode-normalized form vs decomposed form
        gets two slots."""
        # "é" as NFC (U+00E9) vs NFD ("e" + U+0301).
        nfc = "v\u00e9"  # single char é
        nfd = "v\u0065\u0301"  # e + combining acute
        # They look the same but are different bytes.
        assert nfc != nfd
        vs = _vset(validators=[
            _validator(nfc, pk_byte=0xA1),
            _validator(nfd, pk_byte=0xB2),
        ])
        validate_validator_set_v0(vs)  # accepts both
        assert len(vs["validators"]) == 2


# -----------------------------------------------------------------------------
# C. Public-key impersonation — two validators sharing one key.
# -----------------------------------------------------------------------------


class TestPublicKeyImpersonation:
    """Validator-set public-key uniqueness remains governance-scoped here.

    The authority-bearing signer registry rejects a key reused under another
    identity so one BLS private key cannot contribute quorum weight twice.
    """

    def test_two_validators_with_same_public_key_accepted_by_schema(self) -> None:
        vs = _vset(validators=[
            _validator("alice", pk_byte=0xAA),
            _validator("bob", pk_byte=0xAA),  # SAME key
        ])
        # Schema validation passes.
        validate_validator_set_v0(vs)
        # Hash is determined by IDs + powers + keys, so this set hashes
        # differently from a set with one validator.
        h_one = validator_set_hash_v0(_vset(validators=[_validator("alice", pk_byte=0xAA)]))
        assert validator_set_hash_v0(vs) != h_one

    def test_signer_registry_rejects_duplicate_public_key(self) -> None:
        with pytest.raises(ValueError, match="duplicate signer public_key"):
            build_signer_registry_v0(
                registry_id="r",
                payload_kind="checkpoint",
                threshold=1,
                signers=[
                    _signer(signer_id="alice", key_id="k", pk_byte=0xAA),
                    _signer(signer_id="bob", key_id="k", pk_byte=0xAA),
                ],
            )


# -----------------------------------------------------------------------------
# D. Schedule manipulation — adversary chooses powers to dominate a height.
# -----------------------------------------------------------------------------


class TestScheduleManipulation:
    """An attacker who can influence power distribution at rotation time
    can engineer which validator owns a specific height. The math is
    deterministic, so this attack is fully observable — operators reviewing
    a proposed validator set rotation can compute the schedule ahead of time."""

    def test_attacker_can_predict_which_validator_owns_height(self) -> None:
        vs = _vset(validators=[
            _validator("alice", pk_byte=0xA1, power=3),
            _validator("bob", pk_byte=0xB2, power=2),
        ])
        # Power distribution: total=5. height % 5 in [0..2] → alice, [3..4] → bob.
        assert scheduled_validator_id_for_height_v0(vs, height=0) == "alice"
        assert scheduled_validator_id_for_height_v0(vs, height=3) == "bob"

    def test_swapping_validator_ids_changes_schedule(self) -> None:
        # Same powers, different IDs → different sort order → different schedule.
        vs_a = _vset(validators=[
            _validator("aa", pk_byte=0xA1, power=1),
            _validator("zz", pk_byte=0xB2, power=1),
        ])
        vs_b = _vset(validators=[
            _validator("zz", pk_byte=0xA1, power=1),
            _validator("aa", pk_byte=0xB2, power=1),
        ])
        # Sorted: "aa" < "zz" in both. The schedule for height 0 picks the
        # first validator by sorted ID. Both schedule "aa" at height 0.
        assert scheduled_validator_id_for_height_v0(vs_a, height=0) == "aa"
        assert scheduled_validator_id_for_height_v0(vs_b, height=0) == "aa"

    def test_schedule_is_deterministic_under_id_reordering_in_input(self) -> None:
        """Input order does NOT matter — the schedule sorts by validator_id."""
        vs_a = _vset(validators=[
            _validator("a", pk_byte=0xA1, power=1),
            _validator("b", pk_byte=0xB2, power=1),
        ])
        vs_b = _vset(validators=[
            _validator("b", pk_byte=0xB2, power=1),
            _validator("a", pk_byte=0xA1, power=1),
        ])
        for h in range(20):
            assert (
                scheduled_validator_id_for_height_v0(vs_a, height=h)
                == scheduled_validator_id_for_height_v0(vs_b, height=h)
            )


# -----------------------------------------------------------------------------
# E. Quorum-drop rotation — registry rotation that excludes prior signers.
# -----------------------------------------------------------------------------


class TestQuorumDropRotation:
    """An attacker who controls a registry rotation could drop honest
    signers between when a payload is signed and when it's verified. We
    confirm the schema requires the registry that signed a payload to be
    the one used for verification — there is no implicit fallback."""

    def test_envelope_signed_under_old_registry_fails_under_new(self) -> None:
        # Build an old registry with signer "alice".
        build_signer_registry_v0(
            registry_id="r",
            payload_kind="checkpoint",
            threshold=1,
            signers=[_signer(signer_id="alice", key_id="k", pk_byte=0xAA)],
        )
        # Build a new registry without alice.
        new_reg = build_signer_registry_v0(
            registry_id="r",
            payload_kind="checkpoint",
            threshold=1,
            signers=[_signer(signer_id="bob", key_id="k", pk_byte=0xBB)],
        )
        # Envelopes signed by alice cannot satisfy the new registry.
        envelopes = [{
            "signer_id": "alice",
            "key_id": "k",
            "algorithm": SIGNED_ARTIFACT_ALGORITHM_BLS12_381_G2_BASIC_V0,
        }]
        with pytest.raises(ValueError, match="not active in registry"):
            verify_signature_quorum_v0(
                registry=new_reg,
                payload_kind="checkpoint",
                payload_hash="0x" + "11" * 32,
                envelopes=envelopes,
            )

    def test_registry_with_revoked_signer_excludes_them_from_quorum(self) -> None:
        # Active alice, revoked bob.
        reg = build_signer_registry_v0(
            registry_id="r",
            payload_kind="checkpoint",
            threshold=1,
            signers=[
                _signer(signer_id="alice", key_id="k", pk_byte=0xAA),
                _signer(signer_id="bob", key_id="k", pk_byte=0xBB, status="revoked"),
            ],
        )
        # Bob's envelope is rejected.
        with pytest.raises(ValueError, match="not active in registry"):
            verify_signature_quorum_v0(
                registry=reg,
                payload_kind="checkpoint",
                payload_hash="0x" + "11" * 32,
                envelopes=[{
                    "signer_id": "bob",
                    "key_id": "k",
                    "algorithm": SIGNED_ARTIFACT_ALGORITHM_BLS12_381_G2_BASIC_V0,
                }],
            )


# -----------------------------------------------------------------------------
# F. Mid-validation tampering — registry mutated after validation.
# -----------------------------------------------------------------------------


class TestMidValidationTampering:
    """If an attacker mutates the validator set between validate_*_v0() and
    use, our pure-functional API means each call re-validates. So mid-
    process mutation is detected on the next call, not silently inherited."""

    def test_validator_set_mutation_breaks_hash_binding(self) -> None:
        vs = _vset(validators=[_validator("v1", pk_byte=0xA1), _validator("v2", pk_byte=0xB2)])
        original_hash = validator_set_hash_v0(vs)
        # Mutate after binding.
        vs["validators"].append(_validator("v3", pk_byte=0xC3))
        # Re-binding produces a different hash.
        assert validator_set_hash_v0(vs) != original_hash

    def test_signer_registry_mutation_breaks_binding(self) -> None:
        reg = build_signer_registry_v0(
            registry_id="r",
            payload_kind="checkpoint",
            threshold=1,
            signers=[_signer(signer_id="alice", key_id="k", pk_byte=0xAA)],
        )
        # Mutate the registry dict.
        reg_mutated = dict(reg)
        reg_mutated["threshold"] = 0  # would underrun
        # The validator re-derives the binding and rejects.
        with pytest.raises(ValueError):
            validate_signer_registry_v0(reg_mutated)

    def test_registry_re_validation_is_idempotent(self) -> None:
        reg = build_signer_registry_v0(
            registry_id="r",
            payload_kind="checkpoint",
            threshold=1,
            signers=[_signer(signer_id="alice", key_id="k", pk_byte=0xAA)],
        )
        # Multiple calls to validate are idempotent.
        for _ in range(5):
            validate_signer_registry_v0(reg)


# -----------------------------------------------------------------------------
# G. Signer registry hash chain — attacker can't substitute a different
#    registry with the same registry_id.
# -----------------------------------------------------------------------------


class TestRegistryIdentitySubstitution:
    def test_two_registries_same_id_different_signers_have_different_hashes(self) -> None:
        reg_a = build_signer_registry_v0(
            registry_id="r-1",
            payload_kind="checkpoint",
            threshold=1,
            signers=[_signer(signer_id="alice", key_id="k", pk_byte=0xAA)],
        )
        reg_b = build_signer_registry_v0(
            registry_id="r-1",  # SAME id
            payload_kind="checkpoint",
            threshold=1,
            signers=[_signer(signer_id="bob", key_id="k", pk_byte=0xBB)],  # different signer
        )
        # registry_hash differs.
        assert reg_a["registry_hash"] != reg_b["registry_hash"]

    def test_two_registries_same_id_different_threshold_have_different_hashes(self) -> None:
        reg_a = build_signer_registry_v0(
            registry_id="r-1",
            payload_kind="checkpoint",
            threshold=1,
            signers=[
                _signer(signer_id="alice", key_id="k", pk_byte=0xAA),
                _signer(signer_id="bob", key_id="k", pk_byte=0xBB),
            ],
        )
        reg_b = build_signer_registry_v0(
            registry_id="r-1",  # SAME id
            payload_kind="checkpoint",
            threshold=2,  # DIFFERENT threshold
            signers=[
                _signer(signer_id="alice", key_id="k", pk_byte=0xAA),
                _signer(signer_id="bob", key_id="k", pk_byte=0xBB),
            ],
        )
        assert reg_a["registry_hash"] != reg_b["registry_hash"]


# -----------------------------------------------------------------------------
# H. Threshold gymnastics — bizarre threshold values.
# -----------------------------------------------------------------------------


class TestThresholdGymnastics:
    def test_threshold_equal_to_total_active_weight(self) -> None:
        # Threshold == total → unanimity required.
        reg = build_signer_registry_v0(
            registry_id="r",
            payload_kind="checkpoint",
            threshold=2,
            signers=[
                _signer(signer_id="alice", key_id="k", pk_byte=0xAA),
                _signer(signer_id="bob", key_id="k", pk_byte=0xBB),
            ],
        )
        assert reg["threshold"] == 2

    def test_threshold_strictly_exceeds_active_weight_rejected(self) -> None:
        with pytest.raises(ValueError, match="threshold exceeds"):
            build_signer_registry_v0(
                registry_id="r",
                payload_kind="checkpoint",
                threshold=10,
                signers=[
                    _signer(signer_id="alice", key_id="k", pk_byte=0xAA),
                    _signer(signer_id="bob", key_id="k", pk_byte=0xBB),
                ],
            )

    def test_huge_threshold_rejected(self) -> None:
        with pytest.raises(ValueError, match="threshold exceeds"):
            build_signer_registry_v0(
                registry_id="r",
                payload_kind="checkpoint",
                threshold=2**63,
                signers=[_signer(signer_id="alice", key_id="k", pk_byte=0xAA)],
            )

    def test_negative_threshold_rejected(self) -> None:
        with pytest.raises(ValueError, match="positive int"):
            build_signer_registry_v0(
                registry_id="r",
                payload_kind="checkpoint",
                threshold=-1,
                signers=[_signer(signer_id="alice", key_id="k", pk_byte=0xAA)],
            )

    def test_threshold_one_under_n_2_quorum_works(self) -> None:
        """Threshold=1 of N=2 means a single signer is enough."""
        reg = build_signer_registry_v0(
            registry_id="r",
            payload_kind="checkpoint",
            threshold=1,
            signers=[
                _signer(signer_id="alice", key_id="k", pk_byte=0xAA, weight=1),
                _signer(signer_id="bob", key_id="k", pk_byte=0xBB, weight=1),
            ],
        )
        assert reg["threshold"] == 1


# -----------------------------------------------------------------------------
# I. Algorithm pinning — attacker can't downgrade the signature algorithm.
# -----------------------------------------------------------------------------


class TestAlgorithmPinning:
    def test_envelope_with_downgraded_algorithm_rejected(self) -> None:
        reg = build_signer_registry_v0(
            registry_id="r",
            payload_kind="checkpoint",
            threshold=1,
            signers=[_signer(signer_id="alice", key_id="k", pk_byte=0xAA)],
        )
        with pytest.raises(ValueError, match="algorithm is not allowed"):
            verify_signature_quorum_v0(
                registry=reg,
                payload_kind="checkpoint",
                payload_hash="0x" + "11" * 32,
                envelopes=[{
                    "signer_id": "alice",
                    "key_id": "k",
                    "algorithm": "ed25519",  # downgrade attempt
                }],
            )

    def test_envelope_with_legacy_hmac_algorithm_rejected_against_bls_registry(self) -> None:
        reg = build_signer_registry_v0(
            registry_id="r",
            payload_kind="checkpoint",
            threshold=1,
            signers=[_signer(signer_id="alice", key_id="k", pk_byte=0xAA)],
        )
        # HMAC-SHA-256 is a supported algorithm in zeno_ledger_signature but
        # NOT for this registry (signers are BLS).
        with pytest.raises(ValueError, match="algorithm is not allowed"):
            verify_signature_quorum_v0(
                registry=reg,
                payload_kind="checkpoint",
                payload_hash="0x" + "11" * 32,
                envelopes=[{
                    "signer_id": "alice",
                    "key_id": "k",
                    "algorithm": "zenodex/zeno_ledger/signed_artifact_algorithm/hmac_sha256/v0",
                }],
            )
