"""Private test seal for the future Firecracker-to-Spot-V7 store boundary.

Raw ``SpotSettlementV7VerifierOutputV1`` bytes are data.  They never enter the
store directly.  The only constructor in this module is deliberately test-only
and permanently reports every authority flag as false.  A future production
binder must consume a private runner-owned Firecracker execution capability,
validate the exact output and host input, and mint a separate authority type.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from typing import Final, NoReturn, SupportsIndex, final

from src.integration.zrpf_spot_v7_atomic_settlement_types import (
    MAX_U64,
    SPOT_V7_ATOMIC_SETTLEMENT_AUTHORITY_BLOCKED_REASON_V1,
    SpotV7AssetEffectV1,
    SpotV7CellKindV1,
    SpotV7CellRoleV1,
    SpotV7CellTransitionV1,
    _hash_bytes,
    _hex_hash,
    _require_uint,
    _sha256_prefixed,
    spot_v7_cell_transitions_root_v1,
)

_CAPABILITY_COMMITMENT_DOMAIN_V1: Final = (
    b"zenodex.zrpf.spot_v7_test_only_atomic_settlement_capability.v1"
)
_ACTION_IDS_ROOT_DOMAIN_V1: Final = b"zenodex.zrpf.economic_action_ids_root.v1"
_ACTION_BINDINGS_ROOT_DOMAIN_V1: Final = (
    b"zenodex.zrpf.action_authorization_bindings_root.v1"
)
_GRANT_SPENDS_ROOT_DOMAIN_V1: Final = b"zenodex.zrpf.authorization_grant_spends_root.v1"
_CONSUMED_OBJECTS_ROOT_DOMAIN_V1: Final = b"zenodex.zrpf.economic_consumed_objects_root.v1"

_MAX_RECEIPT_BYTES_V1 = 16 * 1_024 * 1_024
_MAX_JOURNAL_BYTES_V1 = 64 * 1_024
_MAX_PLAN_BYTES_V1 = 512 * 1_024
_MAX_EXECUTION_RECORD_BYTES_V1 = 1 * 1_024 * 1_024
_MAX_FIRECRACKER_OUTPUT_BYTES_V1 = 64 * 1_024


@dataclass(frozen=True, slots=True)
class _SpotV7SettlementCandidateInputV1:
    """Untrusted values used only by the explicit test sealer."""

    application_id: str
    chain_or_domain_id: str
    epoch_id: int
    verified_program_id: str
    verified_profile_id: str
    verified_program_manifest_root: str
    source_child_claim_binding: str
    source_child_journal_sha256: str
    data_availability_certificate_root: str
    data_root: str
    settlement_effect_plan_commitment: str
    pre_state_root: str
    post_state_root: str
    economic_action_id: str
    authorization_nullifier: str
    authorization_grant_spend_nullifier: str
    consumed_object_ids: tuple[str, ...]
    cell_transitions: tuple[SpotV7CellTransitionV1, ...]
    cell_transitions_root: str
    asset_effects: tuple[SpotV7AssetEffectV1, ...]
    exact_v7_receipt_bytes: bytes
    exact_v7_journal_bytes: bytes
    exact_plan_b_bytes: bytes
    exact_firecracker_execution_record_bytes: bytes
    exact_firecracker_output_bytes: bytes


class _TestOnlySealV1:
    __slots__ = ()


_TEST_ONLY_SEAL_V1 = _TestOnlySealV1()


@final
class _TestOnlySealedSpotV7SettlementV1:
    """Non-copyable candidate accepted only by the test-only store sink."""

    __slots__ = ("_input", "_seal", "_settlement_commitment")

    _input: _SpotV7SettlementCandidateInputV1
    _seal: _TestOnlySealV1
    _settlement_commitment: str

    def __init__(
        self,
        candidate_input: _SpotV7SettlementCandidateInputV1,
        *,
        seal: _TestOnlySealV1,
    ) -> None:
        if seal is not _TEST_ONLY_SEAL_V1:
            raise TypeError("Spot V7 test-only capability requires the module-private seal")
        _validate_candidate(candidate_input)
        object.__setattr__(self, "_input", candidate_input)
        object.__setattr__(self, "_seal", seal)
        object.__setattr__(
            self,
            "_settlement_commitment",
            _derive_capability_commitment(candidate_input),
        )

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("_TestOnlySealedSpotV7SettlementV1 cannot be subclassed")

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise TypeError("Spot V7 test-only capability cannot be mutated")

    def __copy__(self) -> NoReturn:
        raise TypeError("Spot V7 test-only capability cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("Spot V7 test-only capability cannot be deep-copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("Spot V7 test-only capability cannot be serialized")

    def __reduce_ex__(self, _protocol: SupportsIndex) -> NoReturn:
        raise TypeError("Spot V7 test-only capability cannot be serialized")

    def _has_private_test_seal(self) -> bool:
        return self._seal is _TEST_ONLY_SEAL_V1

    @property
    def settlement_authority(self) -> bool:
        return False

    @property
    def production_authority(self) -> bool:
        return False

    @property
    def firecracker_execution_verified(self) -> bool:
        return False

    @property
    def authority_blocked_reason(self) -> str:
        return SPOT_V7_ATOMIC_SETTLEMENT_AUTHORITY_BLOCKED_REASON_V1

    @property
    def settlement_commitment(self) -> str:
        return self._settlement_commitment

    @property
    def application_id(self) -> str:
        return self._input.application_id

    @property
    def chain_or_domain_id(self) -> str:
        return self._input.chain_or_domain_id

    @property
    def epoch_id(self) -> int:
        return self._input.epoch_id

    @property
    def verified_program_id(self) -> str:
        return self._input.verified_program_id

    @property
    def verified_profile_id(self) -> str:
        return self._input.verified_profile_id

    @property
    def verified_program_manifest_root(self) -> str:
        return self._input.verified_program_manifest_root

    @property
    def source_child_claim_binding(self) -> str:
        return self._input.source_child_claim_binding

    @property
    def source_child_journal_sha256(self) -> str:
        return self._input.source_child_journal_sha256

    @property
    def data_availability_certificate_root(self) -> str:
        return self._input.data_availability_certificate_root

    @property
    def data_root(self) -> str:
        return self._input.data_root

    @property
    def settlement_effect_plan_commitment(self) -> str:
        return self._input.settlement_effect_plan_commitment

    @property
    def pre_state_root(self) -> str:
        return self._input.pre_state_root

    @property
    def post_state_root(self) -> str:
        return self._input.post_state_root

    @property
    def economic_action_id(self) -> str:
        return self._input.economic_action_id

    @property
    def authorization_nullifier(self) -> str:
        return self._input.authorization_nullifier

    @property
    def authorization_grant_spend_nullifier(self) -> str:
        return self._input.authorization_grant_spend_nullifier

    @property
    def consumed_object_ids(self) -> tuple[str, ...]:
        return self._input.consumed_object_ids

    @property
    def cell_transitions(self) -> tuple[SpotV7CellTransitionV1, ...]:
        return self._input.cell_transitions

    @property
    def cell_transitions_root(self) -> str:
        return self._input.cell_transitions_root

    @property
    def asset_effects(self) -> tuple[SpotV7AssetEffectV1, ...]:
        return self._input.asset_effects

    @property
    def exact_v7_receipt_bytes(self) -> bytes:
        return self._input.exact_v7_receipt_bytes

    @property
    def exact_v7_journal_bytes(self) -> bytes:
        return self._input.exact_v7_journal_bytes

    @property
    def exact_plan_b_bytes(self) -> bytes:
        return self._input.exact_plan_b_bytes

    @property
    def exact_firecracker_execution_record_bytes(self) -> bytes:
        return self._input.exact_firecracker_execution_record_bytes

    @property
    def exact_firecracker_output_bytes(self) -> bytes:
        return self._input.exact_firecracker_output_bytes

    @property
    def receipt_sha256(self) -> str:
        return _sha256_prefixed(self.exact_v7_receipt_bytes)

    @property
    def journal_sha256(self) -> str:
        return _sha256_prefixed(self.exact_v7_journal_bytes)

    @property
    def plan_b_sha256(self) -> str:
        return _sha256_prefixed(self.exact_plan_b_bytes)

    @property
    def firecracker_execution_record_sha256(self) -> str:
        return _sha256_prefixed(self.exact_firecracker_execution_record_bytes)

    @property
    def firecracker_output_sha256(self) -> str:
        return _sha256_prefixed(self.exact_firecracker_output_bytes)

    @property
    def action_ids_root(self) -> str:
        return _list_root(_ACTION_IDS_ROOT_DOMAIN_V1, (self.economic_action_id,))

    @property
    def action_authorization_bindings_root(self) -> str:
        return _list_root(
            _ACTION_BINDINGS_ROOT_DOMAIN_V1,
            (self.authorization_nullifier,),
        )

    @property
    def authorization_grant_spends_root(self) -> str:
        return _list_root(
            _GRANT_SPENDS_ROOT_DOMAIN_V1,
            (self.authorization_grant_spend_nullifier,),
        )

    @property
    def consumed_object_ids_root(self) -> str:
        return _list_root(_CONSUMED_OBJECTS_ROOT_DOMAIN_V1, self.consumed_object_ids)


def _seal_test_only_spot_v7_settlement_v1(
    candidate_input: _SpotV7SettlementCandidateInputV1,
) -> _TestOnlySealedSpotV7SettlementV1:
    """Mint a permanent-authority-false capability for tests and local mechanics."""

    if type(candidate_input) is not _SpotV7SettlementCandidateInputV1:
        raise TypeError("candidate_input must be exact _SpotV7SettlementCandidateInputV1")
    return _TestOnlySealedSpotV7SettlementV1(candidate_input, seal=_TEST_ONLY_SEAL_V1)


def _validate_candidate(candidate: _SpotV7SettlementCandidateInputV1) -> None:
    for name in (
        "application_id",
        "chain_or_domain_id",
        "verified_program_id",
        "verified_profile_id",
        "verified_program_manifest_root",
        "source_child_claim_binding",
        "source_child_journal_sha256",
        "data_availability_certificate_root",
        "data_root",
        "settlement_effect_plan_commitment",
        "pre_state_root",
        "post_state_root",
        "economic_action_id",
        "authorization_nullifier",
        "authorization_grant_spend_nullifier",
        "cell_transitions_root",
    ):
        _hash_bytes(getattr(candidate, name), name=f"Spot V7 candidate {name}")
    _require_uint(candidate.epoch_id, name="Spot V7 candidate epoch_id", maximum=MAX_U64)
    _validate_consumed_objects(candidate.consumed_object_ids)
    _validate_artifact_bytes(candidate)
    _validate_transition_and_effect_shape(candidate)


def _validate_consumed_objects(object_ids: tuple[str, ...]) -> None:
    if type(object_ids) is not tuple or not 1 <= len(object_ids) <= 64:
        raise ValueError("Spot V7 consumed objects must contain 1..64 identifiers")
    for object_id in object_ids:
        _hash_bytes(object_id, name="Spot V7 consumed object")
    if object_ids != tuple(sorted(object_ids)) or len(set(object_ids)) != len(object_ids):
        raise ValueError("Spot V7 consumed objects must be sorted and unique")


def _validate_artifact_bytes(candidate: _SpotV7SettlementCandidateInputV1) -> None:
    fields = (
        ("receipt", candidate.exact_v7_receipt_bytes, _MAX_RECEIPT_BYTES_V1),
        ("journal", candidate.exact_v7_journal_bytes, _MAX_JOURNAL_BYTES_V1),
        ("Plan B", candidate.exact_plan_b_bytes, _MAX_PLAN_BYTES_V1),
        (
            "Firecracker execution record",
            candidate.exact_firecracker_execution_record_bytes,
            _MAX_EXECUTION_RECORD_BYTES_V1,
        ),
        (
            "Firecracker output",
            candidate.exact_firecracker_output_bytes,
            _MAX_FIRECRACKER_OUTPUT_BYTES_V1,
        ),
    )
    for name, value, maximum in fields:
        if type(value) is not bytes or not value or len(value) > maximum:
            raise ValueError(f"Spot V7 exact {name} bytes are empty or oversized")


def _validate_transition_and_effect_shape(
    candidate: _SpotV7SettlementCandidateInputV1,
) -> None:
    transitions = candidate.cell_transitions
    if type(transitions) is not tuple or len(transitions) != 4:
        raise ValueError("restricted Spot V7 requires exactly four cell transitions")
    expected_root = spot_v7_cell_transitions_root_v1(transitions)
    if expected_root != candidate.cell_transitions_root:
        raise ValueError("Spot V7 cell transition root mismatch")
    effects = candidate.asset_effects
    if type(effects) is not tuple or len(effects) != 2:
        raise ValueError("restricted Spot V7 requires exactly two asset effects")
    if any(type(row) is not SpotV7AssetEffectV1 for row in effects):
        raise TypeError("Spot V7 asset effects must be exact SpotV7AssetEffectV1 values")
    effect_keys = tuple((row.asset_id, row.effect_id) for row in effects)
    if effect_keys != tuple(sorted(effect_keys)) or len({row.asset_id for row in effects}) != 2:
        raise ValueError("Spot V7 asset effects must be ordered with unique assets")
    if any(row.economic_action_id != candidate.economic_action_id for row in effects):
        raise ValueError("Spot V7 asset effect action identity mismatch")
    leg_shapes = tuple(
        _validate_asset_transition_pair(effect, transitions) for effect in effects
    )
    expected_leg_shapes = {
        (SpotV7CellKindV1.ACCOUNT_BALANCE, SpotV7CellKindV1.POOL_RESERVE),
        (SpotV7CellKindV1.POOL_RESERVE, SpotV7CellKindV1.ACCOUNT_BALANCE),
    }
    if set(leg_shapes) != expected_leg_shapes:
        raise ValueError("restricted Spot V7 requires one input leg and one output leg")
    pool_subjects = {
        row.pre.subject_id
        for row in transitions
        if row.pre.kind is SpotV7CellKindV1.POOL_RESERVE
    }
    if len(pool_subjects) != 1:
        raise ValueError("restricted Spot V7 transitions must update one exact pool")


def _validate_asset_transition_pair(
    effect: SpotV7AssetEffectV1,
    transitions: tuple[SpotV7CellTransitionV1, ...],
) -> tuple[SpotV7CellKindV1, SpotV7CellKindV1]:
    matching = tuple(row for row in transitions if row.pre.asset_id == effect.asset_id)
    if len(matching) != 2:
        raise ValueError("Spot V7 asset must have exactly one debit and one credit")
    debits = tuple(row for row in matching if row.role is SpotV7CellRoleV1.DEBIT)
    credits = tuple(row for row in matching if row.role is SpotV7CellRoleV1.CREDIT)
    if len(debits) != 1 or len(credits) != 1:
        raise ValueError("Spot V7 asset transition directions are incomplete")
    debit, credit = debits[0], credits[0]
    if debit.amount_atoms != effect.amount_atoms or credit.amount_atoms != effect.amount_atoms:
        raise ValueError("Spot V7 asset effect amount disagrees with cell transitions")
    shape = (debit.pre.kind, credit.pre.kind)
    allowed = {
        (SpotV7CellKindV1.ACCOUNT_BALANCE, SpotV7CellKindV1.POOL_RESERVE),
        (SpotV7CellKindV1.POOL_RESERVE, SpotV7CellKindV1.ACCOUNT_BALANCE),
    }
    if shape not in allowed:
        raise ValueError("Spot V7 asset transfer must cross account and pool cells")
    return shape


def _derive_capability_commitment(candidate: _SpotV7SettlementCandidateInputV1) -> str:
    fixed_hashes = (
        candidate.application_id,
        candidate.chain_or_domain_id,
        candidate.verified_program_id,
        candidate.verified_profile_id,
        candidate.verified_program_manifest_root,
        candidate.source_child_claim_binding,
        candidate.source_child_journal_sha256,
        candidate.data_availability_certificate_root,
        candidate.data_root,
        candidate.settlement_effect_plan_commitment,
        candidate.pre_state_root,
        candidate.post_state_root,
        candidate.economic_action_id,
        candidate.authorization_nullifier,
        candidate.authorization_grant_spend_nullifier,
        candidate.cell_transitions_root,
        _sha256_prefixed(candidate.exact_v7_receipt_bytes),
        _sha256_prefixed(candidate.exact_v7_journal_bytes),
        _sha256_prefixed(candidate.exact_plan_b_bytes),
        _sha256_prefixed(candidate.exact_firecracker_execution_record_bytes),
        _sha256_prefixed(candidate.exact_firecracker_output_bytes),
    )
    body = b"".join(
        (
            (1).to_bytes(2, "big"),
            candidate.epoch_id.to_bytes(8, "big"),
            *(_hash_bytes(value, name="Spot V7 capability field") for value in fixed_hashes),
            len(candidate.consumed_object_ids).to_bytes(4, "big"),
            *(
                _hash_bytes(value, name="Spot V7 capability consumed object")
                for value in candidate.consumed_object_ids
            ),
            len(candidate.asset_effects).to_bytes(4, "big"),
            *(
                _hash_bytes(effect.effect_id, name="Spot V7 capability asset effect")
                for effect in candidate.asset_effects
            ),
        )
    )
    return _domain_hash(_CAPABILITY_COMMITMENT_DOMAIN_V1, body)


def _list_root(domain: bytes, identifiers: tuple[str, ...]) -> str:
    body = len(identifiers).to_bytes(4, "big") + b"".join(
        _hash_bytes(identifier, name="Spot V7 list identifier") for identifier in identifiers
    )
    return _domain_hash(domain, body)


def _domain_hash(domain: bytes, body: bytes) -> str:
    hasher = hashlib.sha256()
    hasher.update(len(domain).to_bytes(2, "big"))
    hasher.update(domain)
    hasher.update(body)
    return _hex_hash(hasher.digest())
