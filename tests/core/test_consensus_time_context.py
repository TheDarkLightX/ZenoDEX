from __future__ import annotations

from dataclasses import fields, replace

import pytest

from src.core.consensus_time import (
    U64_MAX,
    ClockAuthorityProfileV1,
    ClockPolicyScheduleV1,
    ClockPolicyV1,
    ExecutionHeaderCoreV1,
    FinalHeaderV1,
    FinalizedBlockContextV1,
    ProofJournalBindingV1,
    VerifiedExecutionClockV1,
    VerifiedExecutionContextV1,
    VerifiedProofJournalBindingV1,
    build_final_header_v1,
    clock_policy_hash_v1,
    clock_policy_schedule_hash_v1,
    derive_child_execution_clock_v1,
    execution_context_hash_v1,
    final_header_hash_v1,
    proof_journal_binding_hash_v1,
    verify_execution_clock_v1,
    verify_execution_context_v1,
    verify_finalized_block_context_v1,
    verify_proof_journal_binding_v1,
)
from src.state.canonical import domain_sep_bytes, encode_bytes, sha256_hex


def _root(byte: int) -> str:
    return "0x" + f"{byte:02x}" * 32


def _policy(
    *,
    activation_height: int = 10,
    epoch_base: int = 7,
    blocks_per_epoch: int = 5,
) -> ClockPolicyV1:
    return ClockPolicyV1(
        clock_policy_id="HEIGHT_ONLY_V1",
        clock_policy_version=1,
        chain_id="zenodex-testnet-1",
        deployment_profile=ClockAuthorityProfileV1.ZENO_LEDGER_TAU_CHECKPOINTED_V1,
        consensus_domain_id="zeno-ledger:testnet-1",
        activation_height=activation_height,
        epoch_base=epoch_base,
        blocks_per_epoch=blocks_per_epoch,
    )


def _schedule(*policies: ClockPolicyV1) -> ClockPolicyScheduleV1:
    selected = policies or (_policy(),)
    return ClockPolicyScheduleV1(policies=tuple(selected))


def _core(policy: ClockPolicyV1, *, height: int = 10) -> ExecutionHeaderCoreV1:
    schedule = _schedule(policy)
    return ExecutionHeaderCoreV1(
        schema_version=1,
        chain_id="zenodex-testnet-1",
        consensus_domain_id=policy.consensus_domain_id,
        deployment_profile=policy.deployment_profile,
        height=height,
        derived_epoch=policy.epoch_at_height(height),
        parent_header_hash=_root(1),
        sequencer_or_validator_set_hash=_root(2),
        ingress_root=_root(3),
        tx_root=_root(4),
        pre_state_root=_root(5),
        post_state_root=_root(6),
        app_hash=_root(7),
        effect_plan_hash=_root(13),
        evidence_root=_root(8),
        body_root=_root(9),
        data_availability_root=_root(10),
        clock_policy_hash=clock_policy_hash_v1(policy),
        clock_policy_schedule_hash=clock_policy_schedule_hash_v1(schedule),
        finality_policy_hash=_root(14),
        config_digest=_root(11),
        module_versions_digest=_root(12),
    )


class _ProofVerifier:
    def __init__(
        self,
        *,
        raw_journal_hash: str = _root(41),
        bind_wrong_context: bool = False,
        bind_wrong_artifact: bool = False,
        bind_wrong_policy: bool = False,
    ) -> None:
        self._raw_journal_hash = raw_journal_hash
        self._bind_wrong_context = bind_wrong_context
        self._bind_wrong_artifact = bind_wrong_artifact
        self._bind_wrong_policy = bind_wrong_policy

    def verify_proof_journal_v1(
        self,
        *,
        proof_artifact: bytes,
        expected_execution_context_hash: str,
    ) -> dict[str, object]:
        artifact_hash = sha256_hex(
            domain_sep_bytes("proof_artifact", version=1)
            + encode_bytes(proof_artifact)
        )
        return {
            "execution_context_hash": (
                _root(45)
                if self._bind_wrong_context
                else expected_execution_context_hash
            ),
            "proof_metadata_hash": _root(40),
            "raw_journal_hash": self._raw_journal_hash,
            "proof_artifact_hash": (
                _root(46) if self._bind_wrong_artifact else artifact_hash
            ),
            "proof_verifier_policy_hash": (
                _root(47) if self._bind_wrong_policy else _root(44)
            ),
        }


def _verified_context(policy: ClockPolicyV1) -> VerifiedExecutionContextV1:
    schedule = _schedule(policy)
    return verify_execution_context_v1(
        core=_core(policy),
        schedule=schedule,
        expected_schedule_hash=clock_policy_schedule_hash_v1(schedule),
    )


def _verified_proof(
    verified_context: VerifiedExecutionContextV1,
    *,
    proof_artifact: bytes = b"authenticated proof artifact",
    verifier: _ProofVerifier | None = None,
) -> VerifiedProofJournalBindingV1:
    return verify_proof_journal_binding_v1(
        verified_execution_context=verified_context,
        proof_artifact=proof_artifact,
        verifier=verifier or _ProofVerifier(),
        expected_proof_verifier_policy_hash=_root(44),
    )


@pytest.mark.parametrize(
    ("height", "expected_epoch"),
    ((10, 7), (14, 7), (15, 8), (19, 8), (20, 9)),
)
def test_height_only_epoch_activation_and_boundary_bva(
    height: int,
    expected_epoch: int,
) -> None:
    assert _policy().epoch_at_height(height) == expected_epoch


def test_height_only_epoch_rejects_pre_activation_and_invalid_widths() -> None:
    with pytest.raises(ValueError, match="before clock policy activation"):
        _policy().epoch_at_height(9)
    with pytest.raises(ValueError, match="blocks_per_epoch must be positive"):
        _policy(blocks_per_epoch=0)
    with pytest.raises(TypeError, match="blocks_per_epoch must be an int"):
        _policy(blocks_per_epoch=True)  # type: ignore[arg-type]


def test_clock_and_header_versions_reject_bool_alias_for_one() -> None:
    with pytest.raises(TypeError, match="clock_policy_version must be an int"):
        replace(_policy(), clock_policy_version=True)

    with pytest.raises(TypeError, match="schema_version must be an int"):
        replace(_core(_policy()), schema_version=True)


def test_height_only_epoch_handles_one_and_u64_max_boundaries() -> None:
    one = _policy(activation_height=0, epoch_base=0, blocks_per_epoch=1)
    assert one.epoch_at_height(U64_MAX) == U64_MAX

    maximum = _policy(
        activation_height=0,
        epoch_base=0,
        blocks_per_epoch=U64_MAX,
    )
    assert maximum.epoch_at_height(U64_MAX - 1) == 0
    assert maximum.epoch_at_height(U64_MAX) == 1

    overflowing = _policy(
        activation_height=0,
        epoch_base=U64_MAX,
        blocks_per_epoch=1,
    )
    with pytest.raises(ValueError, match="derived epoch overflows u64"):
        overflowing.epoch_at_height(1)


def test_policy_upgrade_requires_epoch_continuity() -> None:
    previous = _policy(activation_height=0, epoch_base=3, blocks_per_epoch=5)
    continuous = _policy(activation_height=10, epoch_base=5, blocks_per_epoch=8)
    previous.require_continuous_upgrade(continuous)

    discontinuous = replace(continuous, epoch_base=6)
    with pytest.raises(ValueError, match="clock policy epoch discontinuity"):
        previous.require_continuous_upgrade(discontinuous)


def test_governed_schedule_selects_successor_exactly_at_activation() -> None:
    previous = _policy(activation_height=10, epoch_base=7, blocks_per_epoch=5)
    successor = _policy(activation_height=20, epoch_base=9, blocks_per_epoch=8)
    schedule = _schedule(previous, successor)

    assert schedule.active_policy_at_height(19) is previous
    assert schedule.active_policy_at_height(20) is successor

    with pytest.raises(ValueError, match="epoch boundary"):
        _schedule(previous, replace(successor, activation_height=19))


def test_execution_clock_rejects_uncommitted_schedule_substitution() -> None:
    governed = _schedule(_policy())
    substituted = _schedule(_policy(blocks_per_epoch=1))

    with pytest.raises(ValueError, match="schedule hash mismatch"):
        verify_execution_clock_v1(
            chain_id="zenodex-testnet-1",
            height=15,
            schedule=substituted,
            expected_schedule_hash=clock_policy_schedule_hash_v1(governed),
        )


def test_verified_execution_clock_rejects_forged_derived_facts() -> None:
    policy = _policy()
    schedule = _schedule(policy)
    clock = verify_execution_clock_v1(
        chain_id=policy.chain_id,
        height=15,
        schedule=schedule,
        expected_schedule_hash=clock_policy_schedule_hash_v1(schedule),
    )

    def validate_forged(**changes: object) -> None:
        forged = object.__new__(VerifiedExecutionClockV1)
        for field in fields(clock):
            object.__setattr__(
                forged,
                field.name,
                changes.get(field.name, getattr(clock, field.name)),
            )
        forged.__post_init__()

    with pytest.raises(ValueError, match="derived_epoch mismatch"):
        validate_forged(derived_epoch=clock.derived_epoch + 100)
    with pytest.raises(ValueError, match="consensus_domain_id mismatch"):
        validate_forged(consensus_domain_id="attacker-domain")
    with pytest.raises(ValueError, match="deployment_profile mismatch"):
        validate_forged(deployment_profile=ClockAuthorityProfileV1.TAU_NATIVE_V1)


def test_clock_policy_schedule_decoder_is_strict_and_roundtrips() -> None:
    schedule = _schedule(_policy())
    assert ClockPolicyScheduleV1.from_obj(schedule.to_obj()) == schedule

    unknown = dict(schedule.to_obj())
    unknown["caller_epoch"] = 99
    with pytest.raises(ValueError, match="fields mismatch"):
        ClockPolicyScheduleV1.from_obj(unknown)


def test_verified_execution_context_rejects_caller_epoch() -> None:
    policy = _policy()
    schedule = _schedule(policy)
    schedule_hash = clock_policy_schedule_hash_v1(schedule)
    core = _core(policy)
    verified = verify_execution_context_v1(
        core=core,
        schedule=schedule,
        expected_schedule_hash=schedule_hash,
    )
    assert verified.derived_epoch == 7

    with pytest.raises(ValueError, match="derived_epoch mismatch"):
        verify_execution_context_v1(
            core=replace(core, derived_epoch=8),
            schedule=schedule,
            expected_schedule_hash=schedule_hash,
        )
    assert "time_ms_or_zero" not in core.to_obj()


def test_execution_context_rejects_zero_parent_outside_genesis() -> None:
    policy = _policy()
    with pytest.raises(ValueError, match="non-genesis.*must be non-zero"):
        replace(_core(policy), parent_header_hash=_root(0))

    genesis_policy = _policy(
        activation_height=0,
        epoch_base=0,
        blocks_per_epoch=5,
    )
    with pytest.raises(ValueError, match="genesis.*must be zero"):
        replace(
            _core(genesis_policy, height=1),
            height=0,
            derived_epoch=0,
            parent_header_hash=_root(1),
        )


def test_pre_execution_clock_is_height_derived_and_has_no_finality_claim() -> None:
    policy = _policy()
    clock = verify_execution_clock_v1(
        chain_id="zenodex-testnet-1",
        height=15,
        schedule=_schedule(policy),
        expected_schedule_hash=clock_policy_schedule_hash_v1(_schedule(policy)),
    )

    assert clock.height == 15
    assert clock.derived_epoch == 8
    assert not hasattr(clock, "final_header_hash")
    assert not hasattr(clock, "finality_certificate")


def test_context_hash_binds_every_execution_field_and_excludes_proof_cycle() -> None:
    policy = _policy()
    core = _core(policy)
    context_hash = execution_context_hash_v1(core)
    mutations = {
        "chain_id": "zenodex-testnet-2",
        "consensus_domain_id": "zeno-ledger:testnet-2",
        "deployment_profile": ClockAuthorityProfileV1.ZENO_LEDGER_SOVEREIGN_V1,
        "height": 11,
        "derived_epoch": 8,
        "parent_header_hash": _root(21),
        "sequencer_or_validator_set_hash": _root(22),
        "ingress_root": _root(23),
        "tx_root": _root(24),
        "pre_state_root": _root(25),
        "post_state_root": _root(26),
        "app_hash": _root(27),
        "effect_plan_hash": _root(28),
        "evidence_root": _root(29),
        "body_root": _root(30),
        "data_availability_root": _root(31),
        "clock_policy_hash": _root(32),
        "clock_policy_schedule_hash": _root(35),
        "finality_policy_hash": _root(36),
        "config_digest": _root(33),
        "module_versions_digest": _root(34),
    }
    for field_name, value in mutations.items():
        mutated = replace(core, **{field_name: value})
        assert execution_context_hash_v1(mutated) != context_hash, field_name

    verified = _verified_context(policy)
    proof_a = _verified_proof(
        verified,
        proof_artifact=b"proof-a",
        verifier=_ProofVerifier(raw_journal_hash=_root(41)),
    )
    proof_b = _verified_proof(
        verified,
        proof_artifact=b"proof-b",
        verifier=_ProofVerifier(raw_journal_hash=_root(42)),
    )
    final_a = build_final_header_v1(
        verified_execution_context=verified,
        verified_proof_binding=proof_a,
    )
    final_b = build_final_header_v1(
        verified_execution_context=verified,
        verified_proof_binding=proof_b,
    )

    assert execution_context_hash_v1(final_a.execution_header_core) == context_hash
    assert execution_context_hash_v1(final_b.execution_header_core) == context_hash
    assert final_header_hash_v1(final_a) != final_header_hash_v1(final_b)
    assert "proof_journal_hash" not in final_a.execution_header_core.to_obj()
    assert "signature_set_root" not in final_a.to_obj()
    assert "finality_certificate" not in final_a.to_obj()


def test_execution_context_binds_the_complete_schedule_hash() -> None:
    current = _policy(activation_height=0, epoch_base=0, blocks_per_epoch=5)
    successor_a = _policy(activation_height=10, epoch_base=2, blocks_per_epoch=5)
    successor_b = _policy(activation_height=10, epoch_base=2, blocks_per_epoch=10)
    schedule_a = _schedule(current, successor_a)
    schedule_b = _schedule(current, successor_b)
    core_a = replace(
        _core(current, height=5),
        clock_policy_schedule_hash=clock_policy_schedule_hash_v1(schedule_a),
    )

    verified_a = verify_execution_context_v1(
        core=core_a,
        schedule=schedule_a,
        expected_schedule_hash=clock_policy_schedule_hash_v1(schedule_a),
    )
    with pytest.raises(ValueError, match="clock_policy_schedule_hash mismatch"):
        verify_execution_context_v1(
            core=core_a,
            schedule=schedule_b,
            expected_schedule_hash=clock_policy_schedule_hash_v1(schedule_b),
        )

    core_b = replace(
        core_a,
        clock_policy_schedule_hash=clock_policy_schedule_hash_v1(schedule_b),
    )
    assert execution_context_hash_v1(core_b) != verified_a.execution_context_hash


def test_execution_and_final_headers_reject_missing_effect_or_proof_commitments() -> None:
    policy = _policy()
    core = _core(policy)
    with pytest.raises(ValueError, match="effect_plan_hash must be non-zero"):
        replace(core, effect_plan_hash=_root(0))
    with pytest.raises(TypeError):
        FinalHeaderV1(
            execution_header_core=core,
            execution_context_hash=execution_context_hash_v1(core),
            proof_journal_hash=_root(0),
        )  # type: ignore[call-arg]


def test_proof_journal_binding_is_acyclic_and_context_specific() -> None:
    context_hash = execution_context_hash_v1(_core(_policy()))
    binding = ProofJournalBindingV1(
        schema_version=1,
        execution_context_hash=context_hash,
        proof_metadata_hash=_root(40),
        raw_journal_hash=_root(41),
    )
    binding_hash = proof_journal_binding_hash_v1(binding)

    assert binding_hash != proof_journal_binding_hash_v1(
        replace(binding, execution_context_hash=_root(42))
    )
    assert binding_hash != proof_journal_binding_hash_v1(
        replace(binding, raw_journal_hash=_root(43))
    )
    assert "proof_journal_hash" not in binding.to_obj()
    assert "final_header_hash" not in binding.to_obj()


def test_proof_journal_binding_rejects_zero_or_bool_aliases() -> None:
    with pytest.raises(ValueError, match="raw_journal_hash must be non-zero"):
        ProofJournalBindingV1(
            schema_version=1,
            execution_context_hash=_root(1),
            proof_metadata_hash=_root(2),
            raw_journal_hash=_root(0),
        )
    with pytest.raises(TypeError, match="schema_version must be an int"):
        ProofJournalBindingV1(
            schema_version=True,  # type: ignore[arg-type]
            execution_context_hash=_root(1),
            proof_metadata_hash=_root(2),
            raw_journal_hash=_root(3),
        )


def test_verified_proof_binding_rejects_substituted_authority_facts() -> None:
    verified = _verified_context(_policy())
    with pytest.raises(ValueError, match="execution_context_hash mismatch"):
        _verified_proof(
            verified,
            verifier=_ProofVerifier(bind_wrong_context=True),
        )
    with pytest.raises(ValueError, match="proof_artifact_hash mismatch"):
        _verified_proof(
            verified,
            verifier=_ProofVerifier(bind_wrong_artifact=True),
        )
    with pytest.raises(ValueError, match="policy hash mismatch"):
        _verified_proof(
            verified,
            verifier=_ProofVerifier(bind_wrong_policy=True),
        )


def test_clock_and_context_hash_vectors_are_stable() -> None:
    policy = _policy()
    schedule = _schedule(policy)
    core = _core(policy)
    context_hash = execution_context_hash_v1(core)
    verified = _verified_context(policy)
    verified_proof = _verified_proof(verified)
    final_header = build_final_header_v1(
        verified_execution_context=verified,
        verified_proof_binding=verified_proof,
    )

    assert clock_policy_hash_v1(policy) == (
        "0xce4b6137cb4f20a88d32da84f61747a04f3000c46d4b5c54e8cc4f3bc708166a"
    )
    assert clock_policy_schedule_hash_v1(schedule) == (
        "0x1c3a8c85d0a5610b1086e9b8cbe4a84f13f3525ec1ab3b1de8e9870d309d603d"
    )
    assert context_hash == ("0x34b42c51a3809d59e19c7c6b8bbaa473565fc2771b9df00082a51e109f6f49ac")
    assert final_header_hash_v1(final_header) == (
        "0x6874ebdc432369b1970dce6068cd65181cf7164eaf8d284dd94749b50a1364a7"
    )


class _FinalityVerifier:
    def __init__(
        self,
        *,
        bind_wrong_header: bool = False,
        bind_wrong_signer_set: bool = False,
        bind_wrong_policy: bool = False,
        signer_set_root: str = _root(2),
        finality_policy_hash: str = _root(14),
    ) -> None:
        self._bind_wrong_header = bind_wrong_header
        self._bind_wrong_signer_set = bind_wrong_signer_set
        self._bind_wrong_policy = bind_wrong_policy
        self._signer_set_root = signer_set_root
        self._finality_policy_hash = finality_policy_hash

    def verify_finality_certificate_v1(
        self,
        *,
        final_header_hash: str,
        certificate: bytes,
    ) -> dict[str, object]:
        bound_hash = _root(31) if self._bind_wrong_header else final_header_hash
        return {
            "final_header_hash": bound_hash,
            "certificate_hash": sha256_hex(
                domain_sep_bytes("finality_certificate", version=1) + encode_bytes(certificate)
            ),
            "finality_policy_hash": (
                _root(28) if self._bind_wrong_policy else self._finality_policy_hash
            ),
            "signer_set_root": (
                _root(30) if self._bind_wrong_signer_set else self._signer_set_root
            ),
            "signed_power": 3,
            "total_power": 4,
        }


def test_finalized_context_requires_verified_certificate_bound_to_header() -> None:
    policy = _policy()
    schedule = _schedule(policy)
    verified = verify_execution_context_v1(
        core=_core(policy),
        schedule=schedule,
        expected_schedule_hash=clock_policy_schedule_hash_v1(schedule),
    )
    verified_proof = _verified_proof(verified)
    final_header = build_final_header_v1(
        verified_execution_context=verified,
        verified_proof_binding=verified_proof,
    )

    finalized = verify_finalized_block_context_v1(
        verified_execution_context=verified,
        verified_proof_binding=verified_proof,
        final_header=final_header,
        certificate=b"verified quorum certificate",
        verifier=_FinalityVerifier(),
        expected_finality_policy_hash=_root(14),
    )
    assert finalized.final_header_hash == final_header_hash_v1(final_header)
    child_clock = derive_child_execution_clock_v1(
        finalized_parent=finalized,
        schedule=schedule,
        expected_schedule_hash=clock_policy_schedule_hash_v1(schedule),
    )
    assert child_clock.height == verified.core.height + 1

    with pytest.raises(ValueError, match="final_header_hash mismatch"):
        verify_finalized_block_context_v1(
            verified_execution_context=verified,
            verified_proof_binding=verified_proof,
            final_header=final_header,
            certificate=b"certificate for another header",
            verifier=_FinalityVerifier(bind_wrong_header=True),
            expected_finality_policy_hash=_root(14),
        )

    with pytest.raises(ValueError, match="signer_set_root mismatch"):
        verify_finalized_block_context_v1(
            verified_execution_context=verified,
            verified_proof_binding=verified_proof,
            final_header=final_header,
            certificate=b"certificate for another signer set",
            verifier=_FinalityVerifier(bind_wrong_signer_set=True),
            expected_finality_policy_hash=_root(14),
        )

    with pytest.raises(ValueError, match="policy hash mismatch"):
        verify_finalized_block_context_v1(
            verified_execution_context=verified,
            verified_proof_binding=verified_proof,
            final_header=final_header,
            certificate=b"certificate under another policy",
            verifier=_FinalityVerifier(bind_wrong_policy=True),
            expected_finality_policy_hash=_root(14),
        )


def test_verified_authority_values_cannot_be_constructed_directly() -> None:
    policy = _policy()
    core = _core(policy)
    with pytest.raises(TypeError):
        VerifiedExecutionClockV1(  # type: ignore[call-arg]
            chain_id=policy.chain_id,
            consensus_domain_id=policy.consensus_domain_id,
            deployment_profile=policy.deployment_profile,
            height=core.height,
            derived_epoch=core.derived_epoch,
            clock_policy_hash=core.clock_policy_hash,
        )
    with pytest.raises(TypeError):
        VerifiedExecutionContextV1(  # type: ignore[call-arg]
            core=core,
            execution_context_hash=execution_context_hash_v1(core),
        )
    with pytest.raises(TypeError):
        VerifiedProofJournalBindingV1(  # type: ignore[call-arg]
            binding=object(),
            binding_hash=_root(1),
            proof_artifact_hash=_root(2),
            proof_verifier_policy_hash=_root(3),
        )
    with pytest.raises(TypeError):
        FinalHeaderV1(  # type: ignore[call-arg]
            execution_header_core=core,
            execution_context_hash=execution_context_hash_v1(core),
            proof_journal_hash=_root(4),
        )
    with pytest.raises(TypeError):
        FinalizedBlockContextV1(  # type: ignore[call-arg]
            verified_execution_context=object(),
            verified_proof_binding=object(),
            final_header=object(),
            final_header_hash=_root(1),
            _finality_facts=object(),
        )


@pytest.mark.parametrize(
    ("verifier", "error"),
    (
        (_FinalityVerifier(signer_set_root=_root(30)), "signer_set_root mismatch"),
        (_FinalityVerifier(finality_policy_hash=_root(29)), "policy hash mismatch"),
    ),
)
def test_finalized_context_binds_signer_set_and_finality_policy(
    verifier: _FinalityVerifier,
    error: str,
) -> None:
    policy = _policy()
    schedule = _schedule(policy)
    verified = verify_execution_context_v1(
        core=_core(policy),
        schedule=schedule,
        expected_schedule_hash=clock_policy_schedule_hash_v1(schedule),
    )
    verified_proof = _verified_proof(verified)
    final_header = build_final_header_v1(
        verified_execution_context=verified,
        verified_proof_binding=verified_proof,
    )

    with pytest.raises(ValueError, match=error):
        verify_finalized_block_context_v1(
            verified_execution_context=verified,
            verified_proof_binding=verified_proof,
            final_header=final_header,
            certificate=b"certificate",
            verifier=verifier,
            expected_finality_policy_hash=_root(14),
        )
