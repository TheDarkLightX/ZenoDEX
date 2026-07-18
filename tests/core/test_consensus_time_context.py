from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.consensus_time import (
    U64_MAX,
    ClockAuthorityProfileV1,
    ClockPolicyScheduleV1,
    ClockPolicyV1,
    ExecutionHeaderCoreV1,
    FinalHeaderV1,
    clock_policy_hash_v1,
    clock_policy_schedule_hash_v1,
    derive_child_execution_clock_v1,
    execution_context_hash_v1,
    final_header_hash_v1,
    verify_execution_clock_v1,
    verify_execution_context_v1,
    verify_finalized_block_context_v1,
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
        parent_final_header_hash=_root(1),
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

    with pytest.raises(ValueError, match="derived_epoch mismatch"):
        replace(clock, derived_epoch=clock.derived_epoch + 100)
    with pytest.raises(ValueError, match="consensus_domain_id mismatch"):
        replace(clock, consensus_domain_id="attacker-domain")
    with pytest.raises(ValueError, match="deployment_profile mismatch"):
        replace(clock, deployment_profile=ClockAuthorityProfileV1.TAU_NATIVE_V1)


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
        "parent_final_header_hash": _root(21),
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

    final_a = FinalHeaderV1(
        execution_header_core=core,
        execution_context_hash=context_hash,
        proof_journal_hash=_root(14),
    )
    final_b = replace(final_a, proof_journal_hash=_root(15))

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


def test_clock_and_context_hash_vectors_are_stable() -> None:
    policy = _policy()
    schedule = _schedule(policy)
    core = _core(policy)
    context_hash = execution_context_hash_v1(core)
    final_header = FinalHeaderV1(
        execution_header_core=core,
        execution_context_hash=context_hash,
        proof_journal_hash=_root(14),
    )

    assert clock_policy_hash_v1(policy) == (
        "0xce4b6137cb4f20a88d32da84f61747a04f3000c46d4b5c54e8cc4f3bc708166a"
    )
    assert clock_policy_schedule_hash_v1(schedule) == (
        "0x1c3a8c85d0a5610b1086e9b8cbe4a84f13f3525ec1ab3b1de8e9870d309d603d"
    )
    assert context_hash == ("0xc7344d1c2ca0edcceca6b13af6c8ae61e61e1a4224f1b19d1918e866146b314e")
    assert final_header_hash_v1(final_header) == (
        "0xcbcd50b2cc32848199558ff15e4cfede58d6771eec56eadfbd7e17440a1a6363"
    )


class _FinalityVerifier:
    def __init__(
        self,
        *,
        bind_wrong_header: bool = False,
        signer_set_root: str = _root(2),
        finality_policy_hash: str = _root(14),
    ) -> None:
        self._bind_wrong_header = bind_wrong_header
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
            "finality_policy_hash": self._finality_policy_hash,
            "signer_set_root": self._signer_set_root,
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
    final_header = FinalHeaderV1(
        execution_header_core=verified.core,
        execution_context_hash=verified.execution_context_hash,
        proof_journal_hash=_root(14),
    )

    finalized = verify_finalized_block_context_v1(
        verified_execution_context=verified,
        final_header=final_header,
        certificate=b"verified quorum certificate",
        verifier=_FinalityVerifier(),
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
            final_header=final_header,
            certificate=b"certificate for another header",
            verifier=_FinalityVerifier(bind_wrong_header=True),
        )


@pytest.mark.parametrize(
    ("verifier", "error"),
    (
        (_FinalityVerifier(signer_set_root=_root(30)), "signer_set_root mismatch"),
        (_FinalityVerifier(finality_policy_hash=_root(29)), "finality_policy_hash mismatch"),
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
    final_header = FinalHeaderV1(
        execution_header_core=verified.core,
        execution_context_hash=verified.execution_context_hash,
        proof_journal_hash=_root(15),
    )

    with pytest.raises(ValueError, match=error):
        verify_finalized_block_context_v1(
            verified_execution_context=verified,
            final_header=final_header,
            certificate=b"certificate",
            verifier=verifier,
        )
