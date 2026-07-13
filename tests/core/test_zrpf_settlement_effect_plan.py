from __future__ import annotations

import copy
import inspect
from dataclasses import replace

import pytest

from src.core.zrpf_settlement_effect_plan import (
    MAX_U128,
    AssetEffectKindV1,
    AssetEffectV1,
    AuthorizationConsumptionV1,
    CarryEffectKindV1,
    CarryEffectV1,
    LedgerCellWriteV1,
    MessageEffectKindV1,
    MessageEffectV1,
    ProposedSettlementEffectPlanV1,
    RewardEffectV1,
    SettlementEffectPlanRejectCodeV1,
    SettlementEffectPlanValidationError,
    authorization_consumption_nullifier_v1,
    authorization_grant_spend_nullifier_v1,
    build_settlement_effect_plan_v1,
)


def _hash(index: int) -> str:
    assert index > 0
    return f"0x{index:064x}"


def _repeated_byte_hash(byte: int) -> str:
    assert 0 < byte <= 255
    return "0x" + f"{byte:02x}" * 32


def _authorization(
    *,
    action_id: str = _hash(10),
    application_id: str = _hash(1),
    domain_id: str = _hash(2),
    subject_id: str = _hash(20),
    grant_id: str = _hash(21),
    scope_id: str = _hash(22),
    nonce: int = 7,
    pre_state_root: str = _hash(3),
) -> AuthorizationConsumptionV1:
    nullifier = authorization_consumption_nullifier_v1(
        application_id=application_id,
        chain_or_domain_id=domain_id,
        economic_action_id=action_id,
        authorization_subject_id=subject_id,
        authorization_grant_id=grant_id,
        authorization_scope_id=scope_id,
        authorization_nonce=nonce,
        action_pre_state_root=pre_state_root,
    )
    return AuthorizationConsumptionV1(
        application_id=application_id,
        chain_or_domain_id=domain_id,
        economic_action_id=action_id,
        authorization_subject_id=subject_id,
        authorization_grant_id=grant_id,
        authorization_scope_id=scope_id,
        authorization_nonce=nonce,
        action_pre_state_root=pre_state_root,
        authorization_nullifier=nullifier,
    )


def _proposal(**overrides: object) -> ProposedSettlementEffectPlanV1:
    action_a = _hash(10)
    action_b = _hash(11)
    authorization = _authorization(action_id=action_b)
    values: dict[str, object] = {
        "application_id": _hash(1),
        "chain_or_domain_id": _hash(2),
        "epoch_id": 9,
        "source_root_journal_hash": _hash(30),
        "public_policy_hash": _hash(31),
        "pre_state_root": _hash(3),
        "post_state_root": _hash(4),
        "economic_action_ids": (action_b, action_a),
        "ledger_cell_writes": (
            LedgerCellWriteV1(
                economic_action_id=action_b,
                cell_key=_hash(43),
                pre_value_hash=_hash(44),
                post_value_hash=_hash(45),
            ),
            LedgerCellWriteV1(
                economic_action_id=action_a,
                cell_key=_hash(40),
                pre_value_hash=_hash(41),
                post_value_hash=_hash(42),
            ),
        ),
        "asset_effects": (
            AssetEffectV1(
                kind=AssetEffectKindV1.AUTHORIZED_MINT,
                economic_action_id=action_b,
                asset_id=_hash(61),
                debit_atoms=0,
                credit_atoms=50,
                authorized_mint_atoms=50,
                authorized_burn_atoms=0,
                authority_scope_id=authorization.authorization_scope_id,
                authorization_nullifier=authorization.authorization_nullifier,
            ),
            AssetEffectV1(
                kind=AssetEffectKindV1.ORDINARY_TRANSFER,
                economic_action_id=action_a,
                asset_id=_hash(60),
                debit_atoms=100,
                credit_atoms=100,
                authorized_mint_atoms=0,
                authorized_burn_atoms=0,
            ),
        ),
        "authorization_consumptions": (authorization,),
        "message_effects": (),
        "carry_effects": (),
        "reward_effects": (),
    }
    values.update(overrides)
    return ProposedSettlementEffectPlanV1(**values)  # type: ignore[arg-type]


def _proposal_with_pre_state_root(pre_state_root: str) -> ProposedSettlementEffectPlanV1:
    proposal = _proposal()
    mint = proposal.asset_effects[0]
    authorization = _authorization(
        action_id=mint.economic_action_id,
        pre_state_root=pre_state_root,
    )
    rebound_mint = replace(
        mint,
        authorization_nullifier=authorization.authorization_nullifier,
    )
    return replace(
        proposal,
        pre_state_root=pre_state_root,
        asset_effects=(rebound_mint, proposal.asset_effects[1]),
        authorization_consumptions=(authorization,),
    )


def _assert_reject(
    proposal: ProposedSettlementEffectPlanV1,
    code: SettlementEffectPlanRejectCodeV1,
) -> SettlementEffectPlanValidationError:
    with pytest.raises(SettlementEffectPlanValidationError) as caught:
        build_settlement_effect_plan_v1(proposal)
    assert caught.value.code is code
    return caught.value


def test_valid_plan_is_canonical_and_binds_all_derived_roots() -> None:
    plan = build_settlement_effect_plan_v1(_proposal())

    assert plan.economic_action_ids == tuple(sorted(plan.economic_action_ids))
    assert plan.ledger_cell_writes == tuple(
        sorted(plan.ledger_cell_writes, key=lambda row: row.cell_key)
    )
    assert plan.asset_effects == tuple(sorted(plan.asset_effects, key=lambda row: row.effect_id))
    assert plan.authorization_consumptions == tuple(
        sorted(
            plan.authorization_consumptions,
            key=lambda row: row.authorization_nullifier,
        )
    )
    assert plan.economic_action_ids_root.startswith("0x")
    assert plan.authorization_nullifiers_root.startswith("0x")
    assert plan.ledger_cell_writes_root.startswith("0x")
    assert plan.asset_effects_root.startswith("0x")
    assert plan.commitment.startswith("0x")
    assert len(plan.commitment) == 66


def test_canonical_plan_and_nullifier_vectors_are_stable() -> None:
    authorization = _authorization()
    plan = build_settlement_effect_plan_v1(_proposal())

    assert authorization.authorization_nullifier == (
        "0x04da42ae3e508ff068a07e03a186250155dc3145d9d28320b0f90b83d1baa3b3"
    )
    assert len(plan.canonical_bytes()) == 4_429
    assert plan.commitment == ("0x62b5fe3f2f5772273c36d58a77c139bd91e8d6b6f216be6a85c29669a1d7f854")
    assert plan.economic_action_ids_root == (
        "0x4855086eac66dcd81ca8941a79b90c1f993cedaa51f6d58375b6f5528a9a15e6"
    )
    assert plan.authorization_nullifiers_root == (
        "0x02bb56f56831529081aa10c3bc03f4adb22ca983ee77464b872944b7a8cbbd6e"
    )
    assert plan.authorization_grant_spend_nullifiers_root == (
        "0x9e69c0e1ed951de492f893473f373bdc4b4883cc4f061a55d7fbff8ae337bfc9"
    )
    assert plan.asset_effects_root == (
        "0x644305fb7a13a4c0f11558f6e43f1d6b5cf1d60fbf03ee245a3e60984b89b2d1"
    )


def test_authorization_nullifier_matches_rust_economic_action_vector() -> None:
    action_id = "0x8613bdc85d4618ed79c0d927c107b4682423091f8d1856251ad9e355a6525143"

    nullifier = authorization_consumption_nullifier_v1(
        application_id=_repeated_byte_hash(1),
        chain_or_domain_id=_repeated_byte_hash(2),
        economic_action_id=action_id,
        authorization_subject_id=_repeated_byte_hash(4),
        authorization_grant_id=_repeated_byte_hash(9),
        authorization_scope_id=_repeated_byte_hash(5),
        authorization_nonce=17,
        action_pre_state_root=_repeated_byte_hash(6),
    )

    assert nullifier == ("0x03c908ee0fd74c394865c11453a51a0b059bfb35ceb62956beb00c00d49ff913")


def test_grant_spend_nullifier_matches_rust_vector() -> None:
    nullifier = authorization_grant_spend_nullifier_v1(
        application_id=_repeated_byte_hash(1),
        chain_or_domain_id=_repeated_byte_hash(2),
        authorization_grant_id=_repeated_byte_hash(9),
        authorization_nonce=17,
    )

    assert nullifier == ("0x1f5970f7f3ba7ec6dd111b488f0229256aa683c032111f950e08293c7ac63c38")


def test_grant_spend_identity_excludes_action_subject_scope_and_pre_state() -> None:
    first = _authorization()
    changed_action_context = _authorization(
        action_id=_hash(220),
        subject_id=_hash(221),
        scope_id=_hash(222),
        pre_state_root=_hash(223),
    )

    assert (
        changed_action_context.authorization_grant_spend_nullifier
        == first.authorization_grant_spend_nullifier
    )
    assert changed_action_context.authorization_nullifier != first.authorization_nullifier


def test_plan_commitment_is_invariant_under_all_input_tuple_permutations() -> None:
    proposal = _proposal()
    reversed_proposal = replace(
        proposal,
        economic_action_ids=tuple(reversed(proposal.economic_action_ids)),
        ledger_cell_writes=tuple(reversed(proposal.ledger_cell_writes)),
        asset_effects=tuple(reversed(proposal.asset_effects)),
        authorization_consumptions=tuple(reversed(proposal.authorization_consumptions)),
    )

    first = build_settlement_effect_plan_v1(proposal)
    second = build_settlement_effect_plan_v1(reversed_proposal)

    assert first == second
    assert first.canonical_bytes() == second.canonical_bytes()
    assert first.commitment == second.commitment


def test_pre_and_post_state_roots_are_commitment_bearing() -> None:
    base = build_settlement_effect_plan_v1(_proposal())
    changed_pre = build_settlement_effect_plan_v1(_proposal_with_pre_state_root(_hash(70)))
    changed_post = build_settlement_effect_plan_v1(_proposal(post_state_root=_hash(71)))

    assert changed_pre.commitment != base.commitment
    assert changed_post.commitment != base.commitment
    assert changed_pre.commitment != changed_post.commitment


def test_single_atom_asset_imbalance_rejects() -> None:
    proposal = _proposal()
    ordinary = proposal.asset_effects[1]
    bad = replace(ordinary, credit_atoms=ordinary.credit_atoms - 1)

    _assert_reject(
        replace(proposal, asset_effects=(proposal.asset_effects[0], bad)),
        SettlementEffectPlanRejectCodeV1.ASSET_CONSERVATION_VIOLATION,
    )


def test_per_asset_accumulation_rejects_u128_overflow() -> None:
    proposal = _proposal()
    action = proposal.economic_action_ids[0]
    asset = _hash(80)
    overflowing = (
        AssetEffectV1(
            kind=AssetEffectKindV1.ORDINARY_TRANSFER,
            economic_action_id=action,
            asset_id=asset,
            debit_atoms=MAX_U128,
            credit_atoms=MAX_U128,
            authorized_mint_atoms=0,
            authorized_burn_atoms=0,
        ),
        AssetEffectV1(
            kind=AssetEffectKindV1.ORDINARY_TRANSFER,
            economic_action_id=action,
            asset_id=asset,
            debit_atoms=1,
            credit_atoms=1,
            authorized_mint_atoms=0,
            authorized_burn_atoms=0,
        ),
    )

    _assert_reject(
        replace(
            proposal,
            economic_action_ids=(action,),
            ledger_cell_writes=(proposal.ledger_cell_writes[0],),
            asset_effects=overflowing,
            authorization_consumptions=(),
        ),
        SettlementEffectPlanRejectCodeV1.ARITHMETIC_OVERFLOW,
    )


def test_authorized_mint_requires_matching_consumption() -> None:
    proposal = _proposal(authorization_consumptions=())

    _assert_reject(
        proposal,
        SettlementEffectPlanRejectCodeV1.MISSING_AUTHORIZATION_CONSUMPTION,
    )


def test_authorized_burn_shape_is_accepted_with_one_consumption() -> None:
    proposal = _proposal()
    mint = proposal.asset_effects[0]
    burn = replace(
        mint,
        kind=AssetEffectKindV1.AUTHORIZED_BURN,
        debit_atoms=mint.authorized_mint_atoms,
        credit_atoms=0,
        authorized_mint_atoms=0,
        authorized_burn_atoms=mint.authorized_mint_atoms,
    )

    plan = build_settlement_effect_plan_v1(
        replace(proposal, asset_effects=(burn, proposal.asset_effects[1]))
    )

    assert plan.asset_effects[1].authorized_burn_atoms == 50
    assert plan.asset_effects[1].authorized_mint_atoms == 0


def test_detached_authorization_consumption_rejects() -> None:
    proposal = _proposal()
    detached = _authorization(
        action_id=proposal.economic_action_ids[0],
        scope_id=_hash(90),
        nonce=91,
    )

    _assert_reject(
        replace(
            proposal,
            authorization_consumptions=proposal.authorization_consumptions + (detached,),
        ),
        SettlementEffectPlanRejectCodeV1.DETACHED_AUTHORIZATION_CONSUMPTION,
    )


def test_one_authorization_consumption_cannot_back_two_supply_effects() -> None:
    proposal = _proposal()
    minted = proposal.asset_effects[0]
    second_mint = replace(
        minted,
        asset_id=_hash(93),
        credit_atoms=1,
        authorized_mint_atoms=1,
    )

    _assert_reject(
        replace(proposal, asset_effects=proposal.asset_effects + (second_mint,)),
        SettlementEffectPlanRejectCodeV1.AUTHORIZATION_CONSUMPTION_REUSED,
    )


def test_grant_and_nonce_cannot_be_freshened_with_a_different_action() -> None:
    proposal = _proposal()
    ordinary = proposal.asset_effects[1]
    second = _authorization(action_id=ordinary.economic_action_id)
    reward_asset_effect = replace(
        ordinary,
        kind=AssetEffectKindV1.AUTHORIZED_REWARD,
        authority_scope_id=second.authorization_scope_id,
        authorization_nullifier=second.authorization_nullifier,
    )
    reward = RewardEffectV1(
        economic_action_id=ordinary.economic_action_id,
        asset_effect_id=reward_asset_effect.effect_id,
        recipient_cell_key=proposal.ledger_cell_writes[1].cell_key,
        asset_id=ordinary.asset_id,
        amount_atoms=ordinary.credit_atoms,
        authority_scope_id=second.authorization_scope_id,
        authorization_nullifier=second.authorization_nullifier,
    )

    _assert_reject(
        replace(
            proposal,
            asset_effects=(proposal.asset_effects[0], reward_asset_effect),
            authorization_consumptions=proposal.authorization_consumptions + (second,),
            reward_effects=(reward,),
        ),
        SettlementEffectPlanRejectCodeV1.DUPLICATE_AUTHORIZATION_GRANT_SPEND,
    )


def test_authorization_nullifier_is_recomputed_and_mismatch_rejects() -> None:
    proposal = _proposal()
    authorization = replace(
        proposal.authorization_consumptions[0],
        authorization_nullifier=_hash(999),
    )

    _assert_reject(
        replace(proposal, authorization_consumptions=(authorization,)),
        SettlementEffectPlanRejectCodeV1.AUTHORIZATION_NULLIFIER_MISMATCH,
    )


def test_authorization_consumption_is_bound_to_plan_application_and_domain() -> None:
    proposal = _proposal(application_id=_hash(98))

    _assert_reject(
        proposal,
        SettlementEffectPlanRejectCodeV1.AUTHORIZATION_SCOPE_MISMATCH,
    )


def test_authorization_action_pre_state_must_equal_plan_pre_state() -> None:
    proposal = _proposal()
    mint = proposal.asset_effects[0]
    foreign = _authorization(
        action_id=mint.economic_action_id,
        pre_state_root=_hash(309),
    )
    rebound_mint = replace(
        mint,
        authorization_nullifier=foreign.authorization_nullifier,
    )

    _assert_reject(
        replace(
            proposal,
            asset_effects=(rebound_mint, proposal.asset_effects[1]),
            authorization_consumptions=(foreign,),
        ),
        SettlementEffectPlanRejectCodeV1.AUTHORIZATION_PRE_STATE_MISMATCH,
    )


def test_supply_effect_cannot_combine_mint_and_burn() -> None:
    with pytest.raises(SettlementEffectPlanValidationError) as caught:
        AssetEffectV1(
            kind=AssetEffectKindV1.AUTHORIZED_MINT,
            economic_action_id=_hash(10),
            asset_id=_hash(60),
            debit_atoms=1,
            credit_atoms=1,
            authorized_mint_atoms=1,
            authorized_burn_atoms=1,
            authority_scope_id=_hash(22),
            authorization_nullifier=_hash(23),
        )

    assert caught.value.code is SettlementEffectPlanRejectCodeV1.COMBINED_MINT_AND_BURN


def test_ordinary_effect_cannot_carry_authority_material() -> None:
    with pytest.raises(SettlementEffectPlanValidationError) as caught:
        AssetEffectV1(
            kind=AssetEffectKindV1.ORDINARY_TRANSFER,
            economic_action_id=_hash(10),
            asset_id=_hash(60),
            debit_atoms=1,
            credit_atoms=1,
            authorized_mint_atoms=0,
            authorized_burn_atoms=0,
            authority_scope_id=_hash(22),
            authorization_nullifier=_hash(23),
        )

    assert caught.value.code is SettlementEffectPlanRejectCodeV1.UNEXPECTED_AUTHORITY_MATERIAL


def test_nonempty_effect_plan_requires_state_root_change() -> None:
    proposal = _proposal(pre_state_root=_hash(3), post_state_root=_hash(3))

    _assert_reject(
        proposal,
        SettlementEffectPlanRejectCodeV1.NON_CHANGING_STATE_ROOT,
    )


def test_each_action_requires_a_cell_write_and_asset_effect() -> None:
    proposal = _proposal()
    orphan_action = _hash(150)

    _assert_reject(
        replace(
            proposal,
            economic_action_ids=proposal.economic_action_ids + (orphan_action,),
        ),
        SettlementEffectPlanRejectCodeV1.ACTION_WITHOUT_CELL_WRITE,
    )


def test_message_and_carry_effects_must_form_one_exact_pair() -> None:
    proposal = _proposal()
    ordinary = proposal.asset_effects[1]
    action = ordinary.economic_action_id
    message = MessageEffectV1(
        economic_action_id=action,
        asset_effect_id=ordinary.effect_id,
        source_domain_id=proposal.chain_or_domain_id,
        destination_domain_id=_hash(162),
        asset_id=ordinary.asset_id,
        amount_atoms=ordinary.debit_atoms,
        kind=MessageEffectKindV1.OUTBOX_ENQUEUE,
    )
    carry = CarryEffectV1(
        economic_action_id=action,
        message_id=message.message_id,
        asset_id=message.asset_id,
        amount_atoms=message.amount_atoms,
        kind=CarryEffectKindV1.LOCK,
    )

    accepted = build_settlement_effect_plan_v1(
        replace(proposal, message_effects=(message,), carry_effects=(carry,))
    )
    assert accepted.message_effects == (message,)
    assert accepted.carry_effects == (carry,)

    _assert_reject(
        replace(proposal, message_effects=(message,), carry_effects=()),
        SettlementEffectPlanRejectCodeV1.MESSAGE_CARRY_MISMATCH,
    )

    foreign_source = replace(message, source_domain_id=_hash(164))
    _assert_reject(
        replace(proposal, message_effects=(foreign_source,), carry_effects=(carry,)),
        SettlementEffectPlanRejectCodeV1.MESSAGE_CARRY_MISMATCH,
    )


def test_reward_effect_must_bind_matching_asset_effect_and_recipient_write() -> None:
    proposal = _proposal()
    ordinary = proposal.asset_effects[1]
    recipient_write = proposal.ledger_cell_writes[1]
    reward_authorization = _authorization(
        action_id=ordinary.economic_action_id,
        scope_id=_hash(171),
        nonce=172,
    )
    reward_asset_effect = replace(
        ordinary,
        kind=AssetEffectKindV1.AUTHORIZED_REWARD,
        authority_scope_id=reward_authorization.authorization_scope_id,
        authorization_nullifier=reward_authorization.authorization_nullifier,
    )
    reward = RewardEffectV1(
        economic_action_id=reward_asset_effect.economic_action_id,
        asset_effect_id=reward_asset_effect.effect_id,
        recipient_cell_key=recipient_write.cell_key,
        asset_id=reward_asset_effect.asset_id,
        amount_atoms=reward_asset_effect.credit_atoms,
        authority_scope_id=reward_authorization.authorization_scope_id,
        authorization_nullifier=reward_authorization.authorization_nullifier,
    )

    with_reward = replace(
        proposal,
        asset_effects=(proposal.asset_effects[0], reward_asset_effect),
        authorization_consumptions=proposal.authorization_consumptions + (reward_authorization,),
        reward_effects=(reward,),
    )
    accepted = build_settlement_effect_plan_v1(with_reward)
    assert accepted.reward_effects == (reward,)

    bad_reward = replace(reward, amount_atoms=reward.amount_atoms - 1)
    _assert_reject(
        replace(with_reward, reward_effects=(bad_reward,)),
        SettlementEffectPlanRejectCodeV1.REWARD_EFFECT_MISMATCH,
    )

    wrong_scope = replace(reward, authority_scope_id=_hash(999))
    _assert_reject(
        replace(with_reward, reward_effects=(wrong_scope,)),
        SettlementEffectPlanRejectCodeV1.REWARD_EFFECT_MISMATCH,
    )

    wrong_nullifier = replace(reward, authorization_nullifier=_hash(998))
    _assert_reject(
        replace(with_reward, reward_effects=(wrong_nullifier,)),
        SettlementEffectPlanRejectCodeV1.REWARD_EFFECT_MISMATCH,
    )

    _assert_reject(
        replace(with_reward, reward_effects=()),
        SettlementEffectPlanRejectCodeV1.REWARD_EFFECT_MISMATCH,
    )


def test_referenceable_effect_ids_are_derived_from_semantic_fields() -> None:
    proposal = _proposal()
    ordinary = proposal.asset_effects[1]
    changed = replace(ordinary, credit_atoms=ordinary.credit_atoms - 1)

    assert changed.effect_id != ordinary.effect_id
    assert "effect_id" not in inspect.signature(AssetEffectV1).parameters
    assert "message_id" not in inspect.signature(MessageEffectV1).parameters
    assert "carry_id" not in inspect.signature(CarryEffectV1).parameters
    assert "reward_id" not in inspect.signature(RewardEffectV1).parameters


def test_semantically_duplicate_effect_rejects_without_caller_rename_escape() -> None:
    proposal = _proposal()
    duplicate = copy.deepcopy(proposal.asset_effects[1])

    _assert_reject(
        replace(proposal, asset_effects=proposal.asset_effects + (duplicate,)),
        SettlementEffectPlanRejectCodeV1.DUPLICATE_ASSET_EFFECT,
    )


def test_tampered_derived_effect_id_rejects_on_revalidation() -> None:
    proposal = _proposal()
    tampered = copy.deepcopy(proposal.asset_effects[1])
    object.__setattr__(tampered, "effect_id", _hash(999))

    _assert_reject(
        replace(proposal, asset_effects=(proposal.asset_effects[0], tampered)),
        SettlementEffectPlanRejectCodeV1.DERIVED_ID_MISMATCH,
    )


def test_duplicate_action_identity_rejects_before_canonicalization() -> None:
    proposal = _proposal()

    _assert_reject(
        replace(
            proposal,
            economic_action_ids=(
                proposal.economic_action_ids[0],
                proposal.economic_action_ids[0],
            ),
        ),
        SettlementEffectPlanRejectCodeV1.DUPLICATE_ECONOMIC_ACTION,
    )


def test_rejection_does_not_mutate_the_proposal_or_nested_rows() -> None:
    proposal = _proposal()
    before = copy.deepcopy(proposal)
    original_writes = proposal.ledger_cell_writes
    ordinary = proposal.asset_effects[1]
    invalid = replace(
        proposal,
        asset_effects=(proposal.asset_effects[0], replace(ordinary, credit_atoms=99)),
    )
    invalid_before = copy.deepcopy(invalid)

    _assert_reject(
        invalid,
        SettlementEffectPlanRejectCodeV1.ASSET_CONSERVATION_VIOLATION,
    )

    assert invalid == invalid_before
    assert proposal == before
    assert proposal.ledger_cell_writes is original_writes


def test_bool_is_not_accepted_as_an_integer_amount() -> None:
    with pytest.raises(SettlementEffectPlanValidationError) as caught:
        AssetEffectV1(
            kind=AssetEffectKindV1.ORDINARY_TRANSFER,
            economic_action_id=_hash(10),
            asset_id=_hash(60),
            debit_atoms=True,
            credit_atoms=1,
            authorized_mint_atoms=0,
            authorized_burn_atoms=0,
        )

    assert caught.value.code is SettlementEffectPlanRejectCodeV1.INVALID_INTEGER


def test_authorization_nullifier_excludes_proof_and_signature_representations() -> None:
    authorization = _authorization()
    expected = authorization_consumption_nullifier_v1(
        application_id=authorization.application_id,
        chain_or_domain_id=authorization.chain_or_domain_id,
        economic_action_id=authorization.economic_action_id,
        authorization_subject_id=authorization.authorization_subject_id,
        authorization_grant_id=authorization.authorization_grant_id,
        authorization_scope_id=authorization.authorization_scope_id,
        authorization_nonce=authorization.authorization_nonce,
        action_pre_state_root=authorization.action_pre_state_root,
    )

    assert expected == authorization.authorization_nullifier
    assert not hasattr(authorization, "proof_program_id")
    assert not hasattr(authorization, "receipt_bytes")
    assert not hasattr(authorization, "intent_salt")
    assert not hasattr(authorization, "signature")


@pytest.mark.parametrize(
    ("field", "replacement"),
    (
        ("application_id", _hash(201)),
        ("chain_or_domain_id", _hash(202)),
        ("economic_action_id", _hash(203)),
        ("authorization_subject_id", _hash(204)),
        ("authorization_grant_id", _hash(205)),
        ("authorization_scope_id", _hash(206)),
        ("authorization_nonce", 208),
        ("action_pre_state_root", _hash(209)),
    ),
)
def test_every_authorization_identity_field_changes_the_nullifier(
    field: str,
    replacement: object,
) -> None:
    authorization = _authorization()
    fields: dict[str, object] = {
        "application_id": authorization.application_id,
        "chain_or_domain_id": authorization.chain_or_domain_id,
        "economic_action_id": authorization.economic_action_id,
        "authorization_subject_id": authorization.authorization_subject_id,
        "authorization_grant_id": authorization.authorization_grant_id,
        "authorization_scope_id": authorization.authorization_scope_id,
        "authorization_nonce": authorization.authorization_nonce,
        "action_pre_state_root": authorization.action_pre_state_root,
    }
    fields[field] = replacement

    mutated = authorization_consumption_nullifier_v1(**fields)  # type: ignore[arg-type]

    assert mutated != authorization.authorization_nullifier
