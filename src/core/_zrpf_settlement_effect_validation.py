"""Canonicalization and relational validation for ZRPF effect plans."""

from __future__ import annotations

from typing import Any, NoReturn

from ._zrpf_settlement_effect_canonical import (
    _canonical_hashes,
    _canonical_records,
    _require_canonical_hashes,
    _require_canonical_records,
)
from ._zrpf_settlement_effect_common import (
    MAX_U64,
    MAX_U128,
    AssetEffectKindV1,
    CarryEffectKindV1,
    MessageEffectKindV1,
    SettlementEffectPlanRejectCodeV1,
    _reject,
    _require_nonzero_hash,
    _require_uint,
)
from ._zrpf_settlement_effect_records import (
    AssetEffectV1,
    AuthorizationConsumptionV1,
    CarryEffectV1,
    LedgerCellWriteV1,
    MessageEffectV1,
    RewardEffectV1,
)
from .zrpf_settlement_effect_plan import (
    ProposedSettlementEffectPlanV1,
    SettlementEffectPlanV1,
)


def build_settlement_effect_plan_v1(
    proposal: ProposedSettlementEffectPlanV1,
) -> SettlementEffectPlanV1:
    """Canonicalize and validate an authority-free proposed effect plan."""

    if type(proposal) is not ProposedSettlementEffectPlanV1:
        _reject(
            SettlementEffectPlanRejectCodeV1.INVALID_PROPOSAL,
            "proposal must be exactly ProposedSettlementEffectPlanV1",
        )
    actions = _canonical_hashes(
        proposal.economic_action_ids,
        name="economic_action_ids",
        duplicate_code=SettlementEffectPlanRejectCodeV1.DUPLICATE_ECONOMIC_ACTION,
        allow_empty=False,
    )
    return SettlementEffectPlanV1(
        application_id=proposal.application_id,
        chain_or_domain_id=proposal.chain_or_domain_id,
        epoch_id=proposal.epoch_id,
        source_root_journal_hash=proposal.source_root_journal_hash,
        public_policy_hash=proposal.public_policy_hash,
        pre_state_root=proposal.pre_state_root,
        post_state_root=proposal.post_state_root,
        economic_action_ids=actions,
        ledger_cell_writes=_canonical_records(
            proposal.ledger_cell_writes,
            record_type=LedgerCellWriteV1,
            key=lambda row: row.cell_key,
            name="ledger_cell_writes",
            duplicate_code=SettlementEffectPlanRejectCodeV1.DUPLICATE_CELL_WRITE,
            allow_empty=False,
        ),
        asset_effects=_canonical_records(
            proposal.asset_effects,
            record_type=AssetEffectV1,
            key=lambda row: row.effect_id,
            name="asset_effects",
            duplicate_code=SettlementEffectPlanRejectCodeV1.DUPLICATE_ASSET_EFFECT,
            allow_empty=False,
        ),
        authorization_consumptions=_canonical_records(
            proposal.authorization_consumptions,
            record_type=AuthorizationConsumptionV1,
            key=lambda row: row.authorization_nullifier,
            name="authorization_consumptions",
            duplicate_code=SettlementEffectPlanRejectCodeV1.DUPLICATE_AUTHORIZATION_NULLIFIER,
            allow_empty=True,
        ),
        message_effects=_canonical_records(
            proposal.message_effects,
            record_type=MessageEffectV1,
            key=lambda row: row.message_id,
            name="message_effects",
            duplicate_code=SettlementEffectPlanRejectCodeV1.DUPLICATE_MESSAGE,
            allow_empty=True,
        ),
        carry_effects=_canonical_records(
            proposal.carry_effects,
            record_type=CarryEffectV1,
            key=lambda row: row.carry_id,
            name="carry_effects",
            duplicate_code=SettlementEffectPlanRejectCodeV1.DUPLICATE_CARRY,
            allow_empty=True,
        ),
        reward_effects=_canonical_records(
            proposal.reward_effects,
            record_type=RewardEffectV1,
            key=lambda row: row.reward_id,
            name="reward_effects",
            duplicate_code=SettlementEffectPlanRejectCodeV1.DUPLICATE_REWARD,
            allow_empty=True,
        ),
    )


def validate_canonical_plan(plan: SettlementEffectPlanV1) -> None:
    _validate_plan_header(plan)
    _require_canonical_hashes(
        plan.economic_action_ids, name="economic_action_ids", allow_empty=False
    )
    _require_canonical_records(plan.ledger_cell_writes, LedgerCellWriteV1, lambda row: row.cell_key)
    _require_canonical_records(plan.asset_effects, AssetEffectV1, lambda row: row.effect_id)
    _require_canonical_records(
        plan.authorization_consumptions,
        AuthorizationConsumptionV1,
        lambda row: row.authorization_nullifier,
        allow_empty=True,
    )
    _require_canonical_records(
        plan.message_effects,
        MessageEffectV1,
        lambda row: row.message_id,
        allow_empty=True,
    )
    _require_canonical_records(
        plan.carry_effects,
        CarryEffectV1,
        lambda row: row.carry_id,
        allow_empty=True,
    )
    _require_canonical_records(
        plan.reward_effects,
        RewardEffectV1,
        lambda row: row.reward_id,
        allow_empty=True,
    )
    _validate_derived_record_ids(plan)
    _validate_action_coverage(plan)
    _validate_authorization_grant_spend_uniqueness(plan)
    _validate_authorization_consumptions(plan)
    _validate_asset_conservation(plan.asset_effects)
    _validate_message_carry_pairs(plan)
    _validate_reward_effects(plan)


def _validate_derived_record_ids(plan: SettlementEffectPlanV1) -> None:
    identities = (
        *((row.effect_id, row.expected_id()) for row in plan.asset_effects),
        *((row.message_id, row.expected_id()) for row in plan.message_effects),
        *((row.carry_id, row.expected_id()) for row in plan.carry_effects),
        *((row.reward_id, row.expected_id()) for row in plan.reward_effects),
    )
    for actual, expected in identities:
        if actual != expected:
            _reject(
                SettlementEffectPlanRejectCodeV1.DERIVED_ID_MISMATCH,
                f"record ID {actual} does not match canonical fields",
            )


def _validate_plan_header(plan: SettlementEffectPlanV1) -> None:
    for name in (
        "application_id",
        "chain_or_domain_id",
        "source_root_journal_hash",
        "public_policy_hash",
        "pre_state_root",
        "post_state_root",
    ):
        _require_nonzero_hash(getattr(plan, name), name=f"plan.{name}")
    _require_uint(plan.epoch_id, name="plan.epoch_id", maximum=MAX_U64)
    if plan.pre_state_root == plan.post_state_root:
        _reject(
            SettlementEffectPlanRejectCodeV1.NON_CHANGING_STATE_ROOT,
            "nonempty effect plan requires different pre and post state roots",
        )


def _validate_action_coverage(plan: SettlementEffectPlanV1) -> None:
    action_ids = set(plan.economic_action_ids)
    record_groups: tuple[tuple[Any, ...], ...] = (
        plan.ledger_cell_writes,
        plan.asset_effects,
        plan.authorization_consumptions,
        plan.message_effects,
        plan.carry_effects,
        plan.reward_effects,
    )
    for records in record_groups:
        for record in records:
            if record.economic_action_id not in action_ids:
                _reject(
                    SettlementEffectPlanRejectCodeV1.UNKNOWN_ECONOMIC_ACTION,
                    f"record references unknown action {record.economic_action_id}",
                )
    write_actions = {row.economic_action_id for row in plan.ledger_cell_writes}
    missing_writes = action_ids - write_actions
    if missing_writes:
        _reject(
            SettlementEffectPlanRejectCodeV1.ACTION_WITHOUT_CELL_WRITE,
            f"action lacks a ledger cell write: {min(missing_writes)}",
        )
    asset_actions = {row.economic_action_id for row in plan.asset_effects}
    missing_assets = action_ids - asset_actions
    if missing_assets:
        _reject(
            SettlementEffectPlanRejectCodeV1.ACTION_WITHOUT_ASSET_EFFECT,
            f"action lacks an asset effect: {min(missing_assets)}",
        )


def _validate_authorization_consumptions(plan: SettlementEffectPlanV1) -> None:
    authorizations = {row.authorization_nullifier: row for row in plan.authorization_consumptions}
    used: set[str] = set()
    for row in plan.authorization_consumptions:
        if (
            row.application_id != plan.application_id
            or row.chain_or_domain_id != plan.chain_or_domain_id
        ):
            _reject(
                SettlementEffectPlanRejectCodeV1.AUTHORIZATION_SCOPE_MISMATCH,
                "authorization application or domain differs from the plan",
            )
        if row.authorization_nullifier != row.expected_nullifier():
            _reject(
                SettlementEffectPlanRejectCodeV1.AUTHORIZATION_NULLIFIER_MISMATCH,
                f"authorization nullifier mismatch: {row.authorization_nullifier}",
            )
        if row.action_pre_state_root != plan.pre_state_root:
            _reject(
                SettlementEffectPlanRejectCodeV1.AUTHORIZATION_PRE_STATE_MISMATCH,
                "authorization action pre-state differs from the plan pre-state",
            )
        if row.authorization_grant_spend_nullifier != row.expected_grant_spend_nullifier():
            _reject(
                SettlementEffectPlanRejectCodeV1.DERIVED_ID_MISMATCH,
                "authorization grant-spend nullifier does not match canonical fields",
            )
    for effect in plan.asset_effects:
        if not effect.requires_authorization:
            continue
        authorization = authorizations.get(effect.authorization_nullifier)
        if authorization is None:
            _reject(
                SettlementEffectPlanRejectCodeV1.MISSING_AUTHORIZATION_CONSUMPTION,
                f"authorized effect lacks authorization: {effect.effect_id}",
            )
        if (
            authorization.economic_action_id != effect.economic_action_id
            or authorization.authorization_scope_id != effect.authority_scope_id
        ):
            _reject(
                SettlementEffectPlanRejectCodeV1.AUTHORIZATION_SCOPE_MISMATCH,
                f"authorized effect scope mismatch: {effect.effect_id}",
            )
        _consume_authorization(used, effect.authorization_nullifier, effect.effect_id)
    detached = set(authorizations) - used
    if detached:
        _reject(
            SettlementEffectPlanRejectCodeV1.DETACHED_AUTHORIZATION_CONSUMPTION,
            f"authorization is not consumed by an authorized asset effect: {min(detached)}",
        )


def _validate_authorization_grant_spend_uniqueness(
    plan: SettlementEffectPlanV1,
) -> None:
    values = tuple(
        row.authorization_grant_spend_nullifier for row in plan.authorization_consumptions
    )
    if len(values) != len(set(values)):
        _reject(
            SettlementEffectPlanRejectCodeV1.DUPLICATE_AUTHORIZATION_GRANT_SPEND,
            "one grant and nonce cannot back multiple authorization consumptions",
        )


def _consume_authorization(used: set[str], nullifier: str, effect_id: str) -> None:
    if nullifier in used:
        _reject(
            SettlementEffectPlanRejectCodeV1.AUTHORIZATION_CONSUMPTION_REUSED,
            f"authorization consumption backs more than one effect: {effect_id}",
        )
    used.add(nullifier)


def _validate_asset_conservation(rows: tuple[AssetEffectV1, ...]) -> None:
    totals: dict[str, tuple[int, int, int, int]] = {}
    for row in rows:
        prior = totals.get(row.asset_id, (0, 0, 0, 0))
        totals[row.asset_id] = tuple(
            _checked_add_u128(left, right, field="asset flow total")
            for left, right in zip(
                prior,
                (
                    row.debit_atoms,
                    row.credit_atoms,
                    row.authorized_mint_atoms,
                    row.authorized_burn_atoms,
                ),
                strict=True,
            )
        )  # type: ignore[assignment]
    for asset_id, (debit, credit, mint, burn) in sorted(totals.items()):
        left = _checked_add_u128(debit, mint, field="debit plus mint")
        right = _checked_add_u128(credit, burn, field="credit plus burn")
        if left != right:
            _reject(
                SettlementEffectPlanRejectCodeV1.ASSET_CONSERVATION_VIOLATION,
                f"asset {asset_id} has {left} input atoms and {right} output atoms",
            )


def _validate_message_carry_pairs(plan: SettlementEffectPlanV1) -> None:
    messages = {row.message_id: row for row in plan.message_effects}
    asset_effects = {row.effect_id: row for row in plan.asset_effects}
    used_asset_effects: set[str] = set()
    carries: dict[str, CarryEffectV1] = {}
    for carry in plan.carry_effects:
        if carry.message_id in carries:
            _reject(
                SettlementEffectPlanRejectCodeV1.MESSAGE_CARRY_MISMATCH,
                f"message has multiple carry effects: {carry.message_id}",
            )
        carries[carry.message_id] = carry
    if set(messages) != set(carries):
        _reject(
            SettlementEffectPlanRejectCodeV1.MESSAGE_CARRY_MISMATCH,
            "message IDs and carry message IDs differ",
        )
    expected_kind = {
        MessageEffectKindV1.OUTBOX_ENQUEUE: CarryEffectKindV1.LOCK,
        MessageEffectKindV1.INBOX_CONSUME: CarryEffectKindV1.RELEASE,
    }
    for message_id, message in messages.items():
        carry = carries[message_id]
        effect = asset_effects.get(message.asset_effect_id)
        local_domain_matches = (
            message.kind is MessageEffectKindV1.OUTBOX_ENQUEUE
            and message.source_domain_id == plan.chain_or_domain_id
        ) or (
            message.kind is MessageEffectKindV1.INBOX_CONSUME
            and message.destination_domain_id == plan.chain_or_domain_id
        )
        directional_amount_matches = effect is not None and (
            (
                message.kind is MessageEffectKindV1.OUTBOX_ENQUEUE
                and effect.debit_atoms == message.amount_atoms
            )
            or (
                message.kind is MessageEffectKindV1.INBOX_CONSUME
                and effect.credit_atoms == message.amount_atoms
            )
        )
        if (
            effect is None
            or message.asset_effect_id in used_asset_effects
            or not local_domain_matches
            or not directional_amount_matches
            or effect.economic_action_id != message.economic_action_id
            or effect.asset_id != message.asset_id
            or carry.economic_action_id != message.economic_action_id
            or carry.asset_id != message.asset_id
            or carry.amount_atoms != message.amount_atoms
            or carry.kind is not expected_kind[message.kind]
        ):
            _reject(
                SettlementEffectPlanRejectCodeV1.MESSAGE_CARRY_MISMATCH,
                f"message and carry fields differ: {message_id}",
            )
        used_asset_effects.add(message.asset_effect_id)


def _validate_reward_effects(plan: SettlementEffectPlanV1) -> None:
    asset_effects = {row.effect_id: row for row in plan.asset_effects}
    cell_writes = {row.cell_key: row for row in plan.ledger_cell_writes}
    used_effects = {message.asset_effect_id for message in plan.message_effects}
    for reward in plan.reward_effects:
        effect = asset_effects.get(reward.asset_effect_id)
        cell_write = cell_writes.get(reward.recipient_cell_key)
        if effect is None or cell_write is None or reward.asset_effect_id in used_effects:
            _reward_mismatch(reward.reward_id)
        if (
            effect.kind is not AssetEffectKindV1.AUTHORIZED_REWARD
            or effect.economic_action_id != reward.economic_action_id
            or effect.asset_id != reward.asset_id
            or effect.credit_atoms != reward.amount_atoms
            or effect.authority_scope_id != reward.authority_scope_id
            or effect.authorization_nullifier != reward.authorization_nullifier
            or cell_write.economic_action_id != reward.economic_action_id
        ):
            _reward_mismatch(reward.reward_id)
        used_effects.add(reward.asset_effect_id)
    reward_effect_ids = {
        effect.effect_id
        for effect in plan.asset_effects
        if effect.kind is AssetEffectKindV1.AUTHORIZED_REWARD
    }
    submitted_reward_effect_ids = {reward.asset_effect_id for reward in plan.reward_effects}
    if reward_effect_ids != submitted_reward_effect_ids:
        _reject(
            SettlementEffectPlanRejectCodeV1.REWARD_EFFECT_MISMATCH,
            "authorized reward asset effects and reward records differ",
        )


def _reward_mismatch(reward_id: str) -> NoReturn:
    _reject(
        SettlementEffectPlanRejectCodeV1.REWARD_EFFECT_MISMATCH,
        f"reward does not exactly bind one asset effect and recipient write: {reward_id}",
    )


def _checked_add_u128(left: int, right: int, *, field: str) -> int:
    result = left + right
    if result > MAX_U128:
        _reject(
            SettlementEffectPlanRejectCodeV1.ARITHMETIC_OVERFLOW,
            f"{field} exceeds unsigned 128-bit range",
        )
    return result
