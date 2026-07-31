"""Pure unmounted SRGD-v1 grouping, allocation, and sparse-state transition."""

from __future__ import annotations

from typing import cast

from ..state.state_snapshot_values import (
    MAX_STATE_STRING_CHARACTERS_V1,
    MAX_STATE_STRING_UTF8_BYTES_V1,
)
from .fcis_fee_apportionment_selector import (
    FeeBonusSelectorRejectV2,
    select_fee_bonuses_v2,
)
from .fcis_fee_apportionment_transition import FeeQuotaV2, compute_fee_quota_v2
from .fcis_fee_apportionment_values import (
    BPS_DENOMINATOR_V2,
    MAX_FEE_AMOUNT_CANDIDATES_V2,
    MAX_FEE_AMOUNT_V2,
    MAX_FEE_APPORTIONMENT_KEYS_V2,
    SRGD_ALGORITHM_VERSION_V1,
    AssetFeeAllocationV2,
    CommittedFeeApportionmentStateV2,
    FeeAmountCandidateV2,
    FeeApportionmentKeyV2,
    FeeApportionmentTransitionCodeV2,
    FeeApportionmentTransitionRejectV2,
    FeeApportionmentTransitionResultV2,
    FeeDeficitEntryV2,
    FeeDistributionPolicyV2,
    _asset_fee_allocation_v2,
    _fee_apportionment_ok_v2,
)


def _reject_v2(
    code: FeeApportionmentTransitionCodeV2,
    path: tuple[str, ...],
) -> FeeApportionmentTransitionRejectV2:
    return FeeApportionmentTransitionRejectV2(code, path)


def _top_level_shape_reject_v2(
    contributions: object,
    policy: object,
    state: object,
) -> FeeApportionmentTransitionRejectV2 | None:
    if type(contributions) is not tuple:
        return _reject_v2(
            FeeApportionmentTransitionCodeV2.WRONG_EXACT_TYPE,
            ("contributions",),
        )
    if type(policy) is not FeeDistributionPolicyV2:
        return _reject_v2(
            FeeApportionmentTransitionCodeV2.WRONG_EXACT_TYPE,
            ("policy",),
        )
    if type(state) is not CommittedFeeApportionmentStateV2:
        return _reject_v2(
            FeeApportionmentTransitionCodeV2.WRONG_EXACT_TYPE,
            ("state",),
        )
    exact_state = cast(CommittedFeeApportionmentStateV2, state)
    entries_object: object = exact_state.entries
    if type(entries_object) is not tuple:
        return _reject_v2(
            FeeApportionmentTransitionCodeV2.WRONG_EXACT_TYPE,
            ("state", "entries"),
        )
    if len(contributions) > MAX_FEE_AMOUNT_CANDIDATES_V2:
        return _reject_v2(
            FeeApportionmentTransitionCodeV2.ITEM_LIMIT,
            ("contributions",),
        )
    if len(entries_object) > MAX_FEE_APPORTIONMENT_KEYS_V2:
        return _reject_v2(
            FeeApportionmentTransitionCodeV2.ITEM_LIMIT,
            ("state", "entries"),
        )
    return None


def _contribution_type_reject_v2(
    contributions: tuple[object, ...],
) -> FeeApportionmentTransitionRejectV2 | None:
    for index, candidate_object in enumerate(contributions):
        base: tuple[str, ...] = ("contributions", str(index))
        if type(candidate_object) is not FeeAmountCandidateV2:
            return _reject_v2(
                FeeApportionmentTransitionCodeV2.WRONG_EXACT_TYPE,
                base,
            )
        candidate = cast(FeeAmountCandidateV2, candidate_object)
        key_object: object = candidate.key
        if type(key_object) is not FeeApportionmentKeyV2:
            return _reject_v2(
                FeeApportionmentTransitionCodeV2.WRONG_EXACT_TYPE,
                base + ("key",),
            )
        key = cast(FeeApportionmentKeyV2, key_object)
        domain_object: object = key.fee_distribution_domain_id
        asset_object: object = key.asset
        amount_object: object = candidate.amount
        if type(domain_object) is not str:
            return _reject_v2(
                FeeApportionmentTransitionCodeV2.WRONG_EXACT_TYPE,
                base + ("key", "fee_distribution_domain_id"),
            )
        if type(asset_object) is not str:
            return _reject_v2(
                FeeApportionmentTransitionCodeV2.WRONG_EXACT_TYPE,
                base + ("key", "asset"),
            )
        if type(amount_object) is not int:
            return _reject_v2(
                FeeApportionmentTransitionCodeV2.WRONG_EXACT_TYPE,
                base + ("amount",),
            )
    return None


def _policy_type_reject_v2(
    policy: FeeDistributionPolicyV2,
) -> FeeApportionmentTransitionRejectV2 | None:
    policy_fields: tuple[tuple[str, object, type[object]], ...] = (
        ("buyback_bps", policy.buyback_bps, int),
        ("treasury_bps", policy.treasury_bps, int),
        ("rewards_bps", policy.rewards_bps, int),
        ("buyback_destination", policy.buyback_destination, str),
        ("treasury_destination", policy.treasury_destination, str),
        ("rewards_destination", policy.rewards_destination, str),
    )
    for field, value, expected in policy_fields:
        if type(value) is not expected:
            return _reject_v2(
                FeeApportionmentTransitionCodeV2.WRONG_EXACT_TYPE,
                ("policy", field),
            )
    return None


def _state_type_reject_v2(
    state: CommittedFeeApportionmentStateV2,
) -> FeeApportionmentTransitionRejectV2 | None:
    algorithm_object: object = state.algorithm_version
    exact_state = cast(CommittedFeeApportionmentStateV2, state)
    entries_object: object = exact_state.entries
    if type(algorithm_object) is not str:
        return _reject_v2(
            FeeApportionmentTransitionCodeV2.WRONG_EXACT_TYPE,
            ("state", "algorithm_version"),
        )
    if type(entries_object) is not tuple:
        return _reject_v2(
            FeeApportionmentTransitionCodeV2.WRONG_EXACT_TYPE,
            ("state", "entries"),
        )
    entry_objects = cast(tuple[object, ...], entries_object)
    for index, entry_object in enumerate(entry_objects):
        base = ("state", "entries", str(index))
        if type(entry_object) is not FeeDeficitEntryV2:
            return _reject_v2(
                FeeApportionmentTransitionCodeV2.WRONG_EXACT_TYPE,
                base,
            )
        entry = cast(FeeDeficitEntryV2, entry_object)
        entry_key_object: object = entry.key
        if type(entry_key_object) is not FeeApportionmentKeyV2:
            return _reject_v2(
                FeeApportionmentTransitionCodeV2.WRONG_EXACT_TYPE,
                base + ("key",),
            )
        key = cast(FeeApportionmentKeyV2, entry_key_object)
        domain_object = key.fee_distribution_domain_id
        asset_object = key.asset
        buyback_object: object = entry.deficit_buyback
        treasury_object: object = entry.deficit_treasury
        if type(domain_object) is not str:
            return _reject_v2(
                FeeApportionmentTransitionCodeV2.WRONG_EXACT_TYPE,
                base + ("key", "fee_distribution_domain_id"),
            )
        if type(asset_object) is not str:
            return _reject_v2(
                FeeApportionmentTransitionCodeV2.WRONG_EXACT_TYPE,
                base + ("key", "asset"),
            )
        if type(buyback_object) is not int:
            return _reject_v2(
                FeeApportionmentTransitionCodeV2.WRONG_EXACT_TYPE,
                base + ("deficit_buyback",),
            )
        if type(treasury_object) is not int:
            return _reject_v2(
                FeeApportionmentTransitionCodeV2.WRONG_EXACT_TYPE,
                base + ("deficit_treasury",),
            )
    return None


def _exact_type_reject_v2(
    contributions: object,
    policy: object,
    state: object,
) -> FeeApportionmentTransitionRejectV2 | None:
    rejected = _top_level_shape_reject_v2(contributions, policy, state)
    if rejected is not None:
        return rejected
    exact_contributions = cast(tuple[object, ...], contributions)
    exact_policy = cast(FeeDistributionPolicyV2, policy)
    exact_state = cast(CommittedFeeApportionmentStateV2, state)
    for rejected in (
        _contribution_type_reject_v2(exact_contributions),
        _policy_type_reject_v2(exact_policy),
        _state_type_reject_v2(exact_state),
    ):
        if rejected is not None:
            return rejected
    return None


def _text_is_canonical_v2(value: str) -> bool:
    if not value or len(value) > MAX_STATE_STRING_CHARACTERS_V1:
        return False
    try:
        encoded = value.encode("utf-8")
    except UnicodeEncodeError:
        return False
    return bool(len(encoded) <= MAX_STATE_STRING_UTF8_BYTES_V1)


def _identifier_reject_v2(
    contributions: tuple[FeeAmountCandidateV2, ...],
    policy: FeeDistributionPolicyV2,
    state: CommittedFeeApportionmentStateV2,
) -> FeeApportionmentTransitionRejectV2 | None:
    for index, candidate in enumerate(contributions):
        for field, value in (
            (
                "fee_distribution_domain_id",
                candidate.key.fee_distribution_domain_id,
            ),
            ("asset", candidate.key.asset),
        ):
            if not _text_is_canonical_v2(value):
                return _reject_v2(
                    FeeApportionmentTransitionCodeV2.NONCANONICAL_IDENTIFIER,
                    ("contributions", str(index), "key", field),
                )
    for field, value in (
        ("buyback_destination", policy.buyback_destination),
        ("treasury_destination", policy.treasury_destination),
        ("rewards_destination", policy.rewards_destination),
    ):
        if not _text_is_canonical_v2(value):
            return _reject_v2(
                FeeApportionmentTransitionCodeV2.NONCANONICAL_IDENTIFIER,
                ("policy", field),
            )
    for index, entry in enumerate(state.entries):
        for field, value in (
            (
                "fee_distribution_domain_id",
                entry.key.fee_distribution_domain_id,
            ),
            ("asset", entry.key.asset),
        ):
            if not _text_is_canonical_v2(value):
                return _reject_v2(
                    FeeApportionmentTransitionCodeV2.NONCANONICAL_IDENTIFIER,
                    ("state", "entries", str(index), "key", field),
                )
    return None


def _amount_reject_v2(
    contributions: tuple[FeeAmountCandidateV2, ...],
) -> FeeApportionmentTransitionRejectV2 | None:
    for index, candidate in enumerate(contributions):
        if not 0 <= candidate.amount <= MAX_FEE_AMOUNT_V2:
            return _reject_v2(
                FeeApportionmentTransitionCodeV2.AMOUNT_OUT_OF_RANGE,
                ("contributions", str(index), "amount"),
            )
    return None


def _policy_reject_v2(
    policy: FeeDistributionPolicyV2,
) -> FeeApportionmentTransitionRejectV2 | None:
    if any(not 0 <= weight <= BPS_DENOMINATOR_V2 for weight in policy.weights):
        return _reject_v2(
            FeeApportionmentTransitionCodeV2.INVALID_POLICY,
            ("policy", "weights"),
        )
    if sum(policy.weights) != BPS_DENOMINATOR_V2:
        return _reject_v2(
            FeeApportionmentTransitionCodeV2.INVALID_POLICY,
            ("policy", "weight_sum"),
        )
    return None


def _prestate_reject_v2(
    state: CommittedFeeApportionmentStateV2,
) -> FeeApportionmentTransitionRejectV2 | None:
    if state.algorithm_version != SRGD_ALGORITHM_VERSION_V1:
        return _reject_v2(
            FeeApportionmentTransitionCodeV2.INVALID_PRESTATE,
            ("state", "algorithm_version"),
        )
    previous: tuple[bytes, bytes] | None = None
    for index, entry in enumerate(state.entries):
        base = ("state", "entries", str(index))
        deficits = entry.deficits
        if any(not -BPS_DENOMINATOR_V2 < value < BPS_DENOMINATOR_V2 for value in deficits):
            return _reject_v2(
                FeeApportionmentTransitionCodeV2.INVALID_PRESTATE,
                base + ("deficits",),
            )
        if sum(deficits) != 0:
            return _reject_v2(
                FeeApportionmentTransitionCodeV2.INVALID_PRESTATE,
                base + ("deficit_sum",),
            )
        if deficits == (0, 0, 0):
            return _reject_v2(
                FeeApportionmentTransitionCodeV2.INVALID_PRESTATE,
                base + ("retained_zero",),
            )
        current = entry.key.protocol_order_key
        if previous is not None and previous >= current:
            return _reject_v2(
                FeeApportionmentTransitionCodeV2.INVALID_PRESTATE,
                base + ("protocol_order",),
            )
        previous = current
    return None


def _validated_inputs_v2(
    contributions: object,
    policy: object,
    state: object,
) -> (
    tuple[
        tuple[FeeAmountCandidateV2, ...],
        FeeDistributionPolicyV2,
        CommittedFeeApportionmentStateV2,
    ]
    | FeeApportionmentTransitionRejectV2
):
    rejected = _exact_type_reject_v2(contributions, policy, state)
    if rejected is not None:
        return rejected
    exact_contributions = cast(tuple[FeeAmountCandidateV2, ...], contributions)
    exact_policy = cast(FeeDistributionPolicyV2, policy)
    exact_state = cast(CommittedFeeApportionmentStateV2, state)
    rejected = _identifier_reject_v2(
        exact_contributions,
        exact_policy,
        exact_state,
    )
    if rejected is not None:
        return rejected
    rejected = _amount_reject_v2(exact_contributions)
    if rejected is not None:
        return rejected
    rejected = _policy_reject_v2(exact_policy)
    if rejected is not None:
        return rejected
    rejected = _prestate_reject_v2(exact_state)
    if rejected is not None:
        return rejected
    return exact_contributions, exact_policy, exact_state


def _group_amounts_v2(
    contributions: tuple[FeeAmountCandidateV2, ...],
) -> tuple[tuple[FeeApportionmentKeyV2, int], ...] | FeeApportionmentTransitionRejectV2:
    grouped: dict[FeeApportionmentKeyV2, int] = {}
    for candidate in contributions:
        grouped[candidate.key] = grouped.get(candidate.key, 0) + candidate.amount
    ordered = tuple(sorted(grouped.items(), key=lambda item: item[0].protocol_order_key))
    for key, amount in ordered:
        if amount > MAX_FEE_AMOUNT_V2:
            return _reject_v2(
                FeeApportionmentTransitionCodeV2.AGGREGATE_OVERFLOW,
                (
                    "contributions",
                    "aggregate",
                    key.fee_distribution_domain_id,
                    key.asset,
                ),
            )
    return ordered


def _select_bonuses_v2(
    deficits: tuple[int, int, int],
    fractions: tuple[int, int, int],
    *,
    denominator: int = BPS_DENOMINATOR_V2,
) -> tuple[int, int, int]:
    """Compatibility wrapper for the typed exact three-role selector."""

    selection = select_fee_bonuses_v2(
        deficits=deficits,
        fractions=fractions,
        denominator=denominator,
    )
    if type(selection) is FeeBonusSelectorRejectV2:
        raise ValueError(f"{selection.code.value}: {selection.path}")
    return selection.bonuses


def _allocation_v2(
    *,
    key: FeeApportionmentKeyV2,
    amount: int,
    policy: FeeDistributionPolicyV2,
    deficits_pre: tuple[int, int, int],
) -> AssetFeeAllocationV2 | FeeApportionmentTransitionRejectV2:
    quota_results = tuple(
        compute_fee_quota_v2(amount=amount, weight=weight)
        for weight in policy.weights
    )
    if any(type(quota) is not FeeQuotaV2 for quota in quota_results):
        return _reject_v2(
            FeeApportionmentTransitionCodeV2.INTERNAL_RELATION_FAILURE,
            ("relation", "quota"),
        )
    quotas = cast(tuple[FeeQuotaV2, ...], quota_results)
    lowers = quotas[0].base, quotas[1].base, quotas[2].base
    fractions = quotas[0].remainder, quotas[1].remainder, quotas[2].remainder
    try:
        bonuses = _select_bonuses_v2(deficits_pre, fractions)
    except ValueError:
        return _reject_v2(
            FeeApportionmentTransitionCodeV2.INTERNAL_RELATION_FAILURE,
            ("relation", "selector"),
        )
    amounts = (
        lowers[0] + bonuses[0],
        lowers[1] + bonuses[1],
        lowers[2] + bonuses[2],
    )
    deficits_post = (
        deficits_pre[0] + fractions[0] - BPS_DENOMINATOR_V2 * bonuses[0],
        deficits_pre[1] + fractions[1] - BPS_DENOMINATOR_V2 * bonuses[1],
        deficits_pre[2] + fractions[2] - BPS_DENOMINATOR_V2 * bonuses[2],
    )
    if (
        sum(amounts) != amount
        or sum(deficits_post) != 0
        or any(not -BPS_DENOMINATOR_V2 < value < BPS_DENOMINATOR_V2 for value in deficits_post)
        or any(bonus and fraction == 0 for bonus, fraction in zip(bonuses, fractions, strict=True))
        or any(amount_value > MAX_FEE_AMOUNT_V2 for amount_value in amounts)
    ):
        return _reject_v2(
            FeeApportionmentTransitionCodeV2.INTERNAL_RELATION_FAILURE,
            ("relation", "postconditions"),
        )
    try:
        return _asset_fee_allocation_v2(
            key=key,
            amount=amount,
            destinations=policy.destinations,
            fractions=fractions,
            bonuses=bonuses,
            amounts=amounts,
            deficits_pre=deficits_pre,
            deficits_post=deficits_post,
        )
    except (TypeError, ValueError, ArithmeticError):
        return _reject_v2(
            FeeApportionmentTransitionCodeV2.INTERNAL_RELATION_FAILURE,
            ("relation", "result_construction"),
        )


def apply_fee_apportionment_v2(
    *,
    contributions: object,
    policy: object,
    state: object,
) -> FeeApportionmentTransitionResultV2:
    """Apply one bounded SRGD-v1 candidate transition with no external effects."""

    validated = _validated_inputs_v2(contributions, policy, state)
    if type(validated) is FeeApportionmentTransitionRejectV2:
        return validated
    exact_contributions, exact_policy, exact_state = validated
    grouped = _group_amounts_v2(exact_contributions)
    if type(grouped) is FeeApportionmentTransitionRejectV2:
        return grouped

    state_by_key = {entry.key: entry for entry in exact_state.entries}
    allocations: list[AssetFeeAllocationV2] = []
    for key, amount in grouped:
        previous = state_by_key.get(key)
        deficits_pre = (0, 0, 0) if previous is None else previous.deficits
        allocation = _allocation_v2(
            key=key,
            amount=amount,
            policy=exact_policy,
            deficits_pre=deficits_pre,
        )
        if type(allocation) is FeeApportionmentTransitionRejectV2:
            return allocation
        allocations.append(allocation)
        if allocation.deficits_post == (0, 0, 0):
            state_by_key.pop(key, None)
        else:
            state_by_key[key] = FeeDeficitEntryV2(
                key,
                allocation.deficit_buyback_post,
                allocation.deficit_treasury_post,
            )

    next_entries = tuple(
        entry
        for _, entry in sorted(
            state_by_key.items(),
            key=lambda item: item[0].protocol_order_key,
        )
    )
    try:
        next_state = CommittedFeeApportionmentStateV2(
            SRGD_ALGORITHM_VERSION_V1,
            next_entries,
        )
        return _fee_apportionment_ok_v2(
            state=next_state,
            allocations=tuple(allocations),
        )
    except (TypeError, ValueError, ArithmeticError):
        return _reject_v2(
            FeeApportionmentTransitionCodeV2.INTERNAL_RELATION_FAILURE,
            ("relation", "successor_construction"),
        )


__all__ = ("apply_fee_apportionment_v2",)
