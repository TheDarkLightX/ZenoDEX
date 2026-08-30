"""Exact global-state refinement for the atomic ZDEX buyback route."""

from __future__ import annotations

from dataclasses import dataclass

from .global_economic_proof_v1 import (
    EconomicCommandOccurrenceV1,
    RouteCompositionJournalV1,
)
from .global_economic_refinement_snapshot_v1 import (
    _snapshot_effect_plan_v1,
    _snapshot_occurrence_v1,
    _snapshot_route_journal_v1,
    _snapshot_state_v1,
)
from .global_economic_replay_refinement_v1 import _derive_replay_insertions_v1
from .global_economic_state_delta_v1 import _derive_global_economic_state_delta_v1
from .global_economic_state_effect_refinement_v1 import (
    GlobalEconomicStateEffectRefinementCandidateV1,
    _require_conservation_refinement_v1,
    _require_fixed_context_v1,
    _require_nonzero_sparse_amounts_v1,
    _require_supported_effects_v1,
)
from .global_settlement_types_v1 import (
    FEE_RESIDUE_CONTROL_DOMAIN_V1,
    FEE_RESIDUE_PRINCIPAL_V1,
    MAX_DELTA_ATOMS_V1,
    MIN_DELTA_ATOMS_V1,
    EconomicEffectKindV1,
    GlobalEconomicEffectPlanV1,
    GlobalEconomicStateV1,
    _require_root,
    hash_global_v1,
)
from .zdex_atomic_buyback_receipt_verification_v2 import (
    VerifiedZDEXSpotBuybackLeafV2,
    VerifiedZDEXTokenomicsBuybackLeafV2,
    snapshot_verified_zdex_spot_buyback_leaf_v2,
    snapshot_verified_zdex_tokenomics_buyback_leaf_v2,
)
from .zdex_fee_allocation_types_v1 import FEE_BUYBACK_PRINCIPAL_V1
from .zdex_purchase_burn_route_types_v1 import (
    AMM_POOL_CUSTODY_DOMAIN_V1,
    PROTOCOL_BUYBACK_CUSTODY_DOMAIN_V1,
    zdex_pool_reserve_principal_v1,
)


@dataclass(frozen=True, slots=True)
class ZDEXAtomicBuybackStateRefinementCandidateV2:
    pre_state: GlobalEconomicStateV1
    post_state: GlobalEconomicStateV1
    effects: GlobalEconomicEffectPlanV1
    occurrence: EconomicCommandOccurrenceV1
    route_journal: RouteCompositionJournalV1
    verified_spot_leaf: VerifiedZDEXSpotBuybackLeafV2
    verified_tokenomics_leaf: VerifiedZDEXTokenomicsBuybackLeafV2

    def __post_init__(self) -> None:
        expected = (
            (self.pre_state, GlobalEconomicStateV1),
            (self.post_state, GlobalEconomicStateV1),
            (self.effects, GlobalEconomicEffectPlanV1),
            (self.occurrence, EconomicCommandOccurrenceV1),
            (self.route_journal, RouteCompositionJournalV1),
            (self.verified_spot_leaf, VerifiedZDEXSpotBuybackLeafV2),
            (self.verified_tokenomics_leaf, VerifiedZDEXTokenomicsBuybackLeafV2),
        )
        if any(type(value) is not expected_type for value, expected_type in expected):
            raise TypeError("ZDEX atomic buyback refinement candidate is not closed")


@dataclass(frozen=True, slots=True)
class ZDEXAtomicBuybackStateRefinementV2:
    state_delta_root: str
    fee_disposition_root: str

    def __post_init__(self) -> None:
        _require_root(self.state_delta_root, name="ZDEX atomic buyback state delta")
        _require_root(
            self.fee_disposition_root,
            name="ZDEX atomic buyback fee disposition",
        )


def _checked_delta_v2(value: int) -> int:
    if not MIN_DELTA_ATOMS_V1 <= value <= MAX_DELTA_ATOMS_V1:
        raise ValueError("ZDEX atomic buyback aggregate exceeds signed i128")
    return value


def _amount_at_v2(
    state: GlobalEconomicStateV1,
    key: tuple[str, str, str],
) -> int:
    principal, asset, domain = key
    return next(
        (
            row.amount_atoms
            for row in state.custody
            if row.owner == principal
            and row.asset == asset
            and row.custody_domain == domain
        ),
        0,
    )


def _state_bearing_deltas_v2(
    effects: GlobalEconomicEffectPlanV1,
) -> dict[tuple[str, str, str], int]:
    result: dict[tuple[str, str, str], int] = {}
    for row in effects.rows:
        if row.kind not in {
            EconomicEffectKindV1.ACCOUNT_MOVEMENT,
            EconomicEffectKindV1.CUSTODY,
            EconomicEffectKindV1.RESERVE,
        }:
            continue
        key = (row.principal, row.asset, row.custody_domain)
        result[key] = _checked_delta_v2(result.get(key, 0) + row.delta_atoms)
    return result


def _require_allocation_dispositions_v2(
    effects: GlobalEconomicEffectPlanV1,
    state_deltas: dict[tuple[str, str, str], int],
    buyback_key: tuple[str, str, str],
    quote_spend_atoms: int,
) -> int:
    allocations = tuple(
        row for row in effects.rows if row.kind is EconomicEffectKindV1.FEE_ALLOCATION
    )
    for row in allocations:
        key = (row.principal, row.asset, row.custody_domain)
        consumed = quote_spend_atoms if key == buyback_key else 0
        if state_deltas.get(key, 0) + consumed != row.delta_atoms:
            raise ValueError("ZDEX fee allocation disposition does not refine state")
    matching = tuple(
        row
        for row in allocations
        if (row.principal, row.asset, row.custody_domain) == buyback_key
    )
    if len(matching) != 1:
        raise ValueError("ZDEX buyback allocation must have one exact destination")
    return matching[0].delta_atoms


def _require_residue_mapping_v2(effects: GlobalEconomicEffectPlanV1) -> None:
    actual = {
        row.asset: row.delta_atoms
        for row in effects.rows
        if row.kind is EconomicEffectKindV1.RESERVE
        and row.principal == FEE_RESIDUE_PRINCIPAL_V1
        and row.custody_domain == FEE_RESIDUE_CONTROL_DOMAIN_V1
        and row.delta_atoms > 0
    }
    expected = {
        row.asset: row.carried_residue_atoms
        for row in effects.fee_conservation
        if row.carried_residue_atoms > 0
    }
    if actual != expected:
        raise ValueError("ZDEX buyback fee residue mapping mismatch")


def _temporal_fee_disposition_root_v2(
    candidate: ZDEXAtomicBuybackStateRefinementCandidateV2,
) -> str:
    spot = snapshot_verified_zdex_spot_buyback_leaf_v2(
        candidate.verified_spot_leaf
    ).journal
    tokenomics = snapshot_verified_zdex_tokenomics_buyback_leaf_v2(
        candidate.verified_tokenomics_leaf
    ).journal
    buyback_key = (
        FEE_BUYBACK_PRINCIPAL_V1,
        tokenomics.quote_asset_id,
        PROTOCOL_BUYBACK_CUSTODY_DOMAIN_V1,
    )
    pool_key = (
        zdex_pool_reserve_principal_v1(
            pool_id=tokenomics.selected_pool_id,
            asset_id=tokenomics.quote_asset_id,
        ),
        tokenomics.quote_asset_id,
        AMM_POOL_CUSTODY_DOMAIN_V1,
    )
    state_deltas = _state_bearing_deltas_v2(candidate.effects)
    allocation = _require_allocation_dispositions_v2(
        candidate.effects,
        state_deltas,
        buyback_key,
        tokenomics.quote_spend_atoms,
    )
    pre_reserve = _amount_at_v2(candidate.pre_state, buyback_key)
    post_reserve = _amount_at_v2(candidate.post_state, buyback_key)
    if (
        allocation != tokenomics.buyback_allocation_atoms
        or spot.quote_input_atoms != tokenomics.quote_spend_atoms
        or state_deltas.get(pool_key, 0) != tokenomics.quote_spend_atoms
        or pre_reserve != tokenomics.buyback_reserve_pre_atoms
        or post_reserve != tokenomics.buyback_reserve_post_atoms
        or post_reserve + tokenomics.quote_spend_atoms != pre_reserve + allocation
    ):
        raise ValueError("ZDEX buyback fee disposition witness is disconnected")
    _require_residue_mapping_v2(candidate.effects)
    return hash_global_v1(
        "zdex-atomic-buyback-fee-disposition-v2",
        {
            "effect_plan_root": candidate.effects.effect_plan_root,
            "buyback_principal": buyback_key[0],
            "quote_asset": buyback_key[1],
            "buyback_allocation_atoms": allocation,
            "buyback_reserve_pre_atoms": pre_reserve,
            "quote_spend_atoms": tokenomics.quote_spend_atoms,
            "buyback_reserve_post_atoms": post_reserve,
            "pool_principal": pool_key[0],
        },
    )


def refine_zdex_atomic_buyback_route_state_v2(
    candidate: ZDEXAtomicBuybackStateRefinementCandidateV2,
) -> ZDEXAtomicBuybackStateRefinementV2:
    """Check the full state delta and the one permitted temporal allocation."""

    if type(candidate) is not ZDEXAtomicBuybackStateRefinementCandidateV2:
        raise TypeError("ZDEX atomic buyback refinement candidate must be exact typed data")
    candidate.__post_init__()
    owned = ZDEXAtomicBuybackStateRefinementCandidateV2(
        _snapshot_state_v1(candidate.pre_state),
        _snapshot_state_v1(candidate.post_state),
        _snapshot_effect_plan_v1(candidate.effects),
        _snapshot_occurrence_v1(candidate.occurrence),
        _snapshot_route_journal_v1(candidate.route_journal),
        candidate.verified_spot_leaf,
        candidate.verified_tokenomics_leaf,
    )
    _require_fixed_context_v1(
        owned.pre_state,
        owned.post_state,
        expected_post_height=owned.occurrence.height,
    )
    _require_nonzero_sparse_amounts_v1(owned.pre_state)
    _require_nonzero_sparse_amounts_v1(owned.post_state)
    _require_supported_effects_v1(owned.effects)
    global_candidate = GlobalEconomicStateEffectRefinementCandidateV1(
        owned.pre_state,
        owned.post_state,
        owned.effects,
        (owned.occurrence,),
        (owned.route_journal,),
    )
    replay = _derive_replay_insertions_v1(global_candidate)
    delta = _derive_global_economic_state_delta_v1(
        owned.pre_state,
        owned.post_state,
        owned.effects,
        replay,
    )
    _require_conservation_refinement_v1(
        owned.pre_state,
        owned.post_state,
        owned.effects,
        delta,
    )
    return ZDEXAtomicBuybackStateRefinementV2(
        delta.delta_root,
        _temporal_fee_disposition_root_v2(owned),
    )


__all__ = [
    "ZDEXAtomicBuybackStateRefinementCandidateV2",
    "ZDEXAtomicBuybackStateRefinementV2",
    "refine_zdex_atomic_buyback_route_state_v2",
]
