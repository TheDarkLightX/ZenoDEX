"""Tiny advisory selector for UPBA v2 neighborhood repair proposals."""

from __future__ import annotations

from dataclasses import dataclass
from math import log1p
from typing import Mapping, Sequence

from src.core.uniform_batch_clearing import UniformBatchCertificateV1
from src.energy.upba_v2_energy_model import LinearEnergyModel
from src.energy.upba_v2_features import extract_upba_v2_feature_record
from src.energy.upba_v2_hand_energy import hard_barrier_energy_from_record, hand_energy_from_record
from src.energy.upba_v2_neighborhood import UpbaV2NeighborhoodProposal
from src.energy.upba_v2_ranker import advisory_candidate_hash
from src.state.balances import BalanceTable
from src.state.intents import Intent
from src.state.pools import PoolState


REPAIR_SELECTOR_FEATURE_NAMES: tuple[str, ...] = (
    "source_rank_norm",
    "proposal_index_norm",
    "recipe_canonical_clamped_flag",
    "recipe_full_balance_clamped_flag",
    "recipe_snap_fraction_flag",
    "recipe_snap_fraction_ratio",
    "recipe_increase_step_flag",
    "recipe_decrease_step_flag",
    "recipe_single_direction_flag",
    "source_hand_energy_log1p",
    "proposal_hand_energy_log1p",
    "hand_energy_delta_signed",
    "source_hard_barrier_log1p",
    "proposal_hard_barrier_log1p",
    "hard_barrier_delta_signed",
    "proposal_candidate_price_ratio_vs_spot",
    "proposal_candidate_positive_fill_count_norm",
    "proposal_candidate_zero_fill_count_norm",
    "proposal_candidate_partial_fill_count_norm",
    "proposal_candidate_volume_log1p",
    "proposal_candidate_surplus_signed",
    "proposal_candidate_k_margin_signed",
    "proposal_candidate_negative_reserve_flag",
    "proposal_candidate_invariant_violation_flag",
    "proposal_candidate_limit_violation_count_norm",
    "proposal_candidate_balance_violation_count_norm",
    "proposal_candidate_noncanonical_fill_vector_flag",
    "proposal_candidate_zero_net_input_count_norm",
    "proposal_candidate_output_mismatch_count_norm",
    "proposal_candidate_all_zero_fill_vector_flag",
    "proposal_candidate_schema_policy_mismatch_flag",
    "proposal_candidate_price_ratio_unreduced_flag",
    "proposal_candidate_normalized_executed_volume",
    "proposal_candidate_normalized_surplus",
)

REPAIR_SELECTOR_FEATURE_DIM = len(REPAIR_SELECTOR_FEATURE_NAMES)


@dataclass(frozen=True)
class UpbaV2RepairSelectorFeatureRecord:
    feature_names: tuple[str, ...]
    values: tuple[float, ...]
    raw: dict[str, object]

    def feature_dict(self) -> dict[str, float]:
        return dict(zip(self.feature_names, self.values, strict=True))


def extract_upba_v2_repair_selector_features(
    *,
    pool: PoolState,
    intents: Sequence[Intent],
    balances: BalanceTable,
    source_candidate: UniformBatchCertificateV1,
    proposal: UpbaV2NeighborhoodProposal,
    source_rank: int,
    source_count: int,
    proposal_index: int,
    proposal_count: int,
) -> UpbaV2RepairSelectorFeatureRecord:
    """Extract advisory features for selecting one repair proposal.

    This extractor does not call the verifier and does not include verifier
    labels. Training and evaluation tools attach labels separately.
    """

    source_record = extract_upba_v2_feature_record(
        pool=pool,
        intents=intents,
        balances=balances,
        candidate=source_candidate,
        include_verifier_label=False,
    )
    proposal_record = extract_upba_v2_feature_record(
        pool=pool,
        intents=intents,
        balances=balances,
        candidate=proposal.candidate,
        include_verifier_label=False,
    )
    source_hand = hand_energy_from_record(source_record)
    proposal_hand = hand_energy_from_record(proposal_record)
    source_barrier = hard_barrier_energy_from_record(source_record)
    proposal_barrier = hard_barrier_energy_from_record(proposal_record)
    proposal_features = proposal_record.feature_dict()
    recipe = _recipe_features(proposal.recipe_id)
    feature_map: dict[str, float] = {
        "source_rank_norm": _clip01(source_rank / max(1, source_count)),
        "proposal_index_norm": _clip01(proposal_index / max(1, proposal_count)),
        **recipe,
        "source_hand_energy_log1p": _signed_log(source_hand),
        "proposal_hand_energy_log1p": _signed_log(proposal_hand),
        "hand_energy_delta_signed": _signed_delta(proposal_hand, source_hand),
        "source_hard_barrier_log1p": _log_nonnegative(source_barrier),
        "proposal_hard_barrier_log1p": _log_nonnegative(proposal_barrier),
        "hard_barrier_delta_signed": _signed_delta(proposal_barrier, source_barrier),
    }
    for name in REPAIR_SELECTOR_FEATURE_NAMES:
        if name.startswith("proposal_candidate_"):
            candidate_name = "candidate_" + name.removeprefix("proposal_candidate_")
            feature_map[name] = float(proposal_features[candidate_name])
    values = tuple(float(feature_map[name]) for name in REPAIR_SELECTOR_FEATURE_NAMES)
    return UpbaV2RepairSelectorFeatureRecord(
        feature_names=REPAIR_SELECTOR_FEATURE_NAMES,
        values=values,
        raw={
            "feature_schema": "zenodex/energy/upba_v2_repair_selector_features/v1",
            "feature_dim": REPAIR_SELECTOR_FEATURE_DIM,
            "source_hash": advisory_candidate_hash(source_candidate),
            "proposal_hash": proposal.candidate_hash,
            "recipe_id": proposal.recipe_id,
        },
    )


def rank_repair_proposals(
    *,
    pool: PoolState,
    intents: Sequence[Intent],
    balances: BalanceTable,
    proposals: Sequence[UpbaV2NeighborhoodProposal],
    source_candidates_by_hash: Mapping[str, UniformBatchCertificateV1],
    source_ranks_by_hash: Mapping[str, int],
    model: LinearEnergyModel,
) -> tuple[UpbaV2NeighborhoodProposal, ...]:
    """Rank repair proposals by a learned advisory selector energy."""

    if tuple(model.feature_names) != REPAIR_SELECTOR_FEATURE_NAMES:
        raise ValueError("repair selector model feature schema mismatch")
    proposal_count = len(proposals)
    scored: list[tuple[float, str, int, UpbaV2NeighborhoodProposal]] = []
    for index, proposal in enumerate(proposals):
        source = source_candidates_by_hash[proposal.source_hash]
        source_rank = int(source_ranks_by_hash.get(proposal.source_hash, 0))
        record = extract_upba_v2_repair_selector_features(
            pool=pool,
            intents=intents,
            balances=balances,
            source_candidate=source,
            proposal=proposal,
            source_rank=source_rank,
            source_count=max(1, len(source_candidates_by_hash)),
            proposal_index=index,
            proposal_count=max(1, proposal_count),
        )
        scored.append((model.energy(record.values), proposal.candidate_hash, index, proposal))
    scored.sort(key=lambda item: (item[0], item[1], item[2]))
    return tuple(item[3] for item in scored)


def _recipe_features(recipe_id: str) -> dict[str, float]:
    snap_ratio = 0.0
    parts = recipe_id.split("_")
    if recipe_id.startswith("snap_fraction_") and len(parts) >= 4:
        try:
            snap_ratio = _clip01(int(parts[2]) / max(1, int(parts[3])))
        except ValueError:
            snap_ratio = 0.0
    return {
        "recipe_canonical_clamped_flag": float(recipe_id == "canonical_clamped"),
        "recipe_full_balance_clamped_flag": float(recipe_id == "full_balance_clamped"),
        "recipe_snap_fraction_flag": float(recipe_id.startswith("snap_fraction_")),
        "recipe_snap_fraction_ratio": snap_ratio,
        "recipe_increase_step_flag": float(recipe_id.startswith("increase_step:")),
        "recipe_decrease_step_flag": float(recipe_id.startswith("decrease_step:")),
        "recipe_single_direction_flag": float(recipe_id.startswith("single_direction:")),
    }


def _clip01(value: float) -> float:
    return max(0.0, min(1.0, float(value)))


def _signed_delta(left: float, right: float) -> float:
    scale = max(1.0, abs(float(left)), abs(float(right)))
    return max(-1.0, min(1.0, (float(left) - float(right)) / scale))


def _signed_log(value: float) -> float:
    sign = -1.0 if value < 0 else 1.0
    return sign * min(1.0, log1p(abs(float(value))) / 20.0)


def _log_nonnegative(value: float) -> float:
    return min(1.0, log1p(max(0.0, float(value))) / 20.0)
