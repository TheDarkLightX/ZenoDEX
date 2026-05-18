"""Advisory candidate scorers for ZenoDEX search experiments.

Energy modules are outside the consensus-critical verifier path. They may
consume verifier APIs for labeling and benchmarks, but verifier modules must not
import this package.
"""

from .upba_v2_features import (
    FEATURE_DIM,
    FEATURE_NAMES,
    UpbaV2FeatureRecord,
    extract_upba_v2_feature_record,
)
from .autotrader_energy import (
    AUTOTRADER_FEATURE_NAMES,
    AutoTraderLinearEnergyModel,
    evaluate_autotrader_rows,
    generate_rows,
    group_counts,
    hand_energy_from_autotrader_row,
    initial_autotrader_hand_model,
    shadow_rows_from_observations,
    train_autotrader_linear_ranker,
)
from .upba_v2_hand_energy import (
    hard_barrier_energy_from_record,
    hand_energy_from_record,
    score_upba_v2_hand_energy,
)
from .upba_v2_listwise_set_ranker import (
    LISTWISE_SET_FEATURE_DIM,
    LISTWISE_SET_FEATURE_NAMES,
    order_rows_by_listwise_set_model,
    score_listwise_batch,
    train_listwise_set_ranker,
)
from .upba_v2_neighborhood import (
    UpbaV2NeighborhoodAugmentation,
    UpbaV2NeighborhoodProposal,
    augment_candidates_with_neighborhood,
    propose_upba_v2_neighborhood,
)
from .upba_v2_ranker import (
    candidate_hash_multiset,
    candidate_orders_are_hash_permutation,
    rank_upba_v2_candidates,
    verified_checked_stop_certificate_holds,
)
from .upba_v2_repair_selector import (
    REPAIR_SELECTOR_FEATURE_DIM,
    REPAIR_SELECTOR_FEATURE_NAMES,
    UpbaV2RepairSelectorFeatureRecord,
    extract_upba_v2_repair_selector_features,
    rank_repair_proposals,
)
from .upba_v2_set_features import (
    SET_AWARE_FEATURE_DIM,
    SET_AWARE_FEATURE_NAMES,
    SET_FEATURE_DIM,
    SET_FEATURE_NAMES,
    UpbaV2SetFeatureRecord,
    extract_upba_v2_set_aware_feature_record,
    extract_upba_v2_set_feature_record,
)

__all__ = [
    "FEATURE_DIM",
    "FEATURE_NAMES",
    "SET_AWARE_FEATURE_DIM",
    "SET_AWARE_FEATURE_NAMES",
    "SET_FEATURE_DIM",
    "SET_FEATURE_NAMES",
    "REPAIR_SELECTOR_FEATURE_DIM",
    "REPAIR_SELECTOR_FEATURE_NAMES",
    "LISTWISE_SET_FEATURE_DIM",
    "LISTWISE_SET_FEATURE_NAMES",
    "AUTOTRADER_FEATURE_NAMES",
    "AutoTraderLinearEnergyModel",
    "UpbaV2FeatureRecord",
    "UpbaV2NeighborhoodAugmentation",
    "UpbaV2NeighborhoodProposal",
    "UpbaV2RepairSelectorFeatureRecord",
    "UpbaV2SetFeatureRecord",
    "augment_candidates_with_neighborhood",
    "extract_upba_v2_feature_record",
    "extract_upba_v2_repair_selector_features",
    "extract_upba_v2_set_aware_feature_record",
    "extract_upba_v2_set_feature_record",
    "evaluate_autotrader_rows",
    "generate_rows",
    "group_counts",
    "hard_barrier_energy_from_record",
    "hand_energy_from_autotrader_row",
    "hand_energy_from_record",
    "initial_autotrader_hand_model",
    "shadow_rows_from_observations",
    "candidate_hash_multiset",
    "candidate_orders_are_hash_permutation",
    "propose_upba_v2_neighborhood",
    "rank_repair_proposals",
    "order_rows_by_listwise_set_model",
    "score_upba_v2_hand_energy",
    "score_listwise_batch",
    "train_autotrader_linear_ranker",
    "train_listwise_set_ranker",
    "verified_checked_stop_certificate_holds",
    "rank_upba_v2_candidates",
]
