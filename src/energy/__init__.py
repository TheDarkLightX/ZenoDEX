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
from .upba_v2_hand_energy import (
    hard_barrier_energy_from_record,
    hand_energy_from_record,
    score_upba_v2_hand_energy,
)
from .upba_v2_ranker import (
    candidate_hash_multiset,
    candidate_orders_are_hash_permutation,
    rank_upba_v2_candidates,
    verified_checked_stop_certificate_holds,
)

__all__ = [
    "FEATURE_DIM",
    "FEATURE_NAMES",
    "UpbaV2FeatureRecord",
    "extract_upba_v2_feature_record",
    "hard_barrier_energy_from_record",
    "hand_energy_from_record",
    "candidate_hash_multiset",
    "candidate_orders_are_hash_permutation",
    "score_upba_v2_hand_energy",
    "verified_checked_stop_certificate_holds",
    "rank_upba_v2_candidates",
]
