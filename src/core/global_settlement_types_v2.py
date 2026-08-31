"""Compatibility facade for GlobalSettlementABI V2 values.

V2 is an explicit research-only successor. It has distinct schemas and hash
domains from V1, and values from the two ABI majors are never interchangeable.
Implementations live in acyclic, assurance-scoped modules; this facade preserves
the original import surface and grants no settlement or release authority.
"""

from __future__ import annotations

from .global_settlement_effect_plan_v2 import (
    MAX_ASSET_CONSERVATION_ROWS_PER_PLAN_V2,
    MAX_ECONOMIC_EFFECT_PLAN_CANONICAL_BYTES_V2,
    MAX_ECONOMIC_EFFECT_PLAN_ITEMS_V2,
    MAX_ECONOMIC_EFFECT_ROWS_PER_PLAN_V2,
    MAX_EXTERNAL_OUTBOX_ENQUEUES_PER_PLAN_V2,
    MAX_FEE_CONSERVATION_ROWS_PER_PLAN_V2,
    MAX_LANE_WRITES_PER_PLAN_V2,
    MAX_OCCURRENCE_CONSUMPTIONS_PER_PLAN_V2,
    GlobalEconomicEffectPlanV2,
)
from .global_settlement_effect_plan_v2 import (
    _require_economic_effect_plan_item_bounds_v2 as _require_economic_effect_plan_item_bounds_v2,
)
from .global_settlement_effect_values_v2 import (
    AssetConservationRowV2,
    EconomicEffectKindV2,
    EconomicEffectRowV2,
    ExternalOutboxEnqueueV2,
    FeeConservationRowV2,
    LaneWriteV2,
)
from .global_settlement_lifecycle_v2 import (
    MAX_ORACLE_OCCURRENCE_DELTAS_PER_PLAN_V2,
    MAX_TERMINAL_OBLIGATION_DELTAS_PER_PLAN_V2,
    GlobalOracleOccurrencePlanV2,
    GlobalTerminalObligationPlanV2,
    OracleOccurrenceDeltaV2,
    OracleOccurrenceStateV2,
    TerminalObligationDeltaV2,
    TerminalObligationStatusV2,
    TerminalObligationV2,
)
from .global_settlement_ownership_v2 import (
    _DataclassTupleSnapshotPropertyV2 as _DataclassTupleSnapshotPropertyV2,
)
from .global_settlement_ownership_v2 import (
    _SortedTokenTupleSnapshotPropertyV2 as _SortedTokenTupleSnapshotPropertyV2,
)
from .global_settlement_primitives_v2 import (
    ALL_LANE_IDS_V2,
    GLOBAL_SETTLEMENT_ABI_V2,
    MAX_ATOMS_V2,
    MAX_DELTA_ATOMS_V2,
    MAX_TOKEN_BYTES_V2,
    MAX_U64_V2,
    MIN_DELTA_ATOMS_V2,
    ZERO_ROOT_V2,
    AssetSupplyV2,
    EconomicAmountV2,
    LaneIdV2,
    canonical_economic_command_body_bytes_v2,
    canonical_global_bytes_v2,
    hash_economic_command_body_bytes_v2,
    hash_economic_command_body_v2,
    hash_global_v2,
)
from .global_settlement_primitives_v2 import (
    _canonical_value_v2 as _canonical_value_v2,
)
from .global_settlement_primitives_v2 import (
    _CanonicalizableV2 as _CanonicalizableV2,
)
from .global_settlement_primitives_v2 import (
    _require_atoms_u128_v2 as _require_atoms_u128_v2,
)
from .global_settlement_primitives_v2 import (
    _require_bool_v2 as _require_bool_v2,
)
from .global_settlement_primitives_v2 import (
    _require_delta_atoms_i128_v2 as _require_delta_atoms_i128_v2,
)
from .global_settlement_primitives_v2 import (
    _require_nonnegative_int_v2 as _require_nonnegative_int_v2,
)
from .global_settlement_primitives_v2 import (
    _require_ordered_objects_v2 as _require_ordered_objects_v2,
)
from .global_settlement_primitives_v2 import (
    _require_root_v2 as _require_root_v2,
)
from .global_settlement_primitives_v2 import (
    _require_sorted_unique_tokens_v2 as _require_sorted_unique_tokens_v2,
)
from .global_settlement_primitives_v2 import (
    _require_token_v2 as _require_token_v2,
)
from .global_settlement_primitives_v2 import (
    _require_tuple_v2 as _require_tuple_v2,
)
from .global_settlement_primitives_v2 import (
    _snapshot_dataclass_tuple_v2 as _snapshot_dataclass_tuple_v2,
)

__all__ = [
    "GLOBAL_SETTLEMENT_ABI_V2",
    "MAX_TOKEN_BYTES_V2",
    "MAX_U64_V2",
    "MAX_ATOMS_V2",
    "MIN_DELTA_ATOMS_V2",
    "MAX_DELTA_ATOMS_V2",
    "MAX_ORACLE_OCCURRENCE_DELTAS_PER_PLAN_V2",
    "MAX_TERMINAL_OBLIGATION_DELTAS_PER_PLAN_V2",
    "MAX_ECONOMIC_EFFECT_ROWS_PER_PLAN_V2",
    "MAX_ASSET_CONSERVATION_ROWS_PER_PLAN_V2",
    "MAX_FEE_CONSERVATION_ROWS_PER_PLAN_V2",
    "MAX_LANE_WRITES_PER_PLAN_V2",
    "MAX_OCCURRENCE_CONSUMPTIONS_PER_PLAN_V2",
    "MAX_EXTERNAL_OUTBOX_ENQUEUES_PER_PLAN_V2",
    "MAX_ECONOMIC_EFFECT_PLAN_ITEMS_V2",
    "MAX_ECONOMIC_EFFECT_PLAN_CANONICAL_BYTES_V2",
    "ZERO_ROOT_V2",
    "LaneIdV2",
    "ALL_LANE_IDS_V2",
    "EconomicAmountV2",
    "AssetSupplyV2",
    "OracleOccurrenceStateV2",
    "OracleOccurrenceDeltaV2",
    "GlobalOracleOccurrencePlanV2",
    "TerminalObligationStatusV2",
    "TerminalObligationV2",
    "TerminalObligationDeltaV2",
    "GlobalTerminalObligationPlanV2",
    "EconomicEffectKindV2",
    "EconomicEffectRowV2",
    "AssetConservationRowV2",
    "FeeConservationRowV2",
    "LaneWriteV2",
    "ExternalOutboxEnqueueV2",
    "GlobalEconomicEffectPlanV2",
    "canonical_global_bytes_v2",
    "canonical_economic_command_body_bytes_v2",
    "hash_economic_command_body_bytes_v2",
    "hash_economic_command_body_v2",
    "hash_global_v2",
]
