"""Explicit data-only position of a module pair in one prospective epoch.

The shell authenticates epoch_source. The consuming epoch fold pairs every
later predecessor with the immediately preceding checked disclosure. A position
value alone proves neither premise and grants no authority.
"""

from dataclasses import dataclass

from .global_economic_proof_v1 import MAX_EPOCH_COMMANDS_V1
from .global_economic_refinement_snapshot_v1 import _snapshot_state_v1
from .global_settlement_types_v1 import GlobalEconomicStateV1


@dataclass(frozen=True, slots=True)
class AssetTransferEpochPositionV1:
    epoch_source: GlobalEconomicStateV1
    occurrence_index: int

    def __post_init__(self) -> None:
        if type(self.epoch_source) is not GlobalEconomicStateV1:
            raise TypeError("epoch position source must be exact global state")
        if type(self.occurrence_index) is not int:
            raise TypeError("epoch position index must be exact int")
        if not 0 <= self.occurrence_index < MAX_EPOCH_COMMANDS_V1:
            raise ValueError("epoch position index must lie in 0..63")


def _snapshot_epoch_position_v1(
    position: AssetTransferEpochPositionV1,
) -> AssetTransferEpochPositionV1:
    if type(position) is not AssetTransferEpochPositionV1:
        raise TypeError("epoch position must have the exact typed value")
    return AssetTransferEpochPositionV1(
        _snapshot_state_v1(position.epoch_source),
        position.occurrence_index,
    )
