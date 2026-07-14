"""Private projection for governed Spot V7 sampled DA prerequisite V2."""

from __future__ import annotations

from dataclasses import dataclass

from src.integration._zrpf_spot_v7_governed_da_projection import (
    _SpotV7GovernedDaPrerequisiteProjectionV1,
)
from src.integration.zrpf_sampled_retrievability_v1.model import (
    require_root,
    require_u64,
)


@dataclass(frozen=True, slots=True)
class _SpotV7GovernedDaPrerequisiteProjectionV2:
    """V1 exact-content/sample projection plus governed chain/beacon provenance."""

    base: _SpotV7GovernedDaPrerequisiteProjectionV1
    zeno_ledger_chain_id: str
    source_network_id: str
    source_protocol_id: str
    source_epoch_lag: int
    source_checkpoint_sequence: int
    source_checkpoint_hash: str
    source_finality_policy_root: str
    source_finality_certificate_root: str
    source_finality_evidence_root: str

    def __post_init__(self) -> None:
        if type(self.base) is not _SpotV7GovernedDaPrerequisiteProjectionV1:
            raise TypeError("governed DA V2 base projection has the wrong type")
        if type(self.zeno_ledger_chain_id) is not str or not self.zeno_ledger_chain_id:
            raise ValueError("governed DA V2 chain id must be nonempty")
        for name in ("source_epoch_lag", "source_checkpoint_sequence"):
            require_u64(getattr(self, name), name=f"governed DA V2 {name}")
        for name in (
            "source_network_id",
            "source_protocol_id",
            "source_checkpoint_hash",
            "source_finality_policy_root",
            "source_finality_certificate_root",
            "source_finality_evidence_root",
        ):
            require_root(getattr(self, name), name=f"governed DA V2 {name}")
