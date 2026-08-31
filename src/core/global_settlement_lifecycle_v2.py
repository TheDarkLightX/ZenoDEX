"""Oracle and terminal lifecycle values for GlobalSettlementABI V2."""

from __future__ import annotations

from dataclasses import dataclass, replace
from enum import Enum
from typing import ClassVar, Final

from .global_settlement_ownership_v2 import _DataclassTupleSnapshotPropertyV2
from .global_settlement_primitives_v2 import (
    GLOBAL_SETTLEMENT_ABI_V2,
    ZERO_ROOT_V2,
    LaneIdV2,
    _require_atoms_u128_v2,
    _require_bool_v2,
    _require_nonnegative_int_v2,
    _require_ordered_objects_v2,
    _require_root_v2,
    _require_token_v2,
    hash_global_v2,
)

MAX_ORACLE_OCCURRENCE_DELTAS_PER_PLAN_V2: Final = 64
MAX_TERMINAL_OBLIGATION_DELTAS_PER_PLAN_V2: Final = 64


@dataclass(frozen=True, slots=True, order=True)
class OracleOccurrenceStateV2:
    oracle_id: str
    occurrence_root: str
    observed_height: int
    finalized: bool

    def __post_init__(self) -> None:
        _require_token_v2(self.oracle_id, name="Oracle id")
        _require_root_v2(self.occurrence_root, name="Oracle occurrence root")
        _require_nonnegative_int_v2(self.observed_height, name="Oracle observed height")
        _require_bool_v2(self.finalized, name="Oracle finalized")

    def to_canonical(self) -> dict[str, object]:
        return {
            "oracle_id": self.oracle_id,
            "occurrence_root": self.occurrence_root,
            "observed_height": self.observed_height,
            "finalized": self.finalized,
        }


@dataclass(frozen=True, slots=True, order=True)
class OracleOccurrenceDeltaV2:
    oracle_id: str
    pre_occurrence: OracleOccurrenceStateV2 | None
    post_occurrence: OracleOccurrenceStateV2

    def __post_init__(self) -> None:
        _require_token_v2(self.oracle_id, name="Oracle occurrence delta id")
        if (
            self.pre_occurrence is not None
            and type(self.pre_occurrence) is not OracleOccurrenceStateV2
        ):
            raise TypeError("Oracle occurrence delta pre-value must be exact")
        if type(self.post_occurrence) is not OracleOccurrenceStateV2:
            raise TypeError("Oracle occurrence delta post-value must be exact")
        if self.pre_occurrence is not None:
            object.__setattr__(self, "pre_occurrence", replace(self.pre_occurrence))
        object.__setattr__(self, "post_occurrence", replace(self.post_occurrence))
        if self.post_occurrence.oracle_id != self.oracle_id:
            raise ValueError("Oracle occurrence delta post identity mismatch")
        if self.pre_occurrence is None:
            return
        if self.pre_occurrence.oracle_id != self.oracle_id:
            raise ValueError("Oracle occurrence delta pre identity mismatch")
        if self.pre_occurrence == self.post_occurrence:
            raise ValueError("Oracle occurrence delta must change the occurrence")
        if self.post_occurrence.observed_height < self.pre_occurrence.observed_height:
            raise ValueError("Oracle occurrence height cannot regress")
        if self.pre_occurrence.finalized and not self.post_occurrence.finalized:
            raise ValueError("Oracle occurrence finality cannot regress")
        if (
            self.post_occurrence.observed_height == self.pre_occurrence.observed_height
            and self.post_occurrence.occurrence_root != self.pre_occurrence.occurrence_root
        ):
            raise ValueError("Oracle occurrence root is immutable at one observed height")

    def to_canonical(self) -> dict[str, object]:
        return {
            "oracle_id": self.oracle_id,
            "pre_occurrence": self.pre_occurrence,
            "post_occurrence": self.post_occurrence,
        }


@dataclass(frozen=True)
class GlobalOracleOccurrencePlanV2:
    __slots__ = ("_deltas",)

    _deltas: ClassVar[tuple[OracleOccurrenceDeltaV2, ...]]
    deltas: tuple[OracleOccurrenceDeltaV2, ...] = (
        _DataclassTupleSnapshotPropertyV2(  # type: ignore[assignment]
            "_deltas",
            OracleOccurrenceDeltaV2,
            "global Oracle occurrence plan deltas",
            empty_default=True,
        )
    )

    def __post_init__(self) -> None:
        _require_ordered_objects_v2(
            self._deltas,
            name="global Oracle occurrence plan deltas",
            expected_type=OracleOccurrenceDeltaV2,
            key="oracle_id",
        )
        if len(self._deltas) > MAX_ORACLE_OCCURRENCE_DELTAS_PER_PLAN_V2:
            raise ValueError("global Oracle occurrence plan exceeds its bounded shape")

    @property
    def plan_root(self) -> str:
        if not self._deltas:
            return ZERO_ROOT_V2
        return hash_global_v2("global-oracle-occurrence-plan-v2", self.to_canonical())

    @classmethod
    def empty(cls) -> GlobalOracleOccurrencePlanV2:
        if cls is not GlobalOracleOccurrencePlanV2:
            raise TypeError("Oracle occurrence plan factory requires the exact type")
        return cls(())

    def to_canonical(self) -> dict[str, object]:
        return {"schema": GLOBAL_SETTLEMENT_ABI_V2, "deltas": self.deltas}


class TerminalObligationStatusV2(str, Enum):
    OPEN = "OPEN"
    DRAINED = "DRAINED"
    TOMBSTONED = "TOMBSTONED"


@dataclass(frozen=True, slots=True, order=True)
class TerminalObligationV2:
    obligation_id: str
    lane_id: LaneIdV2
    claimant: str
    asset: str
    liability_domain: str
    amount_atoms: int
    status: TerminalObligationStatusV2

    def __post_init__(self) -> None:
        _require_token_v2(self.obligation_id, name="terminal obligation id")
        if type(self.lane_id) is not LaneIdV2:
            raise TypeError("terminal obligation lane is not closed")
        _require_token_v2(self.claimant, name="terminal obligation claimant")
        _require_token_v2(self.asset, name="terminal obligation asset")
        _require_token_v2(
            self.liability_domain,
            name="terminal obligation liability domain",
        )
        _require_atoms_u128_v2(self.amount_atoms, name="terminal obligation amount")
        if type(self.status) is not TerminalObligationStatusV2:
            raise TypeError("terminal obligation status is not closed")

    def to_canonical(self) -> dict[str, object]:
        return {
            "obligation_id": self.obligation_id,
            "lane_id": self.lane_id,
            "claimant": self.claimant,
            "asset": self.asset,
            "liability_domain": self.liability_domain,
            "amount_atoms": self.amount_atoms,
            "status": self.status,
        }


@dataclass(frozen=True, slots=True, order=True)
class TerminalObligationDeltaV2:
    obligation_id: str
    pre_obligation: TerminalObligationV2 | None
    post_obligation: TerminalObligationV2

    def __post_init__(self) -> None:
        _require_token_v2(self.obligation_id, name="terminal obligation delta id")
        if (
            self.pre_obligation is not None
            and type(self.pre_obligation) is not TerminalObligationV2
        ):
            raise TypeError("terminal obligation delta pre-value must be exact")
        if type(self.post_obligation) is not TerminalObligationV2:
            raise TypeError("terminal obligation delta post-value must be exact")
        if self.pre_obligation is not None:
            object.__setattr__(self, "pre_obligation", replace(self.pre_obligation))
        object.__setattr__(self, "post_obligation", replace(self.post_obligation))
        if self.post_obligation.obligation_id != self.obligation_id:
            raise ValueError("terminal obligation delta post identity mismatch")
        if self.pre_obligation is None:
            if self.post_obligation.status is not TerminalObligationStatusV2.OPEN:
                raise ValueError("new terminal obligation must begin open")
            return
        if self.pre_obligation.obligation_id != self.obligation_id:
            raise ValueError("terminal obligation delta pre identity mismatch")
        if (
            self.pre_obligation.lane_id,
            self.pre_obligation.claimant,
            self.pre_obligation.asset,
            self.pre_obligation.liability_domain,
        ) != (
            self.post_obligation.lane_id,
            self.post_obligation.claimant,
            self.post_obligation.asset,
            self.post_obligation.liability_domain,
        ):
            raise ValueError("terminal obligation identity fields are immutable")
        if self.pre_obligation.status is not TerminalObligationStatusV2.OPEN:
            raise ValueError("terminal obligation is already terminal")
        if self.post_obligation.status is TerminalObligationStatusV2.OPEN:
            if self.post_obligation.amount_atoms == self.pre_obligation.amount_atoms:
                raise ValueError("open terminal obligation must change amount or become terminal")
            return
        if self.post_obligation.amount_atoms != self.pre_obligation.amount_atoms:
            raise ValueError("terminal transition must preserve the final open amount")
        if self.post_obligation.status not in {
            TerminalObligationStatusV2.DRAINED,
            TerminalObligationStatusV2.TOMBSTONED,
        }:
            raise ValueError("open terminal obligation must move to a terminal status")

    def to_canonical(self) -> dict[str, object]:
        return {
            "obligation_id": self.obligation_id,
            "pre_obligation": self.pre_obligation,
            "post_obligation": self.post_obligation,
        }


@dataclass(frozen=True)
class GlobalTerminalObligationPlanV2:
    __slots__ = ("_deltas",)

    _deltas: ClassVar[tuple[TerminalObligationDeltaV2, ...]]
    deltas: tuple[TerminalObligationDeltaV2, ...] = (
        _DataclassTupleSnapshotPropertyV2(  # type: ignore[assignment]
            "_deltas",
            TerminalObligationDeltaV2,
            "global terminal obligation plan deltas",
            empty_default=True,
        )
    )

    def __post_init__(self) -> None:
        _require_ordered_objects_v2(
            self._deltas,
            name="global terminal obligation plan deltas",
            expected_type=TerminalObligationDeltaV2,
            key="obligation_id",
        )
        if len(self._deltas) > MAX_TERMINAL_OBLIGATION_DELTAS_PER_PLAN_V2:
            raise ValueError("global terminal obligation plan exceeds its bounded shape")

    @property
    def plan_root(self) -> str:
        if not self._deltas:
            return ZERO_ROOT_V2
        return hash_global_v2("global-terminal-obligation-plan-v2", self.to_canonical())

    @classmethod
    def empty(cls) -> GlobalTerminalObligationPlanV2:
        if cls is not GlobalTerminalObligationPlanV2:
            raise TypeError("terminal obligation plan factory requires the exact type")
        return cls(())

    def to_canonical(self) -> dict[str, object]:
        return {"schema": GLOBAL_SETTLEMENT_ABI_V2, "deltas": self.deltas}


__all__ = [
    "MAX_ORACLE_OCCURRENCE_DELTAS_PER_PLAN_V2",
    "MAX_TERMINAL_OBLIGATION_DELTAS_PER_PLAN_V2",
    "OracleOccurrenceStateV2",
    "OracleOccurrenceDeltaV2",
    "GlobalOracleOccurrencePlanV2",
    "TerminalObligationStatusV2",
    "TerminalObligationV2",
    "TerminalObligationDeltaV2",
    "GlobalTerminalObligationPlanV2",
]
