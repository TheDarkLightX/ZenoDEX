"""Injective route-effect identities retained across epoch aggregation.

An epoch effect plan may combine equal rows from several commands.  This value
keeps each authenticated route row addressable by its command occurrence and
canonical row index.  It is provenance data and grants no verification or
publication authority.
"""

from __future__ import annotations

from dataclasses import dataclass

from .global_settlement_types_v1 import (
    GLOBAL_SETTLEMENT_ABI_V1,
    MAX_U64_V1,
    EconomicEffectRowV1,
    GlobalEconomicEffectPlanV1,
    _require_root,
    hash_global_v1,
)


@dataclass(frozen=True, slots=True)
class EconomicEffectOccurrenceV1:
    effect_occurrence_id: str
    command_occurrence_id: str
    route_release_id: str
    effect_index: int
    effect_row: EconomicEffectRowV1

    def __post_init__(self) -> None:
        self._validate_content_fields(
            command_occurrence_id=self.command_occurrence_id,
            route_release_id=self.route_release_id,
            effect_index=self.effect_index,
            effect_row=self.effect_row,
        )
        if type(self.effect_occurrence_id) is not str:
            raise TypeError("economic effect occurrence id must be exact str")
        _require_root(
            self.effect_occurrence_id,
            name="economic effect occurrence id",
        )
        if self.effect_occurrence_id != self.derived_effect_occurrence_id:
            raise ValueError("economic effect occurrence id is not content-derived")

    @classmethod
    def build(
        cls,
        *,
        command_occurrence_id: str,
        route_release_id: str,
        effect_index: int,
        effect_row: EconomicEffectRowV1,
    ) -> EconomicEffectOccurrenceV1:
        cls._validate_content_fields(
            command_occurrence_id=command_occurrence_id,
            route_release_id=route_release_id,
            effect_index=effect_index,
            effect_row=effect_row,
        )
        content = cls._content(
            command_occurrence_id=command_occurrence_id,
            route_release_id=route_release_id,
            effect_index=effect_index,
            effect_row=effect_row,
        )
        return cls(
            effect_occurrence_id=hash_global_v1(
                "global-economic-effect-occurrence-v1",
                content,
            ),
            command_occurrence_id=command_occurrence_id,
            route_release_id=route_release_id,
            effect_index=effect_index,
            effect_row=effect_row,
        )

    @staticmethod
    def _validate_content_fields(
        *,
        command_occurrence_id: str,
        route_release_id: str,
        effect_index: int,
        effect_row: EconomicEffectRowV1,
    ) -> None:
        for name, value in (
            ("command occurrence id", command_occurrence_id),
            ("route release id", route_release_id),
        ):
            if type(value) is not str:
                raise TypeError(f"economic effect {name} must be exact str")
            _require_root(value, name=f"economic effect {name}")
        if type(effect_index) is not int:
            raise TypeError("economic effect index must be an exact integer")
        if not 0 <= effect_index <= MAX_U64_V1:
            raise ValueError("economic effect index must fit an unsigned 64-bit integer")
        if type(effect_row) is not EconomicEffectRowV1:
            raise TypeError("economic effect occurrence row must be exact typed data")

    @staticmethod
    def _content(
        *,
        command_occurrence_id: str,
        route_release_id: str,
        effect_index: int,
        effect_row: EconomicEffectRowV1,
    ) -> dict[str, object]:
        return {
            "schema": GLOBAL_SETTLEMENT_ABI_V1,
            "command_occurrence_id": command_occurrence_id,
            "route_release_id": route_release_id,
            "effect_index": effect_index,
            "effect_row": effect_row,
        }

    @property
    def derived_effect_occurrence_id(self) -> str:
        return hash_global_v1(
            "global-economic-effect-occurrence-v1",
            self._content(
                command_occurrence_id=self.command_occurrence_id,
                route_release_id=self.route_release_id,
                effect_index=self.effect_index,
                effect_row=self.effect_row,
            ),
        )

    def to_canonical(self) -> dict[str, object]:
        return {
            **self._content(
                command_occurrence_id=self.command_occurrence_id,
                route_release_id=self.route_release_id,
                effect_index=self.effect_index,
                effect_row=self.effect_row,
            ),
            "effect_occurrence_id": self.effect_occurrence_id,
        }


def derive_route_effect_occurrences_v1(
    *,
    command_occurrence_id: str,
    route_release_id: str,
    effect_plan: GlobalEconomicEffectPlanV1,
) -> tuple[EconomicEffectOccurrenceV1, ...]:
    """Derive one stable identity for every canonical route effect row."""

    if type(command_occurrence_id) is not str:
        raise TypeError("route effect command occurrence id must be exact str")
    if type(route_release_id) is not str:
        raise TypeError("route effect release id must be exact str")
    if type(effect_plan) is not GlobalEconomicEffectPlanV1:
        raise TypeError("route effect plan must be exact typed data")
    _require_root(
        command_occurrence_id,
        name="route effect command occurrence id",
    )
    _require_root(route_release_id, name="route effect release id")
    if effect_plan.occurrence_consumptions != (command_occurrence_id,):
        raise ValueError("route effect plan must consume the exact consumed occurrence")
    return tuple(
        EconomicEffectOccurrenceV1.build(
            command_occurrence_id=command_occurrence_id,
            route_release_id=route_release_id,
            effect_index=index,
            effect_row=row,
        )
        for index, row in enumerate(effect_plan.rows)
    )


__all__ = [
    "EconomicEffectOccurrenceV1",
    "derive_route_effect_occurrences_v1",
]
