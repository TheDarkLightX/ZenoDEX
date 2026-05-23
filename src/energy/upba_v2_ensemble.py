"""Small ensemble helpers for advisory UPBA v2 energy rankers."""

from __future__ import annotations

from dataclasses import dataclass
from math import sqrt
from pathlib import Path
from statistics import fmean
from typing import Any, Callable, Sequence

from .upba_v2_energy_model import LinearEnergyModel, load_linear_model


FeatureGetter = Callable[[dict[str, Any]], Sequence[float]]


@dataclass(frozen=True)
class RankStats:
    """Per-candidate rank statistics across an advisory model ensemble."""

    mean_rank: float
    std_rank: float
    min_rank: int
    max_rank: int


@dataclass(frozen=True)
class LinearEnergyEnsemble:
    """A tiny ensemble of linear energy models with shared feature schema."""

    models: tuple[LinearEnergyModel, ...]

    def __post_init__(self) -> None:
        if not self.models:
            raise ValueError("ensemble must contain at least one model")
        feature_names = self.models[0].feature_names
        for model in self.models[1:]:
            if model.feature_names != feature_names:
                raise ValueError("all ensemble members must share feature_names")

    @property
    def feature_names(self) -> tuple[str, ...]:
        return self.models[0].feature_names

    def member_energies(self, features: Sequence[float]) -> tuple[float, ...]:
        return tuple(model.energy(features) for model in self.models)

    def mean_energy(self, features: Sequence[float]) -> float:
        return fmean(self.member_energies(features))

    def energy_stddev(self, features: Sequence[float]) -> float:
        values = self.member_energies(features)
        return _stddev(values)

    def rank_stats(
        self,
        rows: Sequence[dict[str, Any]],
        *,
        feature_getter: FeatureGetter,
    ) -> dict[str, RankStats]:
        """Return candidate rank moments across ensemble members.

        Ranks are one-based within the supplied candidate set. The helper is
        deliberately batch-local, because cross-batch raw energies may have
        different scales.
        """

        ranks_by_hash: dict[str, list[int]] = {
            str(row["candidate_hash"]): [] for row in rows
        }
        for model in self.models:
            ordered = sorted(
                rows,
                key=lambda row: (
                    model.energy(feature_getter(row)),
                    str(row["candidate_hash"]),
                ),
            )
            for index, row in enumerate(ordered, start=1):
                ranks_by_hash[str(row["candidate_hash"])].append(index)
        return {
            candidate_hash: RankStats(
                mean_rank=fmean(ranks),
                std_rank=_stddev(ranks),
                min_rank=min(ranks),
                max_rank=max(ranks),
            )
            for candidate_hash, ranks in ranks_by_hash.items()
        }

    def order_by_rank_consensus(
        self,
        rows: Sequence[dict[str, Any]],
        *,
        feature_getter: FeatureGetter,
        disagreement_weight: float = 0.0,
        tiebreaker: Callable[[dict[str, Any]], object] | None = None,
    ) -> list[dict[str, Any]]:
        if disagreement_weight < 0:
            raise ValueError("disagreement_weight must be nonnegative")
        stats = self.rank_stats(rows, feature_getter=feature_getter)
        return sorted(
            rows,
            key=lambda row: (
                stats[str(row["candidate_hash"])].mean_rank
                + disagreement_weight
                * stats[str(row["candidate_hash"])].std_rank,
                stats[str(row["candidate_hash"])].std_rank,
                tiebreaker(row) if tiebreaker is not None else str(row["candidate_hash"]),
            ),
        )


def load_linear_ensemble(paths: Sequence[str | Path]) -> LinearEnergyEnsemble:
    return LinearEnergyEnsemble(tuple(load_linear_model(path) for path in paths))


def _stddev(values: Sequence[float | int]) -> float:
    if len(values) <= 1:
        return 0.0
    avg = fmean(float(value) for value in values)
    return sqrt(fmean((float(value) - avg) ** 2 for value in values))
