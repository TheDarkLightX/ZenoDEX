from __future__ import annotations

from dataclasses import dataclass

from .strategy_budget_guard_v1_adapter import MAX_U32


def _require_u32(name: str, value: object, *, minimum: int = 0) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    out = int(value)
    if out < minimum or out > MAX_U32:
        raise ValueError(f"{name} out of u32 range: {out}")
    return out


@dataclass(frozen=True)
class StrategyOracleFreshnessResult:
    ok: bool
    quote_epoch_not_future: bool
    freshness_ok: bool
    age_epochs: int | None
    error: str | None = None


def check_oracle_freshness(
    *,
    current_epoch: int,
    quote_epoch: int,
    max_oracle_staleness_epochs: int,
) -> StrategyOracleFreshnessResult:
    current_epoch = _require_u32("current_epoch", current_epoch)
    quote_epoch = _require_u32("quote_epoch", quote_epoch)
    max_oracle_staleness_epochs = _require_u32(
        "max_oracle_staleness_epochs",
        max_oracle_staleness_epochs,
        minimum=1,
    )

    if quote_epoch > current_epoch:
        return StrategyOracleFreshnessResult(
            ok=False,
            quote_epoch_not_future=False,
            freshness_ok=False,
            age_epochs=None,
            error=f"quote_epoch_in_future:{quote_epoch}>{current_epoch}",
        )

    age_epochs = current_epoch - quote_epoch
    freshness_ok = age_epochs <= max_oracle_staleness_epochs
    if not freshness_ok:
        return StrategyOracleFreshnessResult(
            ok=False,
            quote_epoch_not_future=True,
            freshness_ok=False,
            age_epochs=age_epochs,
            error=f"quote_receipt_stale:age={age_epochs},max={max_oracle_staleness_epochs}",
        )

    return StrategyOracleFreshnessResult(
        ok=True,
        quote_epoch_not_future=True,
        freshness_ok=True,
        age_epochs=age_epochs,
    )
