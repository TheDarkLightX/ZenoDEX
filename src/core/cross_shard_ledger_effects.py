from __future__ import annotations

from dataclasses import dataclass

from .cross_shard_ledger_posting import (
    CrossShardLedgerPostingBuildResult,
)

CROSS_SHARD_DEBIT_ESCROW_ACCOUNT_V1 = "system:cross_shard:debit_escrow"
CROSS_SHARD_CREDIT_ESCROW_ACCOUNT_V1 = "system:cross_shard:credit_escrow"
CROSS_SHARD_LEDGER_EFFECT_SOURCE_V1 = "cross_shard_posting_summary_v1"
CROSS_SHARD_LEDGER_EFFECT_SCHEMA_V1 = "zenodex/cross_shard_ledger_effect/v1"


@dataclass(frozen=True)
class CrossShardLedgerEffectV1:
    asset_id: str
    account_id: str
    delta_atoms: int
    source: str = CROSS_SHARD_LEDGER_EFFECT_SOURCE_V1

    def __post_init__(self) -> None:
        _require_id(self.asset_id, name="effect.asset_id")
        _require_id(self.account_id, name="effect.account_id")
        _require_non_zero_int(self.delta_atoms, name="effect.delta_atoms")
        if self.source != CROSS_SHARD_LEDGER_EFFECT_SOURCE_V1:
            raise ValueError("cross-shard ledger effect source mismatch")

    def to_payload(self) -> dict[str, object]:
        return {
            "schema": CROSS_SHARD_LEDGER_EFFECT_SCHEMA_V1,
            "asset_id": self.asset_id,
            "account_id": self.account_id,
            "delta_atoms": int(self.delta_atoms),
            "source": self.source,
        }


@dataclass(frozen=True)
class CrossShardLedgerEffectsBuildResult:
    ok: bool
    error: str | None
    effects: tuple[CrossShardLedgerEffectV1, ...] = ()
    total_debit_atoms: int | None = None
    total_credit_atoms: int | None = None

    def __post_init__(self) -> None:
        if not isinstance(self.ok, bool):
            raise TypeError("ok must be bool")
        if self.ok:
            if self.error is not None:
                raise ValueError("accepted cross-shard ledger effects result cannot include error")
            if not isinstance(self.effects, tuple):
                raise TypeError("result.effects must be a tuple")
            for effect in self.effects:
                if not isinstance(effect, CrossShardLedgerEffectV1):
                    raise TypeError("result.effects must contain ledger effects")
            debit = _require_non_negative_int(
                self.total_debit_atoms,
                name="result.total_debit_atoms",
            )
            credit = _require_non_negative_int(
                self.total_credit_atoms,
                name="result.total_credit_atoms",
            )
            if debit != _sum_debit_atoms(self.effects):
                raise ValueError("cross-shard ledger effects debit total mismatch")
            if credit != _sum_credit_atoms(self.effects):
                raise ValueError("cross-shard ledger effects credit total mismatch")
            if debit != credit:
                raise ValueError("cross-shard ledger effects totals must balance")
            return
        if not isinstance(self.error, str) or not self.error:
            raise ValueError("rejected cross-shard ledger effects result must include error")
        if (
            self.effects
            or self.total_debit_atoms is not None
            or self.total_credit_atoms is not None
        ):
            raise ValueError("rejected cross-shard ledger effects result cannot include artifacts")


def build_cross_shard_ledger_effects_from_posting_result(
    posting_result: CrossShardLedgerPostingBuildResult,
) -> CrossShardLedgerEffectsBuildResult:
    try:
        if not isinstance(posting_result, CrossShardLedgerPostingBuildResult):
            raise TypeError("posting_result must be CrossShardLedgerPostingBuildResult")
        if not posting_result.ok:
            raise ValueError("cross-shard posting result is rejected")
        effects: list[CrossShardLedgerEffectV1] = []
        for posting in posting_result.postings:
            effects.append(
                CrossShardLedgerEffectV1(
                    asset_id=posting.asset_id,
                    account_id=CROSS_SHARD_DEBIT_ESCROW_ACCOUNT_V1,
                    delta_atoms=-int(posting.committed_debit_atoms),
                )
            )
            effects.append(
                CrossShardLedgerEffectV1(
                    asset_id=posting.asset_id,
                    account_id=CROSS_SHARD_CREDIT_ESCROW_ACCOUNT_V1,
                    delta_atoms=int(posting.committed_credit_atoms),
                )
            )
        effect_tuple = tuple(effects)
        total_debit = _sum_debit_atoms(effect_tuple)
        total_credit = _sum_credit_atoms(effect_tuple)
        return CrossShardLedgerEffectsBuildResult(
            ok=True,
            error=None,
            effects=effect_tuple,
            total_debit_atoms=total_debit,
            total_credit_atoms=total_credit,
        )
    except (TypeError, ValueError) as exc:
        return CrossShardLedgerEffectsBuildResult(ok=False, error=str(exc))


def _sum_debit_atoms(effects: tuple[CrossShardLedgerEffectV1, ...]) -> int:
    return sum(-effect.delta_atoms for effect in effects if effect.delta_atoms < 0)


def _sum_credit_atoms(effects: tuple[CrossShardLedgerEffectV1, ...]) -> int:
    return sum(effect.delta_atoms for effect in effects if effect.delta_atoms > 0)


def _require_id(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a str")
    if not value:
        raise ValueError(f"{name} must be non-empty")
    if "\x00" in value:
        raise ValueError(f"{name} must not contain NUL")
    return value


def _require_non_zero_int(value: object, *, name: str) -> int:
    out = _require_int(value, name=name)
    if out == 0:
        raise ValueError(f"{name} must be non-zero")
    return out


def _require_non_negative_int(value: object, *, name: str) -> int:
    out = _require_int(value, name=name)
    if out < 0:
        raise ValueError(f"{name} must be non-negative")
    return out


def _require_int(value: object, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    return int(value)
