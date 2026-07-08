from __future__ import annotations

from dataclasses import dataclass

from .cross_shard_settlement_admission import CrossShardSettlementAdmissionResult


@dataclass(frozen=True)
class CrossShardLedgerPostingSummaryV1:
    asset_id: str
    committed_debit_atoms: int
    committed_credit_atoms: int

    def __post_init__(self) -> None:
        _require_id(self.asset_id, name="posting.asset_id")
        debit = _require_positive_int(
            self.committed_debit_atoms,
            name="posting.committed_debit_atoms",
        )
        credit = _require_positive_int(
            self.committed_credit_atoms,
            name="posting.committed_credit_atoms",
        )
        if debit != credit:
            raise ValueError("cross-shard ledger posting summary must balance debit and credit")

    def to_payload(self) -> dict[str, object]:
        return {
            "asset_id": self.asset_id,
            "committed_debit_atoms": int(self.committed_debit_atoms),
            "committed_credit_atoms": int(self.committed_credit_atoms),
        }


@dataclass(frozen=True)
class CrossShardLedgerPostingBuildResult:
    ok: bool
    error: str | None
    sharded_settlement_certificate_hash: str | None = None
    postings: tuple[CrossShardLedgerPostingSummaryV1, ...] = ()
    total_committed_debit_atoms: int | None = None
    total_committed_credit_atoms: int | None = None

    def __post_init__(self) -> None:
        if not isinstance(self.ok, bool):
            raise TypeError("ok must be bool")
        if self.ok:
            if self.error is not None:
                raise ValueError("accepted cross-shard ledger posting result cannot include error")
            _require_hash(
                self.sharded_settlement_certificate_hash,
                name="result.sharded_settlement_certificate_hash",
            )
            if not isinstance(self.postings, tuple):
                raise TypeError("result.postings must be a tuple")
            for posting in self.postings:
                if not isinstance(posting, CrossShardLedgerPostingSummaryV1):
                    raise TypeError("result.postings must contain posting summaries")
            debit = _require_non_negative_int(
                self.total_committed_debit_atoms,
                name="result.total_committed_debit_atoms",
            )
            credit = _require_non_negative_int(
                self.total_committed_credit_atoms,
                name="result.total_committed_credit_atoms",
            )
            if debit != credit:
                raise ValueError("cross-shard ledger posting totals must balance")
            return
        if not isinstance(self.error, str) or not self.error:
            raise ValueError("rejected cross-shard ledger posting result must include error")
        if (
            self.sharded_settlement_certificate_hash is not None
            or self.postings
            or self.total_committed_debit_atoms is not None
            or self.total_committed_credit_atoms is not None
        ):
            raise ValueError("rejected cross-shard ledger posting result cannot include artifacts")


def build_cross_shard_ledger_posting_summary(
    admission_result: CrossShardSettlementAdmissionResult,
) -> CrossShardLedgerPostingBuildResult:
    try:
        if not isinstance(admission_result, CrossShardSettlementAdmissionResult):
            raise TypeError("admission_result must be CrossShardSettlementAdmissionResult")
        if not admission_result.ok:
            raise ValueError("cross-shard admission result is rejected")
        postings = tuple(
            CrossShardLedgerPostingSummaryV1(
                asset_id=asset_id,
                committed_debit_atoms=amount_atoms,
                committed_credit_atoms=amount_atoms,
            )
            for asset_id, amount_atoms in admission_result.applied_cross_shard_amounts_by_asset
        )
        total = sum(posting.committed_debit_atoms for posting in postings)
        return CrossShardLedgerPostingBuildResult(
            ok=True,
            error=None,
            sharded_settlement_certificate_hash=admission_result.sharded_settlement_certificate_hash,
            postings=postings,
            total_committed_debit_atoms=total,
            total_committed_credit_atoms=total,
        )
    except (TypeError, ValueError) as exc:
        return CrossShardLedgerPostingBuildResult(ok=False, error=str(exc))


def _require_id(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a str")
    if not value:
        raise ValueError(f"{name} must be non-empty")
    if "\x00" in value:
        raise ValueError(f"{name} must not contain NUL")
    return value


def _require_hash(value: object, *, name: str) -> str:
    text = _require_id(value, name=name)
    if not text.startswith("0x") or len(text) != 66:
        raise ValueError(f"{name} must be a 0x-prefixed sha256 hex digest")
    try:
        int(text[2:], 16)
    except ValueError as exc:
        raise ValueError(f"{name} must be a 0x-prefixed sha256 hex digest") from exc
    if text[2:].lower() != text[2:]:
        raise ValueError(f"{name} must use lowercase hex")
    return text


def _require_positive_int(value: object, *, name: str) -> int:
    out = _require_int(value, name=name)
    if out <= 0:
        raise ValueError(f"{name} must be positive")
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
