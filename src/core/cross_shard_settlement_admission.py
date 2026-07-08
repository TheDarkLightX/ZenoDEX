from __future__ import annotations

from collections import defaultdict
from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from typing import Any

from .cross_shard_decision_certificate import (
    CrossShardDecisionCertificateV1,
    CrossShardDecisionState,
    verify_cross_shard_decision_certificate_payload,
)
from .sharded_settlement_certificate import (
    CrossShardLegV1,
    ShardedSettlementCertificateV1,
    verify_sharded_settlement_certificate_payload,
)


@dataclass(frozen=True)
class CrossShardSettlementAdmissionResult:
    ok: bool
    error: str | None
    sharded_settlement_certificate_hash: str | None = None
    shard_count: int | None = None
    cross_shard_transfer_count: int | None = None
    decision_certificate_count: int | None = None
    committed_transfer_count: int | None = None
    rejected_transfer_count: int | None = None
    pending_transfer_count: int | None = None
    applied_cross_shard_transfer_count: int | None = None
    applied_cross_shard_amounts_by_asset: tuple[tuple[str, int], ...] = ()
    user_statuses: tuple[str, ...] = ()

    def __post_init__(self) -> None:
        if not isinstance(self.ok, bool):
            raise TypeError("ok must be bool")
        if self.ok:
            if self.error is not None:
                raise ValueError("accepted cross-shard admission result cannot include error")
            _require_hash(
                self.sharded_settlement_certificate_hash,
                name="result.sharded_settlement_certificate_hash",
            )
            _require_positive_int(self.shard_count, name="result.shard_count")
            _require_non_negative_int(
                self.cross_shard_transfer_count,
                name="result.cross_shard_transfer_count",
            )
            _require_non_negative_int(
                self.decision_certificate_count,
                name="result.decision_certificate_count",
            )
            _require_non_negative_int(
                self.committed_transfer_count,
                name="result.committed_transfer_count",
            )
            _require_non_negative_int(
                self.rejected_transfer_count,
                name="result.rejected_transfer_count",
            )
            _require_non_negative_int(
                self.pending_transfer_count,
                name="result.pending_transfer_count",
            )
            _require_non_negative_int(
                self.applied_cross_shard_transfer_count,
                name="result.applied_cross_shard_transfer_count",
            )
            _validate_amount_summary(
                self.applied_cross_shard_amounts_by_asset,
                name="result.applied_cross_shard_amounts_by_asset",
            )
            if not isinstance(self.user_statuses, tuple):
                raise TypeError("result.user_statuses must be a tuple")
            for status in self.user_statuses:
                _require_id(status, name="result.user_status")
            return
        if not isinstance(self.error, str) or not self.error:
            raise ValueError("rejected cross-shard admission result must include error")
        if (
            self.sharded_settlement_certificate_hash is not None
            or self.shard_count is not None
            or self.cross_shard_transfer_count is not None
            or self.decision_certificate_count is not None
            or self.committed_transfer_count is not None
            or self.rejected_transfer_count is not None
            or self.pending_transfer_count is not None
            or self.applied_cross_shard_transfer_count is not None
            or self.applied_cross_shard_amounts_by_asset
            or self.user_statuses
        ):
            raise ValueError("rejected cross-shard admission result cannot include accepted artifacts")


def verify_cross_shard_settlement_admission_payload(
    sharded_settlement_payload: Mapping[str, Any],
    *,
    decision_certificate_payloads: Sequence[Mapping[str, Any]] | None = None,
    expected_shard_ids: Sequence[str] | None = None,
    expected_shard_ids_hash: str | None = None,
    current_step: int | None = None,
) -> CrossShardSettlementAdmissionResult:
    """Verify sharded settlement plus one global decision per cross-shard transfer.

    The sharded settlement certificate owns local balance and matched transfer
    legs. The decision certificates own user-visible global commit/reject/pending
    status. This function composes the two boundaries and fails closed if either
    side is missing or mismatched.
    """

    try:
        decision_payloads = _parse_decision_payloads(decision_certificate_payloads)
        sharded_result = verify_sharded_settlement_certificate_payload(
            sharded_settlement_payload,
            expected_shard_ids=expected_shard_ids,
            expected_shard_ids_hash=expected_shard_ids_hash,
        )
        if not sharded_result.ok:
            raise ValueError(f"sharded settlement certificate rejected: {sharded_result.error}")
        certificate = ShardedSettlementCertificateV1.from_payload(sharded_settlement_payload)
        transfers = _expected_transfer_participants(certificate.cross_shard_legs)
        transfer_amounts = _cross_shard_transfer_amounts(certificate.cross_shard_legs)
        decisions = _parse_decision_certificates(decision_payloads)
        _validate_decision_coverage(
            decisions=decisions,
            transfers=transfers,
            batch_id=certificate.batch_id,
            sharded_settlement_certificate_hash=sharded_result.certificate_hash,
            current_step=current_step,
        )
    except (TypeError, ValueError) as exc:
        return CrossShardSettlementAdmissionResult(ok=False, error=str(exc))

    counts = _decision_counts(decisions)
    applied_count, applied_amounts = _applied_cross_shard_amounts_by_asset(
        decisions=decisions,
        transfer_amounts=transfer_amounts,
    )
    return CrossShardSettlementAdmissionResult(
        ok=True,
        error=None,
        sharded_settlement_certificate_hash=sharded_result.certificate_hash,
        shard_count=sharded_result.shard_count,
        cross_shard_transfer_count=len(transfers),
        decision_certificate_count=len(decisions),
        committed_transfer_count=counts[CrossShardDecisionState.COMMIT],
        rejected_transfer_count=counts[CrossShardDecisionState.REJECT],
        pending_transfer_count=counts[CrossShardDecisionState.PENDING],
        applied_cross_shard_transfer_count=applied_count,
        applied_cross_shard_amounts_by_asset=applied_amounts,
        user_statuses=tuple(decisions[transfer_id].user_status for transfer_id in sorted(decisions)),
    )


@dataclass(frozen=True)
class _DecisionRecord:
    transfer_id: str
    decision: CrossShardDecisionState
    user_status: str
    payload: Mapping[str, Any]


@dataclass(frozen=True)
class _TransferAmount:
    asset_id: str
    amount_atoms: int


def _parse_decision_payloads(
    value: Sequence[Mapping[str, Any]] | None,
) -> tuple[Mapping[str, Any], ...]:
    if value is None:
        return ()
    if not isinstance(value, Sequence) or isinstance(value, (str, bytes, bytearray)):
        raise TypeError("decision_certificate_payloads must be a sequence")
    return tuple(_require_mapping(row, name="decision_certificate_payload") for row in value)


def _expected_transfer_participants(
    legs: Sequence[CrossShardLegV1],
) -> dict[str, tuple[str, ...]]:
    grouped: dict[str, set[str]] = defaultdict(set)
    for leg in legs:
        grouped[leg.transfer_id].add(leg.shard_id)
        grouped[leg.transfer_id].add(leg.counterparty_shard_id)
    return {
        transfer_id: tuple(sorted(participants))
        for transfer_id, participants in grouped.items()
    }


def _cross_shard_transfer_amounts(
    legs: Sequence[CrossShardLegV1],
) -> dict[str, _TransferAmount]:
    grouped: dict[str, list[CrossShardLegV1]] = defaultdict(list)
    for leg in legs:
        grouped[leg.transfer_id].append(leg)

    out: dict[str, _TransferAmount] = {}
    for transfer_id, transfer_legs in grouped.items():
        if len(transfer_legs) != 2:
            raise ValueError(f"cross-shard transfer {transfer_id} must have exactly two legs")
        debit = next((leg for leg in transfer_legs if leg.side == "debit"), None)
        credit = next((leg for leg in transfer_legs if leg.side == "credit"), None)
        if debit is None or credit is None:
            raise ValueError(f"cross-shard transfer {transfer_id} must have one debit and one credit")
        if debit.asset_id != credit.asset_id:
            raise ValueError(f"cross-shard transfer {transfer_id} asset mismatch")
        if debit.amount_atoms != credit.amount_atoms:
            raise ValueError(f"cross-shard transfer {transfer_id} amount mismatch")
        out[transfer_id] = _TransferAmount(
            asset_id=debit.asset_id,
            amount_atoms=debit.amount_atoms,
        )
    return out


def _parse_decision_certificates(
    decision_payloads: Sequence[Mapping[str, Any]],
) -> dict[str, _DecisionRecord]:
    decisions: dict[str, _DecisionRecord] = {}
    for payload in decision_payloads:
        certificate = CrossShardDecisionCertificateV1.from_payload(payload)
        if certificate.transfer_id in decisions:
            raise ValueError(
                f"duplicate decision certificate for cross-shard transfer {certificate.transfer_id}"
            )
        decisions[certificate.transfer_id] = _DecisionRecord(
            transfer_id=certificate.transfer_id,
            decision=certificate.decision,
            user_status=_decision_status(certificate),
            payload=payload,
        )
    return decisions


def _validate_decision_coverage(
    *,
    decisions: dict[str, _DecisionRecord],
    transfers: dict[str, tuple[str, ...]],
    batch_id: str,
    sharded_settlement_certificate_hash: str | None,
    current_step: int | None,
) -> None:
    if sharded_settlement_certificate_hash is None:
        raise ValueError("sharded settlement certificate hash is missing")
    if not transfers and decisions:
        raise ValueError("decision certificates supplied for settlement with no cross-shard transfers")
    for transfer_id in sorted(decisions):
        if transfer_id not in transfers:
            raise ValueError(f"decision certificate references unknown cross-shard transfer {transfer_id}")
    for transfer_id in sorted(transfers):
        if transfer_id not in decisions:
            raise ValueError(f"missing decision certificate for cross-shard transfer {transfer_id}")
    if transfers and current_step is None:
        raise ValueError("current_step is required for cross-shard decision admission")

    for transfer_id in sorted(transfers):
        record = decisions[transfer_id]
        certificate = CrossShardDecisionCertificateV1.from_payload(record.payload)
        if certificate.batch_id != batch_id:
            raise ValueError(
                f"decision certificate batch_id mismatch for transfer {certificate.transfer_id}"
            )
        participant_ids = transfers[certificate.transfer_id]
        result = verify_cross_shard_decision_certificate_payload(
            record.payload,
            expected_participant_shard_ids=participant_ids,
            expected_sharded_settlement_certificate_hash=sharded_settlement_certificate_hash,
            current_step=current_step,
        )
        if not result.ok:
            raise ValueError(
                f"decision certificate {certificate.transfer_id} rejected: {result.error}"
            )


def _decision_status(certificate: CrossShardDecisionCertificateV1) -> str:
    if certificate.decision == CrossShardDecisionState.COMMIT:
        return "global_cross_shard_commit_accepted"
    if certificate.decision == CrossShardDecisionState.REJECT:
        return "global_cross_shard_commit_rejected"
    return "pending_global_cross_shard_decision"


def _decision_counts(
    decisions: Mapping[str, _DecisionRecord],
) -> dict[CrossShardDecisionState, int]:
    counts = {
        CrossShardDecisionState.COMMIT: 0,
        CrossShardDecisionState.REJECT: 0,
        CrossShardDecisionState.PENDING: 0,
    }
    for decision in decisions.values():
        counts[decision.decision] += 1
    return counts


def _applied_cross_shard_amounts_by_asset(
    *,
    decisions: Mapping[str, _DecisionRecord],
    transfer_amounts: Mapping[str, _TransferAmount],
) -> tuple[int, tuple[tuple[str, int], ...]]:
    by_asset: dict[str, int] = defaultdict(int)
    applied_count = 0
    for transfer_id, decision in decisions.items():
        if decision.decision != CrossShardDecisionState.COMMIT:
            continue
        amount = transfer_amounts.get(transfer_id)
        if amount is None:
            raise ValueError(f"missing cross-shard transfer amount for {transfer_id}")
        applied_count += 1
        by_asset[amount.asset_id] += amount.amount_atoms
    return applied_count, tuple(sorted(by_asset.items()))


def _validate_amount_summary(
    value: object,
    *,
    name: str,
) -> None:
    if not isinstance(value, tuple):
        raise TypeError(f"{name} must be a tuple")
    previous_asset: str | None = None
    for idx, row in enumerate(value):
        if not isinstance(row, tuple) or len(row) != 2:
            raise TypeError(f"{name}[{idx}] must be an (asset_id, amount_atoms) tuple")
        asset_id = _require_id(row[0], name=f"{name}[{idx}].asset_id")
        _require_positive_int(row[1], name=f"{name}[{idx}].amount_atoms")
        if previous_asset is not None and asset_id <= previous_asset:
            raise ValueError(f"{name} must be strictly sorted by asset_id")
        previous_asset = asset_id


def _require_mapping(value: object, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be an object")
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


def _require_id(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a str")
    if not value:
        raise ValueError(f"{name} must be non-empty")
    if "\x00" in value:
        raise ValueError(f"{name} must not contain NUL")
    return value


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
