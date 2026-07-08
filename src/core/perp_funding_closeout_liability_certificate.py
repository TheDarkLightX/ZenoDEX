from __future__ import annotations

import hashlib
from collections.abc import Mapping
from dataclasses import asdict, dataclass

from ..state.canonical import canonical_json_bytes
from .perp_funding_closeout_limited_liability import (
    build_limited_liability_funding_closeout_allocation,
)
from .perp_funding_closeout_receiver_rationing import (
    ReceiverClaimRow,
    ReceiverHaircutRationing,
    build_receiver_haircut_rationing,
    receiver_haircut_rationing_from_payload,
    receiver_haircut_rationing_to_payload,
)
from .perp_v2.math import funding_payment

CERT_SCHEMA = "zenodex.perp.funding_closeout_liability_certificate.v1"
RECEIPT_SCHEMA = "zenodex.perp.funding_closeout_liability_receipt.v1"
ALLOCATION_CERT_SCHEMA = "zenodex.perp.funding_closeout_liability_certificate.v2"
ALLOCATION_RECEIPT_SCHEMA = "zenodex.perp.funding_closeout_liability_receipt.v2"
RATIONED_ALLOCATION_RECEIPT_SCHEMA = (
    "zenodex.perp.funding_closeout_liability_receipt.v3"
)
SOURCE_AVAILABILITY_SCHEMA = "zenodex.perp.funding_closeout_source_availability.v1"
SOURCE_BOUND_RATIONED_ALLOCATION_RECEIPT_SCHEMA = (
    "zenodex.perp.funding_closeout_liability_receipt.v4"
)
SOURCE_PORTFOLIO_BOUND_RATIONED_ALLOCATION_RECEIPT_SCHEMA = (
    "zenodex.perp.funding_closeout_liability_receipt.v5"
)
CARRY_FORWARD_RECEIPT_SCHEMA = "zenodex.perp.funding_closeout_carry_forward_receipt.v1"
CARRIED_LIABILITY_ROOT_SCHEMA = "zenodex.perp.funding_closeout_carried_liability_root.v1"
DUE_VECTOR_SCHEMA = "zenodex.perp.pre_close_funding_due_vector.v1"
PRE_CLOSE_SNAPSHOT_SCHEMA = "zenodex.perp.funding_closeout_pre_close_snapshot.v1"
PRE_CLOSE_POSITION_SNAPSHOT_SCHEMA = "zenodex.perp.funding_closeout_pre_close_position_snapshot.v1"


def _require_int(value: object, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    return int(value)


def _require_non_negative_int(value: object, *, name: str) -> int:
    out = _require_int(value, name=name)
    if out < 0:
        raise ValueError(f"{name} must be non-negative")
    return out


def _require_positive_int(value: object, *, name: str) -> int:
    out = _require_int(value, name=name)
    if out <= 0:
        raise ValueError(f"{name} must be positive")
    return out


def _require_account(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a str")
    if not value:
        raise ValueError(f"{name} must be non-empty")
    if "\x00" in value:
        raise ValueError(f"{name} must not contain NUL")
    return value


@dataclass(frozen=True)
class PositionAccount:
    account_pubkey: str
    position_base: int

    def __post_init__(self) -> None:
        _require_account(self.account_pubkey, name="account_pubkey")
        _require_int(self.position_base, name="position_base")


@dataclass(frozen=True)
class DueRow:
    account_pubkey: str
    epoch: int
    position_base: int
    due_quote: int

    def __post_init__(self) -> None:
        _require_account(self.account_pubkey, name="account_pubkey")
        _require_non_negative_int(self.epoch, name="epoch")
        _require_int(self.position_base, name="position_base")
        _require_int(self.due_quote, name="due_quote")


@dataclass(frozen=True)
class ClosedLiabilityRow:
    account_pubkey: str
    epoch: int
    closed_due_quote: int
    carried_due_quote: int
    sink_draw_quote: int
    subrogated_claim_quote: int

    def __post_init__(self) -> None:
        _require_account(self.account_pubkey, name="account_pubkey")
        _require_non_negative_int(self.epoch, name="epoch")
        _require_int(self.closed_due_quote, name="closed_due_quote")
        _require_int(self.carried_due_quote, name="carried_due_quote")
        _require_non_negative_int(self.sink_draw_quote, name="sink_draw_quote")
        _require_non_negative_int(
            self.subrogated_claim_quote,
            name="subrogated_claim_quote",
        )


@dataclass(frozen=True)
class ClosedLiabilityAllocationRow:
    account_pubkey: str
    epoch: int
    closed_due_quote: int
    payer_available_quote: int
    sink_capacity_quote: int
    payer_debit_quote: int
    sink_draw_quote: int
    subrogated_claim_quote: int
    receiver_haircut_quote: int
    paid_to_receiver_quote: int

    def __post_init__(self) -> None:
        _require_account(self.account_pubkey, name="account_pubkey")
        _require_non_negative_int(self.epoch, name="epoch")
        _require_positive_int(self.closed_due_quote, name="closed_due_quote")
        _require_non_negative_int(
            self.payer_available_quote,
            name="payer_available_quote",
        )
        _require_non_negative_int(
            self.sink_capacity_quote,
            name="sink_capacity_quote",
        )
        _require_non_negative_int(self.payer_debit_quote, name="payer_debit_quote")
        _require_non_negative_int(self.sink_draw_quote, name="sink_draw_quote")
        _require_non_negative_int(
            self.subrogated_claim_quote,
            name="subrogated_claim_quote",
        )
        _require_non_negative_int(
            self.receiver_haircut_quote,
            name="receiver_haircut_quote",
        )
        _require_non_negative_int(
            self.paid_to_receiver_quote,
            name="paid_to_receiver_quote",
        )


@dataclass(frozen=True)
class ClosedFundingSourceRow:
    account_pubkey: str
    epoch: int
    payer_available_quote: int
    sink_capacity_quote: int

    def __post_init__(self) -> None:
        _require_account(self.account_pubkey, name="account_pubkey")
        _require_non_negative_int(self.epoch, name="epoch")
        _require_non_negative_int(
            self.payer_available_quote,
            name="payer_available_quote",
        )
        _require_non_negative_int(
            self.sink_capacity_quote,
            name="sink_capacity_quote",
        )


@dataclass(frozen=True)
class FundingCloseoutLiabilityCertificate:
    schema: str
    epoch: int
    price_e8: int
    funding_rate_bps: int
    pre_due_vector_hash: str
    pre_due_rows: tuple[DueRow, ...]
    closed_liability_rows: tuple[ClosedLiabilityRow, ...]
    post_open_due_sum_quote: int

    def __post_init__(self) -> None:
        if self.schema != CERT_SCHEMA:
            _require_account(self.schema, name="schema")
        _require_non_negative_int(self.epoch, name="epoch")
        _require_positive_int(self.price_e8, name="price_e8")
        _require_int(self.funding_rate_bps, name="funding_rate_bps")
        _require_hash(self.pre_due_vector_hash, name="pre_due_vector_hash")
        _require_due_rows(self.pre_due_rows)
        _require_closed_liability_rows(self.closed_liability_rows)
        _require_int(self.post_open_due_sum_quote, name="post_open_due_sum_quote")


@dataclass(frozen=True)
class FundingCloseoutAllocationCertificate:
    schema: str
    epoch: int
    price_e8: int
    funding_rate_bps: int
    pre_due_vector_hash: str
    pre_due_rows: tuple[DueRow, ...]
    closed_allocation_rows: tuple[ClosedLiabilityAllocationRow, ...]
    raw_post_open_due_sum_quote: int
    payable_post_open_due_sum_quote: int
    receiver_haircut_sum_quote: int

    def __post_init__(self) -> None:
        if self.schema != ALLOCATION_CERT_SCHEMA:
            _require_account(self.schema, name="schema")
        _require_non_negative_int(self.epoch, name="epoch")
        _require_positive_int(self.price_e8, name="price_e8")
        _require_int(self.funding_rate_bps, name="funding_rate_bps")
        _require_hash(self.pre_due_vector_hash, name="pre_due_vector_hash")
        _require_due_rows(self.pre_due_rows)
        _require_closed_allocation_rows(self.closed_allocation_rows)
        _require_int(
            self.raw_post_open_due_sum_quote,
            name="raw_post_open_due_sum_quote",
        )
        _require_int(
            self.payable_post_open_due_sum_quote,
            name="payable_post_open_due_sum_quote",
        )
        _require_non_negative_int(
            self.receiver_haircut_sum_quote,
            name="receiver_haircut_sum_quote",
        )


@dataclass(frozen=True)
class FundingCloseoutLiabilityReceipt:
    schema: str
    market_id: str
    epoch: int
    pre_due_vector_hash: str
    pre_close_state_root_hash: str
    certificate: FundingCloseoutLiabilityCertificate

    def __post_init__(self) -> None:
        if self.schema != RECEIPT_SCHEMA:
            _require_account(self.schema, name="schema")
        _require_account(self.market_id, name="market_id")
        _require_non_negative_int(self.epoch, name="epoch")
        _require_hash(self.pre_due_vector_hash, name="pre_due_vector_hash")
        _require_hash(self.pre_close_state_root_hash, name="pre_close_state_root_hash")
        if not isinstance(self.certificate, FundingCloseoutLiabilityCertificate):
            raise TypeError("certificate must be a FundingCloseoutLiabilityCertificate")


@dataclass(frozen=True)
class FundingCloseoutAllocationReceipt:
    schema: str
    market_id: str
    epoch: int
    pre_due_vector_hash: str
    pre_close_state_root_hash: str
    certificate: FundingCloseoutAllocationCertificate

    def __post_init__(self) -> None:
        if self.schema != ALLOCATION_RECEIPT_SCHEMA:
            _require_account(self.schema, name="schema")
        _require_account(self.market_id, name="market_id")
        _require_non_negative_int(self.epoch, name="epoch")
        _require_hash(self.pre_due_vector_hash, name="pre_due_vector_hash")
        _require_hash(self.pre_close_state_root_hash, name="pre_close_state_root_hash")
        if not isinstance(self.certificate, FundingCloseoutAllocationCertificate):
            raise TypeError("certificate must be a FundingCloseoutAllocationCertificate")


@dataclass(frozen=True)
class FundingCloseoutRationedAllocationReceipt:
    schema: str
    market_id: str
    epoch: int
    pre_due_vector_hash: str
    pre_close_state_root_hash: str
    certificate: FundingCloseoutAllocationCertificate
    receiver_haircut_rationing: ReceiverHaircutRationing

    def __post_init__(self) -> None:
        if self.schema != RATIONED_ALLOCATION_RECEIPT_SCHEMA:
            _require_account(self.schema, name="schema")
        _require_account(self.market_id, name="market_id")
        _require_non_negative_int(self.epoch, name="epoch")
        _require_hash(self.pre_due_vector_hash, name="pre_due_vector_hash")
        _require_hash(self.pre_close_state_root_hash, name="pre_close_state_root_hash")
        if not isinstance(self.certificate, FundingCloseoutAllocationCertificate):
            raise TypeError("certificate must be a FundingCloseoutAllocationCertificate")
        if not isinstance(self.receiver_haircut_rationing, ReceiverHaircutRationing):
            raise TypeError(
                "receiver_haircut_rationing must be a ReceiverHaircutRationing"
            )


@dataclass(frozen=True)
class FundingCloseoutSourceBoundRationedAllocationReceipt:
    schema: str
    market_id: str
    epoch: int
    pre_due_vector_hash: str
    pre_close_state_root_hash: str
    source_availability_hash: str
    source_availability_rows: tuple[ClosedFundingSourceRow, ...]
    certificate: FundingCloseoutAllocationCertificate
    receiver_haircut_rationing: ReceiverHaircutRationing

    def __post_init__(self) -> None:
        if self.schema != SOURCE_BOUND_RATIONED_ALLOCATION_RECEIPT_SCHEMA:
            _require_account(self.schema, name="schema")
        _require_account(self.market_id, name="market_id")
        _require_non_negative_int(self.epoch, name="epoch")
        _require_hash(self.pre_due_vector_hash, name="pre_due_vector_hash")
        _require_hash(self.pre_close_state_root_hash, name="pre_close_state_root_hash")
        _require_hash(self.source_availability_hash, name="source_availability_hash")
        _require_source_rows(self.source_availability_rows)
        if not isinstance(self.certificate, FundingCloseoutAllocationCertificate):
            raise TypeError("certificate must be a FundingCloseoutAllocationCertificate")
        if not isinstance(self.receiver_haircut_rationing, ReceiverHaircutRationing):
            raise TypeError(
                "receiver_haircut_rationing must be a ReceiverHaircutRationing"
            )


@dataclass(frozen=True)
class FundingCloseoutSourcePortfolioBoundRationedAllocationReceipt:
    schema: str
    market_id: str
    epoch: int
    pre_due_vector_hash: str
    pre_close_state_root_hash: str
    pending_source_availability_hashes: tuple[str, ...]
    aggregate_sink_capacity_quote: int
    source_availability_hash: str
    source_availability_rows: tuple[ClosedFundingSourceRow, ...]
    emitted_source_availability_rows: tuple[ClosedFundingSourceRow, ...]
    certificate: FundingCloseoutAllocationCertificate
    receiver_haircut_rationing: ReceiverHaircutRationing

    def __post_init__(self) -> None:
        if self.schema != SOURCE_PORTFOLIO_BOUND_RATIONED_ALLOCATION_RECEIPT_SCHEMA:
            _require_account(self.schema, name="schema")
        _require_account(self.market_id, name="market_id")
        _require_non_negative_int(self.epoch, name="epoch")
        _require_hash(self.pre_due_vector_hash, name="pre_due_vector_hash")
        _require_hash(self.pre_close_state_root_hash, name="pre_close_state_root_hash")
        _require_hash_tuple(
            self.pending_source_availability_hashes,
            name="pending_source_availability_hashes",
        )
        _require_non_negative_int(
            self.aggregate_sink_capacity_quote,
            name="aggregate_sink_capacity_quote",
        )
        _require_hash(self.source_availability_hash, name="source_availability_hash")
        _require_source_rows(self.source_availability_rows)
        _require_source_rows(self.emitted_source_availability_rows)
        if not isinstance(self.certificate, FundingCloseoutAllocationCertificate):
            raise TypeError("certificate must be a FundingCloseoutAllocationCertificate")
        if not isinstance(self.receiver_haircut_rationing, ReceiverHaircutRationing):
            raise TypeError(
                "receiver_haircut_rationing must be a ReceiverHaircutRationing"
            )


@dataclass(frozen=True)
class FundingCloseoutCarryForwardReceipt:
    schema: str
    market_id: str
    source_epoch: int
    carry_epoch: int
    pre_close_state_root_hash: str
    pending_source_availability_hashes: tuple[str, ...]
    source_availability_hash: str
    source_portfolio_receipt_hash: str
    carried_liability_hash: str
    source_portfolio_receipt: FundingCloseoutSourcePortfolioBoundRationedAllocationReceipt

    def __post_init__(self) -> None:
        if self.schema != CARRY_FORWARD_RECEIPT_SCHEMA:
            _require_account(self.schema, name="schema")
        _require_account(self.market_id, name="market_id")
        _require_non_negative_int(self.source_epoch, name="source_epoch")
        _require_non_negative_int(self.carry_epoch, name="carry_epoch")
        _require_hash(self.pre_close_state_root_hash, name="pre_close_state_root_hash")
        _require_hash_tuple(
            self.pending_source_availability_hashes,
            name="pending_source_availability_hashes",
        )
        _require_hash(self.source_availability_hash, name="source_availability_hash")
        _require_hash(
            self.source_portfolio_receipt_hash,
            name="source_portfolio_receipt_hash",
        )
        _require_hash(self.carried_liability_hash, name="carried_liability_hash")
        if not isinstance(
            self.source_portfolio_receipt,
            FundingCloseoutSourcePortfolioBoundRationedAllocationReceipt,
        ):
            raise TypeError(
                "source_portfolio_receipt must be a FundingCloseoutSourcePortfolioBoundRationedAllocationReceipt"
            )


@dataclass(frozen=True)
class CertificateVerdict:
    ok: bool
    error: str | None

    def __post_init__(self) -> None:
        if not isinstance(self.ok, bool):
            raise TypeError("ok must be a bool")
        if self.error is not None and not isinstance(self.error, str):
            raise TypeError("error must be None or str")


def _require_hash(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a str")
    if not value.startswith("sha256:") or len(value) != len("sha256:") + 64:
        raise ValueError(f"{name} must be sha256:<64 lowercase hex chars>")
    suffix = value[len("sha256:") :]
    if suffix.lower() != suffix or any(ch not in "0123456789abcdef" for ch in suffix):
        raise ValueError(f"{name} must be sha256:<64 lowercase hex chars>")
    return value


def _require_hash_tuple(value: object, *, name: str) -> tuple[str, ...]:
    if not isinstance(value, tuple):
        raise TypeError(f"{name} must be a tuple")
    return tuple(_require_hash(item, name=name) for item in value)


def _require_payload_mapping(value: object, *, name: str) -> Mapping[str, object]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be an object")
    if not all(isinstance(key, str) for key in value.keys()):
        raise ValueError(f"{name} keys must be strings")
    return value


def _require_exact_keys(value: Mapping[str, object], *, name: str, keys: set[str]) -> None:
    actual = set(value.keys())
    if actual != keys:
        raise ValueError(f"{name} keys mismatch")


def _require_payload_list(value: object, *, name: str) -> tuple[object, ...]:
    if not isinstance(value, list):
        raise TypeError(f"{name} must be a list")
    return tuple(value)


def _require_due_rows(rows: object) -> tuple[DueRow, ...]:
    if not isinstance(rows, tuple):
        raise TypeError("pre_due_rows must be a tuple")
    if not all(isinstance(row, DueRow) for row in rows):
        raise TypeError("pre_due_rows must contain DueRow values")
    return rows


def _require_closed_liability_rows(rows: object) -> tuple[ClosedLiabilityRow, ...]:
    if not isinstance(rows, tuple):
        raise TypeError("closed_liability_rows must be a tuple")
    if not all(isinstance(row, ClosedLiabilityRow) for row in rows):
        raise TypeError("closed_liability_rows must contain ClosedLiabilityRow values")
    return rows


def _require_closed_allocation_rows(
    rows: object,
) -> tuple[ClosedLiabilityAllocationRow, ...]:
    if not isinstance(rows, tuple):
        raise TypeError("closed_allocation_rows must be a tuple")
    if not all(isinstance(row, ClosedLiabilityAllocationRow) for row in rows):
        raise TypeError(
            "closed_allocation_rows must contain ClosedLiabilityAllocationRow values"
        )
    return rows


def _require_source_rows(
    rows: object,
) -> tuple[ClosedFundingSourceRow, ...]:
    if not isinstance(rows, tuple):
        raise TypeError("source_availability_rows must be a tuple")
    if not all(isinstance(row, ClosedFundingSourceRow) for row in rows):
        raise TypeError(
            "source_availability_rows must contain ClosedFundingSourceRow values"
        )
    return rows


def _require_position_accounts(
    accounts: object,
    *,
    name: str,
) -> tuple[PositionAccount, ...]:
    if not isinstance(accounts, tuple):
        raise TypeError(f"{name} must be a tuple")
    if not all(isinstance(account, PositionAccount) for account in accounts):
        raise TypeError(f"{name} must contain PositionAccount values")
    keys = [account.account_pubkey for account in accounts]
    if len(keys) != len(set(keys)):
        raise ValueError(f"{name} contains duplicate account_pubkey")
    return accounts


def _require_sink_draws(
    sink_draw_by_account: object,
    *,
    expected_accounts: set[str],
) -> dict[str, int]:
    if sink_draw_by_account is None:
        return {}
    if not isinstance(sink_draw_by_account, dict):
        raise TypeError("sink_draw_by_account must be a dict")
    out = {}
    for account_pubkey, amount in sink_draw_by_account.items():
        account = _require_account(account_pubkey, name="sink_draw account_pubkey")
        if account not in expected_accounts:
            raise ValueError("sink draw account is not closed with nonzero due")
        out[account] = _require_non_negative_int(amount, name="sink_draw_quote")
    return out


def _require_non_negative_quote_by_account(
    quote_by_account: object,
    *,
    name: str,
    expected_accounts: set[str],
) -> dict[str, int]:
    if not isinstance(quote_by_account, dict):
        raise TypeError(f"{name} must be a dict")
    out = {}
    for account_pubkey, amount in quote_by_account.items():
        account = _require_account(account_pubkey, name=f"{name} account_pubkey")
        if account not in expected_accounts:
            raise ValueError(f"{name} account is not closed with positive due")
        out[account] = _require_non_negative_int(amount, name=f"{name}_quote")
    return out


def _sha256_payload(payload: object) -> str:
    return "sha256:" + hashlib.sha256(canonical_json_bytes(payload)).hexdigest()


def _canonical_due_payload(rows: tuple[DueRow, ...]) -> dict[str, object]:
    return {
        "schema": DUE_VECTOR_SCHEMA,
        "rows": [asdict(row) for row in rows],
    }


def _canonical_source_availability_payload(
    rows: tuple[ClosedFundingSourceRow, ...],
) -> dict[str, object]:
    checked_rows = tuple(
        sorted(
            _require_source_rows(rows),
            key=lambda item: item.account_pubkey,
        )
    )
    return {
        "schema": SOURCE_AVAILABILITY_SCHEMA,
        "rows": [asdict(row) for row in checked_rows],
    }


def _canonical_carried_liability_payload(
    *,
    market_id: str,
    source_epoch: int,
    carry_epoch: int,
    pre_close_state_root_hash: str,
    pending_source_availability_hashes: tuple[str, ...],
    source_availability_hash: str,
    source_portfolio_receipt_hash: str,
) -> dict[str, object]:
    return {
        "schema": CARRIED_LIABILITY_ROOT_SCHEMA,
        "market_id": _require_account(market_id, name="market_id"),
        "source_epoch": _require_non_negative_int(source_epoch, name="source_epoch"),
        "carry_epoch": _require_non_negative_int(carry_epoch, name="carry_epoch"),
        "pre_close_state_root_hash": _require_hash(
            pre_close_state_root_hash,
            name="pre_close_state_root_hash",
        ),
        "pending_source_availability_hashes": [
            _require_hash(root_hash, name="pending_source_availability_hash")
            for root_hash in sorted(set(pending_source_availability_hashes))
        ],
        "source_availability_hash": _require_hash(
            source_availability_hash,
            name="source_availability_hash",
        ),
        "source_portfolio_receipt_hash": _require_hash(
            source_portfolio_receipt_hash,
            name="source_portfolio_receipt_hash",
        ),
    }


def pre_due_vector_hash(rows: tuple[DueRow, ...]) -> str:
    _require_due_rows(rows)
    return _sha256_payload(_canonical_due_payload(rows))


def funding_closeout_source_availability_hash(
    rows: tuple[ClosedFundingSourceRow, ...],
) -> str:
    return _sha256_payload(_canonical_source_availability_payload(rows))


def funding_closeout_source_portfolio_receipt_hash(
    receipt: FundingCloseoutSourcePortfolioBoundRationedAllocationReceipt,
) -> str:
    if not isinstance(
        receipt,
        FundingCloseoutSourcePortfolioBoundRationedAllocationReceipt,
    ):
        raise TypeError(
            "receipt must be a FundingCloseoutSourcePortfolioBoundRationedAllocationReceipt"
        )
    return _sha256_payload(
        funding_closeout_source_portfolio_bound_rationed_allocation_receipt_to_payload(
            receipt
        )
    )


def carried_funding_closeout_liability_hash(
    receipt: FundingCloseoutCarryForwardReceipt,
) -> str:
    if not isinstance(receipt, FundingCloseoutCarryForwardReceipt):
        raise TypeError("receipt must be a FundingCloseoutCarryForwardReceipt")
    return _sha256_payload(
        _canonical_carried_liability_payload(
            market_id=receipt.market_id,
            source_epoch=receipt.source_epoch,
            carry_epoch=receipt.carry_epoch,
            pre_close_state_root_hash=receipt.pre_close_state_root_hash,
            pending_source_availability_hashes=receipt.pending_source_availability_hashes,
            source_availability_hash=receipt.source_availability_hash,
            source_portfolio_receipt_hash=receipt.source_portfolio_receipt_hash,
        )
    )


def _carried_funding_closeout_liability_hash_from_source_portfolio(
    *,
    source_portfolio_receipt: FundingCloseoutSourcePortfolioBoundRationedAllocationReceipt,
    carry_epoch: int,
) -> str:
    source_hash = funding_closeout_source_portfolio_receipt_hash(source_portfolio_receipt)
    return _sha256_payload(
        _canonical_carried_liability_payload(
            market_id=source_portfolio_receipt.market_id,
            source_epoch=source_portfolio_receipt.epoch,
            carry_epoch=carry_epoch,
            pre_close_state_root_hash=source_portfolio_receipt.pre_close_state_root_hash,
            pending_source_availability_hashes=(
                source_portfolio_receipt.pending_source_availability_hashes
            ),
            source_availability_hash=source_portfolio_receipt.source_availability_hash,
            source_portfolio_receipt_hash=source_hash,
        )
    )


def pre_close_position_snapshot_hash(
    pre_accounts: tuple[PositionAccount, ...],
    *,
    market_id: str,
    epoch: int,
) -> str:
    market = _require_account(market_id, name="market_id")
    checked_accounts = tuple(
        sorted(
            _require_position_accounts(pre_accounts, name="pre_accounts"),
            key=lambda item: item.account_pubkey,
        )
    )
    payload = {
        "schema": PRE_CLOSE_POSITION_SNAPSHOT_SCHEMA,
        "market_id": market,
        "epoch": _require_non_negative_int(epoch, name="epoch"),
        "accounts": [asdict(account) for account in checked_accounts],
    }
    return _sha256_payload(payload)


def pre_close_position_snapshot_hash_from_due_rows(
    rows: tuple[DueRow, ...],
    *,
    market_id: str,
    epoch: int,
) -> str:
    _require_due_rows(rows)
    return pre_close_position_snapshot_hash(
        tuple(PositionAccount(row.account_pubkey, row.position_base) for row in rows),
        market_id=market_id,
        epoch=epoch,
    )


def pre_close_snapshot_hash(
    pre_accounts: tuple[PositionAccount, ...],
    *,
    market_id: str,
    epoch: int,
    price_e8: int,
    funding_rate_bps: int,
) -> str:
    market = _require_account(market_id, name="market_id")
    checked_accounts = tuple(
        sorted(
            _require_position_accounts(pre_accounts, name="pre_accounts"),
            key=lambda item: item.account_pubkey,
        )
    )
    due_rows = expected_pre_due_rows(
        checked_accounts,
        epoch=epoch,
        price_e8=price_e8,
        funding_rate_bps=funding_rate_bps,
    )
    payload = {
        "schema": PRE_CLOSE_SNAPSHOT_SCHEMA,
        "market_id": market,
        "epoch": _require_non_negative_int(epoch, name="epoch"),
        "price_e8": _require_positive_int(price_e8, name="price_e8"),
        "funding_rate_bps": _require_int(funding_rate_bps, name="funding_rate_bps"),
        "accounts": [asdict(account) for account in checked_accounts],
        "pre_due_rows": [asdict(row) for row in due_rows],
        "pre_due_vector_hash": pre_due_vector_hash(due_rows),
    }
    return _sha256_payload(payload)


def funding_closeout_liability_certificate_to_payload(
    certificate: FundingCloseoutLiabilityCertificate,
) -> dict[str, object]:
    if not isinstance(certificate, FundingCloseoutLiabilityCertificate):
        raise TypeError("certificate must be a FundingCloseoutLiabilityCertificate")
    return {
        "schema": certificate.schema,
        "epoch": certificate.epoch,
        "price_e8": certificate.price_e8,
        "funding_rate_bps": certificate.funding_rate_bps,
        "pre_due_vector_hash": certificate.pre_due_vector_hash,
        "pre_due_rows": [asdict(row) for row in certificate.pre_due_rows],
        "closed_liability_rows": [asdict(row) for row in certificate.closed_liability_rows],
        "post_open_due_sum_quote": certificate.post_open_due_sum_quote,
    }


def funding_closeout_liability_certificate_from_payload(
    payload: object,
) -> FundingCloseoutLiabilityCertificate:
    data = _require_payload_mapping(payload, name="certificate")
    _require_exact_keys(
        data,
        name="certificate",
        keys={
            "schema",
            "epoch",
            "price_e8",
            "funding_rate_bps",
            "pre_due_vector_hash",
            "pre_due_rows",
            "closed_liability_rows",
            "post_open_due_sum_quote",
        },
    )
    schema = data["schema"]
    if not isinstance(schema, str):
        raise TypeError("schema must be a str")
    return FundingCloseoutLiabilityCertificate(
        schema=schema,
        epoch=_require_non_negative_int(data["epoch"], name="epoch"),
        price_e8=_require_positive_int(data["price_e8"], name="price_e8"),
        funding_rate_bps=_require_int(data["funding_rate_bps"], name="funding_rate_bps"),
        pre_due_vector_hash=_require_hash(
            data["pre_due_vector_hash"],
            name="pre_due_vector_hash",
        ),
        pre_due_rows=tuple(
            _due_row_from_payload(row)
            for row in _require_payload_list(data["pre_due_rows"], name="pre_due_rows")
        ),
        closed_liability_rows=tuple(
            _closed_liability_row_from_payload(row)
            for row in _require_payload_list(
                data["closed_liability_rows"],
                name="closed_liability_rows",
            )
        ),
        post_open_due_sum_quote=_require_int(
            data["post_open_due_sum_quote"],
            name="post_open_due_sum_quote",
        ),
    )


def funding_closeout_allocation_certificate_to_payload(
    certificate: FundingCloseoutAllocationCertificate,
) -> dict[str, object]:
    if not isinstance(certificate, FundingCloseoutAllocationCertificate):
        raise TypeError("certificate must be a FundingCloseoutAllocationCertificate")
    return {
        "schema": certificate.schema,
        "epoch": certificate.epoch,
        "price_e8": certificate.price_e8,
        "funding_rate_bps": certificate.funding_rate_bps,
        "pre_due_vector_hash": certificate.pre_due_vector_hash,
        "pre_due_rows": [asdict(row) for row in certificate.pre_due_rows],
        "closed_allocation_rows": [
            asdict(row) for row in certificate.closed_allocation_rows
        ],
        "raw_post_open_due_sum_quote": certificate.raw_post_open_due_sum_quote,
        "payable_post_open_due_sum_quote": certificate.payable_post_open_due_sum_quote,
        "receiver_haircut_sum_quote": certificate.receiver_haircut_sum_quote,
    }


def funding_closeout_allocation_certificate_from_payload(
    payload: object,
) -> FundingCloseoutAllocationCertificate:
    data = _require_payload_mapping(payload, name="allocation_certificate")
    _require_exact_keys(
        data,
        name="allocation_certificate",
        keys={
            "schema",
            "epoch",
            "price_e8",
            "funding_rate_bps",
            "pre_due_vector_hash",
            "pre_due_rows",
            "closed_allocation_rows",
            "raw_post_open_due_sum_quote",
            "payable_post_open_due_sum_quote",
            "receiver_haircut_sum_quote",
        },
    )
    schema = data["schema"]
    if not isinstance(schema, str):
        raise TypeError("schema must be a str")
    return FundingCloseoutAllocationCertificate(
        schema=schema,
        epoch=_require_non_negative_int(data["epoch"], name="epoch"),
        price_e8=_require_positive_int(data["price_e8"], name="price_e8"),
        funding_rate_bps=_require_int(data["funding_rate_bps"], name="funding_rate_bps"),
        pre_due_vector_hash=_require_hash(
            data["pre_due_vector_hash"],
            name="pre_due_vector_hash",
        ),
        pre_due_rows=tuple(
            _due_row_from_payload(row)
            for row in _require_payload_list(data["pre_due_rows"], name="pre_due_rows")
        ),
        closed_allocation_rows=tuple(
            _closed_allocation_row_from_payload(row)
            for row in _require_payload_list(
                data["closed_allocation_rows"],
                name="closed_allocation_rows",
            )
        ),
        raw_post_open_due_sum_quote=_require_int(
            data["raw_post_open_due_sum_quote"],
            name="raw_post_open_due_sum_quote",
        ),
        payable_post_open_due_sum_quote=_require_int(
            data["payable_post_open_due_sum_quote"],
            name="payable_post_open_due_sum_quote",
        ),
        receiver_haircut_sum_quote=_require_non_negative_int(
            data["receiver_haircut_sum_quote"],
            name="receiver_haircut_sum_quote",
        ),
    )


def funding_closeout_liability_receipt_to_payload(
    receipt: FundingCloseoutLiabilityReceipt,
) -> dict[str, object]:
    if not isinstance(receipt, FundingCloseoutLiabilityReceipt):
        raise TypeError("receipt must be a FundingCloseoutLiabilityReceipt")
    return {
        "schema": receipt.schema,
        "market_id": receipt.market_id,
        "epoch": receipt.epoch,
        "pre_due_vector_hash": receipt.pre_due_vector_hash,
        "pre_close_state_root_hash": receipt.pre_close_state_root_hash,
        "certificate": funding_closeout_liability_certificate_to_payload(receipt.certificate),
    }


def funding_closeout_liability_receipt_from_payload(
    payload: object,
) -> FundingCloseoutLiabilityReceipt:
    data = _require_payload_mapping(payload, name="receipt")
    _require_exact_keys(
        data,
        name="receipt",
        keys={
            "schema",
            "market_id",
            "epoch",
            "pre_due_vector_hash",
            "pre_close_state_root_hash",
            "certificate",
        },
    )
    schema = data["schema"]
    if not isinstance(schema, str):
        raise TypeError("schema must be a str")
    return FundingCloseoutLiabilityReceipt(
        schema=schema,
        market_id=_require_account(data["market_id"], name="market_id"),
        epoch=_require_non_negative_int(data["epoch"], name="epoch"),
        pre_due_vector_hash=_require_hash(
            data["pre_due_vector_hash"],
            name="pre_due_vector_hash",
        ),
        pre_close_state_root_hash=_require_hash(
            data["pre_close_state_root_hash"],
            name="pre_close_state_root_hash",
        ),
        certificate=funding_closeout_liability_certificate_from_payload(data["certificate"]),
    )


def funding_closeout_allocation_receipt_to_payload(
    receipt: FundingCloseoutAllocationReceipt,
) -> dict[str, object]:
    if not isinstance(receipt, FundingCloseoutAllocationReceipt):
        raise TypeError("receipt must be a FundingCloseoutAllocationReceipt")
    return {
        "schema": receipt.schema,
        "market_id": receipt.market_id,
        "epoch": receipt.epoch,
        "pre_due_vector_hash": receipt.pre_due_vector_hash,
        "pre_close_state_root_hash": receipt.pre_close_state_root_hash,
        "certificate": funding_closeout_allocation_certificate_to_payload(receipt.certificate),
    }


def funding_closeout_allocation_receipt_from_payload(
    payload: object,
) -> FundingCloseoutAllocationReceipt:
    data = _require_payload_mapping(payload, name="allocation_receipt")
    _require_exact_keys(
        data,
        name="allocation_receipt",
        keys={
            "schema",
            "market_id",
            "epoch",
            "pre_due_vector_hash",
            "pre_close_state_root_hash",
            "certificate",
        },
    )
    schema = data["schema"]
    if not isinstance(schema, str):
        raise TypeError("schema must be a str")
    return FundingCloseoutAllocationReceipt(
        schema=schema,
        market_id=_require_account(data["market_id"], name="market_id"),
        epoch=_require_non_negative_int(data["epoch"], name="epoch"),
        pre_due_vector_hash=_require_hash(
            data["pre_due_vector_hash"],
            name="pre_due_vector_hash",
        ),
        pre_close_state_root_hash=_require_hash(
            data["pre_close_state_root_hash"],
            name="pre_close_state_root_hash",
        ),
        certificate=funding_closeout_allocation_certificate_from_payload(
            data["certificate"]
        ),
    )


def funding_closeout_rationed_allocation_receipt_to_payload(
    receipt: FundingCloseoutRationedAllocationReceipt,
) -> dict[str, object]:
    if not isinstance(receipt, FundingCloseoutRationedAllocationReceipt):
        raise TypeError(
            "receipt must be a FundingCloseoutRationedAllocationReceipt"
        )
    return {
        "schema": receipt.schema,
        "market_id": receipt.market_id,
        "epoch": receipt.epoch,
        "pre_due_vector_hash": receipt.pre_due_vector_hash,
        "pre_close_state_root_hash": receipt.pre_close_state_root_hash,
        "certificate": funding_closeout_allocation_certificate_to_payload(
            receipt.certificate
        ),
        "receiver_haircut_rationing": receiver_haircut_rationing_to_payload(
            receipt.receiver_haircut_rationing
        ),
    }


def funding_closeout_rationed_allocation_receipt_from_payload(
    payload: object,
) -> FundingCloseoutRationedAllocationReceipt:
    data = _require_payload_mapping(payload, name="rationed_allocation_receipt")
    _require_exact_keys(
        data,
        name="rationed_allocation_receipt",
        keys={
            "schema",
            "market_id",
            "epoch",
            "pre_due_vector_hash",
            "pre_close_state_root_hash",
            "certificate",
            "receiver_haircut_rationing",
        },
    )
    schema = data["schema"]
    if not isinstance(schema, str):
        raise TypeError("schema must be a str")
    return FundingCloseoutRationedAllocationReceipt(
        schema=schema,
        market_id=_require_account(data["market_id"], name="market_id"),
        epoch=_require_non_negative_int(data["epoch"], name="epoch"),
        pre_due_vector_hash=_require_hash(
            data["pre_due_vector_hash"],
            name="pre_due_vector_hash",
        ),
        pre_close_state_root_hash=_require_hash(
            data["pre_close_state_root_hash"],
            name="pre_close_state_root_hash",
        ),
        certificate=funding_closeout_allocation_certificate_from_payload(
            data["certificate"]
        ),
        receiver_haircut_rationing=receiver_haircut_rationing_from_payload(
            data["receiver_haircut_rationing"]
        ),
    )


def funding_closeout_source_bound_rationed_allocation_receipt_to_payload(
    receipt: FundingCloseoutSourceBoundRationedAllocationReceipt,
) -> dict[str, object]:
    if not isinstance(receipt, FundingCloseoutSourceBoundRationedAllocationReceipt):
        raise TypeError(
            "receipt must be a FundingCloseoutSourceBoundRationedAllocationReceipt"
        )
    return {
        "schema": receipt.schema,
        "market_id": receipt.market_id,
        "epoch": receipt.epoch,
        "pre_due_vector_hash": receipt.pre_due_vector_hash,
        "pre_close_state_root_hash": receipt.pre_close_state_root_hash,
        "source_availability_hash": receipt.source_availability_hash,
        "source_availability_rows": [
            asdict(row) for row in receipt.source_availability_rows
        ],
        "certificate": funding_closeout_allocation_certificate_to_payload(
            receipt.certificate
        ),
        "receiver_haircut_rationing": receiver_haircut_rationing_to_payload(
            receipt.receiver_haircut_rationing
        ),
    }


def funding_closeout_source_bound_rationed_allocation_receipt_from_payload(
    payload: object,
) -> FundingCloseoutSourceBoundRationedAllocationReceipt:
    data = _require_payload_mapping(
        payload,
        name="source_bound_rationed_allocation_receipt",
    )
    _require_exact_keys(
        data,
        name="source_bound_rationed_allocation_receipt",
        keys={
            "schema",
            "market_id",
            "epoch",
            "pre_due_vector_hash",
            "pre_close_state_root_hash",
            "source_availability_hash",
            "source_availability_rows",
            "certificate",
            "receiver_haircut_rationing",
        },
    )
    schema = data["schema"]
    if not isinstance(schema, str):
        raise TypeError("schema must be a str")
    return FundingCloseoutSourceBoundRationedAllocationReceipt(
        schema=schema,
        market_id=_require_account(data["market_id"], name="market_id"),
        epoch=_require_non_negative_int(data["epoch"], name="epoch"),
        pre_due_vector_hash=_require_hash(
            data["pre_due_vector_hash"],
            name="pre_due_vector_hash",
        ),
        pre_close_state_root_hash=_require_hash(
            data["pre_close_state_root_hash"],
            name="pre_close_state_root_hash",
        ),
        source_availability_hash=_require_hash(
            data["source_availability_hash"],
            name="source_availability_hash",
        ),
        source_availability_rows=tuple(
            _source_row_from_payload(row)
            for row in _require_payload_list(
                data["source_availability_rows"],
                name="source_availability_rows",
            )
        ),
        certificate=funding_closeout_allocation_certificate_from_payload(
            data["certificate"]
        ),
        receiver_haircut_rationing=receiver_haircut_rationing_from_payload(
            data["receiver_haircut_rationing"]
        ),
    )


def funding_closeout_source_portfolio_bound_rationed_allocation_receipt_to_payload(
    receipt: FundingCloseoutSourcePortfolioBoundRationedAllocationReceipt,
) -> dict[str, object]:
    if not isinstance(receipt, FundingCloseoutSourcePortfolioBoundRationedAllocationReceipt):
        raise TypeError(
            "receipt must be a FundingCloseoutSourcePortfolioBoundRationedAllocationReceipt"
        )
    return {
        "schema": receipt.schema,
        "market_id": receipt.market_id,
        "epoch": receipt.epoch,
        "pre_due_vector_hash": receipt.pre_due_vector_hash,
        "pre_close_state_root_hash": receipt.pre_close_state_root_hash,
        "pending_source_availability_hashes": list(
            receipt.pending_source_availability_hashes
        ),
        "aggregate_sink_capacity_quote": receipt.aggregate_sink_capacity_quote,
        "source_availability_hash": receipt.source_availability_hash,
        "source_availability_rows": [
            asdict(row) for row in receipt.source_availability_rows
        ],
        "emitted_source_availability_rows": [
            asdict(row) for row in receipt.emitted_source_availability_rows
        ],
        "certificate": funding_closeout_allocation_certificate_to_payload(
            receipt.certificate
        ),
        "receiver_haircut_rationing": receiver_haircut_rationing_to_payload(
            receipt.receiver_haircut_rationing
        ),
    }


def funding_closeout_carry_forward_receipt_to_payload(
    receipt: FundingCloseoutCarryForwardReceipt,
) -> dict[str, object]:
    if not isinstance(receipt, FundingCloseoutCarryForwardReceipt):
        raise TypeError("receipt must be a FundingCloseoutCarryForwardReceipt")
    return {
        "schema": receipt.schema,
        "market_id": receipt.market_id,
        "source_epoch": receipt.source_epoch,
        "carry_epoch": receipt.carry_epoch,
        "pre_close_state_root_hash": receipt.pre_close_state_root_hash,
        "pending_source_availability_hashes": list(
            receipt.pending_source_availability_hashes
        ),
        "source_availability_hash": receipt.source_availability_hash,
        "source_portfolio_receipt_hash": receipt.source_portfolio_receipt_hash,
        "carried_liability_hash": receipt.carried_liability_hash,
        "source_portfolio_receipt": (
            funding_closeout_source_portfolio_bound_rationed_allocation_receipt_to_payload(
                receipt.source_portfolio_receipt
            )
        ),
    }


def funding_closeout_source_portfolio_bound_rationed_allocation_receipt_from_payload(
    payload: object,
) -> FundingCloseoutSourcePortfolioBoundRationedAllocationReceipt:
    data = _require_payload_mapping(
        payload,
        name="source_portfolio_bound_rationed_allocation_receipt",
    )
    _require_exact_keys(
        data,
        name="source_portfolio_bound_rationed_allocation_receipt",
        keys={
            "schema",
            "market_id",
            "epoch",
            "pre_due_vector_hash",
            "pre_close_state_root_hash",
            "pending_source_availability_hashes",
            "aggregate_sink_capacity_quote",
            "source_availability_hash",
            "source_availability_rows",
            "emitted_source_availability_rows",
            "certificate",
            "receiver_haircut_rationing",
        },
    )
    schema = data["schema"]
    if not isinstance(schema, str):
        raise TypeError("schema must be a str")
    return FundingCloseoutSourcePortfolioBoundRationedAllocationReceipt(
        schema=schema,
        market_id=_require_account(data["market_id"], name="market_id"),
        epoch=_require_non_negative_int(data["epoch"], name="epoch"),
        pre_due_vector_hash=_require_hash(
            data["pre_due_vector_hash"],
            name="pre_due_vector_hash",
        ),
        pre_close_state_root_hash=_require_hash(
            data["pre_close_state_root_hash"],
            name="pre_close_state_root_hash",
        ),
        pending_source_availability_hashes=tuple(
            _require_hash(root_hash, name="pending_source_availability_hash")
            for root_hash in _require_payload_list(
                data["pending_source_availability_hashes"],
                name="pending_source_availability_hashes",
            )
        ),
        aggregate_sink_capacity_quote=_require_non_negative_int(
            data["aggregate_sink_capacity_quote"],
            name="aggregate_sink_capacity_quote",
        ),
        source_availability_hash=_require_hash(
            data["source_availability_hash"],
            name="source_availability_hash",
        ),
        source_availability_rows=tuple(
            _source_row_from_payload(row)
            for row in _require_payload_list(
                data["source_availability_rows"],
                name="source_availability_rows",
            )
        ),
        emitted_source_availability_rows=tuple(
            _source_row_from_payload(row)
            for row in _require_payload_list(
                data["emitted_source_availability_rows"],
                name="emitted_source_availability_rows",
            )
        ),
        certificate=funding_closeout_allocation_certificate_from_payload(
            data["certificate"]
        ),
        receiver_haircut_rationing=receiver_haircut_rationing_from_payload(
            data["receiver_haircut_rationing"]
        ),
    )


def funding_closeout_carry_forward_receipt_from_payload(
    payload: object,
) -> FundingCloseoutCarryForwardReceipt:
    data = _require_payload_mapping(payload, name="carry_forward_receipt")
    _require_exact_keys(
        data,
        name="carry_forward_receipt",
        keys={
            "schema",
            "market_id",
            "source_epoch",
            "carry_epoch",
            "pre_close_state_root_hash",
            "pending_source_availability_hashes",
            "source_availability_hash",
            "source_portfolio_receipt_hash",
            "carried_liability_hash",
            "source_portfolio_receipt",
        },
    )
    schema = data["schema"]
    if not isinstance(schema, str):
        raise TypeError("schema must be a str")
    return FundingCloseoutCarryForwardReceipt(
        schema=schema,
        market_id=_require_account(data["market_id"], name="market_id"),
        source_epoch=_require_non_negative_int(
            data["source_epoch"],
            name="source_epoch",
        ),
        carry_epoch=_require_non_negative_int(data["carry_epoch"], name="carry_epoch"),
        pre_close_state_root_hash=_require_hash(
            data["pre_close_state_root_hash"],
            name="pre_close_state_root_hash",
        ),
        pending_source_availability_hashes=tuple(
            _require_hash(root_hash, name="pending_source_availability_hash")
            for root_hash in _require_payload_list(
                data["pending_source_availability_hashes"],
                name="pending_source_availability_hashes",
            )
        ),
        source_availability_hash=_require_hash(
            data["source_availability_hash"],
            name="source_availability_hash",
        ),
        source_portfolio_receipt_hash=_require_hash(
            data["source_portfolio_receipt_hash"],
            name="source_portfolio_receipt_hash",
        ),
        carried_liability_hash=_require_hash(
            data["carried_liability_hash"],
            name="carried_liability_hash",
        ),
        source_portfolio_receipt=(
            funding_closeout_source_portfolio_bound_rationed_allocation_receipt_from_payload(
                data["source_portfolio_receipt"]
            )
        ),
    )


def _due_row_from_payload(row: object) -> DueRow:
    data = _require_payload_mapping(row, name="pre_due_row")
    _require_exact_keys(
        data,
        name="pre_due_row",
        keys={"account_pubkey", "epoch", "position_base", "due_quote"},
    )
    return DueRow(
        account_pubkey=_require_account(data["account_pubkey"], name="account_pubkey"),
        epoch=_require_non_negative_int(data["epoch"], name="epoch"),
        position_base=_require_int(data["position_base"], name="position_base"),
        due_quote=_require_int(data["due_quote"], name="due_quote"),
    )


def _closed_liability_row_from_payload(row: object) -> ClosedLiabilityRow:
    data = _require_payload_mapping(row, name="closed_liability_row")
    _require_exact_keys(
        data,
        name="closed_liability_row",
        keys={
            "account_pubkey",
            "epoch",
            "closed_due_quote",
            "carried_due_quote",
            "sink_draw_quote",
            "subrogated_claim_quote",
        },
    )
    return ClosedLiabilityRow(
        account_pubkey=_require_account(data["account_pubkey"], name="account_pubkey"),
        epoch=_require_non_negative_int(data["epoch"], name="epoch"),
        closed_due_quote=_require_int(data["closed_due_quote"], name="closed_due_quote"),
        carried_due_quote=_require_int(data["carried_due_quote"], name="carried_due_quote"),
        sink_draw_quote=_require_non_negative_int(
            data["sink_draw_quote"],
            name="sink_draw_quote",
        ),
        subrogated_claim_quote=_require_non_negative_int(
            data["subrogated_claim_quote"],
            name="subrogated_claim_quote",
        ),
    )


def _closed_allocation_row_from_payload(row: object) -> ClosedLiabilityAllocationRow:
    data = _require_payload_mapping(row, name="closed_allocation_row")
    _require_exact_keys(
        data,
        name="closed_allocation_row",
        keys={
            "account_pubkey",
            "epoch",
            "closed_due_quote",
            "payer_available_quote",
            "sink_capacity_quote",
            "payer_debit_quote",
            "sink_draw_quote",
            "subrogated_claim_quote",
            "receiver_haircut_quote",
            "paid_to_receiver_quote",
        },
    )
    return ClosedLiabilityAllocationRow(
        account_pubkey=_require_account(data["account_pubkey"], name="account_pubkey"),
        epoch=_require_non_negative_int(data["epoch"], name="epoch"),
        closed_due_quote=_require_positive_int(
            data["closed_due_quote"],
            name="closed_due_quote",
        ),
        payer_available_quote=_require_non_negative_int(
            data["payer_available_quote"],
            name="payer_available_quote",
        ),
        sink_capacity_quote=_require_non_negative_int(
            data["sink_capacity_quote"],
            name="sink_capacity_quote",
        ),
        payer_debit_quote=_require_non_negative_int(
            data["payer_debit_quote"],
            name="payer_debit_quote",
        ),
        sink_draw_quote=_require_non_negative_int(
            data["sink_draw_quote"],
            name="sink_draw_quote",
        ),
        subrogated_claim_quote=_require_non_negative_int(
            data["subrogated_claim_quote"],
            name="subrogated_claim_quote",
        ),
        receiver_haircut_quote=_require_non_negative_int(
            data["receiver_haircut_quote"],
            name="receiver_haircut_quote",
        ),
        paid_to_receiver_quote=_require_non_negative_int(
            data["paid_to_receiver_quote"],
            name="paid_to_receiver_quote",
        ),
    )


def _source_row_from_payload(row: object) -> ClosedFundingSourceRow:
    data = _require_payload_mapping(row, name="source_availability_row")
    _require_exact_keys(
        data,
        name="source_availability_row",
        keys={
            "account_pubkey",
            "epoch",
            "payer_available_quote",
            "sink_capacity_quote",
        },
    )
    return ClosedFundingSourceRow(
        account_pubkey=_require_account(data["account_pubkey"], name="account_pubkey"),
        epoch=_require_non_negative_int(data["epoch"], name="epoch"),
        payer_available_quote=_require_non_negative_int(
            data["payer_available_quote"],
            name="payer_available_quote",
        ),
        sink_capacity_quote=_require_non_negative_int(
            data["sink_capacity_quote"],
            name="sink_capacity_quote",
        ),
    )


def _is_sorted_by_account(
    rows: (
        tuple[DueRow, ...]
        | tuple[ClosedLiabilityRow, ...]
        | tuple[ClosedLiabilityAllocationRow, ...]
        | tuple[ClosedFundingSourceRow, ...]
    ),
) -> bool:
    keys = [row.account_pubkey for row in rows]
    return keys == sorted(keys)


def _has_duplicate_accounts(
    rows: (
        tuple[DueRow, ...]
        | tuple[ClosedLiabilityRow, ...]
        | tuple[ClosedLiabilityAllocationRow, ...]
        | tuple[ClosedFundingSourceRow, ...]
    ),
) -> bool:
    keys = [row.account_pubkey for row in rows]
    return len(keys) != len(set(keys))


def _account_map(accounts: tuple[PositionAccount, ...]) -> dict[str, PositionAccount]:
    checked = _require_position_accounts(accounts, name="accounts")
    return {account.account_pubkey: account for account in checked}


def _funding_due(position_base: int, *, price_e8: int, funding_rate_bps: int) -> int:
    return funding_payment(position_base, price_e8, funding_rate_bps)


def expected_pre_due_rows(
    pre_accounts: tuple[PositionAccount, ...],
    *,
    epoch: int,
    price_e8: int,
    funding_rate_bps: int,
) -> tuple[DueRow, ...]:
    checked_accounts = _require_position_accounts(pre_accounts, name="pre_accounts")
    _require_non_negative_int(epoch, name="epoch")
    price = _require_positive_int(price_e8, name="price_e8")
    rate = _require_int(funding_rate_bps, name="funding_rate_bps")

    rows = []
    for account in sorted(checked_accounts, key=lambda item: item.account_pubkey):
        if account.position_base == 0:
            continue
        rows.append(
            DueRow(
                account_pubkey=account.account_pubkey,
                epoch=epoch,
                position_base=account.position_base,
                due_quote=_funding_due(
                    account.position_base,
                    price_e8=price,
                    funding_rate_bps=rate,
                ),
            )
        )
    return tuple(rows)


def post_open_due_sum(
    post_accounts: tuple[PositionAccount, ...],
    *,
    price_e8: int,
    funding_rate_bps: int,
) -> int:
    checked_accounts = _require_position_accounts(post_accounts, name="post_accounts")
    price = _require_positive_int(price_e8, name="price_e8")
    rate = _require_int(funding_rate_bps, name="funding_rate_bps")

    total = 0
    for account in checked_accounts:
        if account.position_base == 0:
            continue
        total += _funding_due(
            account.position_base,
            price_e8=price,
            funding_rate_bps=rate,
        )
    return total


def post_open_receiver_claim_rows(
    post_accounts: tuple[PositionAccount, ...],
    *,
    price_e8: int,
    funding_rate_bps: int,
) -> tuple[ReceiverClaimRow, ...]:
    checked_accounts = _require_position_accounts(post_accounts, name="post_accounts")
    price = _require_positive_int(price_e8, name="price_e8")
    rate = _require_int(funding_rate_bps, name="funding_rate_bps")

    rows = []
    for account in sorted(checked_accounts, key=lambda item: item.account_pubkey):
        if account.position_base == 0:
            continue
        due = _funding_due(
            account.position_base,
            price_e8=price,
            funding_rate_bps=rate,
        )
        if due < 0:
            rows.append(
                ReceiverClaimRow(
                    account_pubkey=account.account_pubkey,
                    claim_quote=-int(due),
                )
            )
    return tuple(rows)


def closed_funding_source_rows_from_allocation_certificate(
    certificate: FundingCloseoutAllocationCertificate,
) -> tuple[ClosedFundingSourceRow, ...]:
    if not isinstance(certificate, FundingCloseoutAllocationCertificate):
        raise TypeError("certificate must be a FundingCloseoutAllocationCertificate")
    return tuple(
        ClosedFundingSourceRow(
            account_pubkey=row.account_pubkey,
            epoch=row.epoch,
            payer_available_quote=row.payer_available_quote,
            sink_capacity_quote=row.sink_capacity_quote,
        )
        for row in certificate.closed_allocation_rows
    )


def _closed_due_by_account(
    pre_accounts: tuple[PositionAccount, ...],
    post_accounts: tuple[PositionAccount, ...],
    *,
    epoch: int,
    price_e8: int,
    funding_rate_bps: int,
) -> dict[str, int]:
    post = _account_map(post_accounts)
    out: dict[str, int] = {}
    for row in expected_pre_due_rows(
        pre_accounts,
        epoch=epoch,
        price_e8=price_e8,
        funding_rate_bps=funding_rate_bps,
    ):
        post_position = post.get(
            row.account_pubkey,
            PositionAccount(row.account_pubkey, 0),
        ).position_base
        if post_position == 0 and row.due_quote != 0:
            out[row.account_pubkey] = row.due_quote
    return out


def build_funding_closeout_liability_certificate(
    pre_accounts: tuple[PositionAccount, ...],
    post_accounts: tuple[PositionAccount, ...],
    *,
    epoch: int,
    price_e8: int,
    funding_rate_bps: int,
    sink_draw_by_account: dict[str, int] | None = None,
) -> FundingCloseoutLiabilityCertificate:
    expected_closed = _closed_due_by_account(
        pre_accounts,
        post_accounts,
        epoch=epoch,
        price_e8=price_e8,
        funding_rate_bps=funding_rate_bps,
    )
    sink_draws = _require_sink_draws(
        sink_draw_by_account,
        expected_accounts=set(expected_closed),
    )
    due_rows = expected_pre_due_rows(
        pre_accounts,
        epoch=epoch,
        price_e8=price_e8,
        funding_rate_bps=funding_rate_bps,
    )
    liabilities = []
    for account_pubkey, due_quote in sorted(expected_closed.items()):
        sink_draw = _require_non_negative_int(
            sink_draws.get(account_pubkey, 0),
            name="sink_draw_quote",
        )
        if due_quote <= 0 and sink_draw != 0:
            raise ValueError("sink draw is only defined for positive closed due")
        if sink_draw > max(0, due_quote):
            raise ValueError("sink_draw_quote exceeds positive closed due")
        carried = due_quote - sink_draw if due_quote > 0 else due_quote
        liabilities.append(
            ClosedLiabilityRow(
                account_pubkey=account_pubkey,
                epoch=epoch,
                closed_due_quote=due_quote,
                carried_due_quote=carried,
                sink_draw_quote=sink_draw,
                subrogated_claim_quote=sink_draw,
            )
        )
    return FundingCloseoutLiabilityCertificate(
        schema=CERT_SCHEMA,
        epoch=epoch,
        price_e8=price_e8,
        funding_rate_bps=funding_rate_bps,
        pre_due_vector_hash=pre_due_vector_hash(due_rows),
        pre_due_rows=due_rows,
        closed_liability_rows=tuple(liabilities),
        post_open_due_sum_quote=post_open_due_sum(
            post_accounts,
            price_e8=price_e8,
            funding_rate_bps=funding_rate_bps,
        ),
    )


def build_funding_closeout_liability_receipt(
    pre_accounts: tuple[PositionAccount, ...],
    post_accounts: tuple[PositionAccount, ...],
    *,
    market_id: str,
    epoch: int,
    price_e8: int,
    funding_rate_bps: int,
    sink_draw_by_account: dict[str, int] | None = None,
) -> FundingCloseoutLiabilityReceipt:
    certificate = build_funding_closeout_liability_certificate(
        pre_accounts,
        post_accounts,
        epoch=epoch,
        price_e8=price_e8,
        funding_rate_bps=funding_rate_bps,
        sink_draw_by_account=sink_draw_by_account,
    )
    return FundingCloseoutLiabilityReceipt(
        schema=RECEIPT_SCHEMA,
        market_id=_require_account(market_id, name="market_id"),
        epoch=_require_non_negative_int(epoch, name="epoch"),
        pre_due_vector_hash=certificate.pre_due_vector_hash,
        pre_close_state_root_hash=pre_close_position_snapshot_hash(
            pre_accounts,
            market_id=market_id,
            epoch=epoch,
        ),
        certificate=certificate,
    )


def build_funding_closeout_allocation_certificate(
    pre_accounts: tuple[PositionAccount, ...],
    post_accounts: tuple[PositionAccount, ...],
    *,
    epoch: int,
    price_e8: int,
    funding_rate_bps: int,
    payer_available_by_account: dict[str, int],
    sink_capacity_by_account: dict[str, int],
) -> FundingCloseoutAllocationCertificate:
    expected_closed = _closed_due_by_account(
        pre_accounts,
        post_accounts,
        epoch=epoch,
        price_e8=price_e8,
        funding_rate_bps=funding_rate_bps,
    )
    if any(due_quote <= 0 for due_quote in expected_closed.values()):
        raise ValueError("allocation certificate only supports positive closed due")
    expected_accounts = set(expected_closed)
    payer_available = _require_non_negative_quote_by_account(
        payer_available_by_account,
        name="payer_available_by_account",
        expected_accounts=expected_accounts,
    )
    sink_capacity = _require_non_negative_quote_by_account(
        sink_capacity_by_account,
        name="sink_capacity_by_account",
        expected_accounts=expected_accounts,
    )
    if set(payer_available) != expected_accounts:
        raise ValueError("payer_available_by_account set mismatch")
    if set(sink_capacity) != expected_accounts:
        raise ValueError("sink_capacity_by_account set mismatch")

    due_rows = expected_pre_due_rows(
        pre_accounts,
        epoch=epoch,
        price_e8=price_e8,
        funding_rate_bps=funding_rate_bps,
    )
    rows = []
    for account_pubkey, closed_due in sorted(expected_closed.items()):
        allocation = build_limited_liability_funding_closeout_allocation(
            closed_due_quote=closed_due,
            payer_available_quote=payer_available[account_pubkey],
            sink_capacity_quote=sink_capacity[account_pubkey],
        )
        rows.append(
            ClosedLiabilityAllocationRow(
                account_pubkey=account_pubkey,
                epoch=epoch,
                closed_due_quote=closed_due,
                payer_available_quote=allocation.payer_available_quote,
                sink_capacity_quote=allocation.sink_capacity_quote,
                payer_debit_quote=allocation.payer_debit_quote,
                sink_draw_quote=allocation.sink_draw_quote,
                subrogated_claim_quote=allocation.subrogated_claim_quote,
                receiver_haircut_quote=allocation.receiver_haircut_quote,
                paid_to_receiver_quote=allocation.paid_to_receiver_quote,
            )
        )
    raw_post_sum = post_open_due_sum(
        post_accounts,
        price_e8=price_e8,
        funding_rate_bps=funding_rate_bps,
    )
    haircut_sum = sum(row.receiver_haircut_quote for row in rows)
    return FundingCloseoutAllocationCertificate(
        schema=ALLOCATION_CERT_SCHEMA,
        epoch=epoch,
        price_e8=price_e8,
        funding_rate_bps=funding_rate_bps,
        pre_due_vector_hash=pre_due_vector_hash(due_rows),
        pre_due_rows=due_rows,
        closed_allocation_rows=tuple(rows),
        raw_post_open_due_sum_quote=raw_post_sum,
        payable_post_open_due_sum_quote=raw_post_sum + haircut_sum,
        receiver_haircut_sum_quote=haircut_sum,
    )


def build_funding_closeout_allocation_receipt(
    pre_accounts: tuple[PositionAccount, ...],
    post_accounts: tuple[PositionAccount, ...],
    *,
    market_id: str,
    epoch: int,
    price_e8: int,
    funding_rate_bps: int,
    payer_available_by_account: dict[str, int],
    sink_capacity_by_account: dict[str, int],
) -> FundingCloseoutAllocationReceipt:
    certificate = build_funding_closeout_allocation_certificate(
        pre_accounts,
        post_accounts,
        epoch=epoch,
        price_e8=price_e8,
        funding_rate_bps=funding_rate_bps,
        payer_available_by_account=payer_available_by_account,
        sink_capacity_by_account=sink_capacity_by_account,
    )
    return FundingCloseoutAllocationReceipt(
        schema=ALLOCATION_RECEIPT_SCHEMA,
        market_id=_require_account(market_id, name="market_id"),
        epoch=_require_non_negative_int(epoch, name="epoch"),
        pre_due_vector_hash=certificate.pre_due_vector_hash,
        pre_close_state_root_hash=pre_close_position_snapshot_hash(
            pre_accounts,
            market_id=market_id,
            epoch=epoch,
        ),
        certificate=certificate,
    )


def build_funding_closeout_rationed_allocation_receipt(
    pre_accounts: tuple[PositionAccount, ...],
    post_accounts: tuple[PositionAccount, ...],
    *,
    market_id: str,
    epoch: int,
    price_e8: int,
    funding_rate_bps: int,
    payer_available_by_account: dict[str, int],
    sink_capacity_by_account: dict[str, int],
) -> FundingCloseoutRationedAllocationReceipt:
    certificate = build_funding_closeout_allocation_certificate(
        pre_accounts,
        post_accounts,
        epoch=epoch,
        price_e8=price_e8,
        funding_rate_bps=funding_rate_bps,
        payer_available_by_account=payer_available_by_account,
        sink_capacity_by_account=sink_capacity_by_account,
    )
    receiver_claim_rows = post_open_receiver_claim_rows(
        post_accounts,
        price_e8=price_e8,
        funding_rate_bps=funding_rate_bps,
    )
    rationing = build_receiver_haircut_rationing(
        receiver_claim_rows,
        total_haircut_quote=certificate.receiver_haircut_sum_quote,
    )
    return FundingCloseoutRationedAllocationReceipt(
        schema=RATIONED_ALLOCATION_RECEIPT_SCHEMA,
        market_id=_require_account(market_id, name="market_id"),
        epoch=_require_non_negative_int(epoch, name="epoch"),
        pre_due_vector_hash=certificate.pre_due_vector_hash,
        pre_close_state_root_hash=pre_close_position_snapshot_hash(
            pre_accounts,
            market_id=market_id,
            epoch=epoch,
        ),
        certificate=certificate,
        receiver_haircut_rationing=rationing,
    )


def build_funding_closeout_source_bound_rationed_allocation_receipt(
    pre_accounts: tuple[PositionAccount, ...],
    post_accounts: tuple[PositionAccount, ...],
    *,
    market_id: str,
    epoch: int,
    price_e8: int,
    funding_rate_bps: int,
    payer_available_by_account: dict[str, int],
    sink_capacity_by_account: dict[str, int],
) -> FundingCloseoutSourceBoundRationedAllocationReceipt:
    receipt = build_funding_closeout_rationed_allocation_receipt(
        pre_accounts,
        post_accounts,
        market_id=market_id,
        epoch=epoch,
        price_e8=price_e8,
        funding_rate_bps=funding_rate_bps,
        payer_available_by_account=payer_available_by_account,
        sink_capacity_by_account=sink_capacity_by_account,
    )
    source_rows = closed_funding_source_rows_from_allocation_certificate(
        receipt.certificate
    )
    return FundingCloseoutSourceBoundRationedAllocationReceipt(
        schema=SOURCE_BOUND_RATIONED_ALLOCATION_RECEIPT_SCHEMA,
        market_id=receipt.market_id,
        epoch=receipt.epoch,
        pre_due_vector_hash=receipt.pre_due_vector_hash,
        pre_close_state_root_hash=receipt.pre_close_state_root_hash,
        source_availability_hash=funding_closeout_source_availability_hash(
            source_rows
        ),
        source_availability_rows=source_rows,
        certificate=receipt.certificate,
        receiver_haircut_rationing=receipt.receiver_haircut_rationing,
    )


def build_funding_closeout_source_portfolio_bound_rationed_allocation_receipt(
    pre_accounts: tuple[PositionAccount, ...],
    post_accounts: tuple[PositionAccount, ...],
    *,
    market_id: str,
    epoch: int,
    price_e8: int,
    funding_rate_bps: int,
    emitted_source_availability_rows: tuple[ClosedFundingSourceRow, ...],
    aggregate_sink_capacity_quote: int,
    sink_capacity_by_account: dict[str, int],
) -> FundingCloseoutSourcePortfolioBoundRationedAllocationReceipt:
    emitted_rows = tuple(
        sorted(
            _require_source_rows(emitted_source_availability_rows),
            key=lambda item: item.account_pubkey,
        )
    )
    payer_available_by_account = {
        row.account_pubkey: row.payer_available_quote for row in emitted_rows
    }
    receipt = build_funding_closeout_rationed_allocation_receipt(
        pre_accounts,
        post_accounts,
        market_id=market_id,
        epoch=epoch,
        price_e8=price_e8,
        funding_rate_bps=funding_rate_bps,
        payer_available_by_account=payer_available_by_account,
        sink_capacity_by_account=sink_capacity_by_account,
    )
    source_rows = closed_funding_source_rows_from_allocation_certificate(
        receipt.certificate
    )
    return FundingCloseoutSourcePortfolioBoundRationedAllocationReceipt(
        schema=SOURCE_PORTFOLIO_BOUND_RATIONED_ALLOCATION_RECEIPT_SCHEMA,
        market_id=receipt.market_id,
        epoch=receipt.epoch,
        pre_due_vector_hash=receipt.pre_due_vector_hash,
        pre_close_state_root_hash=receipt.pre_close_state_root_hash,
        pending_source_availability_hashes=tuple(
            sorted(
                funding_closeout_source_availability_hash((row,))
                for row in emitted_rows
            )
        ),
        aggregate_sink_capacity_quote=_require_non_negative_int(
            aggregate_sink_capacity_quote,
            name="aggregate_sink_capacity_quote",
        ),
        source_availability_hash=funding_closeout_source_availability_hash(
            source_rows
        ),
        source_availability_rows=source_rows,
        emitted_source_availability_rows=emitted_rows,
        certificate=receipt.certificate,
        receiver_haircut_rationing=receipt.receiver_haircut_rationing,
    )


def build_funding_closeout_carry_forward_receipt(
    source_portfolio_receipt: FundingCloseoutSourcePortfolioBoundRationedAllocationReceipt,
    *,
    carry_epoch: int,
) -> FundingCloseoutCarryForwardReceipt:
    if not isinstance(
        source_portfolio_receipt,
        FundingCloseoutSourcePortfolioBoundRationedAllocationReceipt,
    ):
        raise TypeError(
            "source_portfolio_receipt must be a FundingCloseoutSourcePortfolioBoundRationedAllocationReceipt"
        )
    next_epoch = _require_non_negative_int(carry_epoch, name="carry_epoch")
    source_hash = funding_closeout_source_portfolio_receipt_hash(
        source_portfolio_receipt
    )
    carried_hash = _carried_funding_closeout_liability_hash_from_source_portfolio(
        source_portfolio_receipt=source_portfolio_receipt,
        carry_epoch=next_epoch,
    )
    return FundingCloseoutCarryForwardReceipt(
        schema=CARRY_FORWARD_RECEIPT_SCHEMA,
        market_id=source_portfolio_receipt.market_id,
        source_epoch=source_portfolio_receipt.epoch,
        carry_epoch=next_epoch,
        pre_close_state_root_hash=source_portfolio_receipt.pre_close_state_root_hash,
        pending_source_availability_hashes=(
            source_portfolio_receipt.pending_source_availability_hashes
        ),
        source_availability_hash=source_portfolio_receipt.source_availability_hash,
        source_portfolio_receipt_hash=source_hash,
        carried_liability_hash=carried_hash,
        source_portfolio_receipt=source_portfolio_receipt,
    )


def validate_funding_closeout_liability_certificate(
    pre_accounts: tuple[PositionAccount, ...],
    post_accounts: tuple[PositionAccount, ...],
    certificate: FundingCloseoutLiabilityCertificate,
) -> CertificateVerdict:
    if certificate.schema != CERT_SCHEMA:
        return CertificateVerdict(False, "invalid certificate schema")
    if not _is_sorted_by_account(certificate.pre_due_rows):
        return CertificateVerdict(False, "pre_due_rows must be sorted by account_pubkey")
    if not _is_sorted_by_account(certificate.closed_liability_rows):
        return CertificateVerdict(False, "closed_liability_rows must be sorted by account_pubkey")
    if _has_duplicate_accounts(certificate.pre_due_rows):
        return CertificateVerdict(False, "duplicate pre_due account")
    if _has_duplicate_accounts(certificate.closed_liability_rows):
        return CertificateVerdict(False, "duplicate closed liability account")

    expected_rows = expected_pre_due_rows(
        pre_accounts,
        epoch=certificate.epoch,
        price_e8=certificate.price_e8,
        funding_rate_bps=certificate.funding_rate_bps,
    )
    if certificate.pre_due_rows != expected_rows:
        return CertificateVerdict(False, "pre_due_rows do not match pre-close accounts")
    if certificate.pre_due_vector_hash != pre_due_vector_hash(certificate.pre_due_rows):
        return CertificateVerdict(False, "pre_due_vector_hash mismatch")

    expected_closed = _closed_due_by_account(
        pre_accounts,
        post_accounts,
        epoch=certificate.epoch,
        price_e8=certificate.price_e8,
        funding_rate_bps=certificate.funding_rate_bps,
    )
    actual_closed = {row.account_pubkey: row for row in certificate.closed_liability_rows}
    if set(actual_closed) != set(expected_closed):
        return CertificateVerdict(False, "closed liability row set mismatch")

    for row in certificate.closed_liability_rows:
        verdict = _validate_closed_liability_row(row, certificate, expected_closed)
        if not verdict.ok:
            return verdict

    expected_post_sum = post_open_due_sum(
        post_accounts,
        price_e8=certificate.price_e8,
        funding_rate_bps=certificate.funding_rate_bps,
    )
    if certificate.post_open_due_sum_quote != expected_post_sum:
        return CertificateVerdict(False, "post_open_due_sum_quote mismatch")
    pre_sum = sum(row.due_quote for row in certificate.pre_due_rows)
    closed_sum = sum(row.closed_due_quote for row in certificate.closed_liability_rows)
    if certificate.post_open_due_sum_quote + closed_sum != pre_sum:
        return CertificateVerdict(False, "batch funding conservation mismatch")
    return CertificateVerdict(True, None)


def validate_funding_closeout_allocation_certificate(
    pre_accounts: tuple[PositionAccount, ...],
    post_accounts: tuple[PositionAccount, ...],
    certificate: FundingCloseoutAllocationCertificate,
) -> CertificateVerdict:
    base_verdict = _validate_allocation_certificate_shape(certificate)
    if not base_verdict.ok:
        return base_verdict

    expected_rows = expected_pre_due_rows(
        pre_accounts,
        epoch=certificate.epoch,
        price_e8=certificate.price_e8,
        funding_rate_bps=certificate.funding_rate_bps,
    )
    if certificate.pre_due_rows != expected_rows:
        return CertificateVerdict(False, "pre_due_rows do not match pre-close accounts")

    expected_closed = _closed_due_by_account(
        pre_accounts,
        post_accounts,
        epoch=certificate.epoch,
        price_e8=certificate.price_e8,
        funding_rate_bps=certificate.funding_rate_bps,
    )
    if any(due_quote <= 0 for due_quote in expected_closed.values()):
        return CertificateVerdict(
            False,
            "allocation certificate only supports positive closed due",
        )
    actual_closed = {row.account_pubkey: row for row in certificate.closed_allocation_rows}
    if set(actual_closed) != set(expected_closed):
        return CertificateVerdict(False, "closed allocation row set mismatch")

    for row in certificate.closed_allocation_rows:
        verdict = _validate_closed_allocation_row(row, certificate, expected_closed)
        if not verdict.ok:
            return verdict

    expected_raw_post_sum = post_open_due_sum(
        post_accounts,
        price_e8=certificate.price_e8,
        funding_rate_bps=certificate.funding_rate_bps,
    )
    if certificate.raw_post_open_due_sum_quote != expected_raw_post_sum:
        return CertificateVerdict(False, "raw_post_open_due_sum_quote mismatch")
    return _validate_allocation_certificate_sums(certificate)


def verify_funding_closeout_liability_certificate_payload(
    payload: object,
    *,
    expected_epoch: int | None = None,
    expected_price_e8: int | None = None,
    expected_funding_rate_bps: int | None = None,
    expected_pre_due_vector_hash: str | None = None,
    expected_post_open_due_sum_quote: int | None = None,
) -> CertificateVerdict:
    try:
        certificate = funding_closeout_liability_certificate_from_payload(payload)
        if expected_epoch is not None and certificate.epoch != _require_non_negative_int(
            expected_epoch,
            name="expected_epoch",
        ):
            return CertificateVerdict(False, "epoch mismatch")
        if expected_price_e8 is not None and certificate.price_e8 != _require_positive_int(
            expected_price_e8,
            name="expected_price_e8",
        ):
            return CertificateVerdict(False, "price_e8 mismatch")
        if (
            expected_funding_rate_bps is not None
            and certificate.funding_rate_bps
            != _require_int(expected_funding_rate_bps, name="expected_funding_rate_bps")
        ):
            return CertificateVerdict(False, "funding_rate_bps mismatch")
        if expected_pre_due_vector_hash is not None and certificate.pre_due_vector_hash != _require_hash(
            expected_pre_due_vector_hash,
            name="expected_pre_due_vector_hash",
        ):
            return CertificateVerdict(False, "pre_due_vector_hash mismatch")
        if (
            expected_post_open_due_sum_quote is not None
            and certificate.post_open_due_sum_quote
            != _require_int(
                expected_post_open_due_sum_quote,
                name="expected_post_open_due_sum_quote",
            )
        ):
            return CertificateVerdict(False, "post_open_due_sum_quote mismatch")
        return validate_funding_closeout_liability_certificate_payload(certificate)
    except (TypeError, ValueError) as exc:
        return CertificateVerdict(False, str(exc))


def verify_funding_closeout_allocation_certificate_payload(
    payload: object,
    *,
    expected_epoch: int | None = None,
    expected_price_e8: int | None = None,
    expected_funding_rate_bps: int | None = None,
    expected_pre_due_vector_hash: str | None = None,
    expected_raw_post_open_due_sum_quote: int | None = None,
    expected_payable_post_open_due_sum_quote: int | None = None,
) -> CertificateVerdict:
    try:
        certificate = funding_closeout_allocation_certificate_from_payload(payload)
        if expected_epoch is not None and certificate.epoch != _require_non_negative_int(
            expected_epoch,
            name="expected_epoch",
        ):
            return CertificateVerdict(False, "epoch mismatch")
        if expected_price_e8 is not None and certificate.price_e8 != _require_positive_int(
            expected_price_e8,
            name="expected_price_e8",
        ):
            return CertificateVerdict(False, "price_e8 mismatch")
        if (
            expected_funding_rate_bps is not None
            and certificate.funding_rate_bps
            != _require_int(expected_funding_rate_bps, name="expected_funding_rate_bps")
        ):
            return CertificateVerdict(False, "funding_rate_bps mismatch")
        if expected_pre_due_vector_hash is not None and certificate.pre_due_vector_hash != _require_hash(
            expected_pre_due_vector_hash,
            name="expected_pre_due_vector_hash",
        ):
            return CertificateVerdict(False, "pre_due_vector_hash mismatch")
        if (
            expected_raw_post_open_due_sum_quote is not None
            and certificate.raw_post_open_due_sum_quote
            != _require_int(
                expected_raw_post_open_due_sum_quote,
                name="expected_raw_post_open_due_sum_quote",
            )
        ):
            return CertificateVerdict(False, "raw_post_open_due_sum_quote mismatch")
        if (
            expected_payable_post_open_due_sum_quote is not None
            and certificate.payable_post_open_due_sum_quote
            != _require_int(
                expected_payable_post_open_due_sum_quote,
                name="expected_payable_post_open_due_sum_quote",
            )
        ):
            return CertificateVerdict(False, "payable_post_open_due_sum_quote mismatch")
        return validate_funding_closeout_allocation_certificate_payload(certificate)
    except (TypeError, ValueError) as exc:
        return CertificateVerdict(False, str(exc))


def verify_funding_closeout_liability_receipt_payload(
    payload: object,
    *,
    expected_market_id: str | None = None,
    expected_epoch: int | None = None,
    expected_price_e8: int | None = None,
    expected_funding_rate_bps: int | None = None,
    expected_pre_close_state_root_hash: str | None = None,
    expected_post_open_due_sum_quote: int | None = None,
) -> CertificateVerdict:
    try:
        receipt = funding_closeout_liability_receipt_from_payload(payload)
        if expected_market_id is not None and receipt.market_id != _require_account(
            expected_market_id,
            name="expected_market_id",
        ):
            return CertificateVerdict(False, "market_id mismatch")
        if expected_epoch is not None and receipt.epoch != _require_non_negative_int(
            expected_epoch,
            name="expected_epoch",
        ):
            return CertificateVerdict(False, "epoch mismatch")
        if (
            expected_pre_close_state_root_hash is not None
            and receipt.pre_close_state_root_hash
            != _require_hash(
                expected_pre_close_state_root_hash,
                name="expected_pre_close_state_root_hash",
            )
        ):
            return CertificateVerdict(False, "pre_close_state_root_hash mismatch")
        if receipt.certificate.epoch != receipt.epoch:
            return CertificateVerdict(False, "receipt certificate epoch mismatch")
        if receipt.pre_due_vector_hash != receipt.certificate.pre_due_vector_hash:
            return CertificateVerdict(False, "receipt pre_due_vector_hash mismatch")
        derived_root = pre_close_position_snapshot_hash_from_due_rows(
            receipt.certificate.pre_due_rows,
            market_id=receipt.market_id,
            epoch=receipt.epoch,
        )
        if receipt.pre_close_state_root_hash != derived_root:
            return CertificateVerdict(False, "pre_close_state_root_hash does not match pre_due rows")
        return verify_funding_closeout_liability_certificate_payload(
            funding_closeout_liability_certificate_to_payload(receipt.certificate),
            expected_epoch=receipt.epoch,
            expected_price_e8=expected_price_e8,
            expected_funding_rate_bps=expected_funding_rate_bps,
            expected_pre_due_vector_hash=receipt.pre_due_vector_hash,
            expected_post_open_due_sum_quote=expected_post_open_due_sum_quote,
        )
    except (TypeError, ValueError) as exc:
        return CertificateVerdict(False, str(exc))


def verify_funding_closeout_allocation_receipt_payload(
    payload: object,
    *,
    expected_market_id: str | None = None,
    expected_epoch: int | None = None,
    expected_price_e8: int | None = None,
    expected_funding_rate_bps: int | None = None,
    expected_pre_close_state_root_hash: str | None = None,
    expected_raw_post_open_due_sum_quote: int | None = None,
    expected_payable_post_open_due_sum_quote: int | None = None,
) -> CertificateVerdict:
    try:
        receipt = funding_closeout_allocation_receipt_from_payload(payload)
        if expected_market_id is not None and receipt.market_id != _require_account(
            expected_market_id,
            name="expected_market_id",
        ):
            return CertificateVerdict(False, "market_id mismatch")
        if expected_epoch is not None and receipt.epoch != _require_non_negative_int(
            expected_epoch,
            name="expected_epoch",
        ):
            return CertificateVerdict(False, "epoch mismatch")
        if (
            expected_pre_close_state_root_hash is not None
            and receipt.pre_close_state_root_hash
            != _require_hash(
                expected_pre_close_state_root_hash,
                name="expected_pre_close_state_root_hash",
            )
        ):
            return CertificateVerdict(False, "pre_close_state_root_hash mismatch")
        if receipt.certificate.epoch != receipt.epoch:
            return CertificateVerdict(False, "receipt certificate epoch mismatch")
        if receipt.pre_due_vector_hash != receipt.certificate.pre_due_vector_hash:
            return CertificateVerdict(False, "receipt pre_due_vector_hash mismatch")
        derived_root = pre_close_position_snapshot_hash_from_due_rows(
            receipt.certificate.pre_due_rows,
            market_id=receipt.market_id,
            epoch=receipt.epoch,
        )
        if receipt.pre_close_state_root_hash != derived_root:
            return CertificateVerdict(False, "pre_close_state_root_hash does not match pre_due rows")
        return verify_funding_closeout_allocation_certificate_payload(
            funding_closeout_allocation_certificate_to_payload(receipt.certificate),
            expected_epoch=receipt.epoch,
            expected_price_e8=expected_price_e8,
            expected_funding_rate_bps=expected_funding_rate_bps,
            expected_pre_due_vector_hash=receipt.pre_due_vector_hash,
            expected_raw_post_open_due_sum_quote=(
                expected_raw_post_open_due_sum_quote
            ),
            expected_payable_post_open_due_sum_quote=(
                expected_payable_post_open_due_sum_quote
            ),
        )
    except (TypeError, ValueError) as exc:
        return CertificateVerdict(False, str(exc))


def verify_funding_closeout_rationed_allocation_receipt_payload(
    payload: object,
    *,
    expected_market_id: str | None = None,
    expected_epoch: int | None = None,
    expected_price_e8: int | None = None,
    expected_funding_rate_bps: int | None = None,
    expected_pre_close_state_root_hash: str | None = None,
    expected_raw_post_open_due_sum_quote: int | None = None,
    expected_payable_post_open_due_sum_quote: int | None = None,
    expected_receiver_claim_rows: tuple[ReceiverClaimRow, ...] | None = None,
) -> CertificateVerdict:
    try:
        receipt = funding_closeout_rationed_allocation_receipt_from_payload(payload)
        if expected_market_id is not None and receipt.market_id != _require_account(
            expected_market_id,
            name="expected_market_id",
        ):
            return CertificateVerdict(False, "market_id mismatch")
        if expected_epoch is not None and receipt.epoch != _require_non_negative_int(
            expected_epoch,
            name="expected_epoch",
        ):
            return CertificateVerdict(False, "epoch mismatch")
        if (
            expected_pre_close_state_root_hash is not None
            and receipt.pre_close_state_root_hash
            != _require_hash(
                expected_pre_close_state_root_hash,
                name="expected_pre_close_state_root_hash",
            )
        ):
            return CertificateVerdict(False, "pre_close_state_root_hash mismatch")
        if receipt.certificate.epoch != receipt.epoch:
            return CertificateVerdict(False, "receipt certificate epoch mismatch")
        if receipt.pre_due_vector_hash != receipt.certificate.pre_due_vector_hash:
            return CertificateVerdict(False, "receipt pre_due_vector_hash mismatch")
        derived_root = pre_close_position_snapshot_hash_from_due_rows(
            receipt.certificate.pre_due_rows,
            market_id=receipt.market_id,
            epoch=receipt.epoch,
        )
        if receipt.pre_close_state_root_hash != derived_root:
            return CertificateVerdict(
                False,
                "pre_close_state_root_hash does not match pre_due rows",
            )
        certificate_verdict = verify_funding_closeout_allocation_certificate_payload(
            funding_closeout_allocation_certificate_to_payload(receipt.certificate),
            expected_epoch=receipt.epoch,
            expected_price_e8=expected_price_e8,
            expected_funding_rate_bps=expected_funding_rate_bps,
            expected_pre_due_vector_hash=receipt.pre_due_vector_hash,
            expected_raw_post_open_due_sum_quote=(
                expected_raw_post_open_due_sum_quote
            ),
            expected_payable_post_open_due_sum_quote=(
                expected_payable_post_open_due_sum_quote
            ),
        )
        if not certificate_verdict.ok:
            return certificate_verdict
        return validate_funding_closeout_rationed_allocation_receipt_payload(
            receipt,
            expected_receiver_claim_rows=expected_receiver_claim_rows,
        )
    except (TypeError, ValueError) as exc:
        return CertificateVerdict(False, str(exc))


def verify_funding_closeout_source_bound_rationed_allocation_receipt_payload(
    payload: object,
    *,
    expected_market_id: str | None = None,
    expected_epoch: int | None = None,
    expected_price_e8: int | None = None,
    expected_funding_rate_bps: int | None = None,
    expected_pre_close_state_root_hash: str | None = None,
    expected_source_availability_hash: str | None = None,
    expected_raw_post_open_due_sum_quote: int | None = None,
    expected_payable_post_open_due_sum_quote: int | None = None,
    expected_receiver_claim_rows: tuple[ReceiverClaimRow, ...] | None = None,
) -> CertificateVerdict:
    try:
        receipt = funding_closeout_source_bound_rationed_allocation_receipt_from_payload(
            payload
        )
        if expected_market_id is not None and receipt.market_id != _require_account(
            expected_market_id,
            name="expected_market_id",
        ):
            return CertificateVerdict(False, "market_id mismatch")
        if expected_epoch is not None and receipt.epoch != _require_non_negative_int(
            expected_epoch,
            name="expected_epoch",
        ):
            return CertificateVerdict(False, "epoch mismatch")
        if (
            expected_pre_close_state_root_hash is not None
            and receipt.pre_close_state_root_hash
            != _require_hash(
                expected_pre_close_state_root_hash,
                name="expected_pre_close_state_root_hash",
            )
        ):
            return CertificateVerdict(False, "pre_close_state_root_hash mismatch")
        if receipt.certificate.epoch != receipt.epoch:
            return CertificateVerdict(False, "receipt certificate epoch mismatch")
        if receipt.pre_due_vector_hash != receipt.certificate.pre_due_vector_hash:
            return CertificateVerdict(False, "receipt pre_due_vector_hash mismatch")
        derived_root = pre_close_position_snapshot_hash_from_due_rows(
            receipt.certificate.pre_due_rows,
            market_id=receipt.market_id,
            epoch=receipt.epoch,
        )
        if receipt.pre_close_state_root_hash != derived_root:
            return CertificateVerdict(
                False,
                "pre_close_state_root_hash does not match pre_due rows",
            )
        certificate_verdict = verify_funding_closeout_allocation_certificate_payload(
            funding_closeout_allocation_certificate_to_payload(receipt.certificate),
            expected_epoch=receipt.epoch,
            expected_price_e8=expected_price_e8,
            expected_funding_rate_bps=expected_funding_rate_bps,
            expected_pre_due_vector_hash=receipt.pre_due_vector_hash,
            expected_raw_post_open_due_sum_quote=(
                expected_raw_post_open_due_sum_quote
            ),
            expected_payable_post_open_due_sum_quote=(
                expected_payable_post_open_due_sum_quote
            ),
        )
        if not certificate_verdict.ok:
            return certificate_verdict
        return validate_funding_closeout_source_bound_rationed_allocation_receipt_payload(
            receipt,
            expected_source_availability_hash=expected_source_availability_hash,
            expected_receiver_claim_rows=expected_receiver_claim_rows,
        )
    except (TypeError, ValueError) as exc:
        return CertificateVerdict(False, str(exc))


def verify_funding_closeout_source_portfolio_bound_rationed_allocation_receipt_payload(
    payload: object,
    *,
    expected_market_id: str | None = None,
    expected_epoch: int | None = None,
    expected_price_e8: int | None = None,
    expected_funding_rate_bps: int | None = None,
    expected_pre_close_state_root_hash: str | None = None,
    expected_pending_source_availability_hashes: tuple[str, ...] | None = None,
    expected_aggregate_sink_capacity_quote: int | None = None,
    expected_raw_post_open_due_sum_quote: int | None = None,
    expected_payable_post_open_due_sum_quote: int | None = None,
    expected_receiver_claim_rows: tuple[ReceiverClaimRow, ...] | None = None,
) -> CertificateVerdict:
    try:
        receipt = (
            funding_closeout_source_portfolio_bound_rationed_allocation_receipt_from_payload(
                payload
            )
        )
        if expected_market_id is not None and receipt.market_id != _require_account(
            expected_market_id,
            name="expected_market_id",
        ):
            return CertificateVerdict(False, "market_id mismatch")
        if expected_epoch is not None and receipt.epoch != _require_non_negative_int(
            expected_epoch,
            name="expected_epoch",
        ):
            return CertificateVerdict(False, "epoch mismatch")
        if (
            expected_pre_close_state_root_hash is not None
            and receipt.pre_close_state_root_hash
            != _require_hash(
                expected_pre_close_state_root_hash,
                name="expected_pre_close_state_root_hash",
            )
        ):
            return CertificateVerdict(False, "pre_close_state_root_hash mismatch")
        if receipt.certificate.epoch != receipt.epoch:
            return CertificateVerdict(False, "receipt certificate epoch mismatch")
        if receipt.pre_due_vector_hash != receipt.certificate.pre_due_vector_hash:
            return CertificateVerdict(False, "receipt pre_due_vector_hash mismatch")
        derived_root = pre_close_position_snapshot_hash_from_due_rows(
            receipt.certificate.pre_due_rows,
            market_id=receipt.market_id,
            epoch=receipt.epoch,
        )
        if receipt.pre_close_state_root_hash != derived_root:
            return CertificateVerdict(
                False,
                "pre_close_state_root_hash does not match pre_due rows",
            )
        certificate_verdict = verify_funding_closeout_allocation_certificate_payload(
            funding_closeout_allocation_certificate_to_payload(receipt.certificate),
            expected_epoch=receipt.epoch,
            expected_price_e8=expected_price_e8,
            expected_funding_rate_bps=expected_funding_rate_bps,
            expected_pre_due_vector_hash=receipt.pre_due_vector_hash,
            expected_raw_post_open_due_sum_quote=(
                expected_raw_post_open_due_sum_quote
            ),
            expected_payable_post_open_due_sum_quote=(
                expected_payable_post_open_due_sum_quote
            ),
        )
        if not certificate_verdict.ok:
            return certificate_verdict
        return validate_funding_closeout_source_portfolio_bound_rationed_allocation_receipt_payload(
            receipt,
            expected_pending_source_availability_hashes=(
                expected_pending_source_availability_hashes
            ),
            expected_aggregate_sink_capacity_quote=(
                expected_aggregate_sink_capacity_quote
            ),
            expected_receiver_claim_rows=expected_receiver_claim_rows,
        )
    except (TypeError, ValueError) as exc:
        return CertificateVerdict(False, str(exc))


def verify_funding_closeout_carry_forward_receipt_payload(
    payload: object,
    *,
    expected_market_id: str | None = None,
    expected_source_epoch: int | None = None,
    expected_carry_epoch: int | None = None,
    expected_pre_close_state_root_hash: str | None = None,
    expected_pending_source_availability_hashes: tuple[str, ...] | None = None,
    expected_carried_liability_hash: str | None = None,
    expected_aggregate_sink_capacity_quote: int | None = None,
    expected_receiver_claim_rows: tuple[ReceiverClaimRow, ...] | None = None,
) -> CertificateVerdict:
    try:
        receipt = funding_closeout_carry_forward_receipt_from_payload(payload)
        if receipt.schema != CARRY_FORWARD_RECEIPT_SCHEMA:
            return CertificateVerdict(False, "invalid carry-forward receipt schema")
        if receipt.carry_epoch <= receipt.source_epoch:
            return CertificateVerdict(False, "carry_epoch must be greater than source_epoch")
        if expected_market_id is not None and receipt.market_id != _require_account(
            expected_market_id,
            name="expected_market_id",
        ):
            return CertificateVerdict(False, "market_id mismatch")
        if (
            expected_source_epoch is not None
            and receipt.source_epoch
            != _require_non_negative_int(
                expected_source_epoch,
                name="expected_source_epoch",
            )
        ):
            return CertificateVerdict(False, "source_epoch mismatch")
        if (
            expected_carry_epoch is not None
            and receipt.carry_epoch
            != _require_non_negative_int(
                expected_carry_epoch,
                name="expected_carry_epoch",
            )
        ):
            return CertificateVerdict(False, "carry_epoch mismatch")
        if (
            expected_pre_close_state_root_hash is not None
            and receipt.pre_close_state_root_hash
            != _require_hash(
                expected_pre_close_state_root_hash,
                name="expected_pre_close_state_root_hash",
            )
        ):
            return CertificateVerdict(False, "pre_close_state_root_hash mismatch")
        if expected_pending_source_availability_hashes is not None:
            expected_pending = tuple(
                sorted(
                    _require_hash(root_hash, name="expected_pending_source_availability_hash")
                    for root_hash in expected_pending_source_availability_hashes
                )
            )
            if receipt.pending_source_availability_hashes != expected_pending:
                return CertificateVerdict(
                    False,
                    "pending source availability hashes mismatch",
                )
        if (
            expected_carried_liability_hash is not None
            and receipt.carried_liability_hash
            != _require_hash(
                expected_carried_liability_hash,
                name="expected_carried_liability_hash",
            )
        ):
            return CertificateVerdict(False, "carried_liability_hash mismatch")

        source_portfolio_receipt = receipt.source_portfolio_receipt
        if source_portfolio_receipt.market_id != receipt.market_id:
            return CertificateVerdict(False, "source portfolio market_id mismatch")
        if source_portfolio_receipt.epoch != receipt.source_epoch:
            return CertificateVerdict(False, "source portfolio epoch mismatch")
        if (
            source_portfolio_receipt.pre_close_state_root_hash
            != receipt.pre_close_state_root_hash
        ):
            return CertificateVerdict(
                False,
                "source portfolio pre_close_state_root_hash mismatch",
            )
        if (
            source_portfolio_receipt.pending_source_availability_hashes
            != receipt.pending_source_availability_hashes
        ):
            return CertificateVerdict(
                False,
                "source portfolio pending source hashes mismatch",
            )
        if source_portfolio_receipt.source_availability_hash != receipt.source_availability_hash:
            return CertificateVerdict(
                False,
                "source portfolio source_availability_hash mismatch",
            )

        source_hash = funding_closeout_source_portfolio_receipt_hash(
            source_portfolio_receipt
        )
        if receipt.source_portfolio_receipt_hash != source_hash:
            return CertificateVerdict(False, "source_portfolio_receipt_hash mismatch")
        carried_hash = carried_funding_closeout_liability_hash(receipt)
        if receipt.carried_liability_hash != carried_hash:
            return CertificateVerdict(False, "carried_liability_hash mismatch")

        return verify_funding_closeout_source_portfolio_bound_rationed_allocation_receipt_payload(
            funding_closeout_source_portfolio_bound_rationed_allocation_receipt_to_payload(
                source_portfolio_receipt
            ),
            expected_market_id=receipt.market_id,
            expected_epoch=receipt.source_epoch,
            expected_pre_close_state_root_hash=receipt.pre_close_state_root_hash,
            expected_pending_source_availability_hashes=(
                receipt.pending_source_availability_hashes
            ),
            expected_aggregate_sink_capacity_quote=(
                expected_aggregate_sink_capacity_quote
            ),
            expected_receiver_claim_rows=expected_receiver_claim_rows,
        )
    except (TypeError, ValueError) as exc:
        return CertificateVerdict(False, str(exc))


def validate_funding_closeout_liability_certificate_payload(
    certificate: FundingCloseoutLiabilityCertificate,
) -> CertificateVerdict:
    if certificate.schema != CERT_SCHEMA:
        return CertificateVerdict(False, "invalid certificate schema")
    if not _is_sorted_by_account(certificate.pre_due_rows):
        return CertificateVerdict(False, "pre_due_rows must be sorted by account_pubkey")
    if not _is_sorted_by_account(certificate.closed_liability_rows):
        return CertificateVerdict(False, "closed_liability_rows must be sorted by account_pubkey")
    if _has_duplicate_accounts(certificate.pre_due_rows):
        return CertificateVerdict(False, "duplicate pre_due account")
    if _has_duplicate_accounts(certificate.closed_liability_rows):
        return CertificateVerdict(False, "duplicate closed liability account")
    if certificate.pre_due_vector_hash != pre_due_vector_hash(certificate.pre_due_rows):
        return CertificateVerdict(False, "pre_due_vector_hash mismatch")

    due_by_account = {row.account_pubkey: row.due_quote for row in certificate.pre_due_rows}
    for row in certificate.closed_liability_rows:
        if row.account_pubkey not in due_by_account:
            return CertificateVerdict(False, "closed liability account missing from pre_due_rows")
        verdict = _validate_closed_liability_row(
            row,
            certificate,
            {row.account_pubkey: due_by_account[row.account_pubkey]},
        )
        if not verdict.ok:
            return verdict

    pre_sum = sum(row.due_quote for row in certificate.pre_due_rows)
    closed_sum = sum(row.closed_due_quote for row in certificate.closed_liability_rows)
    if certificate.post_open_due_sum_quote + closed_sum != pre_sum:
        return CertificateVerdict(False, "batch funding conservation mismatch")
    return CertificateVerdict(True, None)


def validate_funding_closeout_allocation_certificate_payload(
    certificate: FundingCloseoutAllocationCertificate,
) -> CertificateVerdict:
    base_verdict = _validate_allocation_certificate_shape(certificate)
    if not base_verdict.ok:
        return base_verdict
    due_by_account = {row.account_pubkey: row.due_quote for row in certificate.pre_due_rows}
    for row in certificate.closed_allocation_rows:
        if row.account_pubkey not in due_by_account:
            return CertificateVerdict(False, "closed allocation account missing from pre_due_rows")
        if due_by_account[row.account_pubkey] <= 0:
            return CertificateVerdict(
                False,
                "allocation certificate only supports positive closed due",
            )
        verdict = _validate_closed_allocation_row(
            row,
            certificate,
            {row.account_pubkey: due_by_account[row.account_pubkey]},
        )
        if not verdict.ok:
            return verdict
    return _validate_allocation_certificate_sums(certificate)


def validate_funding_closeout_rationed_allocation_receipt_payload(
    receipt: FundingCloseoutRationedAllocationReceipt,
    *,
    expected_receiver_claim_rows: tuple[ReceiverClaimRow, ...] | None = None,
) -> CertificateVerdict:
    if receipt.schema != RATIONED_ALLOCATION_RECEIPT_SCHEMA:
        return CertificateVerdict(False, "invalid rationed allocation receipt schema")
    certificate = receipt.certificate
    rationing = receipt.receiver_haircut_rationing
    if rationing.total_haircut_quote != certificate.receiver_haircut_sum_quote:
        return CertificateVerdict(False, "receiver haircut rationing total mismatch")
    if certificate.raw_post_open_due_sum_quote >= 0:
        return CertificateVerdict(
            False,
            "rationed allocation receipt requires negative raw receiver sum",
        )
    if rationing.total_claim_quote != -int(certificate.raw_post_open_due_sum_quote):
        return CertificateVerdict(False, "receiver claim total mismatch")
    payable_sum = sum(row.payable_quote for row in rationing.receiver_rows)
    if certificate.payable_post_open_due_sum_quote != -int(payable_sum):
        return CertificateVerdict(False, "receiver payable sum mismatch")
    if expected_receiver_claim_rows is not None:
        expected_rationing = build_receiver_haircut_rationing(
            expected_receiver_claim_rows,
            total_haircut_quote=certificate.receiver_haircut_sum_quote,
        )
        if rationing != expected_rationing:
            return CertificateVerdict(False, "receiver haircut rationing mismatch")
    return CertificateVerdict(True, None)


def validate_funding_closeout_source_bound_rationed_allocation_receipt_payload(
    receipt: FundingCloseoutSourceBoundRationedAllocationReceipt,
    *,
    expected_source_availability_hash: str | None = None,
    expected_receiver_claim_rows: tuple[ReceiverClaimRow, ...] | None = None,
) -> CertificateVerdict:
    if receipt.schema != SOURCE_BOUND_RATIONED_ALLOCATION_RECEIPT_SCHEMA:
        return CertificateVerdict(
            False,
            "invalid source-bound rationed allocation receipt schema",
        )
    if not _is_sorted_by_account(receipt.source_availability_rows):
        return CertificateVerdict(
            False,
            "source_availability_rows must be sorted by account_pubkey",
        )
    if _has_duplicate_accounts(receipt.source_availability_rows):
        return CertificateVerdict(False, "duplicate source availability account")
    derived_source_hash = funding_closeout_source_availability_hash(
        receipt.source_availability_rows
    )
    if receipt.source_availability_hash != derived_source_hash:
        return CertificateVerdict(False, "source_availability_hash mismatch")
    if (
        expected_source_availability_hash is not None
        and receipt.source_availability_hash
        != _require_hash(
            expected_source_availability_hash,
            name="expected_source_availability_hash",
        )
    ):
        return CertificateVerdict(False, "source_availability_hash mismatch")
    expected_source_rows = closed_funding_source_rows_from_allocation_certificate(
        receipt.certificate
    )
    if receipt.source_availability_rows != expected_source_rows:
        return CertificateVerdict(False, "source availability rows mismatch")
    rationed_receipt = FundingCloseoutRationedAllocationReceipt(
        schema=RATIONED_ALLOCATION_RECEIPT_SCHEMA,
        market_id=receipt.market_id,
        epoch=receipt.epoch,
        pre_due_vector_hash=receipt.pre_due_vector_hash,
        pre_close_state_root_hash=receipt.pre_close_state_root_hash,
        certificate=receipt.certificate,
        receiver_haircut_rationing=receipt.receiver_haircut_rationing,
    )
    return validate_funding_closeout_rationed_allocation_receipt_payload(
        rationed_receipt,
        expected_receiver_claim_rows=expected_receiver_claim_rows,
    )


def validate_funding_closeout_source_portfolio_bound_rationed_allocation_receipt_payload(
    receipt: FundingCloseoutSourcePortfolioBoundRationedAllocationReceipt,
    *,
    expected_pending_source_availability_hashes: tuple[str, ...] | None = None,
    expected_aggregate_sink_capacity_quote: int | None = None,
    expected_receiver_claim_rows: tuple[ReceiverClaimRow, ...] | None = None,
) -> CertificateVerdict:
    if receipt.schema != SOURCE_PORTFOLIO_BOUND_RATIONED_ALLOCATION_RECEIPT_SCHEMA:
        return CertificateVerdict(
            False,
            "invalid source-portfolio rationed allocation receipt schema",
        )
    if not _is_sorted_by_account(receipt.emitted_source_availability_rows):
        return CertificateVerdict(
            False,
            "emitted_source_availability_rows must be sorted by account_pubkey",
        )
    if _has_duplicate_accounts(receipt.emitted_source_availability_rows):
        return CertificateVerdict(False, "duplicate emitted source availability account")
    derived_pending_hashes = tuple(
        sorted(
            funding_closeout_source_availability_hash((row,))
            for row in receipt.emitted_source_availability_rows
        )
    )
    if receipt.pending_source_availability_hashes != derived_pending_hashes:
        return CertificateVerdict(False, "pending source availability hashes mismatch")
    if expected_pending_source_availability_hashes is not None:
        expected_pending = tuple(
            sorted(
                _require_hash(root_hash, name="expected_pending_source_availability_hash")
                for root_hash in expected_pending_source_availability_hashes
            )
        )
        if receipt.pending_source_availability_hashes != expected_pending:
            return CertificateVerdict(False, "pending source availability hashes mismatch")
    if (
        expected_aggregate_sink_capacity_quote is not None
        and receipt.aggregate_sink_capacity_quote
        != _require_non_negative_int(
            expected_aggregate_sink_capacity_quote,
            name="expected_aggregate_sink_capacity_quote",
        )
    ):
        return CertificateVerdict(False, "aggregate sink capacity mismatch")
    emitted_by_account = {
        row.account_pubkey: row for row in receipt.emitted_source_availability_rows
    }
    for row in receipt.source_availability_rows:
        emitted = emitted_by_account.get(row.account_pubkey)
        if emitted is None:
            return CertificateVerdict(
                False,
                "source availability account missing from emitted rows",
            )
        if (
            row.epoch != emitted.epoch
            or row.payer_available_quote != emitted.payer_available_quote
        ):
            return CertificateVerdict(
                False,
                "source availability row does not match emitted payer source",
            )
    if (
        sum(row.sink_capacity_quote for row in receipt.source_availability_rows)
        > receipt.aggregate_sink_capacity_quote
    ):
        return CertificateVerdict(
            False,
            "source sink reservation exceeds aggregate capacity",
        )
    source_bound_receipt = FundingCloseoutSourceBoundRationedAllocationReceipt(
        schema=SOURCE_BOUND_RATIONED_ALLOCATION_RECEIPT_SCHEMA,
        market_id=receipt.market_id,
        epoch=receipt.epoch,
        pre_due_vector_hash=receipt.pre_due_vector_hash,
        pre_close_state_root_hash=receipt.pre_close_state_root_hash,
        source_availability_hash=receipt.source_availability_hash,
        source_availability_rows=receipt.source_availability_rows,
        certificate=receipt.certificate,
        receiver_haircut_rationing=receipt.receiver_haircut_rationing,
    )
    return validate_funding_closeout_source_bound_rationed_allocation_receipt_payload(
        source_bound_receipt,
        expected_source_availability_hash=receipt.source_availability_hash,
        expected_receiver_claim_rows=expected_receiver_claim_rows,
    )


def _validate_allocation_certificate_shape(
    certificate: FundingCloseoutAllocationCertificate,
) -> CertificateVerdict:
    if certificate.schema != ALLOCATION_CERT_SCHEMA:
        return CertificateVerdict(False, "invalid allocation certificate schema")
    if not _is_sorted_by_account(certificate.pre_due_rows):
        return CertificateVerdict(False, "pre_due_rows must be sorted by account_pubkey")
    if not _is_sorted_by_account(certificate.closed_allocation_rows):
        return CertificateVerdict(False, "closed_allocation_rows must be sorted by account_pubkey")
    if _has_duplicate_accounts(certificate.pre_due_rows):
        return CertificateVerdict(False, "duplicate pre_due account")
    if _has_duplicate_accounts(certificate.closed_allocation_rows):
        return CertificateVerdict(False, "duplicate closed allocation account")
    if certificate.pre_due_vector_hash != pre_due_vector_hash(certificate.pre_due_rows):
        return CertificateVerdict(False, "pre_due_vector_hash mismatch")
    return CertificateVerdict(True, None)


def _validate_closed_allocation_row(
    row: ClosedLiabilityAllocationRow,
    certificate: FundingCloseoutAllocationCertificate,
    expected_closed: dict[str, int],
) -> CertificateVerdict:
    if row.epoch != certificate.epoch:
        return CertificateVerdict(False, "closed allocation epoch mismatch")
    if row.closed_due_quote != expected_closed[row.account_pubkey]:
        return CertificateVerdict(False, "closed_due_quote mismatch")
    allocation = build_limited_liability_funding_closeout_allocation(
        closed_due_quote=row.closed_due_quote,
        payer_available_quote=row.payer_available_quote,
        sink_capacity_quote=row.sink_capacity_quote,
    )
    if row.payer_debit_quote != allocation.payer_debit_quote:
        return CertificateVerdict(False, "payer_debit_quote mismatch")
    if row.sink_draw_quote != allocation.sink_draw_quote:
        return CertificateVerdict(False, "sink_draw_quote mismatch")
    if row.subrogated_claim_quote != allocation.subrogated_claim_quote:
        return CertificateVerdict(False, "subrogated_claim_quote mismatch")
    if row.receiver_haircut_quote != allocation.receiver_haircut_quote:
        return CertificateVerdict(False, "receiver_haircut_quote mismatch")
    if row.paid_to_receiver_quote != allocation.paid_to_receiver_quote:
        return CertificateVerdict(False, "paid_to_receiver_quote mismatch")
    return CertificateVerdict(True, None)


def _validate_allocation_certificate_sums(
    certificate: FundingCloseoutAllocationCertificate,
) -> CertificateVerdict:
    pre_sum = sum(row.due_quote for row in certificate.pre_due_rows)
    closed_sum = sum(row.closed_due_quote for row in certificate.closed_allocation_rows)
    paid_sum = sum(row.paid_to_receiver_quote for row in certificate.closed_allocation_rows)
    haircut_sum = sum(
        row.receiver_haircut_quote for row in certificate.closed_allocation_rows
    )
    if certificate.receiver_haircut_sum_quote != haircut_sum:
        return CertificateVerdict(False, "receiver_haircut_sum_quote mismatch")
    if certificate.raw_post_open_due_sum_quote + closed_sum != pre_sum:
        return CertificateVerdict(False, "nominal batch funding conservation mismatch")
    if (
        certificate.payable_post_open_due_sum_quote
        != certificate.raw_post_open_due_sum_quote + haircut_sum
    ):
        return CertificateVerdict(False, "payable_post_open_due_sum_quote mismatch")
    if certificate.payable_post_open_due_sum_quote + paid_sum != pre_sum:
        return CertificateVerdict(False, "payable funding conservation mismatch")
    return CertificateVerdict(True, None)


def _validate_closed_liability_row(
    row: ClosedLiabilityRow,
    certificate: FundingCloseoutLiabilityCertificate,
    expected_closed: dict[str, int],
) -> CertificateVerdict:
    if row.epoch != certificate.epoch:
        return CertificateVerdict(False, "closed liability epoch mismatch")
    if row.closed_due_quote != expected_closed[row.account_pubkey]:
        return CertificateVerdict(False, "closed_due_quote mismatch")
    if row.closed_due_quote > 0:
        return _validate_positive_closed_due(row)
    return _validate_non_positive_closed_due(row)


def _validate_positive_closed_due(row: ClosedLiabilityRow) -> CertificateVerdict:
    if row.carried_due_quote < 0:
        return CertificateVerdict(False, "positive closed due cannot have negative carried due")
    if row.sink_draw_quote != row.subrogated_claim_quote:
        return CertificateVerdict(False, "sink draw must create matching subrogated claim")
    if row.carried_due_quote + row.subrogated_claim_quote != row.closed_due_quote:
        return CertificateVerdict(False, "positive closed due is not fully carried or subrogated")
    return CertificateVerdict(True, None)


def _validate_non_positive_closed_due(row: ClosedLiabilityRow) -> CertificateVerdict:
    if row.sink_draw_quote != 0 or row.subrogated_claim_quote != 0:
        return CertificateVerdict(False, "negative closed due cannot use sink subrogation")
    if row.carried_due_quote != row.closed_due_quote:
        return CertificateVerdict(False, "negative closed due must be carried exactly")
    return CertificateVerdict(True, None)
