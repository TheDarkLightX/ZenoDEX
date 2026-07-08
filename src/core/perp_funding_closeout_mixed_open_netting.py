from __future__ import annotations

import hashlib
from collections.abc import Mapping
from dataclasses import asdict, dataclass

from ..state.canonical import canonical_json_bytes
from .perp_funding_closeout_liability_certificate import (
    CertificateVerdict,
    PositionAccount,
)
from .perp_funding_closeout_receiver_rationing import (
    ReceiverClaimRow,
    ReceiverHaircutRationing,
    build_receiver_haircut_rationing,
    receiver_haircut_rationing_from_payload,
    receiver_haircut_rationing_to_payload,
)
from .perp_v2.math import funding_payment

MIXED_OPEN_NETTING_SCHEMA = "zenodex.perp.funding_closeout_mixed_open_netting.v1"


@dataclass(frozen=True)
class OpenFundingDueRow:
    account_pubkey: str
    due_quote: int

    def __post_init__(self) -> None:
        _require_account(self.account_pubkey, name="account_pubkey")
        due = _require_int(self.due_quote, name="due_quote")
        if due == 0:
            raise ValueError("due_quote must be nonzero")


@dataclass(frozen=True)
class MixedOpenFundingNettingCertificate:
    schema: str
    epoch: int
    price_e8: int
    funding_rate_bps: int
    open_due_rows: tuple[OpenFundingDueRow, ...]
    open_payer_due_sum_quote: int
    receiver_claim_sum_quote: int
    raw_post_open_due_sum_quote: int
    receiver_haircut_sum_quote: int
    payable_receiver_sum_quote: int
    payable_post_open_due_sum_quote: int
    receiver_haircut_rationing: ReceiverHaircutRationing

    def __post_init__(self) -> None:
        if not isinstance(self.schema, str):
            raise TypeError("schema must be a str")
        _require_non_negative_int(self.epoch, name="epoch")
        _require_positive_int(self.price_e8, name="price_e8")
        _require_int(self.funding_rate_bps, name="funding_rate_bps")
        _require_open_due_rows(self.open_due_rows)
        _require_non_negative_int(
            self.open_payer_due_sum_quote,
            name="open_payer_due_sum_quote",
        )
        _require_non_negative_int(
            self.receiver_claim_sum_quote,
            name="receiver_claim_sum_quote",
        )
        _require_int(
            self.raw_post_open_due_sum_quote,
            name="raw_post_open_due_sum_quote",
        )
        _require_non_negative_int(
            self.receiver_haircut_sum_quote,
            name="receiver_haircut_sum_quote",
        )
        _require_non_negative_int(
            self.payable_receiver_sum_quote,
            name="payable_receiver_sum_quote",
        )
        _require_int(
            self.payable_post_open_due_sum_quote,
            name="payable_post_open_due_sum_quote",
        )
        if not isinstance(self.receiver_haircut_rationing, ReceiverHaircutRationing):
            raise TypeError(
                "receiver_haircut_rationing must be a ReceiverHaircutRationing"
            )


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


def _require_open_due_rows(rows: object) -> tuple[OpenFundingDueRow, ...]:
    if not isinstance(rows, tuple):
        raise TypeError("open_due_rows must be a tuple")
    if not rows:
        raise ValueError("open_due_rows must be non-empty")
    if not all(isinstance(row, OpenFundingDueRow) for row in rows):
        raise TypeError("open_due_rows must contain OpenFundingDueRow values")
    accounts = [row.account_pubkey for row in rows]
    if accounts != sorted(accounts):
        raise ValueError("open_due_rows must be sorted by account_pubkey")
    if len(accounts) != len(set(accounts)):
        raise ValueError("duplicate open due account")
    return rows


def _require_position_accounts(accounts: object) -> tuple[PositionAccount, ...]:
    if not isinstance(accounts, tuple):
        raise TypeError("post_accounts must be a tuple")
    if not all(isinstance(account, PositionAccount) for account in accounts):
        raise TypeError("post_accounts must contain PositionAccount values")
    by_account = [account.account_pubkey for account in accounts]
    if len(by_account) != len(set(by_account)):
        raise ValueError("duplicate post account")
    return accounts


def expected_open_funding_due_rows(
    post_accounts: tuple[PositionAccount, ...],
    *,
    price_e8: int,
    funding_rate_bps: int,
) -> tuple[OpenFundingDueRow, ...]:
    checked = _require_position_accounts(post_accounts)
    price = _require_positive_int(price_e8, name="price_e8")
    rate = _require_int(funding_rate_bps, name="funding_rate_bps")
    rows: list[OpenFundingDueRow] = []
    for account in sorted(checked, key=lambda item: item.account_pubkey):
        if account.position_base == 0:
            continue
        due = funding_payment(account.position_base, price, rate)
        if due == 0:
            continue
        rows.append(OpenFundingDueRow(account.account_pubkey, due))
    return tuple(rows)


def receiver_claim_rows_from_open_due(
    rows: tuple[OpenFundingDueRow, ...],
) -> tuple[ReceiverClaimRow, ...]:
    checked = _require_open_due_rows(rows)
    return tuple(
        ReceiverClaimRow(row.account_pubkey, -int(row.due_quote))
        for row in checked
        if row.due_quote < 0
    )


def _payer_due_sum(rows: tuple[OpenFundingDueRow, ...]) -> int:
    return sum(row.due_quote for row in rows if row.due_quote > 0)


def _receiver_claim_sum(rows: tuple[OpenFundingDueRow, ...]) -> int:
    return sum(-row.due_quote for row in rows if row.due_quote < 0)


def _validate_mixed_open_sums(
    certificate: MixedOpenFundingNettingCertificate,
) -> CertificateVerdict:
    payer_sum = _payer_due_sum(certificate.open_due_rows)
    receiver_sum = _receiver_claim_sum(certificate.open_due_rows)
    if payer_sum <= 0:
        return CertificateVerdict(False, "mixed open netting requires open payer due")
    if receiver_sum <= 0:
        return CertificateVerdict(False, "mixed open netting requires receiver claims")
    if certificate.open_payer_due_sum_quote != payer_sum:
        return CertificateVerdict(False, "open_payer_due_sum_quote mismatch")
    if certificate.receiver_claim_sum_quote != receiver_sum:
        return CertificateVerdict(False, "receiver_claim_sum_quote mismatch")
    raw_sum = int(payer_sum) - int(receiver_sum)
    if certificate.raw_post_open_due_sum_quote != raw_sum:
        return CertificateVerdict(False, "raw_post_open_due_sum_quote mismatch")
    if certificate.receiver_haircut_sum_quote > receiver_sum:
        return CertificateVerdict(False, "receiver_haircut_sum_quote exceeds receiver claims")
    expected_rationing = build_receiver_haircut_rationing(
        receiver_claim_rows_from_open_due(certificate.open_due_rows),
        total_haircut_quote=certificate.receiver_haircut_sum_quote,
    )
    if certificate.receiver_haircut_rationing != expected_rationing:
        return CertificateVerdict(False, "receiver haircut rationing mismatch")
    payable_receiver_sum = sum(
        row.payable_quote for row in certificate.receiver_haircut_rationing.receiver_rows
    )
    if certificate.payable_receiver_sum_quote != payable_receiver_sum:
        return CertificateVerdict(False, "payable_receiver_sum_quote mismatch")
    payable_post_sum = int(payer_sum) - int(payable_receiver_sum)
    if certificate.payable_post_open_due_sum_quote != payable_post_sum:
        return CertificateVerdict(False, "payable_post_open_due_sum_quote mismatch")
    if certificate.payable_post_open_due_sum_quote != raw_sum + certificate.receiver_haircut_sum_quote:
        return CertificateVerdict(False, "payable net formula mismatch")
    return CertificateVerdict(True, None)


def build_mixed_open_funding_netting_certificate(
    post_accounts: tuple[PositionAccount, ...],
    *,
    epoch: int,
    price_e8: int,
    funding_rate_bps: int,
    receiver_haircut_sum_quote: int,
) -> MixedOpenFundingNettingCertificate:
    rows = expected_open_funding_due_rows(
        post_accounts,
        price_e8=price_e8,
        funding_rate_bps=funding_rate_bps,
    )
    payer_sum = _payer_due_sum(rows)
    receiver_sum = _receiver_claim_sum(rows)
    haircut_sum = _require_non_negative_int(
        receiver_haircut_sum_quote,
        name="receiver_haircut_sum_quote",
    )
    rationing = build_receiver_haircut_rationing(
        receiver_claim_rows_from_open_due(rows),
        total_haircut_quote=haircut_sum,
    )
    payable_receiver_sum = sum(row.payable_quote for row in rationing.receiver_rows)
    return MixedOpenFundingNettingCertificate(
        schema=MIXED_OPEN_NETTING_SCHEMA,
        epoch=_require_non_negative_int(epoch, name="epoch"),
        price_e8=_require_positive_int(price_e8, name="price_e8"),
        funding_rate_bps=_require_int(funding_rate_bps, name="funding_rate_bps"),
        open_due_rows=rows,
        open_payer_due_sum_quote=payer_sum,
        receiver_claim_sum_quote=receiver_sum,
        raw_post_open_due_sum_quote=int(payer_sum) - int(receiver_sum),
        receiver_haircut_sum_quote=haircut_sum,
        payable_receiver_sum_quote=payable_receiver_sum,
        payable_post_open_due_sum_quote=int(payer_sum) - int(payable_receiver_sum),
        receiver_haircut_rationing=rationing,
    )


def validate_mixed_open_funding_netting_certificate(
    post_accounts: tuple[PositionAccount, ...],
    certificate: MixedOpenFundingNettingCertificate,
) -> CertificateVerdict:
    if certificate.schema != MIXED_OPEN_NETTING_SCHEMA:
        return CertificateVerdict(False, "invalid mixed open netting schema")
    try:
        expected_rows = expected_open_funding_due_rows(
            post_accounts,
            price_e8=certificate.price_e8,
            funding_rate_bps=certificate.funding_rate_bps,
        )
    except (TypeError, ValueError) as exc:
        return CertificateVerdict(False, str(exc))
    if certificate.open_due_rows != expected_rows:
        return CertificateVerdict(False, "open_due_rows mismatch")
    return _validate_mixed_open_sums(certificate)


def open_funding_due_row_to_payload(row: OpenFundingDueRow) -> dict[str, object]:
    return asdict(row)


def open_funding_due_row_from_payload(payload: object) -> OpenFundingDueRow:
    data = _require_payload_mapping(payload, name="open_due_row")
    _require_exact_keys(
        data,
        name="open_due_row",
        keys={"account_pubkey", "due_quote"},
    )
    return OpenFundingDueRow(
        account_pubkey=_require_account(data["account_pubkey"], name="account_pubkey"),
        due_quote=_require_int(data["due_quote"], name="due_quote"),
    )


def mixed_open_funding_netting_certificate_to_payload(
    certificate: MixedOpenFundingNettingCertificate,
) -> dict[str, object]:
    return {
        "epoch": int(certificate.epoch),
        "funding_rate_bps": int(certificate.funding_rate_bps),
        "open_due_rows": [
            open_funding_due_row_to_payload(row)
            for row in certificate.open_due_rows
        ],
        "open_payer_due_sum_quote": int(certificate.open_payer_due_sum_quote),
        "payable_post_open_due_sum_quote": int(
            certificate.payable_post_open_due_sum_quote
        ),
        "payable_receiver_sum_quote": int(certificate.payable_receiver_sum_quote),
        "price_e8": int(certificate.price_e8),
        "raw_post_open_due_sum_quote": int(certificate.raw_post_open_due_sum_quote),
        "receiver_claim_sum_quote": int(certificate.receiver_claim_sum_quote),
        "receiver_haircut_rationing": receiver_haircut_rationing_to_payload(
            certificate.receiver_haircut_rationing
        ),
        "receiver_haircut_sum_quote": int(certificate.receiver_haircut_sum_quote),
        "schema": certificate.schema,
    }


def mixed_open_funding_netting_certificate_from_payload(
    payload: object,
) -> MixedOpenFundingNettingCertificate:
    data = _require_payload_mapping(payload, name="mixed_open_netting_certificate")
    _require_exact_keys(
        data,
        name="mixed_open_netting_certificate",
        keys={
            "epoch",
            "funding_rate_bps",
            "open_due_rows",
            "open_payer_due_sum_quote",
            "payable_post_open_due_sum_quote",
            "payable_receiver_sum_quote",
            "price_e8",
            "raw_post_open_due_sum_quote",
            "receiver_claim_sum_quote",
            "receiver_haircut_rationing",
            "receiver_haircut_sum_quote",
            "schema",
        },
    )
    rows_raw = data["open_due_rows"]
    if not isinstance(rows_raw, list):
        raise TypeError("open_due_rows must be a list")
    return MixedOpenFundingNettingCertificate(
        schema=_require_account(data["schema"], name="schema"),
        epoch=_require_non_negative_int(data["epoch"], name="epoch"),
        price_e8=_require_positive_int(data["price_e8"], name="price_e8"),
        funding_rate_bps=_require_int(data["funding_rate_bps"], name="funding_rate_bps"),
        open_due_rows=tuple(open_funding_due_row_from_payload(row) for row in rows_raw),
        open_payer_due_sum_quote=_require_non_negative_int(
            data["open_payer_due_sum_quote"],
            name="open_payer_due_sum_quote",
        ),
        receiver_claim_sum_quote=_require_non_negative_int(
            data["receiver_claim_sum_quote"],
            name="receiver_claim_sum_quote",
        ),
        raw_post_open_due_sum_quote=_require_int(
            data["raw_post_open_due_sum_quote"],
            name="raw_post_open_due_sum_quote",
        ),
        receiver_haircut_sum_quote=_require_non_negative_int(
            data["receiver_haircut_sum_quote"],
            name="receiver_haircut_sum_quote",
        ),
        payable_receiver_sum_quote=_require_non_negative_int(
            data["payable_receiver_sum_quote"],
            name="payable_receiver_sum_quote",
        ),
        payable_post_open_due_sum_quote=_require_int(
            data["payable_post_open_due_sum_quote"],
            name="payable_post_open_due_sum_quote",
        ),
        receiver_haircut_rationing=receiver_haircut_rationing_from_payload(
            data["receiver_haircut_rationing"]
        ),
    )


def mixed_open_funding_netting_certificate_hash(
    certificate: MixedOpenFundingNettingCertificate,
) -> str:
    payload = mixed_open_funding_netting_certificate_to_payload(certificate)
    return "sha256:" + hashlib.sha256(canonical_json_bytes(payload)).hexdigest()


def verify_mixed_open_funding_netting_certificate_payload(
    payload: object,
    *,
    post_accounts: tuple[PositionAccount, ...],
) -> CertificateVerdict:
    try:
        certificate = mixed_open_funding_netting_certificate_from_payload(payload)
    except (TypeError, ValueError) as exc:
        return CertificateVerdict(False, str(exc))
    return validate_mixed_open_funding_netting_certificate(post_accounts, certificate)
