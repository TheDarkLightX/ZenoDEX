from __future__ import annotations

from collections.abc import Mapping
from dataclasses import asdict, dataclass

RATIONING_SCHEMA = "zenodex.perp.funding_closeout_receiver_haircut_rationing.v1"
MAX_RECEIVER_ROWS = 4096


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


def _require_payload_list(value: object, *, name: str) -> tuple[object, ...]:
    if not isinstance(value, list):
        raise TypeError(f"{name} must be a list")
    return tuple(value)


@dataclass(frozen=True)
class ReceiverHaircutRationingVerdict:
    ok: bool
    error: str | None

    def __post_init__(self) -> None:
        if not isinstance(self.ok, bool):
            raise TypeError("ok must be a bool")
        if self.error is not None and not isinstance(self.error, str):
            raise TypeError("error must be None or str")


@dataclass(frozen=True)
class ReceiverClaimRow:
    account_pubkey: str
    claim_quote: int

    def __post_init__(self) -> None:
        _require_account(self.account_pubkey, name="account_pubkey")
        _require_positive_int(self.claim_quote, name="claim_quote")


@dataclass(frozen=True)
class ReceiverHaircutRow:
    account_pubkey: str
    claim_quote: int
    quota_floor_quote: int
    quota_remainder_numerator: int
    haircut_quote: int
    payable_quote: int

    def __post_init__(self) -> None:
        _require_account(self.account_pubkey, name="account_pubkey")
        _require_positive_int(self.claim_quote, name="claim_quote")
        _require_non_negative_int(
            self.quota_floor_quote,
            name="quota_floor_quote",
        )
        _require_non_negative_int(
            self.quota_remainder_numerator,
            name="quota_remainder_numerator",
        )
        _require_non_negative_int(self.haircut_quote, name="haircut_quote")
        _require_non_negative_int(self.payable_quote, name="payable_quote")


@dataclass(frozen=True)
class ReceiverHaircutRationing:
    schema: str
    total_claim_quote: int
    total_haircut_quote: int
    quota_denominator_quote: int
    receiver_rows: tuple[ReceiverHaircutRow, ...]

    def __post_init__(self) -> None:
        if self.schema != RATIONING_SCHEMA:
            raise ValueError("invalid rationing schema")
        _require_positive_int(self.total_claim_quote, name="total_claim_quote")
        _require_non_negative_int(
            self.total_haircut_quote,
            name="total_haircut_quote",
        )
        _require_positive_int(
            self.quota_denominator_quote,
            name="quota_denominator_quote",
        )
        _require_receiver_rows(self.receiver_rows)
        _validate_receiver_haircut_rationing(self)


def _require_claim_rows(rows: object) -> tuple[ReceiverClaimRow, ...]:
    if not isinstance(rows, tuple):
        raise TypeError("receiver_claim_rows must be a tuple")
    if not all(isinstance(row, ReceiverClaimRow) for row in rows):
        raise TypeError("receiver_claim_rows must contain ReceiverClaimRow values")
    if len(rows) == 0:
        raise ValueError("receiver_claim_rows must be non-empty")
    if len(rows) > MAX_RECEIVER_ROWS:
        raise ValueError("receiver_claim_rows exceeds MAX_RECEIVER_ROWS")
    accounts = [row.account_pubkey for row in rows]
    if len(accounts) != len(set(accounts)):
        raise ValueError("duplicate receiver claim account")
    return rows


def _require_receiver_rows(rows: object) -> tuple[ReceiverHaircutRow, ...]:
    if not isinstance(rows, tuple):
        raise TypeError("receiver_rows must be a tuple")
    if not all(isinstance(row, ReceiverHaircutRow) for row in rows):
        raise TypeError("receiver_rows must contain ReceiverHaircutRow values")
    if len(rows) == 0:
        raise ValueError("receiver_rows must be non-empty")
    if len(rows) > MAX_RECEIVER_ROWS:
        raise ValueError("receiver_rows exceeds MAX_RECEIVER_ROWS")
    accounts = [row.account_pubkey for row in rows]
    if accounts != sorted(accounts):
        raise ValueError("receiver_rows must be sorted by account_pubkey")
    if len(accounts) != len(set(accounts)):
        raise ValueError("duplicate receiver account")
    return rows


def build_receiver_haircut_rationing(
    receiver_claim_rows: tuple[ReceiverClaimRow, ...],
    *,
    total_haircut_quote: int,
) -> ReceiverHaircutRationing:
    claims = tuple(
        sorted(
            _require_claim_rows(receiver_claim_rows),
            key=lambda row: row.account_pubkey,
        )
    )
    total_claim = sum(row.claim_quote for row in claims)
    haircut_total = _require_non_negative_int(
        total_haircut_quote,
        name="total_haircut_quote",
    )
    if haircut_total > total_claim:
        raise ValueError("total_haircut_quote exceeds total_claim_quote")

    floors: dict[str, int] = {}
    remainders: dict[str, int] = {}
    floor_sum = 0
    for row in claims:
        numerator = int(row.claim_quote) * int(haircut_total)
        floor = numerator // total_claim
        remainder = numerator % total_claim
        floors[row.account_pubkey] = floor
        remainders[row.account_pubkey] = remainder
        floor_sum += floor

    leftover = int(haircut_total) - int(floor_sum)
    bonus_accounts = {
        account
        for account, _remainder in sorted(
            remainders.items(),
            key=lambda item: (-item[1], item[0]),
        )[:leftover]
    }

    rows = []
    for row in claims:
        bonus = 1 if row.account_pubkey in bonus_accounts else 0
        haircut = int(floors[row.account_pubkey]) + bonus
        rows.append(
            ReceiverHaircutRow(
                account_pubkey=row.account_pubkey,
                claim_quote=row.claim_quote,
                quota_floor_quote=floors[row.account_pubkey],
                quota_remainder_numerator=remainders[row.account_pubkey],
                haircut_quote=haircut,
                payable_quote=int(row.claim_quote) - haircut,
            )
        )

    return ReceiverHaircutRationing(
        schema=RATIONING_SCHEMA,
        total_claim_quote=total_claim,
        total_haircut_quote=haircut_total,
        quota_denominator_quote=total_claim,
        receiver_rows=tuple(rows),
    )


def receiver_haircut_rationing_to_payload(
    rationing: ReceiverHaircutRationing,
) -> dict[str, object]:
    if not isinstance(rationing, ReceiverHaircutRationing):
        raise TypeError("rationing must be a ReceiverHaircutRationing")
    return {
        "schema": rationing.schema,
        "total_claim_quote": rationing.total_claim_quote,
        "total_haircut_quote": rationing.total_haircut_quote,
        "quota_denominator_quote": rationing.quota_denominator_quote,
        "receiver_rows": [asdict(row) for row in rationing.receiver_rows],
    }


def receiver_haircut_rationing_from_payload(
    payload: object,
) -> ReceiverHaircutRationing:
    data = _require_payload_mapping(payload, name="receiver_haircut_rationing")
    _require_exact_keys(
        data,
        name="receiver_haircut_rationing",
        keys={
            "schema",
            "total_claim_quote",
            "total_haircut_quote",
            "quota_denominator_quote",
            "receiver_rows",
        },
    )
    schema = data["schema"]
    if not isinstance(schema, str):
        raise TypeError("schema must be a str")
    return ReceiverHaircutRationing(
        schema=schema,
        total_claim_quote=_require_positive_int(
            data["total_claim_quote"],
            name="total_claim_quote",
        ),
        total_haircut_quote=_require_non_negative_int(
            data["total_haircut_quote"],
            name="total_haircut_quote",
        ),
        quota_denominator_quote=_require_positive_int(
            data["quota_denominator_quote"],
            name="quota_denominator_quote",
        ),
        receiver_rows=tuple(
            _receiver_row_from_payload(row)
            for row in _require_payload_list(
                data["receiver_rows"],
                name="receiver_rows",
            )
        ),
    )


def verify_receiver_haircut_rationing_payload(
    payload: object,
) -> ReceiverHaircutRationingVerdict:
    try:
        receiver_haircut_rationing_from_payload(payload)
    except (TypeError, ValueError) as exc:
        return ReceiverHaircutRationingVerdict(False, str(exc))
    return ReceiverHaircutRationingVerdict(True, None)


def _receiver_row_from_payload(row: object) -> ReceiverHaircutRow:
    data = _require_payload_mapping(row, name="receiver_row")
    _require_exact_keys(
        data,
        name="receiver_row",
        keys={
            "account_pubkey",
            "claim_quote",
            "quota_floor_quote",
            "quota_remainder_numerator",
            "haircut_quote",
            "payable_quote",
        },
    )
    return ReceiverHaircutRow(
        account_pubkey=_require_account(data["account_pubkey"], name="account_pubkey"),
        claim_quote=_require_positive_int(data["claim_quote"], name="claim_quote"),
        quota_floor_quote=_require_non_negative_int(
            data["quota_floor_quote"],
            name="quota_floor_quote",
        ),
        quota_remainder_numerator=_require_non_negative_int(
            data["quota_remainder_numerator"],
            name="quota_remainder_numerator",
        ),
        haircut_quote=_require_non_negative_int(
            data["haircut_quote"],
            name="haircut_quote",
        ),
        payable_quote=_require_non_negative_int(
            data["payable_quote"],
            name="payable_quote",
        ),
    )


def _validate_receiver_haircut_rationing(
    rationing: ReceiverHaircutRationing,
) -> None:
    rows = _require_receiver_rows(rationing.receiver_rows)
    total_claim = sum(row.claim_quote for row in rows)
    if rationing.total_claim_quote != total_claim:
        raise ValueError("total_claim_quote mismatch")
    if rationing.quota_denominator_quote != total_claim:
        raise ValueError("quota_denominator_quote mismatch")
    if rationing.total_haircut_quote > total_claim:
        raise ValueError("total_haircut_quote exceeds total_claim_quote")

    expected = _expected_haircut_by_account(rows, rationing.total_haircut_quote)
    haircut_sum = 0
    payable_sum = 0
    for row in rows:
        numerator = int(row.claim_quote) * int(rationing.total_haircut_quote)
        floor = numerator // total_claim
        remainder = numerator % total_claim
        if row.quota_floor_quote != floor:
            raise ValueError("quota_floor_quote mismatch")
        if row.quota_remainder_numerator != remainder:
            raise ValueError("quota_remainder_numerator mismatch")
        if row.haircut_quote != expected[row.account_pubkey]:
            raise ValueError("haircut_quote is not canonical")
        if row.payable_quote != row.claim_quote - row.haircut_quote:
            raise ValueError("payable_quote mismatch")
        haircut_sum += row.haircut_quote
        payable_sum += row.payable_quote

    if haircut_sum != rationing.total_haircut_quote:
        raise ValueError("total haircut conservation mismatch")
    if payable_sum != rationing.total_claim_quote - rationing.total_haircut_quote:
        raise ValueError("payable conservation mismatch")


def _expected_haircut_by_account(
    rows: tuple[ReceiverHaircutRow, ...],
    total_haircut_quote: int,
) -> dict[str, int]:
    total_claim = sum(row.claim_quote for row in rows)
    floors: dict[str, int] = {}
    remainders: dict[str, int] = {}
    floor_sum = 0
    for row in rows:
        numerator = int(row.claim_quote) * int(total_haircut_quote)
        floor = numerator // total_claim
        remainder = numerator % total_claim
        floors[row.account_pubkey] = floor
        remainders[row.account_pubkey] = remainder
        floor_sum += floor
    leftover = int(total_haircut_quote) - int(floor_sum)
    bonus_accounts = {
        account
        for account, _remainder in sorted(
            remainders.items(),
            key=lambda item: (-item[1], item[0]),
        )[:leftover]
    }
    return {
        row.account_pubkey: int(floors[row.account_pubkey])
        + (1 if row.account_pubkey in bonus_accounts else 0)
        for row in rows
    }
