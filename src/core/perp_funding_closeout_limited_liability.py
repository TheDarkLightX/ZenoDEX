from __future__ import annotations

from collections.abc import Mapping
from dataclasses import asdict, dataclass

ALLOCATION_SCHEMA = "zenodex.perp.funding_closeout_limited_liability_allocation.v1"


def _require_int(value: object, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    return int(value)


def _require_non_negative_int(value: object, *, name: str) -> int:
    out = _require_int(value, name=name)
    if out < 0:
        raise ValueError(f"{name} must be non-negative")
    return out


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


@dataclass(frozen=True)
class LimitedLiabilityAllocationVerdict:
    ok: bool
    error: str | None

    def __post_init__(self) -> None:
        if not isinstance(self.ok, bool):
            raise TypeError("ok must be a bool")
        if self.error is not None and not isinstance(self.error, str):
            raise TypeError("error must be None or str")


@dataclass(frozen=True)
class LimitedLiabilityFundingCloseoutAllocation:
    schema: str
    closed_due_quote: int
    payer_available_quote: int
    sink_capacity_quote: int
    payer_debit_quote: int
    sink_draw_quote: int
    subrogated_claim_quote: int
    receiver_haircut_quote: int
    paid_to_receiver_quote: int

    def __post_init__(self) -> None:
        if self.schema != ALLOCATION_SCHEMA:
            raise ValueError("invalid allocation schema")
        closed_due = _require_non_negative_int(
            self.closed_due_quote,
            name="closed_due_quote",
        )
        payer_available = _require_non_negative_int(
            self.payer_available_quote,
            name="payer_available_quote",
        )
        sink_capacity = _require_non_negative_int(
            self.sink_capacity_quote,
            name="sink_capacity_quote",
        )
        payer_debit = _require_non_negative_int(
            self.payer_debit_quote,
            name="payer_debit_quote",
        )
        sink_draw = _require_non_negative_int(
            self.sink_draw_quote,
            name="sink_draw_quote",
        )
        subrogated_claim = _require_non_negative_int(
            self.subrogated_claim_quote,
            name="subrogated_claim_quote",
        )
        receiver_haircut = _require_non_negative_int(
            self.receiver_haircut_quote,
            name="receiver_haircut_quote",
        )
        paid_to_receiver = _require_non_negative_int(
            self.paid_to_receiver_quote,
            name="paid_to_receiver_quote",
        )

        if payer_debit > payer_available:
            raise ValueError("payer_debit_quote exceeds payer_available_quote")
        if sink_draw > sink_capacity:
            raise ValueError("sink_draw_quote exceeds sink_capacity_quote")
        if sink_draw != subrogated_claim:
            raise ValueError("sink draw must create matching subrogated claim")
        if payer_debit + sink_draw + receiver_haircut != closed_due:
            raise ValueError("limited-liability conservation mismatch")
        if paid_to_receiver != payer_debit + sink_draw:
            raise ValueError("paid_to_receiver_quote mismatch")

        canonical_payer_debit = min(closed_due, payer_available)
        if payer_debit != canonical_payer_debit:
            raise ValueError("payer_debit_quote is not canonical")
        residual_after_payer = closed_due - canonical_payer_debit
        canonical_sink_draw = min(residual_after_payer, sink_capacity)
        if sink_draw != canonical_sink_draw:
            raise ValueError("sink_draw_quote is not canonical")


def build_limited_liability_funding_closeout_allocation(
    *,
    closed_due_quote: int,
    payer_available_quote: int,
    sink_capacity_quote: int,
) -> LimitedLiabilityFundingCloseoutAllocation:
    closed_due = _require_non_negative_int(
        closed_due_quote,
        name="closed_due_quote",
    )
    payer_available = _require_non_negative_int(
        payer_available_quote,
        name="payer_available_quote",
    )
    sink_capacity = _require_non_negative_int(
        sink_capacity_quote,
        name="sink_capacity_quote",
    )

    payer_debit = min(closed_due, payer_available)
    residual_after_payer = closed_due - payer_debit
    sink_draw = min(residual_after_payer, sink_capacity)
    receiver_haircut = residual_after_payer - sink_draw
    paid_to_receiver = payer_debit + sink_draw

    return LimitedLiabilityFundingCloseoutAllocation(
        schema=ALLOCATION_SCHEMA,
        closed_due_quote=closed_due,
        payer_available_quote=payer_available,
        sink_capacity_quote=sink_capacity,
        payer_debit_quote=payer_debit,
        sink_draw_quote=sink_draw,
        subrogated_claim_quote=sink_draw,
        receiver_haircut_quote=receiver_haircut,
        paid_to_receiver_quote=paid_to_receiver,
    )


def limited_liability_allocation_to_payload(
    allocation: LimitedLiabilityFundingCloseoutAllocation,
) -> dict[str, object]:
    if not isinstance(allocation, LimitedLiabilityFundingCloseoutAllocation):
        raise TypeError("allocation must be a LimitedLiabilityFundingCloseoutAllocation")
    return asdict(allocation)


def limited_liability_allocation_from_payload(
    payload: object,
) -> LimitedLiabilityFundingCloseoutAllocation:
    data = _require_payload_mapping(payload, name="allocation")
    _require_exact_keys(
        data,
        name="allocation",
        keys={
            "schema",
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
    schema = data["schema"]
    if not isinstance(schema, str):
        raise TypeError("schema must be a str")
    return LimitedLiabilityFundingCloseoutAllocation(
        schema=schema,
        closed_due_quote=_require_non_negative_int(
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


def verify_limited_liability_allocation_payload(
    payload: object,
) -> LimitedLiabilityAllocationVerdict:
    try:
        limited_liability_allocation_from_payload(payload)
    except (TypeError, ValueError) as exc:
        return LimitedLiabilityAllocationVerdict(False, str(exc))
    return LimitedLiabilityAllocationVerdict(True, None)
