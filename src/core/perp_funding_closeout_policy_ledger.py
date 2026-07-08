from __future__ import annotations

import hashlib
from collections.abc import Mapping
from dataclasses import asdict, dataclass

from ..state.canonical import canonical_json_bytes
from .perp_funding_closeout_liability_certificate import (
    FundingCloseoutSourcePortfolioBoundRationedAllocationReceipt,
    funding_closeout_source_portfolio_receipt_hash,
)

POLICY_LEDGER_SCHEMA = "zenodex.perp.funding_closeout_policy_ledger.v1"
HAIRCUT_POLICY_FINAL_LOSS = "final_loss"
HAIRCUT_POLICY_RECOVERABLE_CLAIM = "recoverable_claim"
SINK_CLAIMANT_PROTOCOL = "protocol_sink"
MAX_POLICY_ROWS = 4096


def _require_int(value: object, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    return int(value)


def _require_non_negative_int(value: object, *, name: str) -> int:
    out = _require_int(value, name=name)
    if out < 0:
        raise ValueError(f"{name} must be non-negative")
    return out


def _require_account(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a str")
    if not value:
        raise ValueError(f"{name} must be non-empty")
    if "\x00" in value:
        raise ValueError(f"{name} must not contain NUL")
    return value


def _require_hash(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a str")
    if not value.startswith("sha256:") or len(value) != len("sha256:") + 64:
        raise ValueError(f"{name} must be sha256:<64 lowercase hex chars>")
    suffix = value[len("sha256:") :]
    if suffix.lower() != suffix or any(ch not in "0123456789abcdef" for ch in suffix):
        raise ValueError(f"{name} must be sha256:<64 lowercase hex chars>")
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


def _require_haircut_policy(value: object) -> str:
    if not isinstance(value, str):
        raise TypeError("haircut_policy must be a str")
    if value not in {HAIRCUT_POLICY_FINAL_LOSS, HAIRCUT_POLICY_RECOVERABLE_CLAIM}:
        raise ValueError("haircut_policy must be final_loss or recoverable_claim")
    return value


@dataclass(frozen=True)
class PolicyLedgerVerdict:
    ok: bool
    error: str | None

    def __post_init__(self) -> None:
        if not isinstance(self.ok, bool):
            raise TypeError("ok must be a bool")
        if self.error is not None and not isinstance(self.error, str):
            raise TypeError("error must be None or str")


@dataclass(frozen=True)
class ReceiverHaircutPolicyRow:
    account_pubkey: str
    epoch: int
    haircut_quote: int
    final_loss_quote: int
    recoverable_claim_quote: int

    def __post_init__(self) -> None:
        _require_account(self.account_pubkey, name="account_pubkey")
        _require_non_negative_int(self.epoch, name="epoch")
        haircut = _require_non_negative_int(self.haircut_quote, name="haircut_quote")
        final_loss = _require_non_negative_int(
            self.final_loss_quote,
            name="final_loss_quote",
        )
        recoverable = _require_non_negative_int(
            self.recoverable_claim_quote,
            name="recoverable_claim_quote",
        )
        if final_loss + recoverable != haircut:
            raise ValueError("haircut policy row does not classify full haircut")


@dataclass(frozen=True)
class SinkSubrogationPolicyRow:
    account_pubkey: str
    epoch: int
    claimant: str
    sink_draw_quote: int
    subrogated_claim_quote: int

    def __post_init__(self) -> None:
        _require_account(self.account_pubkey, name="account_pubkey")
        _require_non_negative_int(self.epoch, name="epoch")
        _require_account(self.claimant, name="claimant")
        sink_draw = _require_non_negative_int(
            self.sink_draw_quote,
            name="sink_draw_quote",
        )
        subrogated_claim = _require_non_negative_int(
            self.subrogated_claim_quote,
            name="subrogated_claim_quote",
        )
        if sink_draw != subrogated_claim:
            raise ValueError("sink draw must equal subrogated claim")


@dataclass(frozen=True)
class FundingCloseoutPolicyLedger:
    schema: str
    market_id: str
    epoch: int
    source_portfolio_receipt_hash: str
    haircut_policy: str
    total_receiver_haircut_quote: int
    total_final_loss_quote: int
    total_recoverable_claim_quote: int
    total_sink_draw_quote: int
    total_subrogated_claim_quote: int
    receiver_haircut_rows: tuple[ReceiverHaircutPolicyRow, ...]
    sink_subrogation_rows: tuple[SinkSubrogationPolicyRow, ...]

    def __post_init__(self) -> None:
        if self.schema != POLICY_LEDGER_SCHEMA:
            raise ValueError("invalid policy ledger schema")
        _require_account(self.market_id, name="market_id")
        _require_non_negative_int(self.epoch, name="epoch")
        _require_hash(
            self.source_portfolio_receipt_hash,
            name="source_portfolio_receipt_hash",
        )
        policy = _require_haircut_policy(self.haircut_policy)
        receiver_rows = _require_receiver_haircut_rows(self.receiver_haircut_rows)
        sink_rows = _require_sink_subrogation_rows(self.sink_subrogation_rows)

        total_haircut = _require_non_negative_int(
            self.total_receiver_haircut_quote,
            name="total_receiver_haircut_quote",
        )
        total_final = _require_non_negative_int(
            self.total_final_loss_quote,
            name="total_final_loss_quote",
        )
        total_recoverable = _require_non_negative_int(
            self.total_recoverable_claim_quote,
            name="total_recoverable_claim_quote",
        )
        total_sink_draw = _require_non_negative_int(
            self.total_sink_draw_quote,
            name="total_sink_draw_quote",
        )
        total_subrogated = _require_non_negative_int(
            self.total_subrogated_claim_quote,
            name="total_subrogated_claim_quote",
        )

        if total_haircut != sum(row.haircut_quote for row in receiver_rows):
            raise ValueError("total_receiver_haircut_quote mismatch")
        if total_final != sum(row.final_loss_quote for row in receiver_rows):
            raise ValueError("total_final_loss_quote mismatch")
        if total_recoverable != sum(row.recoverable_claim_quote for row in receiver_rows):
            raise ValueError("total_recoverable_claim_quote mismatch")
        if total_sink_draw != sum(row.sink_draw_quote for row in sink_rows):
            raise ValueError("total_sink_draw_quote mismatch")
        if total_subrogated != sum(row.subrogated_claim_quote for row in sink_rows):
            raise ValueError("total_subrogated_claim_quote mismatch")

        for row in receiver_rows:
            if policy == HAIRCUT_POLICY_FINAL_LOSS and row.final_loss_quote != row.haircut_quote:
                raise ValueError("final_loss policy must classify every haircut as final loss")
            if policy == HAIRCUT_POLICY_FINAL_LOSS and row.recoverable_claim_quote != 0:
                raise ValueError("final_loss policy cannot create recoverable claims")
            if policy == HAIRCUT_POLICY_RECOVERABLE_CLAIM and row.recoverable_claim_quote != row.haircut_quote:
                raise ValueError(
                    "recoverable_claim policy must classify every haircut as recoverable"
                )
            if policy == HAIRCUT_POLICY_RECOVERABLE_CLAIM and row.final_loss_quote != 0:
                raise ValueError("recoverable_claim policy cannot create final loss")


def _require_receiver_haircut_rows(
    rows: object,
) -> tuple[ReceiverHaircutPolicyRow, ...]:
    if not isinstance(rows, tuple):
        raise TypeError("receiver_haircut_rows must be a tuple")
    if not all(isinstance(row, ReceiverHaircutPolicyRow) for row in rows):
        raise TypeError("receiver_haircut_rows must contain ReceiverHaircutPolicyRow values")
    if len(rows) > MAX_POLICY_ROWS:
        raise ValueError("receiver_haircut_rows exceeds MAX_POLICY_ROWS")
    accounts = [row.account_pubkey for row in rows]
    if accounts != sorted(accounts):
        raise ValueError("receiver_haircut_rows must be sorted by account_pubkey")
    if len(accounts) != len(set(accounts)):
        raise ValueError("duplicate receiver haircut account")
    return rows


def _require_sink_subrogation_rows(
    rows: object,
) -> tuple[SinkSubrogationPolicyRow, ...]:
    if not isinstance(rows, tuple):
        raise TypeError("sink_subrogation_rows must be a tuple")
    if not all(isinstance(row, SinkSubrogationPolicyRow) for row in rows):
        raise TypeError("sink_subrogation_rows must contain SinkSubrogationPolicyRow values")
    if len(rows) > MAX_POLICY_ROWS:
        raise ValueError("sink_subrogation_rows exceeds MAX_POLICY_ROWS")
    keys = [(row.account_pubkey, row.claimant) for row in rows]
    if keys != sorted(keys):
        raise ValueError("sink_subrogation_rows must be sorted by account_pubkey and claimant")
    if len(keys) != len(set(keys)):
        raise ValueError("duplicate sink subrogation row")
    return rows


def build_funding_closeout_policy_ledger(
    source_portfolio_receipt: FundingCloseoutSourcePortfolioBoundRationedAllocationReceipt,
    *,
    haircut_policy: str,
    claimant: str = SINK_CLAIMANT_PROTOCOL,
) -> FundingCloseoutPolicyLedger:
    if not isinstance(
        source_portfolio_receipt,
        FundingCloseoutSourcePortfolioBoundRationedAllocationReceipt,
    ):
        raise TypeError(
            "source_portfolio_receipt must be a FundingCloseoutSourcePortfolioBoundRationedAllocationReceipt"
        )
    policy = _require_haircut_policy(haircut_policy)
    claim_owner = _require_account(claimant, name="claimant")

    receiver_rows = tuple(
        ReceiverHaircutPolicyRow(
            account_pubkey=row.account_pubkey,
            epoch=source_portfolio_receipt.epoch,
            haircut_quote=row.haircut_quote,
            final_loss_quote=(
                row.haircut_quote if policy == HAIRCUT_POLICY_FINAL_LOSS else 0
            ),
            recoverable_claim_quote=(
                row.haircut_quote
                if policy == HAIRCUT_POLICY_RECOVERABLE_CLAIM
                else 0
            ),
        )
        for row in source_portfolio_receipt.receiver_haircut_rationing.receiver_rows
    )
    sink_rows = tuple(
        sorted(
            (
                SinkSubrogationPolicyRow(
                    account_pubkey=row.account_pubkey,
                    epoch=source_portfolio_receipt.epoch,
                    claimant=claim_owner,
                    sink_draw_quote=row.sink_draw_quote,
                    subrogated_claim_quote=row.subrogated_claim_quote,
                )
                for row in source_portfolio_receipt.certificate.closed_allocation_rows
                if row.sink_draw_quote > 0 or row.subrogated_claim_quote > 0
            ),
            key=lambda row: (row.account_pubkey, row.claimant),
        )
    )

    return FundingCloseoutPolicyLedger(
        schema=POLICY_LEDGER_SCHEMA,
        market_id=source_portfolio_receipt.market_id,
        epoch=source_portfolio_receipt.epoch,
        source_portfolio_receipt_hash=(
            funding_closeout_source_portfolio_receipt_hash(source_portfolio_receipt)
        ),
        haircut_policy=policy,
        total_receiver_haircut_quote=sum(row.haircut_quote for row in receiver_rows),
        total_final_loss_quote=sum(row.final_loss_quote for row in receiver_rows),
        total_recoverable_claim_quote=sum(
            row.recoverable_claim_quote for row in receiver_rows
        ),
        total_sink_draw_quote=sum(row.sink_draw_quote for row in sink_rows),
        total_subrogated_claim_quote=sum(row.subrogated_claim_quote for row in sink_rows),
        receiver_haircut_rows=receiver_rows,
        sink_subrogation_rows=sink_rows,
    )


def validate_policy_ledger_against_source_portfolio_receipt(
    ledger: FundingCloseoutPolicyLedger,
    source_portfolio_receipt: FundingCloseoutSourcePortfolioBoundRationedAllocationReceipt,
) -> None:
    if not isinstance(ledger, FundingCloseoutPolicyLedger):
        raise TypeError("ledger must be a FundingCloseoutPolicyLedger")
    if not isinstance(
        source_portfolio_receipt,
        FundingCloseoutSourcePortfolioBoundRationedAllocationReceipt,
    ):
        raise TypeError(
            "source_portfolio_receipt must be a FundingCloseoutSourcePortfolioBoundRationedAllocationReceipt"
        )
    if ledger.market_id != source_portfolio_receipt.market_id:
        raise ValueError("policy ledger market_id mismatch")
    if ledger.epoch != source_portfolio_receipt.epoch:
        raise ValueError("policy ledger epoch mismatch")
    expected_receipt_hash = funding_closeout_source_portfolio_receipt_hash(
        source_portfolio_receipt
    )
    if ledger.source_portfolio_receipt_hash != expected_receipt_hash:
        raise ValueError("policy ledger source receipt hash mismatch")

    expected_receiver_rows = tuple(
        (row.account_pubkey, source_portfolio_receipt.epoch, row.haircut_quote)
        for row in source_portfolio_receipt.receiver_haircut_rationing.receiver_rows
    )
    actual_receiver_rows = tuple(
        (row.account_pubkey, row.epoch, row.haircut_quote)
        for row in ledger.receiver_haircut_rows
    )
    if actual_receiver_rows != expected_receiver_rows:
        raise ValueError("policy ledger receiver haircut rows mismatch")
    if (
        ledger.total_receiver_haircut_quote
        != source_portfolio_receipt.receiver_haircut_rationing.total_haircut_quote
    ):
        raise ValueError("policy ledger receiver haircut total mismatch")

    expected_sink_rows = tuple(
        sorted(
            (
                (
                    row.account_pubkey,
                    source_portfolio_receipt.epoch,
                    row.sink_draw_quote,
                    row.subrogated_claim_quote,
                )
                for row in source_portfolio_receipt.certificate.closed_allocation_rows
                if row.sink_draw_quote > 0 or row.subrogated_claim_quote > 0
            )
        )
    )
    actual_sink_rows = tuple(
        (row.account_pubkey, row.epoch, row.sink_draw_quote, row.subrogated_claim_quote)
        for row in ledger.sink_subrogation_rows
    )
    if actual_sink_rows != expected_sink_rows:
        raise ValueError("policy ledger sink subrogation rows mismatch")


def funding_closeout_policy_ledger_to_payload(
    ledger: FundingCloseoutPolicyLedger,
) -> dict[str, object]:
    if not isinstance(ledger, FundingCloseoutPolicyLedger):
        raise TypeError("ledger must be a FundingCloseoutPolicyLedger")
    return {
        "schema": ledger.schema,
        "market_id": ledger.market_id,
        "epoch": ledger.epoch,
        "source_portfolio_receipt_hash": ledger.source_portfolio_receipt_hash,
        "haircut_policy": ledger.haircut_policy,
        "total_receiver_haircut_quote": ledger.total_receiver_haircut_quote,
        "total_final_loss_quote": ledger.total_final_loss_quote,
        "total_recoverable_claim_quote": ledger.total_recoverable_claim_quote,
        "total_sink_draw_quote": ledger.total_sink_draw_quote,
        "total_subrogated_claim_quote": ledger.total_subrogated_claim_quote,
        "receiver_haircut_rows": [
            asdict(row) for row in ledger.receiver_haircut_rows
        ],
        "sink_subrogation_rows": [asdict(row) for row in ledger.sink_subrogation_rows],
    }


def funding_closeout_policy_ledger_hash(
    ledger: FundingCloseoutPolicyLedger,
) -> str:
    return "sha256:" + hashlib.sha256(
        canonical_json_bytes(funding_closeout_policy_ledger_to_payload(ledger))
    ).hexdigest()


def funding_closeout_policy_ledger_from_payload(
    payload: object,
) -> FundingCloseoutPolicyLedger:
    data = _require_payload_mapping(payload, name="policy_ledger")
    _require_exact_keys(
        data,
        name="policy_ledger",
        keys={
            "schema",
            "market_id",
            "epoch",
            "source_portfolio_receipt_hash",
            "haircut_policy",
            "total_receiver_haircut_quote",
            "total_final_loss_quote",
            "total_recoverable_claim_quote",
            "total_sink_draw_quote",
            "total_subrogated_claim_quote",
            "receiver_haircut_rows",
            "sink_subrogation_rows",
        },
    )
    schema = data["schema"]
    if not isinstance(schema, str):
        raise TypeError("schema must be a str")
    return FundingCloseoutPolicyLedger(
        schema=schema,
        market_id=_require_account(data["market_id"], name="market_id"),
        epoch=_require_non_negative_int(data["epoch"], name="epoch"),
        source_portfolio_receipt_hash=_require_hash(
            data["source_portfolio_receipt_hash"],
            name="source_portfolio_receipt_hash",
        ),
        haircut_policy=_require_haircut_policy(data["haircut_policy"]),
        total_receiver_haircut_quote=_require_non_negative_int(
            data["total_receiver_haircut_quote"],
            name="total_receiver_haircut_quote",
        ),
        total_final_loss_quote=_require_non_negative_int(
            data["total_final_loss_quote"],
            name="total_final_loss_quote",
        ),
        total_recoverable_claim_quote=_require_non_negative_int(
            data["total_recoverable_claim_quote"],
            name="total_recoverable_claim_quote",
        ),
        total_sink_draw_quote=_require_non_negative_int(
            data["total_sink_draw_quote"],
            name="total_sink_draw_quote",
        ),
        total_subrogated_claim_quote=_require_non_negative_int(
            data["total_subrogated_claim_quote"],
            name="total_subrogated_claim_quote",
        ),
        receiver_haircut_rows=tuple(
            _receiver_haircut_row_from_payload(row)
            for row in _require_payload_list(
                data["receiver_haircut_rows"],
                name="receiver_haircut_rows",
            )
        ),
        sink_subrogation_rows=tuple(
            _sink_subrogation_row_from_payload(row)
            for row in _require_payload_list(
                data["sink_subrogation_rows"],
                name="sink_subrogation_rows",
            )
        ),
    )


def verify_funding_closeout_policy_ledger_payload(
    payload: object,
    *,
    source_portfolio_receipt: (
        FundingCloseoutSourcePortfolioBoundRationedAllocationReceipt | None
    ) = None,
) -> PolicyLedgerVerdict:
    try:
        ledger = funding_closeout_policy_ledger_from_payload(payload)
        if source_portfolio_receipt is not None:
            validate_policy_ledger_against_source_portfolio_receipt(
                ledger,
                source_portfolio_receipt,
            )
    except (TypeError, ValueError) as exc:
        return PolicyLedgerVerdict(False, str(exc))
    return PolicyLedgerVerdict(True, None)


def _receiver_haircut_row_from_payload(row: object) -> ReceiverHaircutPolicyRow:
    data = _require_payload_mapping(row, name="receiver_haircut_row")
    _require_exact_keys(
        data,
        name="receiver_haircut_row",
        keys={
            "account_pubkey",
            "epoch",
            "haircut_quote",
            "final_loss_quote",
            "recoverable_claim_quote",
        },
    )
    return ReceiverHaircutPolicyRow(
        account_pubkey=_require_account(data["account_pubkey"], name="account_pubkey"),
        epoch=_require_non_negative_int(data["epoch"], name="epoch"),
        haircut_quote=_require_non_negative_int(
            data["haircut_quote"],
            name="haircut_quote",
        ),
        final_loss_quote=_require_non_negative_int(
            data["final_loss_quote"],
            name="final_loss_quote",
        ),
        recoverable_claim_quote=_require_non_negative_int(
            data["recoverable_claim_quote"],
            name="recoverable_claim_quote",
        ),
    )


def _sink_subrogation_row_from_payload(row: object) -> SinkSubrogationPolicyRow:
    data = _require_payload_mapping(row, name="sink_subrogation_row")
    _require_exact_keys(
        data,
        name="sink_subrogation_row",
        keys={
            "account_pubkey",
            "epoch",
            "claimant",
            "sink_draw_quote",
            "subrogated_claim_quote",
        },
    )
    return SinkSubrogationPolicyRow(
        account_pubkey=_require_account(data["account_pubkey"], name="account_pubkey"),
        epoch=_require_non_negative_int(data["epoch"], name="epoch"),
        claimant=_require_account(data["claimant"], name="claimant"),
        sink_draw_quote=_require_non_negative_int(
            data["sink_draw_quote"],
            name="sink_draw_quote",
        ),
        subrogated_claim_quote=_require_non_negative_int(
            data["subrogated_claim_quote"],
            name="subrogated_claim_quote",
        ),
    )
