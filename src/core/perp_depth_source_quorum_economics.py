from __future__ import annotations

import hashlib
import re
from collections.abc import Mapping, Sequence
from dataclasses import dataclass

from ..state.canonical import canonical_json_bytes

DEPTH_SOURCE_QUORUM_ECONOMICS_SCHEMA = (
    "zenodex.perp.depth_source_quorum_economics.v1"
)
BPS_SCALE = 10_000
MAX_AMOUNT_QUOTE = 10**30
MAX_BPS = 1_000_000
MAX_SOURCES = 64
MAX_QUORUM_WEIGHT = 10_000
TOKEN_RE = re.compile(r"^[a-z][a-z0-9_.:-]{0,127}$")
SHA256_RE = re.compile(r"^sha256:[0-9a-f]{64}$")

_ENVELOPE_KEYS = frozenset(
    {
        "arbitrage_absorb_bps",
        "canonical_sha256",
        "defect_gain_bps",
        "deterrence_margin_bps",
        "market_id",
        "policy_hash",
        "quorum_threshold_weight",
        "reported_depth_quote",
        "schema",
        "source_rows",
        "true_depth_quote",
        "valid_from_epoch",
        "valid_until_epoch",
    }
)
_SOURCE_ROW_KEYS = frozenset(
    {
        "bond_quote",
        "future_value_lost_quote",
        "slash_fraction_bps",
        "source_id",
        "weight",
    }
)


@dataclass(frozen=True)
class DepthSourceEconomicsRow:
    source_id: str
    weight: int
    bond_quote: int
    slash_fraction_bps: int
    future_value_lost_quote: int

    def __post_init__(self) -> None:
        _require_token(self.source_id, name="source_id")
        _require_int_between(
            self.weight,
            name="weight",
            minimum=1,
            maximum=MAX_QUORUM_WEIGHT,
        )
        _require_int_between(
            self.bond_quote,
            name="bond_quote",
            minimum=0,
            maximum=MAX_AMOUNT_QUOTE,
        )
        _require_int_between(
            self.slash_fraction_bps,
            name="slash_fraction_bps",
            minimum=0,
            maximum=BPS_SCALE,
        )
        _require_int_between(
            self.future_value_lost_quote,
            name="future_value_lost_quote",
            minimum=0,
            maximum=MAX_AMOUNT_QUOTE,
        )

    @property
    def slashable_quote(self) -> int:
        return (
            self.bond_quote * self.slash_fraction_bps
        ) // BPS_SCALE + self.future_value_lost_quote

    def to_payload(self) -> dict[str, object]:
        return {
            "bond_quote": int(self.bond_quote),
            "future_value_lost_quote": int(self.future_value_lost_quote),
            "slash_fraction_bps": int(self.slash_fraction_bps),
            "source_id": self.source_id,
            "weight": int(self.weight),
        }


@dataclass(frozen=True)
class DepthSourceQuorumEconomicsEnvelope:
    schema: str
    market_id: str
    valid_from_epoch: int
    valid_until_epoch: int
    policy_hash: str
    source_rows: tuple[DepthSourceEconomicsRow, ...]
    quorum_threshold_weight: int
    true_depth_quote: int
    reported_depth_quote: int
    arbitrage_absorb_bps: int
    defect_gain_bps: int
    deterrence_margin_bps: int
    canonical_sha256: str

    def __post_init__(self) -> None:
        if self.schema != DEPTH_SOURCE_QUORUM_ECONOMICS_SCHEMA:
            raise ValueError("invalid depth source quorum economics schema")
        _require_token(self.market_id, name="market_id")
        _require_int_between(
            self.valid_from_epoch,
            name="valid_from_epoch",
            minimum=0,
            maximum=MAX_AMOUNT_QUOTE,
        )
        _require_int_between(
            self.valid_until_epoch,
            name="valid_until_epoch",
            minimum=0,
            maximum=MAX_AMOUNT_QUOTE,
        )
        if self.valid_from_epoch > self.valid_until_epoch:
            raise ValueError("valid_from_epoch must be <= valid_until_epoch")
        _require_sha256(self.policy_hash, name="policy_hash")
        _require_source_rows(self.source_rows)
        _require_int_between(
            self.quorum_threshold_weight,
            name="quorum_threshold_weight",
            minimum=1,
            maximum=MAX_QUORUM_WEIGHT,
        )
        if total_source_weight(self.source_rows) < self.quorum_threshold_weight:
            raise ValueError("quorum_threshold_weight exceeds total source weight")
        _require_int_between(
            self.true_depth_quote,
            name="true_depth_quote",
            minimum=0,
            maximum=MAX_AMOUNT_QUOTE,
        )
        _require_int_between(
            self.reported_depth_quote,
            name="reported_depth_quote",
            minimum=0,
            maximum=MAX_AMOUNT_QUOTE,
        )
        _require_int_between(
            self.arbitrage_absorb_bps,
            name="arbitrage_absorb_bps",
            minimum=0,
            maximum=BPS_SCALE,
        )
        _require_int_between(
            self.defect_gain_bps,
            name="defect_gain_bps",
            minimum=0,
            maximum=MAX_BPS,
        )
        _require_int_between(
            self.deterrence_margin_bps,
            name="deterrence_margin_bps",
            minimum=0,
            maximum=MAX_BPS,
        )
        _require_sha256(self.canonical_sha256, name="canonical_sha256")
        if self.canonical_sha256 != depth_source_quorum_economics_hash(self):
            raise ValueError("canonical_sha256 mismatch")

    def unsigned_payload(self) -> dict[str, object]:
        return {
            "arbitrage_absorb_bps": int(self.arbitrage_absorb_bps),
            "defect_gain_bps": int(self.defect_gain_bps),
            "deterrence_margin_bps": int(self.deterrence_margin_bps),
            "market_id": self.market_id,
            "policy_hash": self.policy_hash,
            "quorum_threshold_weight": int(self.quorum_threshold_weight),
            "reported_depth_quote": int(self.reported_depth_quote),
            "schema": self.schema,
            "source_rows": [row.to_payload() for row in self.source_rows],
            "true_depth_quote": int(self.true_depth_quote),
            "valid_from_epoch": int(self.valid_from_epoch),
            "valid_until_epoch": int(self.valid_until_epoch),
        }

    def to_payload(self) -> dict[str, object]:
        payload = self.unsigned_payload()
        payload["canonical_sha256"] = self.canonical_sha256
        return payload


@dataclass(frozen=True)
class DepthSourceQuorumEconomicsVerdict:
    ok: bool
    error: str | None = None
    envelope: DepthSourceQuorumEconomicsEnvelope | None = None
    admitted_cap_overstatement_quote: int | None = None
    attack_gain_quote: int | None = None
    required_downside_quote: int | None = None
    min_quorum_downside_quote: int | None = None

    def __post_init__(self) -> None:
        if not isinstance(self.ok, bool):
            raise TypeError("ok must be a bool")
        if self.error is not None and not isinstance(self.error, str):
            raise TypeError("error must be None or str")
        if self.envelope is not None and not isinstance(
            self.envelope,
            DepthSourceQuorumEconomicsEnvelope,
        ):
            raise TypeError(
                "envelope must be a DepthSourceQuorumEconomicsEnvelope or None"
            )


def build_depth_source_quorum_economics_envelope(
    *,
    market_id: str,
    valid_from_epoch: int,
    valid_until_epoch: int,
    policy_hash: str,
    source_rows: tuple[DepthSourceEconomicsRow, ...],
    quorum_threshold_weight: int,
    true_depth_quote: int,
    reported_depth_quote: int,
    arbitrage_absorb_bps: int,
    defect_gain_bps: int,
    deterrence_margin_bps: int,
) -> DepthSourceQuorumEconomicsEnvelope:
    unsigned = {
        "arbitrage_absorb_bps": _require_int_between(
            arbitrage_absorb_bps,
            name="arbitrage_absorb_bps",
            minimum=0,
            maximum=BPS_SCALE,
        ),
        "defect_gain_bps": _require_int_between(
            defect_gain_bps,
            name="defect_gain_bps",
            minimum=0,
            maximum=MAX_BPS,
        ),
        "deterrence_margin_bps": _require_int_between(
            deterrence_margin_bps,
            name="deterrence_margin_bps",
            minimum=0,
            maximum=MAX_BPS,
        ),
        "market_id": _require_token(market_id, name="market_id"),
        "policy_hash": _require_sha256(policy_hash, name="policy_hash"),
        "quorum_threshold_weight": _require_int_between(
            quorum_threshold_weight,
            name="quorum_threshold_weight",
            minimum=1,
            maximum=MAX_QUORUM_WEIGHT,
        ),
        "reported_depth_quote": _require_int_between(
            reported_depth_quote,
            name="reported_depth_quote",
            minimum=0,
            maximum=MAX_AMOUNT_QUOTE,
        ),
        "schema": DEPTH_SOURCE_QUORUM_ECONOMICS_SCHEMA,
        "source_rows": [
            row.to_payload() for row in _require_source_rows(source_rows)
        ],
        "true_depth_quote": _require_int_between(
            true_depth_quote,
            name="true_depth_quote",
            minimum=0,
            maximum=MAX_AMOUNT_QUOTE,
        ),
        "valid_from_epoch": _require_int_between(
            valid_from_epoch,
            name="valid_from_epoch",
            minimum=0,
            maximum=MAX_AMOUNT_QUOTE,
        ),
        "valid_until_epoch": _require_int_between(
            valid_until_epoch,
            name="valid_until_epoch",
            minimum=0,
            maximum=MAX_AMOUNT_QUOTE,
        ),
    }
    if int(unsigned["valid_from_epoch"]) > int(unsigned["valid_until_epoch"]):
        raise ValueError("valid_from_epoch must be <= valid_until_epoch")
    if total_source_weight(source_rows) < int(unsigned["quorum_threshold_weight"]):
        raise ValueError("quorum_threshold_weight exceeds total source weight")
    return DepthSourceQuorumEconomicsEnvelope(
        schema=DEPTH_SOURCE_QUORUM_ECONOMICS_SCHEMA,
        market_id=str(unsigned["market_id"]),
        valid_from_epoch=int(unsigned["valid_from_epoch"]),
        valid_until_epoch=int(unsigned["valid_until_epoch"]),
        policy_hash=str(unsigned["policy_hash"]),
        source_rows=source_rows,
        quorum_threshold_weight=int(unsigned["quorum_threshold_weight"]),
        true_depth_quote=int(unsigned["true_depth_quote"]),
        reported_depth_quote=int(unsigned["reported_depth_quote"]),
        arbitrage_absorb_bps=int(unsigned["arbitrage_absorb_bps"]),
        defect_gain_bps=int(unsigned["defect_gain_bps"]),
        deterrence_margin_bps=int(unsigned["deterrence_margin_bps"]),
        canonical_sha256=_sha256_payload(unsigned),
    )


def depth_source_quorum_economics_hash(
    envelope: DepthSourceQuorumEconomicsEnvelope,
) -> str:
    return _sha256_payload(envelope.unsigned_payload())


def depth_source_quorum_economics_payload(
    envelope: DepthSourceQuorumEconomicsEnvelope,
) -> dict[str, object]:
    if not isinstance(envelope, DepthSourceQuorumEconomicsEnvelope):
        raise TypeError("envelope must be a DepthSourceQuorumEconomicsEnvelope")
    return envelope.to_payload()


def depth_source_quorum_economics_payload_from_fields(
    *,
    market_id: str,
    valid_from_epoch: int,
    valid_until_epoch: int,
    policy_hash: str,
    source_rows: tuple[DepthSourceEconomicsRow, ...],
    quorum_threshold_weight: int,
    true_depth_quote: int,
    reported_depth_quote: int,
    arbitrage_absorb_bps: int,
    defect_gain_bps: int,
    deterrence_margin_bps: int,
) -> dict[str, object]:
    return depth_source_quorum_economics_payload(
        build_depth_source_quorum_economics_envelope(
            market_id=market_id,
            valid_from_epoch=valid_from_epoch,
            valid_until_epoch=valid_until_epoch,
            policy_hash=policy_hash,
            source_rows=source_rows,
            quorum_threshold_weight=quorum_threshold_weight,
            true_depth_quote=true_depth_quote,
            reported_depth_quote=reported_depth_quote,
            arbitrage_absorb_bps=arbitrage_absorb_bps,
            defect_gain_bps=defect_gain_bps,
            deterrence_margin_bps=deterrence_margin_bps,
        )
    )


def verify_depth_source_quorum_economics_payload(
    payload: object,
    *,
    expected_market_id: str,
    now_epoch: int,
    expected_policy_hash: str,
    expected_reported_depth_quote: int | None = None,
    expected_arbitrage_absorb_bps: int | None = None,
    expected_source_ids: Sequence[str] | None = None,
) -> DepthSourceQuorumEconomicsVerdict:
    if not isinstance(payload, Mapping):
        return DepthSourceQuorumEconomicsVerdict(
            False,
            "depth source quorum economics envelope must be an object",
        )
    try:
        envelope = _payload_to_envelope(payload)
        market_id = _require_token(expected_market_id, name="expected_market_id")
        epoch = _require_int_between(
            now_epoch,
            name="now_epoch",
            minimum=0,
            maximum=MAX_AMOUNT_QUOTE,
        )
        policy_hash = _require_sha256(
            expected_policy_hash,
            name="expected_policy_hash",
        )
        if envelope.market_id != market_id:
            return DepthSourceQuorumEconomicsVerdict(False, "market_id mismatch")
        if epoch < envelope.valid_from_epoch or epoch > envelope.valid_until_epoch:
            return DepthSourceQuorumEconomicsVerdict(False, "epoch out of range")
        if envelope.policy_hash != policy_hash:
            return DepthSourceQuorumEconomicsVerdict(False, "policy_hash mismatch")
        if expected_reported_depth_quote is not None:
            reported_depth = _require_int_between(
                expected_reported_depth_quote,
                name="expected_reported_depth_quote",
                minimum=0,
                maximum=MAX_AMOUNT_QUOTE,
            )
            if envelope.reported_depth_quote != reported_depth:
                return DepthSourceQuorumEconomicsVerdict(
                    False,
                    "reported_depth_quote mismatch",
                )
        if expected_arbitrage_absorb_bps is not None:
            absorb = _require_int_between(
                expected_arbitrage_absorb_bps,
                name="expected_arbitrage_absorb_bps",
                minimum=0,
                maximum=BPS_SCALE,
            )
            if envelope.arbitrage_absorb_bps != absorb:
                return DepthSourceQuorumEconomicsVerdict(
                    False,
                    "arbitrage_absorb_bps mismatch",
                )
        if expected_source_ids is not None:
            source_ids = _require_source_id_sequence(expected_source_ids)
            if tuple(row.source_id for row in envelope.source_rows) != source_ids:
                return DepthSourceQuorumEconomicsVerdict(
                    False,
                    "source_rows source_id mismatch",
                )

        cap_overstatement = admitted_cap_overstatement_quote(
            true_depth_quote=envelope.true_depth_quote,
            reported_depth_quote=envelope.reported_depth_quote,
            arbitrage_absorb_bps=envelope.arbitrage_absorb_bps,
        )
        attack_gain = ceil_div(cap_overstatement * envelope.defect_gain_bps, BPS_SCALE)
        required_downside = ceil_div(
            attack_gain * (BPS_SCALE + envelope.deterrence_margin_bps),
            BPS_SCALE,
        )
        min_downside = min_quorum_downside_quote(
            envelope.source_rows,
            envelope.quorum_threshold_weight,
        )
        if min_downside < required_downside:
            return DepthSourceQuorumEconomicsVerdict(
                False,
                "quorum_downside_below_required",
                envelope,
                cap_overstatement,
                attack_gain,
                required_downside,
                min_downside,
            )
    except (TypeError, ValueError) as exc:
        return DepthSourceQuorumEconomicsVerdict(False, str(exc))
    return DepthSourceQuorumEconomicsVerdict(
        True,
        None,
        envelope,
        cap_overstatement,
        attack_gain,
        required_downside,
        min_downside,
    )


def admitted_cap_overstatement_quote(
    *,
    true_depth_quote: int,
    reported_depth_quote: int,
    arbitrage_absorb_bps: int,
) -> int:
    true_depth = _require_int_between(
        true_depth_quote,
        name="true_depth_quote",
        minimum=0,
        maximum=MAX_AMOUNT_QUOTE,
    )
    reported_depth = _require_int_between(
        reported_depth_quote,
        name="reported_depth_quote",
        minimum=0,
        maximum=MAX_AMOUNT_QUOTE,
    )
    absorb = _require_int_between(
        arbitrage_absorb_bps,
        name="arbitrage_absorb_bps",
        minimum=0,
        maximum=BPS_SCALE,
    )
    true_cap = (true_depth * absorb) // BPS_SCALE
    reported_cap = (reported_depth * absorb) // BPS_SCALE
    return max(0, reported_cap - true_cap)


def min_quorum_downside_quote(
    source_rows: tuple[DepthSourceEconomicsRow, ...],
    quorum_threshold_weight: int,
) -> int:
    rows = _require_source_rows(source_rows)
    threshold = _require_int_between(
        quorum_threshold_weight,
        name="quorum_threshold_weight",
        minimum=1,
        maximum=MAX_QUORUM_WEIGHT,
    )
    if total_source_weight(rows) < threshold:
        raise ValueError("quorum_threshold_weight exceeds total source weight")

    best_by_weight: dict[int, int] = {0: 0}
    for row in rows:
        next_best = dict(best_by_weight)
        for weight, downside in best_by_weight.items():
            capped_weight = min(threshold, weight + row.weight)
            candidate_downside = downside + row.slashable_quote
            previous = next_best.get(capped_weight)
            if previous is None or candidate_downside < previous:
                next_best[capped_weight] = candidate_downside
        best_by_weight = next_best
    return best_by_weight[threshold]


def total_source_weight(source_rows: tuple[DepthSourceEconomicsRow, ...]) -> int:
    return sum(row.weight for row in _require_source_rows(source_rows))


def ceil_div(numer: int, denom: int) -> int:
    if not isinstance(numer, int) or isinstance(numer, bool):
        raise TypeError("numer must be an int")
    if not isinstance(denom, int) or isinstance(denom, bool):
        raise TypeError("denom must be an int")
    if numer < 0:
        raise ValueError("numer must be non-negative")
    if denom <= 0:
        raise ValueError("denom must be positive")
    return (numer + denom - 1) // denom


def _payload_to_envelope(
    payload: Mapping[str, object],
) -> DepthSourceQuorumEconomicsEnvelope:
    if set(payload.keys()) != _ENVELOPE_KEYS:
        missing = sorted(_ENVELOPE_KEYS - set(payload.keys()))
        extra = sorted(set(payload.keys()) - _ENVELOPE_KEYS)
        if missing:
            raise ValueError(f"missing depth source quorum economics field: {missing[0]}")
        raise ValueError(f"unknown depth source quorum economics field: {extra[0]}")

    rows_raw = payload["source_rows"]
    if not isinstance(rows_raw, list):
        raise TypeError("source_rows must be a list")
    rows = tuple(_payload_to_source_row(row) for row in rows_raw)
    return DepthSourceQuorumEconomicsEnvelope(
        schema=_require_string(payload["schema"], name="schema"),
        market_id=_require_token(payload["market_id"], name="market_id"),
        valid_from_epoch=_require_int_between(
            payload["valid_from_epoch"],
            name="valid_from_epoch",
            minimum=0,
            maximum=MAX_AMOUNT_QUOTE,
        ),
        valid_until_epoch=_require_int_between(
            payload["valid_until_epoch"],
            name="valid_until_epoch",
            minimum=0,
            maximum=MAX_AMOUNT_QUOTE,
        ),
        policy_hash=_require_sha256(payload["policy_hash"], name="policy_hash"),
        source_rows=rows,
        quorum_threshold_weight=_require_int_between(
            payload["quorum_threshold_weight"],
            name="quorum_threshold_weight",
            minimum=1,
            maximum=MAX_QUORUM_WEIGHT,
        ),
        true_depth_quote=_require_int_between(
            payload["true_depth_quote"],
            name="true_depth_quote",
            minimum=0,
            maximum=MAX_AMOUNT_QUOTE,
        ),
        reported_depth_quote=_require_int_between(
            payload["reported_depth_quote"],
            name="reported_depth_quote",
            minimum=0,
            maximum=MAX_AMOUNT_QUOTE,
        ),
        arbitrage_absorb_bps=_require_int_between(
            payload["arbitrage_absorb_bps"],
            name="arbitrage_absorb_bps",
            minimum=0,
            maximum=BPS_SCALE,
        ),
        defect_gain_bps=_require_int_between(
            payload["defect_gain_bps"],
            name="defect_gain_bps",
            minimum=0,
            maximum=MAX_BPS,
        ),
        deterrence_margin_bps=_require_int_between(
            payload["deterrence_margin_bps"],
            name="deterrence_margin_bps",
            minimum=0,
            maximum=MAX_BPS,
        ),
        canonical_sha256=_require_sha256(
            payload["canonical_sha256"],
            name="canonical_sha256",
        ),
    )


def _payload_to_source_row(payload: object) -> DepthSourceEconomicsRow:
    if not isinstance(payload, Mapping):
        raise TypeError("source row must be an object")
    if set(payload.keys()) != _SOURCE_ROW_KEYS:
        missing = sorted(_SOURCE_ROW_KEYS - set(payload.keys()))
        extra = sorted(set(payload.keys()) - _SOURCE_ROW_KEYS)
        if missing:
            raise ValueError(f"missing source row field: {missing[0]}")
        raise ValueError(f"unknown source row field: {extra[0]}")
    return DepthSourceEconomicsRow(
        source_id=_require_token(payload["source_id"], name="source_id"),
        weight=_require_int_between(
            payload["weight"],
            name="weight",
            minimum=1,
            maximum=MAX_QUORUM_WEIGHT,
        ),
        bond_quote=_require_int_between(
            payload["bond_quote"],
            name="bond_quote",
            minimum=0,
            maximum=MAX_AMOUNT_QUOTE,
        ),
        slash_fraction_bps=_require_int_between(
            payload["slash_fraction_bps"],
            name="slash_fraction_bps",
            minimum=0,
            maximum=BPS_SCALE,
        ),
        future_value_lost_quote=_require_int_between(
            payload["future_value_lost_quote"],
            name="future_value_lost_quote",
            minimum=0,
            maximum=MAX_AMOUNT_QUOTE,
        ),
    )


def _require_source_rows(
    rows: tuple[DepthSourceEconomicsRow, ...],
) -> tuple[DepthSourceEconomicsRow, ...]:
    if not isinstance(rows, tuple):
        raise TypeError("source_rows must be a tuple")
    if not rows:
        raise ValueError("source_rows must be non-empty")
    if len(rows) > MAX_SOURCES:
        raise ValueError(f"source_rows length must be <= {MAX_SOURCES}")
    for row in rows:
        if not isinstance(row, DepthSourceEconomicsRow):
            raise TypeError("source_rows entries must be DepthSourceEconomicsRow")
    source_ids = tuple(row.source_id for row in rows)
    if list(source_ids) != sorted(source_ids):
        raise ValueError("source_rows must be sorted by source_id")
    if len(source_ids) != len(set(source_ids)):
        raise ValueError("source_rows source_id values must be unique")
    return rows


def _require_source_id_sequence(
    source_ids: Sequence[str],
) -> tuple[str, ...]:
    if isinstance(source_ids, (str, bytes)):
        raise TypeError("expected_source_ids must be a non-string sequence")
    if not isinstance(source_ids, Sequence):
        raise TypeError("expected_source_ids must be a sequence")
    out = tuple(
        _require_token(source_id, name="expected_source_ids entry")
        for source_id in source_ids
    )
    if not out:
        raise ValueError("expected_source_ids must be non-empty")
    if list(out) != sorted(out):
        raise ValueError("expected_source_ids must be sorted")
    if len(out) != len(set(out)):
        raise ValueError("expected_source_ids values must be unique")
    return out


def _require_token(value: object, *, name: str) -> str:
    out = _require_string(value, name=name)
    if not TOKEN_RE.match(out):
        raise ValueError(f"{name} must be a token")
    return out


def _require_sha256(value: object, *, name: str) -> str:
    out = _require_string(value, name=name)
    if not SHA256_RE.match(out):
        raise ValueError(f"{name} must be sha256:<64 lowercase hex chars>")
    return out


def _require_string(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a str")
    if not value:
        raise ValueError(f"{name} must be non-empty")
    if "\x00" in value:
        raise ValueError(f"{name} must not contain NUL")
    return value


def _require_int_between(
    value: object,
    *,
    name: str,
    minimum: int,
    maximum: int,
) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    if value < minimum or value > maximum:
        raise ValueError(f"{name} must be between {minimum} and {maximum}")
    return int(value)


def _sha256_payload(payload: object) -> str:
    return "sha256:" + hashlib.sha256(canonical_json_bytes(payload)).hexdigest()
