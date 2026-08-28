"""Canonical aggregate market replacement for exact committed perps state.

Isolated and clearinghouse kernels produce exact market candidates. This leaf
binds one such candidate back into its exact ``CommittedPerpsStateV1`` parent
through a compare-and-replace patch. It emits no effects, receipt, nonce,
outbox record, or mutable compatibility projection.

The operation remains pre-M5 infrastructure. It does not mount exact perps
state into ``DexState`` or authorize shell publication.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import TypeAlias, cast, final

# The inherited ``src.core`` package facade imports state consumers eagerly.
# Loading one core leaf before the snapshot-value module prevents a fresh-process
# import from entering that facade through a partially initialized state module.
from ..core.perps import PERPS_STATE_VERSION_V4, PERPS_STATE_VERSION_V5
from .state_snapshot_values import (
    MAX_STATE_STRING_CHARACTERS_V1,
    MAX_STATE_STRING_UTF8_BYTES_V1,
    CommittedPerpAnyMarketStateV1,
    CommittedPerpClearinghouse2pMarketStateV1,
    CommittedPerpClearinghouse3pTransferMarketStateV1,
    CommittedPerpClearinghouseNpMarketStateV1,
    CommittedPerpMarketStateV1,
    CommittedPerpsStateV1,
)
from .state_transitions import _committed_perps_with_markets_from_transition_v1

FCIS_MUTABLE_LOCAL_BUFFERS_FORBIDDEN = True

PerpsAggregatePathPartV1: TypeAlias = str | int
PerpsAggregatePathV1: TypeAlias = tuple[PerpsAggregatePathPartV1, ...]
_SUPPORTED_MARKET_TYPES_V1 = (
    CommittedPerpMarketStateV1,
    CommittedPerpClearinghouse2pMarketStateV1,
    CommittedPerpClearinghouse3pTransferMarketStateV1,
    CommittedPerpClearinghouseNpMarketStateV1,
)


class PerpsAggregateTransitionCodeV1(Enum):
    """Stable rejection codes for the exact aggregate market-map leaf."""

    WRONG_EXACT_TYPE = "wrong_exact_type"
    NONCANONICAL_MARKET_ID = "noncanonical_market_id"
    INVALID_PRESTATE = "invalid_prestate"
    INVALID_MARKET = "invalid_market"
    INVALID_PATCH = "invalid_patch"
    MARKET_NOT_FOUND = "market_not_found"
    MARKET_VARIANT_MISMATCH = "market_variant_mismatch"
    NO_OP_WRITE = "no_op_write"
    EXPECTED_OLD_MISMATCH = "expected_old_mismatch"
    INVALID_CANDIDATE = "invalid_candidate"


@final
@dataclass(frozen=True, slots=True)
class PerpsAggregateTransitionRejectV1:
    """Typed no-output rejection for aggregate perps replacement."""

    code: PerpsAggregateTransitionCodeV1
    path: PerpsAggregatePathV1

    def __post_init__(self) -> None:
        if type(self.code) is not PerpsAggregateTransitionCodeV1:
            raise TypeError("perps aggregate rejection code must be exact")
        if type(self.path) is not tuple or any(
            type(part) is not str and type(part) is not int for part in self.path
        ):
            raise TypeError("perps aggregate rejection path must be exact")


def _reject(
    code: PerpsAggregateTransitionCodeV1,
    path: PerpsAggregatePathV1,
) -> PerpsAggregateTransitionRejectV1:
    return PerpsAggregateTransitionRejectV1(code, path)


def _market_id_reject(
    market_id: object,
    path: PerpsAggregatePathV1,
) -> PerpsAggregateTransitionRejectV1 | None:
    if type(market_id) is not str:
        return _reject(PerpsAggregateTransitionCodeV1.WRONG_EXACT_TYPE, path)
    if not market_id:
        return _reject(PerpsAggregateTransitionCodeV1.NONCANONICAL_MARKET_ID, path)
    if len(market_id) > MAX_STATE_STRING_CHARACTERS_V1:
        return _reject(PerpsAggregateTransitionCodeV1.NONCANONICAL_MARKET_ID, path)
    try:
        encoded = market_id.encode("utf-8")
    except UnicodeEncodeError:
        return _reject(PerpsAggregateTransitionCodeV1.NONCANONICAL_MARKET_ID, path)
    if len(encoded) > MAX_STATE_STRING_UTF8_BYTES_V1:
        return _reject(PerpsAggregateTransitionCodeV1.NONCANONICAL_MARKET_ID, path)
    return None


def _market_reject(
    market: object,
    path: PerpsAggregatePathV1,
) -> PerpsAggregateTransitionRejectV1 | None:
    if type(market) not in _SUPPORTED_MARKET_TYPES_V1:
        return _reject(PerpsAggregateTransitionCodeV1.WRONG_EXACT_TYPE, path)
    return None


def _validated_prestate(
    pre: object,
) -> CommittedPerpsStateV1 | PerpsAggregateTransitionRejectV1:
    if type(pre) is not CommittedPerpsStateV1:
        return _reject(PerpsAggregateTransitionCodeV1.WRONG_EXACT_TYPE, ("state",))
    from .state_snapshots import StateAdmissionError, snapshot_perps

    try:
        admitted = snapshot_perps(cast(CommittedPerpsStateV1, pre))
    except StateAdmissionError as exc:
        return _reject(
            PerpsAggregateTransitionCodeV1.INVALID_PRESTATE,
            ("state",) + exc.path,
        )
    if type(admitted) is not CommittedPerpsStateV1:  # pragma: no cover
        raise RuntimeError("closed perps admission returned an impossible result")
    exact_admitted = cast(CommittedPerpsStateV1, admitted)
    if exact_admitted.version not in (PERPS_STATE_VERSION_V4, PERPS_STATE_VERSION_V5):
        raise RuntimeError("closed perps admission returned an unsupported version")
    return exact_admitted


@final
@dataclass(frozen=True, slots=True)
class _MarketAdmissionRejectV1:
    path: PerpsAggregatePathV1


def _validated_market(
    pre: CommittedPerpsStateV1,
    market_id: str,
    market: object,
) -> CommittedPerpAnyMarketStateV1 | _MarketAdmissionRejectV1:
    """Re-admit one exact market through the sole closed perps schema."""

    from .state_snapshots import StateAdmissionError, snapshot_perps

    try:
        provisional = _committed_perps_with_markets_from_transition_v1(
            pre,
            ((market_id, cast(CommittedPerpAnyMarketStateV1, market)),),
        )
        admitted = snapshot_perps(provisional)
    except StateAdmissionError as exc:
        return _MarketAdmissionRejectV1(exc.path)
    except (AttributeError, KeyError, TypeError, ValueError):
        return _MarketAdmissionRejectV1(())
    if type(admitted) is not CommittedPerpsStateV1:  # pragma: no cover
        raise RuntimeError("closed perps admission returned an impossible result")
    normalized = admitted.get_market(market_id)
    if normalized is None:  # pragma: no cover
        raise RuntimeError("closed perps admission omitted its sole market")
    return normalized


def _validated_replacement_market(
    pre: CommittedPerpsStateV1,
    market_id: str,
    market: object,
    path: PerpsAggregatePathV1,
) -> CommittedPerpAnyMarketStateV1 | PerpsAggregateTransitionRejectV1:
    representation_reject = _market_reject(market, path)
    if representation_reject is not None:
        return representation_reject
    admitted = _validated_market(pre, market_id, market)
    if type(admitted) is _MarketAdmissionRejectV1:
        return _reject(
            PerpsAggregateTransitionCodeV1.INVALID_MARKET,
            path + admitted.path,
        )
    return admitted


def _validated_patch_market(
    pre: CommittedPerpsStateV1,
    market_id: str,
    market: object,
    path: PerpsAggregatePathV1,
) -> CommittedPerpAnyMarketStateV1 | PerpsAggregateTransitionRejectV1:
    representation_reject = _market_reject(market, path)
    if representation_reject is not None:
        return _reject(PerpsAggregateTransitionCodeV1.INVALID_PATCH, path)
    admitted = _validated_market(pre, market_id, market)
    if type(admitted) is _MarketAdmissionRejectV1:
        return _reject(
            PerpsAggregateTransitionCodeV1.INVALID_PATCH,
            path + admitted.path,
        )
    return admitted


def _write_reject(
    write: object,
    path: PerpsAggregatePathV1,
) -> PerpsAggregateTransitionRejectV1 | None:
    if type(write) is not PerpsMarketWriteV1:
        return _reject(PerpsAggregateTransitionCodeV1.WRONG_EXACT_TYPE, path)
    exact = write
    market_id_reject = _market_id_reject(exact.market_id, path + ("market_id",))
    if market_id_reject is not None:
        return market_id_reject
    expected_reject = _market_reject(exact.expected, path + ("expected",))
    if expected_reject is not None:
        return expected_reject
    replacement_reject = _market_reject(exact.replacement, path + ("replacement",))
    if replacement_reject is not None:
        return replacement_reject
    if type(exact.expected) is not type(exact.replacement):
        return _reject(
            PerpsAggregateTransitionCodeV1.MARKET_VARIANT_MISMATCH,
            path + ("replacement",),
        )
    return None


@final
@dataclass(frozen=True, slots=True)
class PerpsMarketWriteV1:
    """One exact compare-and-replace operation for a committed market cell."""

    market_id: str
    expected: CommittedPerpAnyMarketStateV1
    replacement: CommittedPerpAnyMarketStateV1

    def __post_init__(self) -> None:
        reject = _write_reject(self, ("write",))
        if reject is None:
            return
        if reject.code is PerpsAggregateTransitionCodeV1.WRONG_EXACT_TYPE:
            raise TypeError("perps market write requires exact values")
        raise ValueError(f"perps market write rejected: {reject.code.value}")


@final
@dataclass(frozen=True, slots=True)
class CanonicalPerpsMarketPatchV1:
    """A single canonical compare-and-replace market patch."""

    writes: tuple[PerpsMarketWriteV1, ...]

    def __post_init__(self) -> None:
        if type(self.writes) is not tuple:
            raise TypeError("perps market patch writes must be an exact tuple")
        if len(self.writes) != 1:
            raise ValueError("perps market patch must contain exactly one write")
        reject = _write_reject(self.writes[0], ("writes", 0))
        if reject is not None:
            raise ValueError(f"perps market patch rejected: {reject.code.value}")


@final
@dataclass(frozen=True, slots=True)
class PerpsAggregateTransitionOkV1:
    """One complete exact aggregate candidate and its replayable patch."""

    state: CommittedPerpsStateV1
    patch: CanonicalPerpsMarketPatchV1

    def __post_init__(self) -> None:
        if type(self.state) is not CommittedPerpsStateV1:
            raise TypeError("perps aggregate candidate state must be exact")
        if type(self.patch) is not CanonicalPerpsMarketPatchV1:
            raise TypeError("perps aggregate candidate patch must be exact")
        self.state.__post_init__()
        self.patch.__post_init__()
        write = self.patch.writes[0]
        committed = tuple(
            market
            for market_id, market in self.state.market_entries
            if market_id == write.market_id
        )
        if len(committed) != 1 or committed[0] is not write.replacement:
            raise ValueError("perps aggregate patch does not bind the returned candidate")


PerpsAggregateTransitionResultV1: TypeAlias = (
    PerpsAggregateTransitionOkV1 | PerpsAggregateTransitionRejectV1
)
PerpsMarketPatchBuildResultV1: TypeAlias = (
    CanonicalPerpsMarketPatchV1 | PerpsAggregateTransitionRejectV1
)


@final
@dataclass(frozen=True, slots=True)
class _ValidatedPerpsMarketWriteV1:
    market_id: str
    current: CommittedPerpAnyMarketStateV1
    replacement: CommittedPerpAnyMarketStateV1


def build_canonical_perps_market_patch_v1(
    pre: object,
    *,
    market_id: object,
    replacement: object,
) -> PerpsMarketPatchBuildResultV1:
    """Build one bounded patch under fixed rejection precedence."""

    validated = _validated_prestate(pre)
    if type(validated) is PerpsAggregateTransitionRejectV1:
        return validated
    market_id_reject = _market_id_reject(market_id, ("market_id",))
    if market_id_reject is not None:
        return market_id_reject
    replacement_reject = _market_reject(replacement, ("replacement",))
    if replacement_reject is not None:
        return replacement_reject

    canonical_id = cast(str, market_id)
    current = validated.get_market(canonical_id)
    if current is None:
        return _reject(PerpsAggregateTransitionCodeV1.MARKET_NOT_FOUND, ("market_id",))
    if type(current) is not type(replacement):
        return _reject(
            PerpsAggregateTransitionCodeV1.MARKET_VARIANT_MISMATCH,
            ("replacement",),
        )
    normalized_replacement = _validated_replacement_market(
        validated,
        canonical_id,
        replacement,
        ("replacement",),
    )
    if type(normalized_replacement) is PerpsAggregateTransitionRejectV1:
        return normalized_replacement
    if current == normalized_replacement:
        return _reject(PerpsAggregateTransitionCodeV1.NO_OP_WRITE, ("replacement",))
    return CanonicalPerpsMarketPatchV1(
        (PerpsMarketWriteV1(canonical_id, current, normalized_replacement),)
    )


def _validated_patch_write(
    pre: CommittedPerpsStateV1,
    patch: object,
) -> _ValidatedPerpsMarketWriteV1 | PerpsAggregateTransitionRejectV1:
    if type(patch) is not CanonicalPerpsMarketPatchV1:
        return _reject(PerpsAggregateTransitionCodeV1.WRONG_EXACT_TYPE, ("patch",))
    exact_patch = patch
    try:
        exact_patch.__post_init__()
    except (AttributeError, KeyError, TypeError, ValueError):
        return _reject(PerpsAggregateTransitionCodeV1.INVALID_PATCH, ("patch",))

    write = exact_patch.writes[0]
    current = pre.get_market(write.market_id)
    if current is None:
        return _reject(
            PerpsAggregateTransitionCodeV1.MARKET_NOT_FOUND,
            ("writes", 0, "market_id"),
        )
    if type(current) is not type(write.expected):
        return _reject(
            PerpsAggregateTransitionCodeV1.EXPECTED_OLD_MISMATCH,
            ("writes", 0, "expected"),
        )
    normalized_expected = _validated_patch_market(
        pre,
        write.market_id,
        write.expected,
        ("patch", "writes", 0, "expected"),
    )
    if type(normalized_expected) is PerpsAggregateTransitionRejectV1:
        return normalized_expected
    normalized_replacement = _validated_patch_market(
        pre,
        write.market_id,
        write.replacement,
        ("patch", "writes", 0, "replacement"),
    )
    if type(normalized_replacement) is PerpsAggregateTransitionRejectV1:
        return normalized_replacement
    if type(normalized_expected) is not type(normalized_replacement):
        return _reject(
            PerpsAggregateTransitionCodeV1.MARKET_VARIANT_MISMATCH,
            ("patch", "writes", 0, "replacement"),
        )
    if current != normalized_expected:
        return _reject(
            PerpsAggregateTransitionCodeV1.EXPECTED_OLD_MISMATCH,
            ("writes", 0, "expected"),
        )
    if normalized_expected == normalized_replacement:
        return _reject(
            PerpsAggregateTransitionCodeV1.NO_OP_WRITE,
            ("patch", "writes", 0, "replacement"),
        )
    return _ValidatedPerpsMarketWriteV1(
        write.market_id,
        current,
        normalized_replacement,
    )


def _market_replacement_result(
    pre: CommittedPerpsStateV1,
    write: _ValidatedPerpsMarketWriteV1,
) -> PerpsAggregateTransitionResultV1:
    market_entries = tuple(
        (
            market_id,
            write.replacement if market_id == write.market_id else market,
        )
        for market_id, market in pre.market_entries
    )
    from .state_snapshots import StateAdmissionError, snapshot_perps

    try:
        provisional = _committed_perps_with_markets_from_transition_v1(
            pre,
            market_entries,
        )
        admitted_candidate = snapshot_perps(provisional)
    except StateAdmissionError:
        return _reject(PerpsAggregateTransitionCodeV1.INVALID_CANDIDATE, ("state",))
    except (AttributeError, KeyError, TypeError, ValueError):
        return _reject(PerpsAggregateTransitionCodeV1.INVALID_CANDIDATE, ("state",))
    if type(admitted_candidate) is not CommittedPerpsStateV1:  # pragma: no cover
        raise RuntimeError("closed perps admission returned an impossible result")
    committed_replacement = admitted_candidate.get_market(write.market_id)
    if committed_replacement is None:  # pragma: no cover
        raise RuntimeError("committed perps candidate omitted its replacement")
    committed_patch = CanonicalPerpsMarketPatchV1(
        (
            PerpsMarketWriteV1(
                write.market_id,
                write.current,
                committed_replacement,
            ),
        )
    )
    return PerpsAggregateTransitionOkV1(admitted_candidate, committed_patch)


def apply_canonical_perps_market_patch_v1(
    pre: object,
    patch: object,
) -> PerpsAggregateTransitionResultV1:
    """Apply one exact patch without publishing any partial aggregate."""

    validated = _validated_prestate(pre)
    if type(validated) is PerpsAggregateTransitionRejectV1:
        return validated
    write = _validated_patch_write(validated, patch)
    if type(write) is PerpsAggregateTransitionRejectV1:
        return write
    return _market_replacement_result(validated, write)


def replace_perps_market_v1(
    pre: object,
    *,
    market_id: object,
    replacement: object,
) -> PerpsAggregateTransitionResultV1:
    """Build and apply one exact market replacement against one immutable root."""

    patch = build_canonical_perps_market_patch_v1(
        pre,
        market_id=market_id,
        replacement=replacement,
    )
    if type(patch) is PerpsAggregateTransitionRejectV1:
        return patch
    return apply_canonical_perps_market_patch_v1(pre, patch)
