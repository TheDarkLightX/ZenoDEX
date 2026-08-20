"""Independent shadow checker for Global Economic Source History V2.

This module validates and canonicalizes the public statement consumed by the
Rust proof-admission boundary. It cannot construct the Rust opaque witness and
therefore carries no proof, settlement, publication, or production authority.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from enum import Enum
from types import MappingProxyType
from typing import Final, Mapping, cast

from tools.check_global_economic_delta_v2 import I128_MAX
from tools.global_economic_delta_v2_types import (
    _ID_RE,
    _ROOT_RE,
    _StructuralDeltaPlanDataV2,
)

SOURCE_HISTORY_SCHEMA_V2: Final = (
    "zenodex/global-economic-source-history-statement/v2"
)
SOURCE_HISTORY_ROOT_DOMAIN_V2: Final = (
    b"zenodex:global-economic-source-history-statement:v2\0"
)
MAX_SOURCE_HISTORY_INPUT_BYTES_V2: Final = 1_048_576
U32_MAX: Final = (1 << 32) - 1
U64_MAX: Final = (1 << 64) - 1

_TOP_FIELDS: Final = frozenset(
    {
        "schema",
        "chain_id",
        "deployment_root",
        "profile_root",
        "writer_epoch",
        "history_root",
        "history_height",
        "delta_plan_root",
        "verifier_release_id",
        "verifier_image_id",
        "source_availability_claims",
    }
)
_CLAIM_FIELDS: Final = frozenset(
    {
        "source_root",
        "source_kind",
        "asset",
        "amount_atoms",
        "source_height",
        "tx_index",
        "op_index",
        "finality_anchor_root",
        "finalized_height",
        "consumption_nullifier",
    }
)
_SOURCE_KINDS: Final = frozenset(
    {"external_effect", "ancestor_claim", "refundable_event"}
)


class SourceHistoryRejectCodeV2(str, Enum):
    DECODE_INVALID = "DECODE_INVALID"
    SCHEMA_MISMATCH = "SCHEMA_MISMATCH"
    INPUT_TOO_LARGE = "INPUT_TOO_LARGE"
    WRITER_EPOCH_INVALID = "WRITER_EPOCH_INVALID"
    SOURCE_COUNT_MISMATCH = "SOURCE_COUNT_MISMATCH"
    DUPLICATE_SOURCE_CLAIM = "DUPLICATE_SOURCE_CLAIM"
    NONCANONICAL_SOURCE_ORDER = "NONCANONICAL_SOURCE_ORDER"
    SOURCE_BINDING_MISMATCH = "SOURCE_BINDING_MISMATCH"
    DUPLICATE_OCCURRENCE = "DUPLICATE_OCCURRENCE"
    DUPLICATE_CONSUMPTION_NULLIFIER = "DUPLICATE_CONSUMPTION_NULLIFIER"
    ROOT_ROLE_CONFLICT = "ROOT_ROLE_CONFLICT"
    FINALITY_ORDER_INVALID = "FINALITY_ORDER_INVALID"
    DELTA_PLAN_ROOT_MISMATCH = "DELTA_PLAN_ROOT_MISMATCH"


class SourceHistoryValidationErrorV2(ValueError):
    """Typed no-statement rejection from the Python shadow checker."""

    def __init__(self, code: SourceHistoryRejectCodeV2, detail: str) -> None:
        super().__init__(f"{code.value}: {detail}")
        self.code = code


@dataclass(frozen=True, slots=True)
class _CheckedSourceHistoryStatementDataV2:
    source_availability_claims: tuple[Mapping[str, str | int], ...]
    delta_plan_root: str
    history_root: str
    history_height: int
    writer_epoch: int
    verifier_release_id: str
    verifier_image_id: str
    canonical_bytes: bytes
    root: str


def _reject(code: SourceHistoryRejectCodeV2, detail: str) -> None:
    raise SourceHistoryValidationErrorV2(code, detail)


def _exact_mapping(
    value: object,
    *,
    expected_fields: frozenset[str],
    label: str,
) -> dict[str, object]:
    if type(value) is not dict:
        _reject(SourceHistoryRejectCodeV2.DECODE_INVALID, f"{label} must be an object")
    owned = dict(cast(dict[object, object], value))
    if not all(type(key) is str for key in owned) or frozenset(owned) != expected_fields:
        _reject(SourceHistoryRejectCodeV2.DECODE_INVALID, f"{label} fields are not closed")
    return cast(dict[str, object], owned)


def _root(value: object, *, field: str) -> str:
    if (
        type(value) is not str
        or _ROOT_RE.fullmatch(value) is None
        or value == "sha256:" + "0" * 64
    ):
        _reject(SourceHistoryRejectCodeV2.DECODE_INVALID, f"{field} is not a root")
    return cast(str, value)


def _identifier(value: object, *, field: str) -> str:
    if type(value) is not str or _ID_RE.fullmatch(value) is None:
        _reject(SourceHistoryRejectCodeV2.DECODE_INVALID, f"{field} is not canonical")
    return cast(str, value)


def _integer(value: object, *, field: str, maximum: int) -> int:
    if type(value) is not int or value < 0 or value > maximum:
        _reject(SourceHistoryRejectCodeV2.DECODE_INVALID, f"{field} is out of range")
    return cast(int, value)


def _claim(value: object, *, history_height: int) -> dict[str, str | int]:
    claim = _exact_mapping(value, expected_fields=_CLAIM_FIELDS, label="source claim")
    source_kind = claim["source_kind"]
    if type(source_kind) is not str or source_kind not in _SOURCE_KINDS:
        _reject(SourceHistoryRejectCodeV2.DECODE_INVALID, "source kind is not closed")
    source_kind = cast(str, source_kind)
    amount_atoms = _integer(
        claim["amount_atoms"], field="amount_atoms", maximum=I128_MAX
    )
    if amount_atoms == 0:
        _reject(SourceHistoryRejectCodeV2.DECODE_INVALID, "amount_atoms must be positive")
    source_height = _integer(
        claim["source_height"], field="source_height", maximum=U64_MAX
    )
    finalized_height = _integer(
        claim["finalized_height"], field="finalized_height", maximum=U64_MAX
    )
    if source_height > finalized_height or finalized_height > history_height:
        _reject(
            SourceHistoryRejectCodeV2.FINALITY_ORDER_INVALID,
            "source, finality, and history heights are out of order",
        )
    result: dict[str, str | int] = {
        "amount_atoms": amount_atoms,
        "asset": _identifier(claim["asset"], field="asset"),
        "consumption_nullifier": _root(
            claim["consumption_nullifier"], field="consumption_nullifier"
        ),
        "finality_anchor_root": _root(
            claim["finality_anchor_root"], field="finality_anchor_root"
        ),
        "finalized_height": finalized_height,
        "op_index": _integer(claim["op_index"], field="op_index", maximum=U32_MAX),
        "source_height": source_height,
        "source_kind": source_kind,
        "source_root": _root(claim["source_root"], field="source_root"),
        "tx_index": _integer(claim["tx_index"], field="tx_index", maximum=U32_MAX),
    }
    return result


def _canonical_bytes(
    document: Mapping[str, object],
    claims: tuple[Mapping[str, str | int], ...],
) -> bytes:
    owned = {key: document[key] for key in _TOP_FIELDS - {"source_availability_claims"}}
    owned["source_availability_claims"] = [dict(claim) for claim in claims]
    return (
        json.dumps(owned, ensure_ascii=True, separators=(",", ":"), sort_keys=True)
        + "\n"
    ).encode("ascii")


def _validate_statement_header(
    plan: _StructuralDeltaPlanDataV2,
    statement: Mapping[str, object],
) -> tuple[int, int]:
    if type(statement["schema"]) is not str:
        _reject(SourceHistoryRejectCodeV2.DECODE_INVALID, "schema must be a string")
    if statement["schema"] != SOURCE_HISTORY_SCHEMA_V2:
        _reject(SourceHistoryRejectCodeV2.SCHEMA_MISMATCH, "schema is not V2")
    _identifier(statement["chain_id"], field="chain_id")
    for field in (
        "deployment_root",
        "profile_root",
        "history_root",
        "delta_plan_root",
        "verifier_release_id",
        "verifier_image_id",
    ):
        _root(statement[field], field=field)
    writer_epoch = _integer(
        statement["writer_epoch"], field="writer_epoch", maximum=U64_MAX
    )
    if writer_epoch == 0:
        _reject(SourceHistoryRejectCodeV2.WRITER_EPOCH_INVALID, "writer epoch is zero")
    history_height = _integer(
        statement["history_height"], field="history_height", maximum=U64_MAX
    )
    if statement["delta_plan_root"] != plan.root:
        _reject(
            SourceHistoryRejectCodeV2.DELTA_PLAN_ROOT_MISMATCH,
            "statement names a different delta plan",
        )
    return writer_epoch, history_height


def _validate_claim_uniqueness(
    claims: tuple[dict[str, str | int], ...],
) -> None:
    roots = tuple(str(claim["source_root"]) for claim in claims)
    if len(set(roots)) != len(roots):
        _reject(SourceHistoryRejectCodeV2.DUPLICATE_SOURCE_CLAIM, "source root repeats")
    if roots != tuple(sorted(roots)):
        _reject(
            SourceHistoryRejectCodeV2.NONCANONICAL_SOURCE_ORDER,
            "source roots are not ordered",
        )
    occurrences = tuple(
        (claim["source_height"], claim["tx_index"], claim["op_index"])
        for claim in claims
    )
    if len(set(occurrences)) != len(occurrences):
        _reject(SourceHistoryRejectCodeV2.DUPLICATE_OCCURRENCE, "occurrence repeats")
    nullifiers = {str(claim["consumption_nullifier"]) for claim in claims}
    if len(nullifiers) != len(claims):
        _reject(
            SourceHistoryRejectCodeV2.DUPLICATE_CONSUMPTION_NULLIFIER,
            "consumption nullifier repeats",
        )
    anchors = {str(claim["finality_anchor_root"]) for claim in claims}
    root_set = set(roots)
    if root_set & nullifiers or root_set & anchors or nullifiers & anchors:
        _reject(SourceHistoryRejectCodeV2.ROOT_ROLE_CONFLICT, "root roles alias")


def _validate_exact_bindings(
    plan: _StructuralDeltaPlanDataV2,
    claims: tuple[dict[str, str | int], ...],
) -> None:
    fields = ("source_root", "source_kind", "asset", "amount_atoms")
    for binding, claim in zip(plan.source_bindings, claims, strict=True):
        expected = tuple(binding[field] for field in fields)
        actual = tuple(claim[field] for field in fields)
        if actual != expected:
            _reject(
                SourceHistoryRejectCodeV2.SOURCE_BINDING_MISMATCH,
                "claim does not equal the plan source binding",
            )


def _validate_claims(
    plan: _StructuralDeltaPlanDataV2,
    raw_claims: object,
    *,
    history_height: int,
) -> tuple[dict[str, str | int], ...]:
    if type(raw_claims) is not list:
        _reject(SourceHistoryRejectCodeV2.DECODE_INVALID, "claims must be an array")
    raw_claims = cast(list[object], raw_claims)
    if len(raw_claims) != len(plan.source_bindings):
        _reject(
            SourceHistoryRejectCodeV2.SOURCE_COUNT_MISMATCH,
            "claim count differs from source-binding count",
        )
    claims = tuple(_claim(item, history_height=history_height) for item in raw_claims)
    _validate_claim_uniqueness(claims)
    _validate_exact_bindings(plan, claims)
    return claims


def validate_source_history_statement_v2(
    plan: _StructuralDeltaPlanDataV2,
    value: object,
) -> _CheckedSourceHistoryStatementDataV2:
    """Check one owned statement against an exact structural plan."""

    if type(plan) is not _StructuralDeltaPlanDataV2:
        _reject(SourceHistoryRejectCodeV2.DECODE_INVALID, "plan type is not closed")
    statement = _exact_mapping(
        value, expected_fields=_TOP_FIELDS, label="source-history statement"
    )
    writer_epoch, history_height = _validate_statement_header(plan, statement)
    claims = _validate_claims(
        plan,
        statement["source_availability_claims"],
        history_height=history_height,
    )
    canonical_bytes = _canonical_bytes(statement, claims)
    root = "sha256:" + hashlib.sha256(
        SOURCE_HISTORY_ROOT_DOMAIN_V2 + canonical_bytes
    ).hexdigest()
    frozen_claims = tuple(MappingProxyType(dict(claim)) for claim in claims)
    return _CheckedSourceHistoryStatementDataV2(
        source_availability_claims=frozen_claims,
        delta_plan_root=str(statement["delta_plan_root"]),
        history_root=str(statement["history_root"]),
        history_height=history_height,
        writer_epoch=writer_epoch,
        verifier_release_id=str(statement["verifier_release_id"]),
        verifier_image_id=str(statement["verifier_image_id"]),
        canonical_bytes=canonical_bytes,
        root=root,
    )


def decode_source_history_statement_bytes_v2(
    plan: _StructuralDeltaPlanDataV2,
    input_bytes: bytes,
) -> _CheckedSourceHistoryStatementDataV2:
    """Decode exact bytes under the Rust-compatible malformed-input ABI."""

    if type(input_bytes) is not bytes:
        _reject(SourceHistoryRejectCodeV2.DECODE_INVALID, "input must be exact bytes")
    if len(input_bytes) > MAX_SOURCE_HISTORY_INPUT_BYTES_V2:
        _reject(SourceHistoryRejectCodeV2.INPUT_TOO_LARGE, "input exceeds byte limit")
    duplicates: list[str] = []

    def hook(pairs: list[tuple[str, object]]) -> dict[str, object]:
        result: dict[str, object] = {}
        for key, item in pairs:
            if key in result:
                duplicates.append(key)
            result[key] = item
        return result

    try:
        text = input_bytes.decode("utf-8")
        value = json.loads(text, object_pairs_hook=hook)
    except (UnicodeDecodeError, json.JSONDecodeError, RecursionError) as exc:
        _reject(SourceHistoryRejectCodeV2.DECODE_INVALID, f"invalid JSON: {exc}")
    if duplicates:
        _reject(SourceHistoryRejectCodeV2.DECODE_INVALID, "duplicate JSON keys")
    return validate_source_history_statement_v2(plan, value)
