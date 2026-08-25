"""Scope-bound current Oracle dispute status for critical value consumers.

The status object is a deterministic research witness. Authority comes from an
independently selected expected root at the consumer's commit boundary. The
caller-provided witness never selects its own trusted root.
"""

from __future__ import annotations

import hashlib
from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from typing import Any

from ..state.canonical import canonical_json_bytes
from .global_oracle_occurrence_authority_v1 import GlobalOracleOccurrenceAuthorityV1
from .global_settlement_types_v1 import _require_root

CURRENT_DISPUTE_STATUS_SCHEMA_V1 = "zenodex.oracle.current_dispute_status.v1"
CURRENT_DISPUTE_STATUS_HASH_DOMAIN_V1 = "zenodex.oracle.current_dispute_status/v1"
GLOBAL_CURRENT_DISPUTE_STATUS_ORACLE_ID_V1 = (
    "zenodex.oracle.current-dispute-status.v1"
)
DISPUTE_STATUSES_V1 = frozenset({"open", "rejected", "upheld"})
REVOKING_DISPUTE_STATUSES_V1 = frozenset({"open", "upheld"})

_STATUS_FIELDS = frozenset(
    {
        "schema",
        "as_of_epoch",
        "included_report_ids",
        "disputes",
        "disputed_report_ids",
        "current_dispute_status_root",
    }
)
_DISPUTE_FIELDS = frozenset({"dispute_id", "report_id", "status"})
_MAX_EXACT_JSON_NODES = 100_000


@dataclass(frozen=True)
class OracleCurrentDisputeStatusCheckV1:
    ok: bool
    errors: tuple[str, ...]
    current_dispute_status_root: str | None
    disputed_report_ids: tuple[str, ...]


def _is_canonical_sha256_ref(value: object) -> bool:
    if type(value) is not str or len(value) != 71 or not value.startswith("sha256:"):
        return False
    digest = value.removeprefix("sha256:")
    return digest == digest.lower() and all(char in "0123456789abcdef" for char in digest)


def _status_root(body: Mapping[str, Any]) -> str:
    material = (
        CURRENT_DISPUTE_STATUS_HASH_DOMAIN_V1.encode("ascii")
        + b"\x00"
        + canonical_json_bytes(dict(body))
    )
    return "sha256:" + hashlib.sha256(material).hexdigest()


def global_root_from_current_dispute_status_root_v1(status_root: object) -> str:
    """Convert the legacy SHA-256 reference spelling to ABI V1 root spelling."""

    if type(status_root) is not str or not _is_canonical_sha256_ref(status_root):
        raise ValueError("current dispute status root must be a canonical sha256 reference")
    global_root = "0x" + status_root.removeprefix("sha256:")
    return _require_root(global_root, name="global current dispute status root")


def current_dispute_status_root_from_global_root_v1(global_root: object) -> str:
    """Convert an ABI V1 root spelling to the legacy status reference spelling."""

    if type(global_root) is not str:
        raise TypeError("global current dispute status root must be an exact string")
    canonical_root = _require_root(
        global_root,
        name="global current dispute status root",
    )
    return "sha256:" + canonical_root.removeprefix("0x")


def current_dispute_status_root_from_global_authority_v1(
    authority: GlobalOracleOccurrenceAuthorityV1,
) -> str:
    """Derive the legacy expected root from a checker-owned global witness."""

    if type(authority) is not GlobalOracleOccurrenceAuthorityV1:
        raise TypeError("current dispute status authority must be exact typed data")
    if authority.oracle_id != GLOBAL_CURRENT_DISPUTE_STATUS_ORACLE_ID_V1:
        raise ValueError("global authority is for a different Oracle occurrence")
    return current_dispute_status_root_from_global_root_v1(authority.occurrence_root)


def _normalized_report_ids(report_ids: Sequence[object], *, label: str) -> tuple[str, ...]:
    if type(report_ids) not in (list, tuple) or not report_ids:
        raise ValueError(f"{label} must be a non-empty exact sequence")
    if any(not _is_canonical_sha256_ref(report_id) for report_id in report_ids):
        raise ValueError(f"{label} must contain canonical sha256 references")
    normalized = tuple(sorted(report_ids))
    if len(set(normalized)) != len(normalized):
        raise ValueError(f"{label} must be distinct")
    return normalized


def _project_relevant_disputes(
    dispute_entries: Sequence[Mapping[str, Any]],
    *,
    report_ids: frozenset[str],
) -> list[dict[str, str]]:
    if type(dispute_entries) not in (list, tuple):
        raise ValueError("dispute_entries must be an exact sequence")
    projected: list[dict[str, str]] = []
    for index, entry in enumerate(dispute_entries):
        if type(entry) is not dict:
            raise ValueError(f"dispute_entries[{index}] must be an exact object")
        report_id = entry.get("report_id")
        if type(report_id) is not str:
            raise ValueError(f"dispute_entries[{index}] report_id must be an exact string")
        if report_id not in report_ids:
            continue
        dispute_id = entry.get("dispute_id")
        status = entry.get("status")
        if not _is_canonical_sha256_ref(dispute_id):
            raise ValueError(
                f"dispute_entries[{index}] dispute_id must be a canonical sha256 reference"
            )
        if type(status) is not str or status not in DISPUTE_STATUSES_V1:
            raise ValueError(f"dispute_entries[{index}] status is unsupported")
        projected.append(
            {
                "dispute_id": dispute_id,
                "report_id": report_id,
                "status": status,
            }
        )
    projected.sort(key=lambda dispute: (dispute["report_id"], dispute["dispute_id"]))
    identities = [(dispute["report_id"], dispute["dispute_id"]) for dispute in projected]
    if len(set(identities)) != len(identities):
        raise ValueError("dispute_entries contain duplicate dispute identities")
    return projected


def build_oracle_current_dispute_status_v1(
    *,
    report_ids: Sequence[object],
    dispute_entries: Sequence[Mapping[str, Any]],
    as_of_epoch: int,
) -> dict[str, object]:
    """Project one exact report scope from a current dispute-registry snapshot."""

    normalized_report_ids = _normalized_report_ids(report_ids, label="report_ids")
    if type(as_of_epoch) is not int or as_of_epoch < 0:
        raise ValueError("as_of_epoch must be a non-negative exact int")
    disputes = _project_relevant_disputes(
        dispute_entries,
        report_ids=frozenset(normalized_report_ids),
    )
    disputed_report_ids = sorted(
        {
            dispute["report_id"]
            for dispute in disputes
            if dispute["status"] in REVOKING_DISPUTE_STATUSES_V1
        }
    )
    body: dict[str, object] = {
        "schema": CURRENT_DISPUTE_STATUS_SCHEMA_V1,
        "as_of_epoch": as_of_epoch,
        "included_report_ids": list(normalized_report_ids),
        "disputes": disputes,
        "disputed_report_ids": disputed_report_ids,
    }
    return {
        **body,
        "current_dispute_status_root": _status_root(body),
    }


def _exact_tree_error(
    value: object,
    *,
    path: str,
    depth: int = 0,
    remaining_nodes: list[int] | None = None,
) -> str | None:
    if remaining_nodes is None:
        remaining_nodes = [_MAX_EXACT_JSON_NODES]
    remaining_nodes[0] -= 1
    if remaining_nodes[0] < 0:
        return f"{path} exceeds exact JSON node budget"
    if depth > 16:
        return f"{path} exceeds exact JSON depth budget"
    if type(value) is str:
        if any(0xD800 <= ord(char) <= 0xDFFF for char in value):
            return f"{path} contains a surrogate code point"
        return None
    if value is None or type(value) in (bool, int):
        return None
    if type(value) is list:
        if len(value) > 10_000:
            return f"{path} exceeds exact JSON item budget"
        for index, item in enumerate(value):
            error = _exact_tree_error(
                item,
                path=f"{path}[{index}]",
                depth=depth + 1,
                remaining_nodes=remaining_nodes,
            )
            if error is not None:
                return error
        return None
    if type(value) is dict:
        if len(value) > 10_000:
            return f"{path} exceeds exact JSON item budget"
        for key, item in value.items():
            if type(key) is not str:
                return f"{path} contains a non-exact JSON object key"
            error = _exact_tree_error(
                item,
                path=f"{path}.{key}",
                depth=depth + 1,
                remaining_nodes=remaining_nodes,
            )
            if error is not None:
                return error
        return None
    return f"{path} contains a non-exact JSON primitive: {type(value).__name__}"


def _validate_status_header(
    witness: Mapping[str, Any],
    *,
    expected_report_ids: Sequence[object],
    now_epoch: int,
    errors: list[str],
) -> tuple[str, ...]:
    unknown_fields = sorted(set(witness) - _STATUS_FIELDS)
    if unknown_fields:
        errors.append("current dispute status has unknown fields: " + ", ".join(unknown_fields))
    missing_fields = sorted(_STATUS_FIELDS - set(witness))
    if missing_fields:
        errors.append("current dispute status is missing fields: " + ", ".join(missing_fields))
    if witness.get("schema") != CURRENT_DISPUTE_STATUS_SCHEMA_V1:
        errors.append("current dispute status schema mismatch")

    try:
        expected_scope = _normalized_report_ids(
            expected_report_ids,
            label="expected_report_ids",
        )
    except ValueError as exc:
        expected_scope = ()
        errors.append(str(exc))
    try:
        actual_scope = _normalized_report_ids(
            witness.get("included_report_ids"),
            label="current dispute status included_report_ids",
        )
    except ValueError as exc:
        actual_scope = ()
        errors.append(str(exc))
    included_report_ids = witness.get("included_report_ids")
    if type(included_report_ids) is list and tuple(included_report_ids) != actual_scope:
        errors.append("current dispute status included_report_ids must be canonically sorted")
    if expected_scope and actual_scope != expected_scope:
        errors.append("current dispute status report scope mismatch")

    as_of_epoch = witness.get("as_of_epoch")
    if type(as_of_epoch) is not int or as_of_epoch < 0:
        errors.append("current dispute status as_of_epoch must be a non-negative exact int")
    if type(now_epoch) is not int or now_epoch < 0:
        errors.append("current dispute status runtime epoch must be a non-negative exact int")
    elif type(as_of_epoch) is int and as_of_epoch != now_epoch:
        errors.append("current dispute status as_of_epoch does not match runtime epoch")
    return actual_scope


def _parse_dispute(
    dispute: object,
    *,
    index: int,
    actual_scope: tuple[str, ...],
    seen_identities: set[tuple[str, str]],
    errors: list[str],
) -> dict[str, str] | None:
    label = f"current dispute status disputes[{index}]"
    if type(dispute) is not dict:
        errors.append(f"{label} must be an exact object")
        return None
    unknown = sorted(set(dispute) - _DISPUTE_FIELDS)
    missing = sorted(_DISPUTE_FIELDS - set(dispute))
    if unknown:
        errors.append(f"{label} has unknown fields: " + ", ".join(unknown))
    if missing:
        errors.append(f"{label} is missing fields: " + ", ".join(missing))
    dispute_id = dispute.get("dispute_id")
    report_id = dispute.get("report_id")
    status = dispute.get("status")
    if not _is_canonical_sha256_ref(dispute_id):
        errors.append(f"{label} dispute_id must be a canonical sha256 reference")
        return None
    if not _is_canonical_sha256_ref(report_id):
        errors.append(f"{label} report_id must be a canonical sha256 reference")
        return None
    if type(status) is not str or status not in DISPUTE_STATUSES_V1:
        errors.append(f"{label} status is unsupported")
        return None
    if actual_scope and report_id not in actual_scope:
        errors.append(f"{label} report_id is outside scope")
    identity = (report_id, dispute_id)
    if identity in seen_identities:
        errors.append("current dispute status contains duplicate dispute identities")
    seen_identities.add(identity)
    return {"dispute_id": dispute_id, "report_id": report_id, "status": status}


def _parse_disputes(
    witness: Mapping[str, Any],
    *,
    actual_scope: tuple[str, ...],
    errors: list[str],
) -> list[dict[str, str]]:
    disputes_value = witness.get("disputes")
    if type(disputes_value) is not list:
        errors.append("current dispute status disputes must be an exact list")
        return []
    parsed_disputes: list[dict[str, str]] = []
    seen_identities: set[tuple[str, str]] = set()
    for index, dispute in enumerate(disputes_value):
        parsed = _parse_dispute(
            dispute,
            index=index,
            actual_scope=actual_scope,
            seen_identities=seen_identities,
            errors=errors,
        )
        if parsed is not None:
            parsed_disputes.append(parsed)
    if parsed_disputes != sorted(
        parsed_disputes,
        key=lambda item: (item["report_id"], item["dispute_id"]),
    ):
        errors.append("current dispute status disputes must be canonically sorted")
    return parsed_disputes


def _validate_disputed_report_ids(
    witness: Mapping[str, Any],
    *,
    parsed_disputes: Sequence[Mapping[str, str]],
    errors: list[str],
) -> tuple[str, ...]:
    derived = tuple(
        sorted(
            {
                dispute["report_id"]
                for dispute in parsed_disputes
                if dispute["status"] in REVOKING_DISPUTE_STATUSES_V1
            }
        )
    )
    disputed_value = witness.get("disputed_report_ids")
    if type(disputed_value) is not list or any(
        not _is_canonical_sha256_ref(report_id) for report_id in disputed_value
    ):
        errors.append("current dispute status disputed_report_ids must be canonical sha256 references")
    elif tuple(disputed_value) != derived:
        errors.append("current dispute status disputed_report_ids mismatch")
    return derived


def _validate_status_roots(
    witness: Mapping[str, Any],
    *,
    expected_root: str,
    errors: list[str],
) -> str | None:
    supplied_root = witness.get("current_dispute_status_root")
    if not _is_canonical_sha256_ref(supplied_root):
        errors.append("current dispute status root must be a canonical sha256 reference")
        supplied_root_text: str | None = None
    else:
        supplied_root_text = supplied_root
    body = {key: value for key, value in witness.items() if key != "current_dispute_status_root"}
    try:
        computed_root = _status_root(body)
    except (TypeError, ValueError):
        computed_root = None
        errors.append("current dispute status root could not be computed")
    if computed_root is not None and supplied_root_text != computed_root:
        errors.append("current dispute status root mismatch")
    if not _is_canonical_sha256_ref(expected_root):
        errors.append("expected current dispute status root must be a canonical sha256 reference")
    elif supplied_root_text != expected_root:
        errors.append("current dispute status root does not match verifier-selected root")
    return supplied_root_text


def verify_oracle_current_dispute_status_v1(
    witness: Mapping[str, Any],
    *,
    expected_report_ids: Sequence[object],
    expected_root: str,
    now_epoch: int,
) -> OracleCurrentDisputeStatusCheckV1:
    """Verify scope, epoch, content, and verifier-selected root before use."""

    if type(witness) is not dict:
        return OracleCurrentDisputeStatusCheckV1(
            ok=False,
            errors=("current dispute status must be an exact object",),
            current_dispute_status_root=None,
            disputed_report_ids=(),
        )
    tree_error = _exact_tree_error(witness, path="current dispute status")
    if tree_error is not None:
        return OracleCurrentDisputeStatusCheckV1(
            ok=False,
            errors=(tree_error,),
            current_dispute_status_root=None,
            disputed_report_ids=(),
        )
    errors: list[str] = []
    actual_scope = _validate_status_header(
        witness,
        expected_report_ids=expected_report_ids,
        now_epoch=now_epoch,
        errors=errors,
    )
    parsed_disputes = _parse_disputes(witness, actual_scope=actual_scope, errors=errors)
    derived_disputed_report_ids = _validate_disputed_report_ids(
        witness,
        parsed_disputes=parsed_disputes,
        errors=errors,
    )
    supplied_root_text = _validate_status_roots(
        witness,
        expected_root=expected_root,
        errors=errors,
    )
    if derived_disputed_report_ids:
        errors.append("current dispute status includes open or upheld reports")

    return OracleCurrentDisputeStatusCheckV1(
        ok=not errors,
        errors=tuple(errors),
        current_dispute_status_root=supplied_root_text,
        disputed_report_ids=derived_disputed_report_ids,
    )
