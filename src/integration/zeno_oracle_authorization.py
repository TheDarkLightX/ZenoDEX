"""Typed ZenoOracle authorization checks for critical runtime consumers."""

from __future__ import annotations

import hashlib
import json
from dataclasses import asdict, dataclass
from typing import Any, Mapping

from src.core.oracle_current_dispute_status_v1 import (
    verify_oracle_current_dispute_status_v1,
)
from src.core.oracle_economic_security import (
    ENVELOPE_KEYS as ECONOMIC_SECURITY_ENVELOPE_KEYS,
)
from src.core.oracle_economic_security import (
    verify_economic_security_envelope,
)

SCHEMA = "zenodex/oracle-authorization-semantic-binding-check/v1"
EVIDENCE_RANK = {"O0": 0, "O1": 1, "O2": 2, "O3": 3, "O4": 4, "O5": 5}


def _consumer_profile_id(
    *,
    consumer_module: str,
    action_kind: str,
    query_id: str,
    max_freshness_window_epochs: int,
) -> str:
    payload = {
        "schema": "zenodex.oracle.consumer_profile.v1",
        "consumer_module": consumer_module,
        "action_kind": action_kind,
        "query_id": query_id,
        "required_evidence_floor": "O3",
        "max_freshness_window_epochs": int(max_freshness_window_epochs),
        "critical": True,
    }
    encoded = json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")
    return "sha256:" + hashlib.sha256(encoded).hexdigest()


_CRITICAL_SETTLEMENT_QUERY_ID = (
    "sha256:" + hashlib.sha256(b"zenodex.oracle.query.settlement.price_curr_e8").hexdigest()
)
_ZUSD_COLLATERAL_QUERY_ID = (
    "sha256:" + hashlib.sha256(b"zenodex.oracle.query.zusd.collateral_price_e8").hexdigest()
)
_PERPS_INDEX_QUERY_ID = (
    "sha256:" + hashlib.sha256(b"zenodex.oracle.query.perps.index_price_e8").hexdigest()
)
_TRIGGER_REFERENCE_QUERY_ID = (
    "sha256:" + hashlib.sha256(b"zenodex.oracle.query.trigger.reference_price_e8").hexdigest()
)
_CRITICAL_SETTLEMENT_PROFILE_ID = _consumer_profile_id(
    consumer_module="zenodex.settlement",
    action_kind="critical_settlement",
    query_id=_CRITICAL_SETTLEMENT_QUERY_ID,
    max_freshness_window_epochs=1,
)
_ZUSD_MINT_PROFILE_ID = _consumer_profile_id(
    consumer_module="zenodex.zusd",
    action_kind="mint",
    query_id=_ZUSD_COLLATERAL_QUERY_ID,
    max_freshness_window_epochs=2,
)
_ZUSD_LIQUIDATE_VAULT_PROFILE_ID = _consumer_profile_id(
    consumer_module="zenodex.zusd",
    action_kind="liquidate_vault",
    query_id=_ZUSD_COLLATERAL_QUERY_ID,
    max_freshness_window_epochs=1,
)
_PERPS_SETTLE_EPOCH_PROFILE_ID = _consumer_profile_id(
    consumer_module="zenodex.perps",
    action_kind="settle_epoch",
    query_id=_PERPS_INDEX_QUERY_ID,
    max_freshness_window_epochs=2,
)
_PERPS_LIQUIDATE_ACCOUNT_PROFILE_ID = _consumer_profile_id(
    consumer_module="zenodex.perps",
    action_kind="liquidate_account",
    query_id=_PERPS_INDEX_QUERY_ID,
    max_freshness_window_epochs=1,
)
_TRIGGER_EXECUTE_PROFILE_ID = _consumer_profile_id(
    consumer_module="zenodex.trigger",
    action_kind="execute_trigger",
    query_id=_TRIGGER_REFERENCE_QUERY_ID,
    max_freshness_window_epochs=2,
)

# Stable identifiers consumed by value-moving adapters. These values describe
# the verifier-selected Oracle policy; callers cannot use them to mint an
# authorization.
ZUSD_COLLATERAL_QUERY_ID = _ZUSD_COLLATERAL_QUERY_ID
ZUSD_MINT_PROFILE_ID = _ZUSD_MINT_PROFILE_ID
ZUSD_LIQUIDATE_VAULT_PROFILE_ID = _ZUSD_LIQUIDATE_VAULT_PROFILE_ID


CRITICAL_CONSUMER_PROFILES: dict[tuple[str, str], str] = {
    ("zenodex.zusd", "bootstrap_oracle"): "critical-zusd-v1",
    ("zenodex.zusd", "oracle_report"): "critical-zusd-v1",
    ("zenodex.zusd", "oracle_commit"): "critical-zusd-v1",
    ("zenodex.zusd", "mint"): "critical-zusd-v1",
    ("zenodex.zusd", "liquidate"): "critical-zusd-v1",
    ("zenodex.perps", "settle_epoch"): "critical-perps-v1",
    ("zenodex.perps", "liquidate"): "critical-perps-v1",
    ("zenodex.routing", "protected_swap"): "critical-routing-v1",
    ("zenodex.trigger", "execute"): "critical-trigger-v1",
    ("zenodex.settlement", "critical_settlement"): _CRITICAL_SETTLEMENT_PROFILE_ID,
}

CRITICAL_CONSUMER_MAX_FRESHNESS_WINDOW_EPOCHS: dict[tuple[str, str], int] = {
    ("zenodex.zusd", "bootstrap_oracle"): 2,
    ("zenodex.zusd", "oracle_report"): 2,
    ("zenodex.zusd", "oracle_commit"): 2,
    ("zenodex.zusd", "mint"): 2,
    ("zenodex.zusd", "liquidate"): 1,
    ("zenodex.zusd", "liquidate_vault"): 1,
    ("zenodex.perps", "settle_epoch"): 2,
    ("zenodex.perps", "liquidate"): 1,
    ("zenodex.perps", "liquidate_account"): 1,
    ("zenodex.routing", "guarded_quote"): 4,
    ("zenodex.routing", "protected_swap"): 4,
    ("zenodex.trigger", "execute"): 2,
    ("zenodex.trigger", "execute_trigger"): 2,
    ("zenodex.settlement", "critical_settlement"): 1,
}

CRITICAL_PROFILE_MAX_FRESHNESS_WINDOW_EPOCHS: dict[str, int] = {
    "critical-zusd-v1": 2,
    "critical-perps-v1": 2,
    "critical-routing-v1": 4,
    "critical-trigger-v1": 2,
    _CRITICAL_SETTLEMENT_PROFILE_ID: 1,
    _ZUSD_MINT_PROFILE_ID: 2,
    _ZUSD_LIQUIDATE_VAULT_PROFILE_ID: 1,
    _PERPS_SETTLE_EPOCH_PROFILE_ID: 2,
    _PERPS_LIQUIDATE_ACCOUNT_PROFILE_ID: 1,
    _TRIGGER_EXECUTE_PROFILE_ID: 2,
}


@dataclass(frozen=True)
class OracleAuthorization:
    consumer_module: str
    action_kind: str
    action_id: str
    action_facts_hash: str
    pre_state_hash: str
    profile_id: str
    query_id: str
    value_e8: int
    value_hash: str
    confidence_e8: int
    deviation_bps: int
    observed_epoch: int
    expires_at_epoch: int
    feed_id: str
    feed_registry_root: str
    query_policy_root: str
    source_registry_root: str
    reporter_registry_root: str
    evidence_class: str
    economic_envelope_id: str
    receipt_graph_root: str


@dataclass(frozen=True)
class RuntimeActionFacts:
    consumer_module: str
    action_kind: str
    action_id: str
    action_facts_hash: str
    pre_state_hash: str
    profile_id: str
    query_id: str
    runtime_value_e8: int
    now_epoch: int
    runtime_notional_value_e8: int | None = None
    max_freshness_window_epochs: int | None = None


AUTHORIZATION_FIELDS = frozenset(
    {
        "consumer_module",
        "action_kind",
        "action_id",
        "action_facts_hash",
        "pre_state_hash",
        "profile_id",
        "query_id",
        "value_e8",
        "value_hash",
        "confidence_e8",
        "deviation_bps",
        "observed_epoch",
        "expires_at_epoch",
        "feed_id",
        "feed_registry_root",
        "query_policy_root",
        "source_registry_root",
        "reporter_registry_root",
        "evidence_class",
        "economic_envelope_id",
        "receipt_graph_root",
    }
)
AUTHORIZATION_BUNDLE_FIELDS = frozenset(
    {
        "schema",
        "authorization",
        "runtime_action",
        "receipt_graph",
        "economic_envelope",
        "authorization_id",
        "semantic_check",
        "production_authority",
    }
)
RUNTIME_ACTION_FIELDS = frozenset(
    {
        "consumer_module",
        "action_kind",
        "action_id",
        "action_facts_hash",
        "pre_state_hash",
        "profile_id",
        "query_id",
        "runtime_value_e8",
        "now_epoch",
        "runtime_notional_value_e8",
        "max_freshness_window_epochs",
    }
)
RECEIPT_GRAPH_FIELDS = frozenset(
    {
        "schema",
        "read_id",
        "aggregate_id",
        "query_id",
        "value_hash",
        "value_e8",
        "confidence_e8",
        "deviation_bps",
        "observed_epoch",
        "expires_at_epoch",
        "read_evidence_class",
        "aggregate_evidence_class",
        "reporter_count",
        "min_reporters",
        "source_policy_id",
        "source_count",
        "reporter_control_group_count",
        "included_source_ids",
        "included_report_ids",
        "report_leaf_commitments",
        "report_leaf_root",
        "dispute_state_root",
        "disputed_report_ids",
        "feed_registry_root",
        "query_policy_root",
        "source_registry_root",
        "reporter_registry_root",
        "receipt_graph_root",
    }
)
REPORT_LEAF_FIELDS = frozenset(
    {
        "active",
        "bond_e8",
        "bond_amount_e8",
        "control_group_id",
        "price_e8",
        "query_id",
        "query_ids",
        "report_id",
        "reported_epoch",
        "reporter_id",
        "reporter_state_hash",
        "required_bond_e8",
        "sequence",
        "signature",
        "signing_payload_hash",
        "slash_state",
        "source_id",
        "source_observed_epoch",
        "source_state_hash",
        "source_state_at_submit",
    }
)
SOURCE_STATE_AT_SUBMIT_FIELDS = frozenset(
    {
        "source_id",
        "source_kind",
        "operator_id",
        "source_control_group_id",
        "venue_id",
        "data_family_id",
        "transport_id",
        "jurisdiction",
        "asset_classes",
        "query_ids",
        "assurance_class",
        "active",
        "registered_epoch",
    }
)
ECONOMIC_ENVELOPE_FIELDS = ECONOMIC_SECURITY_ENVELOPE_KEYS


def _unknown_field_errors(
    obj: Mapping[Any, Any],
    *,
    allowed: frozenset[str],
    label: str,
) -> tuple[str, ...]:
    errors: list[str] = []
    if any(type(key) is not str for key in obj):
        errors.append(f"{label} field names must be exact strings")
    unknown = sorted(key for key in obj if type(key) is str and key not in allowed)
    if unknown:
        errors.append(f"{label} has unknown fields: {', '.join(unknown)}")
    return tuple(errors)


def _require_closed_fields(
    obj: Mapping[Any, Any],
    *,
    allowed: frozenset[str],
    label: str,
) -> None:
    errors = _unknown_field_errors(obj, allowed=allowed, label=label)
    if errors:
        raise ValueError("; ".join(errors))


def _canonical_bytes(payload: Mapping[str, Any]) -> bytes:
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")


def semantic_hash(domain: str, payload: Mapping[str, Any]) -> str:
    digest = hashlib.sha256(domain.encode("utf-8") + b"\x00" + _canonical_bytes(payload)).hexdigest()
    return f"sha256:{digest}"


def oracle_value_hash(*, query_id: str, value_e8: int, observed_epoch: int) -> str:
    if type(query_id) is not str or not query_id:
        raise ValueError("query_id must be a non-empty string")
    if type(value_e8) is not int:
        raise ValueError("value_e8 must be an int")
    if type(observed_epoch) is not int:
        raise ValueError("observed_epoch must be an int")
    return semantic_hash(
        "zenodex.oracle.value.v1",
        {
            "observed_epoch": observed_epoch,
            "query_id": query_id,
            "value_e8": value_e8,
        },
    )


def economic_envelope_hash(envelope: Mapping[str, Any]) -> str:
    return semantic_hash("zenodex.oracle.economic_envelope.v1", envelope)


def _is_sha256_ref(value: str) -> bool:
    if type(value) is not str or not value.startswith("sha256:") or len(value) != 71:
        return False
    try:
        int(value.removeprefix("sha256:"), 16)
    except ValueError:
        return False
    return True


def _rank_at_least(actual: Any, minimum: str) -> bool:
    return type(actual) is str and EVIDENCE_RANK.get(actual, -1) >= EVIDENCE_RANK[minimum]


def _expected_max_freshness_window_epochs(
    *,
    consumer_module: str,
    action_kind: str,
    profile_id: str | None,
) -> int | None:
    action_window = CRITICAL_CONSUMER_MAX_FRESHNESS_WINDOW_EPOCHS.get((consumer_module, action_kind))
    profile_window = None
    if profile_id is not None:
        profile_window = CRITICAL_PROFILE_MAX_FRESHNESS_WINDOW_EPOCHS.get(profile_id)
    if action_window is None:
        return profile_window
    if profile_window is None:
        return action_window
    return min(action_window, profile_window)


def _graph_obj_from_payload(payload: Mapping[str, Any]) -> Mapping[str, Any] | None:
    maybe_graph = payload.get("receipt_graph")
    if maybe_graph is None:
        return None
    if type(maybe_graph) is dict:
        return maybe_graph
    raise ValueError("receipt_graph must be an exact object")


def _economic_envelope_obj_from_payload(payload: Mapping[str, Any]) -> Mapping[str, Any] | None:
    maybe_envelope = payload.get("economic_envelope")
    if maybe_envelope is None:
        return None
    if type(maybe_envelope) is dict:
        return maybe_envelope
    raise ValueError("economic_envelope must be an exact object")


def _non_negative_int_obj(obj: Mapping[str, Any], key: str, errors: list[str]) -> int | None:
    value = obj.get(key)
    if type(value) is not int:
        errors.append(f"economic_envelope {key} must be a non-negative int")
        return None
    out = value
    if out < 0:
        errors.append(f"economic_envelope {key} must be a non-negative int")
        return None
    return out


def _positive_int_obj(obj: Mapping[str, Any], key: str, errors: list[str]) -> int | None:
    value = obj.get(key)
    if type(value) is not int:
        errors.append(f"economic_envelope {key} must be a positive int")
        return None
    out = value
    if out <= 0:
        errors.append(f"economic_envelope {key} must be a positive int")
        return None
    return out


def _bps_int_obj(obj: Mapping[str, Any], key: str, errors: list[str]) -> int | None:
    value = obj.get(key)
    if type(value) is not int:
        errors.append(f"economic_envelope {key} must be in [0, 10000]")
        return None
    out = value
    if out < 0 or out > 10_000:
        errors.append(f"economic_envelope {key} must be in [0, 10000]")
        return None
    return out


def _receipt_required_bonds_e8(
    receipt_graph: Mapping[str, Any],
    errors: list[str],
) -> tuple[int, ...]:
    report_leaf_commitments = receipt_graph.get("report_leaf_commitments")
    if type(report_leaf_commitments) is not list:
        return ()
    required_bonds: list[int] = []
    for index, leaf in enumerate(report_leaf_commitments):
        if type(leaf) is not dict:
            continue
        report_id_obj = leaf.get("report_id")
        report_id = report_id_obj if type(report_id_obj) is str and report_id_obj else f"index:{index}"
        required_bonds.append(
            _non_negative_leaf_int(
                leaf,
                "required_bond_e8",
                errors,
                report_id=report_id,
            )
        )
    return tuple(required_bonds)


def verify_economic_envelope_binding(
    authorization: OracleAuthorization,
    economic_envelope: Mapping[str, Any] | None,
    *,
    receipt_graph: Mapping[str, Any] | None = None,
    runtime_notional_value_e8: int | None = None,
    require_economic_envelope: bool = False,
) -> tuple[bool, tuple[str, ...]]:
    """Check that a terminal authorization is bound to its economic envelope."""

    errors: list[str] = []
    if economic_envelope is None:
        if require_economic_envelope:
            return False, ("economic_envelope required",)
        return True, ()
    errors.extend(
        _unknown_field_errors(
            economic_envelope,
            allowed=ECONOMIC_ENVELOPE_FIELDS,
            label="economic_envelope",
        )
    )
    economic_security = verify_economic_security_envelope(economic_envelope)
    errors.extend(
        f"economic_envelope {error}" for error in economic_security.errors
    )
    if economic_envelope.get("schema") != "zenodex.oracle.economic_security_envelope.v1":
        errors.append("economic_envelope schema must be zenodex.oracle.economic_security_envelope.v1")
    for key in ("query_id", "consumer_module", "action_kind"):
        if economic_envelope.get(key) != getattr(authorization, key):
            errors.append(f"economic_envelope {key} does not match authorization")
    notional_value = _non_negative_int_obj(economic_envelope, "notional_value_e8", errors)
    max_extractable = _non_negative_int_obj(economic_envelope, "max_extractable_value_e8", errors)
    reporter_count = _positive_int_obj(economic_envelope, "reporter_count", errors)
    reporter_bond_required = _non_negative_int_obj(
        economic_envelope,
        "reporter_bond_required_e8",
        errors,
    )
    _bps_int_obj(economic_envelope, "slash_fraction_bps", errors)
    _bps_int_obj(economic_envelope, "deterrence_margin_bps", errors)
    if (
        notional_value is not None
        and max_extractable is not None
        and max_extractable > notional_value
    ):
        errors.append("economic_envelope max_extractable_value_e8 exceeds notional_value_e8")
    if runtime_notional_value_e8 is not None:
        if type(runtime_notional_value_e8) is not int:
            errors.append("runtime_notional_value_e8 must be a non-negative int")
        elif runtime_notional_value_e8 < 0:
            errors.append("runtime_notional_value_e8 must be a non-negative int")
        elif notional_value is not None and runtime_notional_value_e8 > notional_value:
            errors.append("runtime_notional_value_e8 exceeds economic envelope")
    if receipt_graph is not None:
        receipt_reporter_count = _non_negative_graph_int(receipt_graph, "reporter_count", errors)
        if reporter_count is not None and reporter_count != receipt_reporter_count:
            errors.append("economic_envelope reporter_count does not match receipt_graph")
        required_bonds = _receipt_required_bonds_e8(receipt_graph, errors)
        if reporter_bond_required is not None and required_bonds:
            if any(required_bond != reporter_bond_required for required_bond in required_bonds):
                errors.append(
                    "economic_envelope reporter_bond_required_e8 does not match receipt_graph required_bond_e8"
                )
    expected_envelope_id = economic_envelope_hash(economic_envelope)
    if authorization.economic_envelope_id != expected_envelope_id:
        errors.append("economic_envelope_id does not bind economic_envelope")
    return not errors, tuple(errors)


def _non_negative_graph_int(graph: Mapping[str, Any], key: str, errors: list[str]) -> int:
    value = graph.get(key)
    if type(value) is not int:
        errors.append(f"receipt_graph {key} must be a non-negative int")
        return 0
    out = value
    if out < 0:
        errors.append(f"receipt_graph {key} must be a non-negative int")
        return 0
    return out


def _non_negative_leaf_int(leaf: Mapping[str, Any], key: str, errors: list[str], *, report_id: str) -> int:
    value = leaf.get(key)
    if type(value) is not int:
        errors.append(f"receipt_graph report leaf {report_id} {key} must be a non-negative int")
        return 0
    out = value
    if out < 0:
        errors.append(f"receipt_graph report leaf {report_id} {key} must be a non-negative int")
        return 0
    return out


def _require_active_leaf_bool(leaf: Mapping[str, Any], errors: list[str], *, report_id: str) -> None:
    if leaf.get("active") is not True:
        errors.append(f"receipt_graph report leaf {report_id} active must be true")


def _exact_json_tree_error(
    value: Any,
    *,
    path: str,
    depth: int = 0,
    remaining_nodes: list[int] | None = None,
) -> str | None:
    if remaining_nodes is None:
        remaining_nodes = [100_000]
    remaining_nodes[0] -= 1
    if remaining_nodes[0] < 0:
        return f"{path} exceeds exact JSON node budget"
    if depth > 64:
        return f"{path} exceeds exact JSON depth budget"
    if value is None or type(value) in (bool, int, str):
        return None
    if type(value) is list:
        for index, item in enumerate(value):
            error = _exact_json_tree_error(
                item,
                path=f"{path}[{index}]",
                depth=depth + 1,
                remaining_nodes=remaining_nodes,
            )
            if error is not None:
                return error
        return None
    if type(value) is dict:
        for key, item in value.items():
            if type(key) is not str:
                return f"{path} contains a non-exact JSON object key"
            error = _exact_json_tree_error(
                item,
                path=f"{path}.{key}",
                depth=depth + 1,
                remaining_nodes=remaining_nodes,
            )
            if error is not None:
                return error
        return None
    return f"{path} contains a non-exact JSON primitive: {type(value).__name__}"


def verify_receipt_graph_binding(
    authorization: OracleAuthorization,
    receipt_graph: Mapping[str, Any] | None,
) -> tuple[bool, tuple[str, ...]]:
    """Check that a terminal receipt graph closes over the authorization.

    This is intentionally a structural verifier, not a live oracle replay. It
    proves that the runtime-consumed authorization is bound to a terminal graph
    carrying the same value, roots, uncertainty, freshness, and O3-or-better
    evidence. The CLI/local-state replay remains responsible for reconstructing
    the full graph from persisted reports.
    """

    errors: list[str] = []
    if receipt_graph is None:
        return False, ("receipt_graph required",)
    if type(receipt_graph) is not dict:
        return False, ("receipt_graph must be an exact object",)
    exact_tree_error = _exact_json_tree_error(receipt_graph, path="receipt_graph")
    if exact_tree_error is not None:
        return False, (exact_tree_error,)
    graph_field_errors = _unknown_field_errors(
        receipt_graph,
        allowed=RECEIPT_GRAPH_FIELDS,
        label="receipt_graph",
    )
    errors.extend(graph_field_errors)
    if receipt_graph.get("schema") != "zeno_oracle.receipt_graph.v1":
        errors.append("receipt_graph schema must be zeno_oracle.receipt_graph.v1")

    for key in (
        "read_id",
        "aggregate_id",
        "value_hash",
        "report_leaf_root",
        "dispute_state_root",
        "feed_registry_root",
        "query_policy_root",
        "source_registry_root",
        "reporter_registry_root",
        "receipt_graph_root",
    ):
        if not _is_sha256_ref(receipt_graph.get(key, "")):
            errors.append(f"receipt_graph {key} must be a sha256 reference")

    for key in (
        "feed_registry_root",
        "query_policy_root",
        "source_registry_root",
        "reporter_registry_root",
        "receipt_graph_root",
    ):
        if getattr(authorization, key) != receipt_graph.get(key):
            errors.append(f"receipt_graph {key} does not match authorization")

    for auth_key, graph_key in (
        ("query_id", "query_id"),
        ("value_e8", "value_e8"),
        ("value_hash", "value_hash"),
        ("confidence_e8", "confidence_e8"),
        ("deviation_bps", "deviation_bps"),
        ("observed_epoch", "observed_epoch"),
        ("expires_at_epoch", "expires_at_epoch"),
        ("evidence_class", "read_evidence_class"),
    ):
        if getattr(authorization, auth_key) != receipt_graph.get(graph_key):
            errors.append(f"receipt_graph {graph_key} does not match authorization")

    observed_epoch = _non_negative_graph_int(receipt_graph, "observed_epoch", errors)
    expires_at_epoch = _non_negative_graph_int(receipt_graph, "expires_at_epoch", errors)
    reporter_count = _non_negative_graph_int(receipt_graph, "reporter_count", errors)
    min_reporters = _non_negative_graph_int(receipt_graph, "min_reporters", errors)
    source_count = _non_negative_graph_int(receipt_graph, "source_count", errors)
    control_group_count = _non_negative_graph_int(receipt_graph, "reporter_control_group_count", errors)
    _non_negative_graph_int(receipt_graph, "confidence_e8", errors)
    deviation_bps = _non_negative_graph_int(receipt_graph, "deviation_bps", errors)
    if expires_at_epoch < observed_epoch:
        errors.append("receipt_graph expires before observed epoch")
    if deviation_bps > 10_000:
        errors.append("receipt_graph deviation_bps must be in [0, 10000]")
    if reporter_count < min_reporters:
        errors.append("receipt_graph reporter_count below min_reporters")
    if source_count < min_reporters:
        errors.append("receipt_graph source_count below min_reporters")
    if control_group_count < min_reporters:
        errors.append("receipt_graph reporter_control_group_count below min_reporters")
    if not _rank_at_least(receipt_graph.get("read_evidence_class"), "O3"):
        errors.append("receipt_graph read_evidence_class below O3")
    if not _rank_at_least(receipt_graph.get("aggregate_evidence_class"), "O3"):
        errors.append("receipt_graph aggregate_evidence_class below O3")

    included_report_ids = receipt_graph.get("included_report_ids")
    if type(included_report_ids) is not list or not included_report_ids:
        errors.append("receipt_graph included_report_ids must be a non-empty list")
        included_report_set: set[str] = set()
    elif any(type(item) is not str or not item for item in included_report_ids):
        errors.append("receipt_graph included_report_ids must contain non-empty strings")
        included_report_set = set()
    else:
        included_report_set = set(included_report_ids)
        if len(included_report_set) != len(included_report_ids):
            errors.append("receipt_graph included_report_ids must be distinct")
    included_source_ids = receipt_graph.get("included_source_ids")
    if type(included_source_ids) is not list or not included_source_ids:
        errors.append("receipt_graph included_source_ids must be a non-empty list")
    elif any(type(item) is not str or not item for item in included_source_ids):
        errors.append("receipt_graph included_source_ids must contain non-empty strings")
    elif len(set(included_source_ids)) != len(included_source_ids):
        errors.append("receipt_graph included_source_ids must be distinct")

    disputed_report_ids = receipt_graph.get("disputed_report_ids")
    if type(disputed_report_ids) is not list:
        errors.append("receipt_graph disputed_report_ids must be a list")
    elif any(type(item) is not str or not item for item in disputed_report_ids):
        errors.append("receipt_graph disputed_report_ids must contain non-empty strings")
    elif disputed_report_ids:
        errors.append("receipt_graph must not include disputed reports")

    report_leaf_commitments = receipt_graph.get("report_leaf_commitments")
    if type(report_leaf_commitments) is not list or not report_leaf_commitments:
        errors.append("receipt_graph report_leaf_commitments must be a non-empty list")
    else:
        leaf_report_ids: list[str] = []
        leaf_source_ids: list[str] = []
        leaf_control_group_ids: list[str] = []
        for index, leaf in enumerate(report_leaf_commitments):
            if type(leaf) is not dict:
                errors.append(f"receipt_graph report_leaf_commitments[{index}] must be an exact object")
                continue
            leaf_field_errors = _unknown_field_errors(
                leaf,
                allowed=REPORT_LEAF_FIELDS,
                label=f"receipt_graph report_leaf_commitments[{index}]",
            )
            errors.extend(leaf_field_errors)
            source_state_at_submit = leaf.get("source_state_at_submit")
            if source_state_at_submit is not None:
                if type(source_state_at_submit) is not dict:
                    errors.append(
                        "receipt_graph report_leaf_commitments"
                        f"[{index}] source_state_at_submit must be an exact object"
                    )
                else:
                    source_field_errors = _unknown_field_errors(
                        source_state_at_submit,
                        allowed=SOURCE_STATE_AT_SUBMIT_FIELDS,
                        label=(
                            "receipt_graph report_leaf_commitments"
                            f"[{index}] source_state_at_submit"
                        ),
                    )
                    errors.extend(source_field_errors)
            report_id_obj = leaf.get("report_id")
            source_id_obj = leaf.get("source_id")
            control_group_id_obj = leaf.get("control_group_id", leaf.get("reporter_id"))
            report_id = report_id_obj if type(report_id_obj) is str else ""
            source_id = source_id_obj if type(source_id_obj) is str else ""
            control_group_id = control_group_id_obj if type(control_group_id_obj) is str else ""
            if not report_id:
                errors.append(
                    f"receipt_graph report_leaf_commitments[{index}] report_id must be a non-empty string"
                )
            if not source_id:
                errors.append(
                    f"receipt_graph report leaf {report_id or index} source_id must be a non-empty string"
                )
            if not control_group_id:
                errors.append(
                    f"receipt_graph report leaf {report_id or index} control_group_id must be a non-empty string"
                )
            leaf_report_ids.append(report_id)
            leaf_source_ids.append(source_id)
            leaf_control_group_ids.append(control_group_id)
            _require_active_leaf_bool(leaf, errors, report_id=report_id)
            if type(leaf.get("slash_state")) is not str or leaf.get("slash_state") != "clear":
                errors.append(f"receipt_graph report leaf {report_id} slash_state not clear")
            if ("bond_e8" in leaf) == ("bond_amount_e8" in leaf):
                errors.append(
                    f"receipt_graph report leaf {report_id} must contain exactly one bond field"
                )
            bond_key = "bond_e8" if "bond_e8" in leaf else "bond_amount_e8"
            bond_e8 = _non_negative_leaf_int(leaf, bond_key, errors, report_id=report_id)
            required_bond_e8 = _non_negative_leaf_int(leaf, "required_bond_e8", errors, report_id=report_id)
            if bond_e8 < required_bond_e8:
                errors.append(f"receipt_graph report leaf {report_id} bond below required")
        if leaf_report_ids != sorted(leaf_report_ids):
            errors.append("receipt_graph report_leaf_commitments must be sorted by report_id")
        if included_report_set and set(leaf_report_ids) != included_report_set:
            errors.append("receipt_graph report_leaf_commitments must match included_report_ids")
        if type(included_source_ids) is list and set(included_source_ids) != set(leaf_source_ids):
            errors.append("receipt_graph report_leaf_commitments must match included_source_ids")
        if len(leaf_report_ids) != reporter_count:
            errors.append("receipt_graph reporter_count does not match report_leaf_commitments")
        if len(set(leaf_source_ids)) != source_count:
            errors.append("receipt_graph source_count does not match distinct report leaf sources")
        if len(set(leaf_control_group_ids)) != control_group_count:
            errors.append("receipt_graph reporter_control_group_count does not match distinct report leaf control groups")
        if len(set(leaf_control_group_ids)) < min_reporters:
            errors.append("receipt_graph distinct control groups below min_reporters")
        expected_report_leaf_root = semantic_hash(
            "zeno_oracle.report_leaf_root.v1",
            {"reports": report_leaf_commitments},
        )
        if receipt_graph.get("report_leaf_root") != expected_report_leaf_root:
            errors.append("receipt_graph report_leaf_root mismatch")

    body = dict(receipt_graph)
    receipt_graph_root = body.pop("receipt_graph_root", None)
    expected_receipt_graph_root = semantic_hash("zeno_oracle.receipt_graph.v1", body)
    if receipt_graph_root != expected_receipt_graph_root:
        errors.append("receipt_graph_root mismatch")
    if authorization.receipt_graph_root != expected_receipt_graph_root:
        errors.append("authorization receipt_graph_root does not match terminal graph")
    return not errors, tuple(errors)


def _strict_int_for_verifier(value: Any, *, name: str, errors: list[str]) -> int:
    if type(value) is not int:
        errors.append(f"{name} must be an int")
        return 0
    return value


def verify_opaque_authorization(
    authorization: OracleAuthorization,
    runtime: RuntimeActionFacts,
) -> tuple[bool, tuple[str, ...]]:
    """Legacy comparison model: match opaque identifiers but not typed semantics."""

    errors: list[str] = []
    now_epoch = _strict_int_for_verifier(runtime.now_epoch, name="now_epoch", errors=errors)
    expires_at_epoch = _strict_int_for_verifier(
        authorization.expires_at_epoch,
        name="expires_at_epoch",
        errors=errors,
    )
    if authorization.consumer_module != runtime.consumer_module:
        errors.append("consumer_module mismatch")
    if authorization.action_kind != runtime.action_kind:
        errors.append("action_kind mismatch")
    if authorization.action_id != runtime.action_id:
        errors.append("action_id mismatch")
    if authorization.profile_id != runtime.profile_id:
        errors.append("profile_id mismatch")
    if authorization.query_id != runtime.query_id:
        errors.append("query_id mismatch")
    if now_epoch > expires_at_epoch:
        errors.append("authorization expired")
    return not errors, tuple(errors)


def verify_typed_authorization(
    authorization: OracleAuthorization,
    runtime: RuntimeActionFacts,
) -> tuple[bool, tuple[str, ...]]:
    """Typed comparison required for critical Oracle consumers."""

    ok, opaque_errors = verify_opaque_authorization(authorization, runtime)
    errors = list(opaque_errors)
    runtime_now_epoch = _strict_int_for_verifier(runtime.now_epoch, name="now_epoch", errors=errors)
    observed_epoch = _strict_int_for_verifier(authorization.observed_epoch, name="observed_epoch", errors=errors)
    expires_at_epoch = _strict_int_for_verifier(authorization.expires_at_epoch, name="expires_at_epoch", errors=errors)
    confidence_e8 = _strict_int_for_verifier(authorization.confidence_e8, name="confidence_e8", errors=errors)
    deviation_bps = _strict_int_for_verifier(authorization.deviation_bps, name="deviation_bps", errors=errors)
    value_e8 = _strict_int_for_verifier(authorization.value_e8, name="value_e8", errors=errors)
    runtime_value_e8 = _strict_int_for_verifier(
        runtime.runtime_value_e8,
        name="runtime_value_e8",
        errors=errors,
    )

    if runtime_now_epoch < 0:
        errors.append("runtime now_epoch must be non-negative")
    if observed_epoch < 0:
        errors.append("observed_epoch must be non-negative")
    if expires_at_epoch < 0:
        errors.append("expires_at_epoch must be non-negative")
    if observed_epoch > expires_at_epoch:
        errors.append("observed_epoch after expires_at_epoch")
    if observed_epoch > runtime_now_epoch:
        errors.append("authorization observed in the future")
    expected_max_window = _expected_max_freshness_window_epochs(
        consumer_module=runtime.consumer_module,
        action_kind=runtime.action_kind,
        profile_id=runtime.profile_id,
    )
    max_window: int | None = None
    if runtime.max_freshness_window_epochs is None:
        max_window = expected_max_window
    elif isinstance(runtime.max_freshness_window_epochs, bool) or not isinstance(
        runtime.max_freshness_window_epochs,
        int,
    ):
        errors.append("max_freshness_window_epochs must be a non-negative int")
    else:
        max_window = int(runtime.max_freshness_window_epochs)
        if max_window < 0:
            errors.append("max_freshness_window_epochs must be a non-negative int")
        if expected_max_window is not None and max_window > expected_max_window:
            errors.append("runtime freshness window exceeds critical profile")
    if max_window is not None and max_window >= 0:
        if expires_at_epoch - observed_epoch > max_window:
            errors.append("authorization freshness window exceeds runtime profile")
        if runtime_now_epoch - observed_epoch > max_window:
            errors.append("authorization observed_epoch outside runtime freshness window")
    if confidence_e8 < 0:
        errors.append("confidence_e8 must be non-negative")
    if deviation_bps < 0 or deviation_bps > 10_000:
        errors.append("deviation_bps must be in [0, 10000]")
    evidence_rank = EVIDENCE_RANK.get(authorization.evidence_class)
    if evidence_rank is None:
        errors.append("evidence_class must be one of O0..O5")
    elif evidence_rank < EVIDENCE_RANK["O3"]:
        errors.append("evidence_class below required O3")
    if authorization.action_facts_hash != runtime.action_facts_hash:
        errors.append("action_facts_hash mismatch")
    if authorization.pre_state_hash != runtime.pre_state_hash:
        errors.append("pre_state_hash mismatch")
    if value_e8 != runtime_value_e8:
        errors.append("runtime_value_e8 mismatch")
    expected_value_hash = oracle_value_hash(
        query_id=authorization.query_id,
        value_e8=value_e8,
        observed_epoch=observed_epoch,
    )
    if authorization.value_hash != expected_value_hash:
        errors.append("value_hash does not bind query_id/value_e8/observed_epoch")
    for key, value in (
        ("action_id", authorization.action_id),
        ("action_facts_hash", authorization.action_facts_hash),
        ("value_hash", authorization.value_hash),
        ("feed_registry_root", authorization.feed_registry_root),
        ("query_policy_root", authorization.query_policy_root),
        ("source_registry_root", authorization.source_registry_root),
        ("reporter_registry_root", authorization.reporter_registry_root),
        ("receipt_graph_root", authorization.receipt_graph_root),
    ):
        if not _is_sha256_ref(value):
            errors.append(f"{key} must be a sha256 reference")
    return bool(ok and not errors), tuple(errors)


def _require_str(obj: Mapping[str, Any], key: str) -> str:
    value = obj.get(key)
    if type(value) is not str or not value:
        raise ValueError(f"{key} must be a non-empty string")
    return value


def _require_int(obj: Mapping[str, Any], key: str) -> int:
    value = obj.get(key)
    if type(value) is not int:
        raise ValueError(f"{key} must be an int")
    return value


def authorization_from_obj(obj: Mapping[str, Any]) -> OracleAuthorization:
    if type(obj) is not dict:
        raise ValueError("authorization must be an exact object")
    _require_closed_fields(obj, allowed=AUTHORIZATION_FIELDS, label="authorization")
    return OracleAuthorization(
        consumer_module=_require_str(obj, "consumer_module"),
        action_kind=_require_str(obj, "action_kind"),
        action_id=_require_str(obj, "action_id"),
        action_facts_hash=_require_str(obj, "action_facts_hash"),
        pre_state_hash=_require_str(obj, "pre_state_hash"),
        profile_id=_require_str(obj, "profile_id"),
        query_id=_require_str(obj, "query_id"),
        value_e8=_require_int(obj, "value_e8"),
        value_hash=_require_str(obj, "value_hash"),
        confidence_e8=_require_int(obj, "confidence_e8"),
        deviation_bps=_require_int(obj, "deviation_bps"),
        observed_epoch=_require_int(obj, "observed_epoch"),
        expires_at_epoch=_require_int(obj, "expires_at_epoch"),
        feed_id=_require_str(obj, "feed_id"),
        feed_registry_root=_require_str(obj, "feed_registry_root"),
        query_policy_root=_require_str(obj, "query_policy_root"),
        source_registry_root=_require_str(obj, "source_registry_root"),
        reporter_registry_root=_require_str(obj, "reporter_registry_root"),
        evidence_class=_require_str(obj, "evidence_class"),
        economic_envelope_id=_require_str(obj, "economic_envelope_id"),
        receipt_graph_root=_require_str(obj, "receipt_graph_root"),
    )


def runtime_from_obj(obj: Mapping[str, Any]) -> RuntimeActionFacts:
    if type(obj) is not dict:
        raise ValueError("runtime_action must be an exact object")
    _require_closed_fields(obj, allowed=RUNTIME_ACTION_FIELDS, label="runtime_action")
    runtime_notional_value = obj.get("runtime_notional_value_e8")
    if runtime_notional_value is not None:
        if type(runtime_notional_value) is not int:
            raise ValueError("runtime_notional_value_e8 must be an int when present")
    max_freshness_window_epochs = obj.get("max_freshness_window_epochs")
    if max_freshness_window_epochs is not None:
        if type(max_freshness_window_epochs) is not int:
            raise ValueError("max_freshness_window_epochs must be an int when present")
    consumer_module = _require_str(obj, "consumer_module")
    action_kind = _require_str(obj, "action_kind")
    profile_id = _require_str(obj, "profile_id")
    if max_freshness_window_epochs is None:
        max_freshness_window_epochs = _expected_max_freshness_window_epochs(
            consumer_module=consumer_module,
            action_kind=action_kind,
            profile_id=profile_id,
        )
    return RuntimeActionFacts(
        consumer_module=consumer_module,
        action_kind=action_kind,
        action_id=_require_str(obj, "action_id"),
        action_facts_hash=_require_str(obj, "action_facts_hash"),
        pre_state_hash=_require_str(obj, "pre_state_hash"),
        profile_id=profile_id,
        query_id=_require_str(obj, "query_id"),
        runtime_value_e8=_require_int(obj, "runtime_value_e8"),
        now_epoch=_require_int(obj, "now_epoch"),
        runtime_notional_value_e8=runtime_notional_value,
        max_freshness_window_epochs=max_freshness_window_epochs,
    )


def _authorization_obj_from_payload(payload: Mapping[str, Any]) -> Mapping[str, Any]:
    maybe_nested = payload.get("authorization")
    if maybe_nested is None:
        return payload
    if type(maybe_nested) is dict:
        return maybe_nested
    raise ValueError("authorization must be an exact object")


def check_authorization_for_runtime(
    authorization_payload: Mapping[str, Any],
    runtime: RuntimeActionFacts,
    *,
    require_receipt_graph: bool = False,
    require_economic_envelope: bool = False,
) -> dict[str, Any]:
    """Check one authorization against runtime facts supplied by the consumer.

    Critical adapters should use this shape instead of trusting a bundle's
    embedded `runtime_action`, because the adapter must compare against the
    action facts it is actually about to execute.
    """

    if type(authorization_payload) is not dict:
        raise ValueError("authorization payload must be an exact object")
    if any(type(key) is not str for key in authorization_payload):
        raise ValueError("authorization payload field names must be exact strings")
    if "authorization" in authorization_payload:
        _require_closed_fields(
            authorization_payload,
            allowed=AUTHORIZATION_BUNDLE_FIELDS,
            label="authorization bundle",
        )
    authorization = authorization_from_obj(_authorization_obj_from_payload(authorization_payload))
    opaque_ok, opaque_errors = verify_opaque_authorization(authorization, runtime)
    typed_ok, typed_errors = verify_typed_authorization(authorization, runtime)
    receipt_graph = _graph_obj_from_payload(authorization_payload)
    economic_envelope = _economic_envelope_obj_from_payload(authorization_payload)
    graph_ok = True
    graph_errors: tuple[str, ...] = ()
    if require_receipt_graph or receipt_graph is not None:
        graph_ok, graph_errors = verify_receipt_graph_binding(authorization, receipt_graph)
        typed_errors = tuple(list(typed_errors) + list(graph_errors))
        typed_ok = bool(typed_ok and graph_ok)
    economic_ok, economic_errors = verify_economic_envelope_binding(
        authorization,
        economic_envelope,
        receipt_graph=receipt_graph if graph_ok else None,
        runtime_notional_value_e8=runtime.runtime_notional_value_e8,
        require_economic_envelope=require_economic_envelope,
    )
    if economic_errors:
        typed_errors = tuple(list(typed_errors) + list(economic_errors))
        typed_ok = bool(typed_ok and economic_ok)
    return {
        "schema": SCHEMA,
        "opaque_ok": bool(opaque_ok),
        "typed_ok": bool(typed_ok),
        "receipt_graph_ok": bool(graph_ok),
        "economic_envelope_ok": bool(economic_ok),
        "opaque_errors": list(opaque_errors),
        "typed_errors": list(typed_errors),
        "receipt_graph_errors": list(graph_errors),
        "economic_envelope_errors": list(economic_errors),
        "authorization": asdict(authorization),
        "runtime_action": asdict(runtime),
    }


def check_authorization_payload(payload: Mapping[str, Any]) -> dict[str, Any]:
    if type(payload) is not dict:
        raise ValueError("authorization payload must be an exact object")
    _require_closed_fields(
        payload,
        allowed=AUTHORIZATION_BUNDLE_FIELDS,
        label="authorization bundle",
    )
    auth_obj = payload.get("authorization")
    runtime_obj = payload.get("runtime_action")
    if not isinstance(auth_obj, Mapping):
        raise ValueError("authorization must be an object")
    if not isinstance(runtime_obj, Mapping):
        raise ValueError("runtime_action must be an object")
    return check_authorization_for_runtime(payload, runtime_from_obj(runtime_obj))


def _check_current_dispute_status_for_critical_consumer(
    *,
    receipt_graph: Mapping[str, Any] | None,
    current_dispute_status: Mapping[str, Any] | None,
    expected_root: str | None,
    now_epoch: int,
    required: bool,
) -> tuple[bool, bool, list[str]]:
    gate_required = bool(
        required or current_dispute_status is not None or expected_root is not None
    )
    if not gate_required:
        return False, True, []
    errors: list[str] = []
    if expected_root is None:
        errors.append("current dispute status root authority required")
    if current_dispute_status is None:
        errors.append("current dispute status required")
        return True, False, errors
    included_report_ids: Any = []
    if type(receipt_graph) is dict:
        included_report_ids = receipt_graph.get("included_report_ids", [])
    dispute_check = verify_oracle_current_dispute_status_v1(
        current_dispute_status,
        expected_report_ids=included_report_ids,
        expected_root=expected_root or "",
        now_epoch=now_epoch,
    )
    errors.extend(dispute_check.errors)
    return True, not errors, errors


def check_critical_consumer_authorization(
    authorization_payload: Mapping[str, Any],
    *,
    consumer_module: str,
    action_kind: str,
    action_id: str,
    action_facts_hash: str,
    pre_state_hash: str,
    query_id: str,
    runtime_value_e8: int,
    now_epoch: int,
    runtime_notional_value_e8: int | None = None,
    profile_id: str | None = None,
    max_freshness_window_epochs: int | None = None,
    expected_receipt_graph_root: str | None = None,
    current_dispute_status: Mapping[str, Any] | None = None,
    expected_current_dispute_status_root: str | None = None,
    require_current_dispute_status: bool = False,
    require_receipt_graph: bool = True,
    require_economic_envelope: bool = True,
) -> dict[str, Any]:
    runtime_field_errors: list[str] = []
    if type(runtime_value_e8) is not int:
        runtime_field_errors.append("runtime_value_e8 must be an int")
        runtime_value_e8_int = 0
    else:
        runtime_value_e8_int = runtime_value_e8
    if type(now_epoch) is not int:
        runtime_field_errors.append("now_epoch must be an int")
        now_epoch_int = 0
    else:
        now_epoch_int = now_epoch
    runtime_notional_value_e8_int: int | None
    if runtime_notional_value_e8 is None:
        runtime_notional_value_e8_int = None
    elif type(runtime_notional_value_e8) is not int:
        runtime_field_errors.append("runtime_notional_value_e8 must be an int when present")
        runtime_notional_value_e8_int = None
    elif runtime_notional_value_e8 < 0:
        runtime_field_errors.append("runtime_notional_value_e8 must be a non-negative int")
        runtime_notional_value_e8_int = None
    else:
        runtime_notional_value_e8_int = runtime_notional_value_e8

    configured_graph_errors: list[str] = []
    if expected_receipt_graph_root is not None and not _is_sha256_ref(expected_receipt_graph_root):
        configured_graph_errors.append("expected_receipt_graph_root must be a sha256 reference")

    expected_profile = profile_id or CRITICAL_CONSUMER_PROFILES.get((consumer_module, action_kind))
    expected_max_freshness_window_epochs = max_freshness_window_epochs
    if expected_max_freshness_window_epochs is None:
        expected_max_freshness_window_epochs = _expected_max_freshness_window_epochs(
            consumer_module=consumer_module,
            action_kind=action_kind,
            profile_id=expected_profile,
        )
    if expected_profile is None:
        current_status_gate_required = bool(
            require_current_dispute_status
            or current_dispute_status is not None
            or expected_current_dispute_status_root is not None
        )
        return {
            "schema": SCHEMA,
            "opaque_ok": False,
            "typed_ok": False,
            "receipt_graph_ok": False,
            "economic_envelope_ok": False,
            "opaque_errors": ["unsupported critical consumer/action"],
            "typed_errors": [
                "unsupported critical consumer/action",
                *runtime_field_errors,
                *configured_graph_errors,
            ],
            "receipt_graph_errors": ["unsupported critical consumer/action", *configured_graph_errors],
            "economic_envelope_errors": ["unsupported critical consumer/action"],
            "authorization": dict(_authorization_obj_from_payload(authorization_payload)),
            "runtime_action": {
                "consumer_module": consumer_module,
                "action_kind": action_kind,
                "action_id": action_id,
                "action_facts_hash": action_facts_hash,
                "pre_state_hash": pre_state_hash,
                "profile_id": profile_id,
                "query_id": query_id,
                "runtime_value_e8": runtime_value_e8,
                "now_epoch": now_epoch,
                "runtime_notional_value_e8": runtime_notional_value_e8,
                "max_freshness_window_epochs": expected_max_freshness_window_epochs,
            },
            "expected_receipt_graph_root": expected_receipt_graph_root,
            "critical_consumer_profile": None,
            "critical_consumer_max_freshness_window_epochs": (
                expected_max_freshness_window_epochs
            ),
            "current_dispute_status_required": current_status_gate_required,
            "current_dispute_status_ok": False,
            "current_dispute_status_errors": (
                ["unsupported critical consumer/action"]
                if current_status_gate_required
                else []
            ),
            "expected_current_dispute_status_root": (
                expected_current_dispute_status_root
            ),
        }
    runtime = RuntimeActionFacts(
        consumer_module=consumer_module,
        action_kind=action_kind,
        action_id=action_id,
        action_facts_hash=action_facts_hash,
        pre_state_hash=pre_state_hash,
        profile_id=expected_profile,
        query_id=query_id,
        runtime_value_e8=runtime_value_e8_int,
        now_epoch=now_epoch_int,
        runtime_notional_value_e8=runtime_notional_value_e8_int,
        max_freshness_window_epochs=expected_max_freshness_window_epochs,
    )
    result = check_authorization_for_runtime(
        authorization_payload,
        runtime,
        require_receipt_graph=require_receipt_graph,
        require_economic_envelope=require_economic_envelope,
    )
    authorization = authorization_from_obj(_authorization_obj_from_payload(authorization_payload))
    typed_errors = list(result["typed_errors"])
    typed_errors.extend(runtime_field_errors)
    if (
        expected_receipt_graph_root is not None
        and not configured_graph_errors
        and authorization.receipt_graph_root != expected_receipt_graph_root
    ):
        configured_graph_errors.append("receipt_graph_root does not match configured root")
    if configured_graph_errors:
        typed_errors.extend(configured_graph_errors)
        result["receipt_graph_errors"] = [
            *list(result["receipt_graph_errors"]),
            *configured_graph_errors,
        ]
        result["receipt_graph_ok"] = False
    if authorization.profile_id != expected_profile:
        typed_errors.append("critical profile mismatch")
    (
        current_dispute_status_required,
        current_dispute_status_ok,
        current_dispute_status_errors,
    ) = _check_current_dispute_status_for_critical_consumer(
        receipt_graph=_graph_obj_from_payload(authorization_payload),
        current_dispute_status=current_dispute_status,
        expected_root=expected_current_dispute_status_root,
        now_epoch=now_epoch_int,
        required=require_current_dispute_status,
    )
    typed_errors.extend(current_dispute_status_errors)
    result["typed_errors"] = typed_errors
    result["typed_ok"] = bool(result["typed_ok"] and not typed_errors)
    result["critical_consumer_profile"] = expected_profile
    result["critical_consumer_max_freshness_window_epochs"] = expected_max_freshness_window_epochs
    result["expected_receipt_graph_root"] = expected_receipt_graph_root
    result["current_dispute_status_required"] = current_dispute_status_required
    result["current_dispute_status_ok"] = current_dispute_status_ok
    result["current_dispute_status_errors"] = current_dispute_status_errors
    result["expected_current_dispute_status_root"] = expected_current_dispute_status_root
    return result
