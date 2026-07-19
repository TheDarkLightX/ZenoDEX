"""Typed ZenoOracle authorization checks for trigger execution."""

from __future__ import annotations

import hashlib
from dataclasses import asdict, dataclass
from typing import Any, Callable, Mapping

from ..state.canonical import canonical_json_bytes
from .oracle_aggregate_adapter_boundary import verify_aggregate_adapter_bridge
from .zeno_oracle_authorization import check_critical_consumer_authorization, semantic_hash

TriggerOracleAdapterBridgeVerifier = Callable[[Mapping[str, Any]], Any]

_ORACLE_CONSUMER_PROFILE_SCHEMA = "zenodex.oracle.consumer_profile.v1"
_ORACLE_TRIGGER_REFERENCE_QUERY_ID = (
    "sha256:" + hashlib.sha256(b"zenodex.oracle.query.trigger.reference_price_e8").hexdigest()
)


def _oracle_consumer_profile_id(*, action_kind: str, max_freshness_window_epochs: int) -> str:
    payload = {
        "schema": _ORACLE_CONSUMER_PROFILE_SCHEMA,
        "consumer_module": "zenodex.trigger",
        "action_kind": action_kind,
        "query_id": _ORACLE_TRIGGER_REFERENCE_QUERY_ID,
        "required_evidence_floor": "O3",
        "max_freshness_window_epochs": int(max_freshness_window_epochs),
        "critical": True,
    }
    return "sha256:" + hashlib.sha256(canonical_json_bytes(payload)).hexdigest()


_ORACLE_TRIGGER_EXECUTE_PROFILE_ID = _oracle_consumer_profile_id(
    action_kind="execute_trigger",
    max_freshness_window_epochs=2,
)


@dataclass(frozen=True)
class TriggerExecutionFacts:
    trigger_id: str
    owner_pubkey: str
    action_kind: str
    query_id: str
    observed_value_e8: int
    trigger_price_e8: int
    condition: str
    current_epoch: int
    valid_from_epoch: int
    valid_until_epoch: int
    max_oracle_staleness_epochs: int
    order_amount: int
    asset_in: str
    asset_out: str
    pre_state_hash: str | None = None

    def __post_init__(self) -> None:
        _require_non_empty_str(self.trigger_id, name="trigger_id")
        _require_non_empty_str(self.owner_pubkey, name="owner_pubkey")
        _require_non_empty_str(self.action_kind, name="action_kind")
        _require_non_empty_str(self.query_id, name="query_id")
        _require_int(self.observed_value_e8, name="observed_value_e8")
        _require_int(self.trigger_price_e8, name="trigger_price_e8")
        _require_non_empty_str(self.condition, name="condition")
        _require_int(self.current_epoch, name="current_epoch", non_negative=True)
        _require_int(self.valid_from_epoch, name="valid_from_epoch", non_negative=True)
        _require_int(self.valid_until_epoch, name="valid_until_epoch", non_negative=True)
        _require_int(
            self.max_oracle_staleness_epochs,
            name="max_oracle_staleness_epochs",
            non_negative=True,
        )
        _require_int(self.order_amount, name="order_amount", non_negative=True)
        if self.order_amount <= 0:
            raise ValueError("order_amount must be positive")
        _require_non_empty_str(self.asset_in, name="asset_in")
        _require_non_empty_str(self.asset_out, name="asset_out")
        if self.pre_state_hash is not None:
            _require_non_empty_str(self.pre_state_hash, name="pre_state_hash")


def _require_non_empty_str(value: Any, *, name: str) -> str:
    if not isinstance(value, str) or not value:
        raise ValueError(f"{name} must be a non-empty string")
    return value


def _require_int(value: Any, *, name: str, non_negative: bool = False) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise ValueError(f"{name} must be an int")
    out = int(value)
    if non_negative and out < 0:
        raise ValueError(f"{name} must be non-negative")
    return out


def _condition_satisfied(*, condition: str, observed_value_e8: int, trigger_price_e8: int) -> bool:
    cond = condition.strip().lower()
    if cond in {"gte", ">=", "at_or_above"}:
        return int(observed_value_e8) >= int(trigger_price_e8)
    if cond in {"lte", "<=", "at_or_below"}:
        return int(observed_value_e8) <= int(trigger_price_e8)
    raise ValueError("condition must be gte or lte")


def trigger_execution_facts_from_obj(obj: Mapping[str, Any]) -> TriggerExecutionFacts:
    return TriggerExecutionFacts(
        trigger_id=_require_non_empty_str(obj.get("trigger_id"), name="trigger_id"),
        owner_pubkey=_require_non_empty_str(obj.get("owner_pubkey"), name="owner_pubkey"),
        action_kind=_require_non_empty_str(obj.get("action_kind", "execute"), name="action_kind"),
        query_id=_require_non_empty_str(obj.get("query_id"), name="query_id"),
        observed_value_e8=_require_int(obj.get("observed_value_e8"), name="observed_value_e8"),
        trigger_price_e8=_require_int(obj.get("trigger_price_e8"), name="trigger_price_e8"),
        condition=_require_non_empty_str(obj.get("condition"), name="condition"),
        current_epoch=_require_int(obj.get("current_epoch"), name="current_epoch", non_negative=True),
        valid_from_epoch=_require_int(obj.get("valid_from_epoch"), name="valid_from_epoch", non_negative=True),
        valid_until_epoch=_require_int(obj.get("valid_until_epoch"), name="valid_until_epoch", non_negative=True),
        max_oracle_staleness_epochs=_require_int(
            obj.get("max_oracle_staleness_epochs"),
            name="max_oracle_staleness_epochs",
            non_negative=True,
        ),
        order_amount=_require_int(obj.get("order_amount"), name="order_amount", non_negative=True),
        asset_in=_require_non_empty_str(obj.get("asset_in"), name="asset_in"),
        asset_out=_require_non_empty_str(obj.get("asset_out"), name="asset_out"),
        pre_state_hash=(None if obj.get("pre_state_hash") is None else _require_non_empty_str(obj.get("pre_state_hash"), name="pre_state_hash")),
    )


def trigger_execute_runtime_facts(facts: TriggerExecutionFacts) -> dict[str, Any]:
    if facts.action_kind != "execute":
        raise ValueError("trigger action_kind must be execute")
    if facts.asset_in == facts.asset_out:
        raise ValueError("trigger assets must differ")
    if facts.valid_from_epoch > facts.valid_until_epoch:
        raise ValueError("valid_from_epoch must be <= valid_until_epoch")
    if not (facts.valid_from_epoch <= facts.current_epoch <= facts.valid_until_epoch):
        raise ValueError("trigger execution outside valid window")
    if not _condition_satisfied(
        condition=facts.condition,
        observed_value_e8=facts.observed_value_e8,
        trigger_price_e8=facts.trigger_price_e8,
    ):
        raise ValueError("trigger condition not satisfied")

    payload = asdict(facts)
    payload["condition"] = facts.condition.strip().lower()
    payload["consumer_module"] = "zenodex.trigger"
    payload["trigger_action_kind"] = facts.action_kind
    payload["action_kind"] = "execute_trigger"
    pre_state_hash = facts.pre_state_hash or semantic_hash("zenodex.trigger.execute.pre_state.v1", payload)
    payload["pre_state_hash"] = pre_state_hash
    action_facts_hash = semantic_hash("zenodex.trigger.execute.facts.v1", payload)
    action_id = semantic_hash(
        "zenodex.trigger.execute.action.v1",
        {
            "action_facts_hash": action_facts_hash,
            "trigger_id": facts.trigger_id,
        },
    )
    return {
        "action_facts_hash": action_facts_hash,
        "action_id": action_id,
        "now_epoch": int(facts.current_epoch),
        "pre_state_hash": pre_state_hash,
        "query_id": facts.query_id,
        "runtime_value_e8": int(facts.observed_value_e8),
    }


def _adapter_result_get(result: Any, key: str) -> Any:
    if isinstance(result, Mapping):
        return result.get(key)
    to_json = getattr(result, "to_json_obj", None)
    if callable(to_json):
        obj = to_json()
        if isinstance(obj, Mapping):
            return obj.get(key)
    return getattr(result, key, None)


def _adapter_error_summary(result: Any) -> str:
    errors = _adapter_result_get(result, "errors")
    if isinstance(errors, list) and errors:
        return "; ".join(str(item) for item in errors[:5])
    status = _adapter_result_get(result, "status")
    return str(status or "unknown")


def _default_oracle_adapter_bridge_verifier(bridge: Mapping[str, Any]) -> Any:
    return verify_aggregate_adapter_bridge(bridge)


def check_trigger_execute_oracle_adapter_bridge(
    *,
    bridge: Mapping[str, Any] | None,
    facts: TriggerExecutionFacts,
    required: bool = True,
    bridge_verifier: TriggerOracleAdapterBridgeVerifier | None = None,
) -> str | None:
    if bridge is None:
        if required:
            return "execute_trigger requires oracle_adapter_bridge"
        return None
    if not isinstance(bridge, Mapping):
        return "oracle_adapter_bridge must be an object"
    if facts.query_id != _ORACLE_TRIGGER_REFERENCE_QUERY_ID:
        return "trigger facts query mismatch"

    verifier = bridge_verifier or _default_oracle_adapter_bridge_verifier
    try:
        result = verifier(bridge)
    except Exception as exc:  # pragma: no cover - defensive fail-closed boundary
        return f"oracle_adapter_bridge verifier error: {type(exc).__name__}"

    if _adapter_result_get(result, "status") != "accepted":
        return f"oracle_adapter_bridge rejected: {_adapter_error_summary(result)}"
    if _adapter_result_get(result, "consumer_module") != "zenodex.trigger":
        return "oracle_adapter_bridge consumer mismatch"
    if _adapter_result_get(result, "action_kind") != "execute_trigger":
        return "oracle_adapter_bridge action mismatch"
    if _adapter_result_get(result, "query_id") != _ORACLE_TRIGGER_REFERENCE_QUERY_ID:
        return "oracle_adapter_bridge query mismatch"
    if _adapter_result_get(result, "profile_id") != _ORACLE_TRIGGER_EXECUTE_PROFILE_ID:
        return "oracle_adapter_bridge profile mismatch"
    expected_action_id = str(trigger_execute_runtime_facts(facts)["action_id"])
    if _adapter_result_get(result, "action_id") != expected_action_id:
        return "oracle_adapter_bridge action_id mismatch"
    return None


def check_trigger_execute_oracle_authorization(
    *,
    authorization_payload: Mapping[str, Any],
    facts: TriggerExecutionFacts,
) -> dict[str, Any]:
    runtime = trigger_execute_runtime_facts(facts)
    return check_critical_consumer_authorization(
        authorization_payload,
        consumer_module="zenodex.trigger",
        action_kind="execute_trigger",
        action_id=str(runtime["action_id"]),
        action_facts_hash=str(runtime["action_facts_hash"]),
        pre_state_hash=str(runtime["pre_state_hash"]),
        profile_id=_ORACLE_TRIGGER_EXECUTE_PROFILE_ID,
        query_id=str(runtime["query_id"]),
        runtime_value_e8=int(runtime["runtime_value_e8"]),
        now_epoch=int(runtime["now_epoch"]),
    )
