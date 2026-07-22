from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping

REJECT_OK = "Ok"
REJECT_INTENT_FIELDS_INVALID = "IntentFieldsInvalid"
REJECT_EXPLICIT_FIELDS_INVALID = "ExplicitFieldsInvalid"


@dataclass(frozen=True)
class DexIntentAuthShapeGateOutcome:
    intent_object_mode: bool
    mapping_mode: bool
    fields_object_ok: bool
    explicit_fields_present: bool
    explicit_fields_mapping_ok: bool
    include_salt: bool
    use_object_fields: bool
    use_explicit_mapping_fields: bool
    use_transport_flattened_fields: bool
    shape_ok: bool
    reject_code: str
    checks: Mapping[str, bool]


def _require_flag(value: Any, *, name: str) -> bool:
    if isinstance(value, bool):
        return bool(value)
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be a bool or 0/1 int")
    if value not in (0, 1):
        raise ValueError(f"{name} must be 0 or 1")
    return bool(value)


def evaluate_dex_intent_auth_shape_gate(
    *,
    intent_object_mode: Any,
    fields_object_ok: Any,
    explicit_fields_present: Any,
    explicit_fields_mapping_ok: Any,
    salt_present: Any,
) -> DexIntentAuthShapeGateOutcome:
    object_mode = _require_flag(intent_object_mode, name="intent_object_mode")
    fields_ok = _require_flag(fields_object_ok, name="fields_object_ok")
    explicit_present = _require_flag(explicit_fields_present, name="explicit_fields_present")
    explicit_mapping_ok = _require_flag(
        explicit_fields_mapping_ok,
        name="explicit_fields_mapping_ok",
    )
    salt = _require_flag(salt_present, name="salt_present")

    mapping_mode = not object_mode
    use_object_fields = object_mode
    use_explicit_mapping_fields = bool(mapping_mode and explicit_present)
    use_transport_flattened_fields = bool(mapping_mode and not explicit_present)
    include_salt = salt

    checks = {
        "intent_object_mode": object_mode,
        "fields_object_ok": fields_ok,
        "explicit_fields_present": explicit_present,
        "explicit_fields_mapping_ok": explicit_mapping_ok,
        "salt_present": salt,
    }

    if object_mode and not fields_ok:
        reject_code = REJECT_INTENT_FIELDS_INVALID
    elif use_explicit_mapping_fields and not explicit_mapping_ok:
        reject_code = REJECT_EXPLICIT_FIELDS_INVALID
    else:
        reject_code = REJECT_OK

    return DexIntentAuthShapeGateOutcome(
        intent_object_mode=object_mode,
        mapping_mode=mapping_mode,
        fields_object_ok=fields_ok,
        explicit_fields_present=explicit_present,
        explicit_fields_mapping_ok=explicit_mapping_ok,
        include_salt=include_salt,
        use_object_fields=use_object_fields,
        use_explicit_mapping_fields=use_explicit_mapping_fields,
        use_transport_flattened_fields=use_transport_flattened_fields,
        shape_ok=bool(reject_code == REJECT_OK),
        reject_code=reject_code,
        checks=checks,
    )


def dex_intent_auth_shape_gate_error(outcome: DexIntentAuthShapeGateOutcome) -> str | None:
    if outcome.reject_code == REJECT_INTENT_FIELDS_INVALID:
        return "intent.fields must be a mapping"
    if outcome.reject_code == REJECT_EXPLICIT_FIELDS_INVALID:
        return "intent.fields must be a mapping when present"
    return None
