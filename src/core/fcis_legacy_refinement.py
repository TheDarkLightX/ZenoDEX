"""Pure, unmounted legacy-to-exact refinement evaluator for M5-P4B0.

Every embedded byte field is admitted by the closed P4B0 grammar before this
module observes its projection.  The evaluator then checks domain semantics,
same-lineage commitments, and the directional legacy-refinement relation.  It
never mounts authority, mutates a state value, or reads ambient process state.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import NoReturn, TypeAlias, cast, final

from ..state.canonical import (
    canonical_json_bytes,
    domain_sep_bytes,
    encode_bytes,
    encode_uvarint,
    sha256_hex,
)
from ..state.fcis_execution_context import admit_fcis_step_execution_context_v1
from ..state.fcis_execution_context_codec import encode_fcis_execution_context_v1
from ..state.fcis_execution_context_values import (
    FCIS_STEP_CONTEXT_SCHEMA_ID_V1,
    FCISFeeSplitPolicySourceV1,
    FCISSettlementExecutionContextSourceV1,
    FCISSettlementModeV1,
    FCISStepExecutionContextSourceV1,
    FCISStepExecutionContextV1,
)
from ..state.lp_duration_policy_schema import LPDurationPolicyAdmissionSourceV1
from ..state.owned_json import JsonProjectionV1
from ..state.snapshot_combinators import AdmitOk
from ..state.state_snapshot_schema import StateEnumTagV1, state_enum_tag_ordinal_v1
from .fcis_commit_bundle_values import FCIS_COMMIT_BUNDLE_SCHEMA_ID_V1
from .fcis_decision_values import (
    FCIS_ACCEPTANCE_RECEIPT_SCHEMA_ID_V1,
    FCIS_AUTHORITY_CODEC_VERSION_V1,
    FCIS_AUTHORITY_SCHEMA_VERSION_V1,
    FCIS_REJECTION_RECEIPT_SCHEMA_ID_V1,
    FCISRejectCodeV1,
)
from .fcis_legacy_refinement_admission import (
    admit_refinement_command_bytes_v1,
    admit_refinement_component_bytes_v1,
    project_admitted_refinement_value_v1,
    revalidate_observation_pair_v1,
)
from .fcis_legacy_refinement_policy import (
    BUDGET_HASH_V1,
    EXACT_ALGORITHM_ID_V1,
    LEGACY_ALGORITHM_ID_V1,
    POLICY_HASH_V1,
    POLICY_VERSION_V1,
    SEMANTIC_STATE_FIELD_ORDER_V1,
    lookup_rejection_mapping_v1,
    lookup_version_delta_v1,
)
from .fcis_legacy_refinement_schema import (
    RefinementComponentKindV1,
    RefinementResourceKindV1,
    check_refinement_resource_limit_v1,
)
from .fcis_legacy_refinement_values import (
    AppliedVersionDeltaV1,
    BoundObservationV1,
    CanonicalBytesFieldV1,
    CanonicalDigestFieldV1,
    EvidenceFieldStatusV1,
    FieldPathV1,
    InvalidEvidenceV1,
    MismatchV1,
    ObservationPairV1,
    ObservationResultKindV1,
    ObservationValueV1,
    RefinementDecisionV1,
    RefinementWitnessV1,
    RefinesV1,
)
from .fcis_outbox_values import OutboxEffectKindV1
from .fcis_step_evaluation_values import (
    FCIS_STEP_EVALUATOR_ALGORITHM_ID_V1,
    FCIS_STEP_EVALUATOR_ALGORITHM_VERSION_V1,
    FCISStepEvaluationPhaseV1,
)
from .fcis_support_profile_v5 import FCIS_SUPPORT_COMMAND_DOMAIN_V5
from .fcis_transition_values import (
    FCIS_COMMIT_PLAN_SCHEMA_ID_V1,
    FCIS_DEX_PATCH_SCHEMA_ID_V1,
)

JsonObjectV1: TypeAlias = dict[str, JsonProjectionV1]
JsonArrayV1: TypeAlias = list[JsonProjectionV1]
_POOL_STATUS_LABELS_V1 = ("ACTIVE", "FROZEN", "DISABLED")
_CONTEXT_HASH_DOMAIN_V1 = "fcis_step_execution_context"
_EFFECT_IDENTITY_DOMAIN_V1 = "zenodex/fcis/outbox-effect-identity"
_IDEMPOTENCY_DOMAIN_V1 = "zenodex/fcis/outbox-idempotency"


@final
class _EvidenceFault(Exception):
    def __init__(self, code: str, path: FieldPathV1) -> None:
        super().__init__(code)
        self.code = code
        self.path = path


@final
@dataclass(frozen=True, slots=True)
class _AcceptedEvidenceV1:
    pre_state: JsonObjectV1
    legacy_state: JsonObjectV1
    exact_state: JsonObjectV1
    settlement_bytes: bytes


def _fault(code: str, path: FieldPathV1) -> NoReturn:
    raise _EvidenceFault(code, path)


def _object(value: JsonProjectionV1, path: FieldPathV1) -> JsonObjectV1:
    if type(value) is not dict:
        _fault("admitted_object_projection_failed", path)
    return cast(JsonObjectV1, value)


def _array(value: JsonProjectionV1, path: FieldPathV1) -> JsonArrayV1:
    if type(value) is not list:
        _fault("admitted_array_projection_failed", path)
    return value


def _field(value: JsonObjectV1, name: str, path: FieldPathV1) -> JsonProjectionV1:
    try:
        return value[name]
    except KeyError:
        _fault("admitted_field_projection_failed", path + (name,))


def _component(
    kind: RefinementComponentKindV1,
    raw: bytes,
    path: FieldPathV1,
) -> JsonProjectionV1:
    admitted = admit_refinement_component_bytes_v1(kind, raw)
    if type(admitted) is InvalidEvidenceV1:
        _fault(admitted.code, path + admitted.path)
    if type(admitted) is not AdmitOk:
        _fault("component_admission_impossible_result", path)
    exact_admitted = cast(AdmitOk, admitted)
    try:
        return project_admitted_refinement_value_v1(exact_admitted.value)
    except (TypeError, ValueError):
        _fault("component_projection_failed", path)


def _command(command_kind: str, raw: bytes, index: int) -> JsonObjectV1:
    admitted = admit_refinement_command_bytes_v1(command_kind, raw)
    path: FieldPathV1 = ("binding", "command_bytes", index)
    if type(admitted) is InvalidEvidenceV1:
        _fault(admitted.code, path + admitted.path)
    if type(admitted) is not AdmitOk:
        _fault("command_admission_impossible_result", path)
    exact_admitted = cast(AdmitOk, admitted)
    projected = project_admitted_refinement_value_v1(exact_admitted.value)
    return _object(projected, path)


def _present_bytes(field: CanonicalBytesFieldV1, path: FieldPathV1) -> bytes:
    if field.status is not EvidenceFieldStatusV1.PRESENT or field.value is None:
        _fault("required_exact_bytes_absent", path)
    return field.value


def _present_digest(field: CanonicalDigestFieldV1, path: FieldPathV1) -> str:
    if field.status is not EvidenceFieldStatusV1.PRESENT or field.value is None:
        _fault("required_exact_digest_absent", path)
    return field.value


def _require_absent_bytes(field: CanonicalBytesFieldV1, path: FieldPathV1) -> None:
    if field.status is not EvidenceFieldStatusV1.ABSENT or field.value is not None:
        _fault("rejection_carries_committable_bytes", path)


def _canonical(value: JsonProjectionV1, path: FieldPathV1) -> bytes:
    try:
        return canonical_json_bytes(value)
    except (TypeError, ValueError, UnicodeEncodeError):
        _fault("canonical_projection_failed", path)


def _compact_value(value: JsonProjectionV1) -> bytes:
    encoded = canonical_json_bytes(value)
    if (
        check_refinement_resource_limit_v1(
            RefinementResourceKindV1.MISMATCH_PAYLOAD_BYTES,
            len(encoded),
        )
        is None
    ):
        return encoded
    return canonical_json_bytes({"bytes": len(encoded), "sha256": sha256_hex(encoded)})


def _claim_root(schema_id: str, payload: bytes) -> str:
    return sha256_hex(domain_sep_bytes(schema_id, version=1) + payload)


def _raw32(value: str) -> bytes:
    return bytes.fromhex(value[2:])


def _u32(value: int) -> bytes:
    return value.to_bytes(4, byteorder="big", signed=False)


def _u64(value: int) -> bytes:
    return value.to_bytes(8, byteorder="big", signed=False)


def _scalar_version(value: str | int | None) -> str:
    return "none" if value is None else str(value)


def _version_deltas(pair: ObservationPairV1) -> tuple[AppliedVersionDeltaV1, ...]:
    legacy = pair.legacy.observation
    exact = pair.exact.observation
    fields = (
        "algorithm_id",
        "algorithm_version",
        "codec_version",
        "schema_version",
        "snapshot_version",
        "support_root_version",
    )
    deltas: list[AppliedVersionDeltaV1] = []
    for field_name in fields:
        legacy_value = _scalar_version(object.__getattribute__(legacy, field_name))
        exact_value = _scalar_version(object.__getattribute__(exact, field_name))
        entry = lookup_version_delta_v1(
            field_name,
            legacy_value,
            exact_value,
            exact.result_kind,
        )
        if entry is None:
            _fault("undeclared_version_delta", ("version", field_name))
        deltas.append(
            AppliedVersionDeltaV1(
                entry.stable_id,
                field_name,
                legacy_value,
                exact_value,
                exact.result_kind,
            )
        )
    return tuple(deltas)


def _witness(
    pair: ObservationPairV1,
    deltas: tuple[AppliedVersionDeltaV1, ...],
) -> RefinementWitnessV1:
    binding = pair.exact.binding
    witness = RefinementWitnessV1(
        fixture_id=binding.fixture_id,
        command_hash=binding.command_hash,
        pre_state_root=binding.pre_state_root,
        context_hash=binding.context_hash,
        policy_version=POLICY_VERSION_V1,
        policy_hash=POLICY_HASH_V1,
        reviewed_source_sha=binding.reviewed_start_sha,
        baseline_artifact_hash=binding.baseline_artifact_hash,
        differential_artifact_hash=binding.differential_artifact_hash,
        packet_commit=binding.packet_commit,
        packet_tree_hash=binding.packet_tree_hash,
        version_deltas=deltas,
    )
    witness_projection: JsonProjectionV1 = [
        witness.fixture_id,
        witness.command_hash,
        witness.pre_state_root,
        witness.context_hash,
        witness.policy_version,
        witness.policy_hash,
        witness.reviewed_source_sha,
        witness.baseline_artifact_hash,
        witness.differential_artifact_hash,
        witness.packet_commit,
        witness.packet_tree_hash,
        [
            [
                delta.stable_id,
                delta.field_name,
                delta.legacy_value,
                delta.exact_value,
                delta.result_kind.value,
            ]
            for delta in witness.version_deltas
        ],
    ]
    if (
        check_refinement_resource_limit_v1(
            RefinementResourceKindV1.WITNESS_BYTES,
            len(canonical_json_bytes(witness_projection)),
        )
        is not None
    ):
        _fault("witness_byte_limit", ("witness",))
    return witness


def _production_context_hash(context_raw: bytes) -> str:
    projection = _component(
        RefinementComponentKindV1.EXECUTION_CONTEXT,
        context_raw,
        ("binding", "context_bytes"),
    )
    context = _object(projection, ("binding", "context_bytes"))
    fee_value = _field(context, "fee_split_policy", ("binding", "context_bytes"))
    fee_source: FCISFeeSplitPolicySourceV1 | None
    if fee_value is None:
        fee_source = None
    else:
        fee = _object(fee_value, ("binding", "context_bytes", "fee_split_policy"))
        fee_source = FCISFeeSplitPolicySourceV1(
            _field(fee, "buyback_bps", ()),
            _field(fee, "treasury_bps", ()),
            _field(fee, "rewards_bps", ()),
        )
    lp_value = _field(context, "lp_duration_policy", ("binding", "context_bytes"))
    lp_source: LPDurationPolicyAdmissionSourceV1 | None
    if lp_value is None:
        lp_source = None
    else:
        lp = _object(lp_value, ("binding", "context_bytes", "lp_duration_policy"))
        lp_source = LPDurationPolicyAdmissionSourceV1(
            _field(lp, "base_age_seconds", ()),
            _field(lp, "max_age_seconds", ()),
            _field(lp, "churn_window_seconds", ()),
            _field(lp, "decay_seconds", ()),
            _field(lp, "multiplier", ()),
            _field(lp, "max_churn_tier", ()),
        )
    settlement_source = FCISSettlementExecutionContextSourceV1(
        _field(context, "now", ()),
        _field(context, "min_lp_position_age_seconds", ()),
        FCISSettlementModeV1.STRONG_PROOF_CARRYING,
        _field(context, "allow_cow_netting", ()),
        _field(context, "allow_snapshot_bound_quote_bindings", ()),
        _field(context, "protocol_fee_share_bps", ()),
        _field(context, "protocol_fee_recipient_pubkey", ()),
    )
    source = FCISStepExecutionContextSourceV1(
        settlement_source,
        _field(context, "require_all_nonces", ()),
        _field(context, "reject_settlements_with_rejected_intents", ()),
        fee_source,
        lp_source,
        _field(context, "snapshot_version", ()),
    )
    admitted = admit_fcis_step_execution_context_v1(source)
    if type(admitted) is not AdmitOk or type(admitted.value) is not FCISStepExecutionContextV1:
        _fault("production_context_admission_failed", ("binding", "context_bytes"))
    encoded = encode_fcis_execution_context_v1(FCIS_STEP_CONTEXT_SCHEMA_ID_V1, admitted.value)
    return sha256_hex(domain_sep_bytes(_CONTEXT_HASH_DOMAIN_V1, version=1) + encoded)


def _command_root(settlement_bytes: bytes, binding: BoundObservationV1) -> str:
    out = bytearray(domain_sep_bytes(FCIS_SUPPORT_COMMAND_DOMAIN_V5, version=5))
    out += b"SET" + encode_bytes(settlement_bytes)
    out += b"INT" + encode_uvarint(len(binding.binding.command_bytes))
    for index, command_bytes in enumerate(binding.binding.command_bytes):
        command = _command(binding.binding.command_kind, command_bytes, index)
        if (
            _field(command, "kind", ("binding", "command_bytes", index))
            != binding.binding.command_kind
        ):
            _fault("command_kind_binding_mismatch", ("binding", "command_bytes", index, "kind"))
        out += encode_bytes(command_bytes)
    return sha256_hex(bytes(out))


def _sequence_key(
    entry: JsonProjectionV1, names: tuple[str, ...], path: FieldPathV1
) -> tuple[str, ...]:
    item = _object(entry, path)
    values: list[str] = []
    for name in names:
        value = _field(item, name, path)
        if type(value) is not str:
            _fault("semantic_key_projection_failed", path + (name,))
        values.append(value)
    return tuple(values)


def _require_strict_object_order(
    values: JsonProjectionV1,
    names: tuple[str, ...],
    path: FieldPathV1,
) -> JsonArrayV1:
    items = _array(values, path)
    previous: tuple[str, ...] | None = None
    for index, item in enumerate(items):
        key = _sequence_key(item, names, path + (index,))
        if previous is not None and key <= previous:
            _fault("noncanonical_semantic_order", path + (index,))
        previous = key
    return items


def _public_state(raw: bytes, path: FieldPathV1) -> JsonObjectV1:
    projected = _component(RefinementComponentKindV1.PUBLIC_STATE, raw, path)
    state = _object(projected, path)
    for field_name, key_names in (
        ("balances", ("pubkey", "asset")),
        ("pools", ("pool_id",)),
        ("lp_balances", ("pubkey", "pool_id")),
        ("lp_mint_timestamps", ("pubkey", "pool_id")),
        ("lp_duration_risk", ("pubkey", "pool_id")),
        ("nonces", ("pubkey",)),
    ):
        _require_strict_object_order(
            _field(state, field_name, path),
            key_names,
            path + (field_name,),
        )
    return state


def _pair_entries(
    container: JsonObjectV1,
    field_name: str,
    path: FieldPathV1,
) -> tuple[tuple[JsonProjectionV1, JsonProjectionV1], ...]:
    rows = _array(_field(container, field_name, path), path + (field_name,))
    result: list[tuple[JsonProjectionV1, JsonProjectionV1]] = []
    previous: bytes | None = None
    for index, row in enumerate(rows):
        parts = _array(row, path + (field_name, index))
        if len(parts) != 2:
            _fault("map_pair_projection_failed", path + (field_name, index))
        key_bytes = _canonical(parts[0], path + (field_name, index, 0))
        if previous is not None and key_bytes <= previous:
            _fault("noncanonical_internal_map_order", path + (field_name, index))
        previous = key_bytes
        result.append((parts[0], parts[1]))
    return tuple(result)


def _key_pair(value: JsonProjectionV1, path: FieldPathV1) -> tuple[str, str]:
    parts = _array(value, path)
    if len(parts) != 2 or type(parts[0]) is not str or type(parts[1]) is not str:
        _fault("semantic_pair_key_projection_failed", path)
    return parts[0], parts[1]


def _pool_public(pool_value: JsonProjectionV1, path: FieldPathV1) -> JsonObjectV1:
    pool = _object(pool_value, path)
    status = _array(_field(pool, "status", path), path + ("status",))
    if len(status) != 3 or status[0] != "zenodex/fcis-authority-state/v1":
        _fault("pool_status_metadata_mismatch", path + ("status",))
    ordinal = status[2]
    if type(ordinal) is not int or not 0 <= ordinal < len(_POOL_STATUS_LABELS_V1):
        _fault("pool_status_ordinal_mismatch", path + ("status", 2))
    return {
        "asset0": _field(pool, "asset0", path),
        "asset1": _field(pool, "asset1", path),
        "created_at": _field(pool, "created_at", path),
        "curve_params": _field(pool, "curve_params", path),
        "curve_tag": _field(pool, "curve_tag", path),
        "fee_bps": _field(pool, "fee_bps", path),
        "lp_supply": _field(pool, "lp_supply", path),
        "pool_id": _field(pool, "pool_id", path),
        "reserve0": _field(pool, "reserve0", path),
        "reserve1": _field(pool, "reserve1", path),
        "status": _POOL_STATUS_LABELS_V1[ordinal],
    }


def _lookup_pair_value(
    entries: tuple[tuple[JsonProjectionV1, JsonProjectionV1], ...],
    key: tuple[str, str],
) -> JsonProjectionV1 | None:
    for raw_key, value in entries:
        if _key_pair(raw_key, ("internal", "lookup")) == key:
            return value
    return None


def _internal_lp_public(
    lp: JsonObjectV1,
    path: FieldPathV1,
) -> tuple[JsonArrayV1, JsonArrayV1, JsonArrayV1]:
    balances = _pair_entries(lp, "_balances", path)
    mint = _pair_entries(lp, "_last_mint_timestamps", path)
    remove = _pair_entries(lp, "_last_remove_timestamps", path)
    tiers = _pair_entries(lp, "_churn_tiers", path)
    churn_updates = _pair_entries(lp, "_last_churn_update_timestamps", path)
    balance_rows: JsonArrayV1 = []
    for raw_key, amount in balances:
        pubkey, pool_id = _key_pair(raw_key, path + ("_balances",))
        if type(amount) is not int or amount <= 0:
            _fault("internal_lp_balance_not_sparse", path + ("_balances",))
        balance_rows.append({"amount": amount, "pool_id": pool_id, "pubkey": pubkey})
    mint_rows: JsonArrayV1 = []
    for raw_key, timestamp in mint:
        pubkey, pool_id = _key_pair(raw_key, path + ("_last_mint_timestamps",))
        mint_rows.append({"last_mint_timestamp": timestamp, "pool_id": pool_id, "pubkey": pubkey})
    risk_keys = sorted(
        {
            _key_pair(raw_key, path + ("lp_risk_key",))
            for entries in (mint, remove, tiers, churn_updates)
            for raw_key, _value in entries
        }
    )
    risk_rows: JsonArrayV1 = []
    for pubkey, pool_id in risk_keys:
        key = (pubkey, pool_id)
        risk_rows.append(
            {
                "churn_tier": _lookup_pair_value(tiers, key) or 0,
                "last_churn_update_timestamp": _lookup_pair_value(churn_updates, key),
                "last_remove_timestamp": _lookup_pair_value(remove, key),
                "pool_id": pool_id,
                "pubkey": pubkey,
            }
        )
    return balance_rows, mint_rows, risk_rows


def _internal_state_public(value: JsonProjectionV1, path: FieldPathV1) -> JsonObjectV1:
    state = _object(value, path)
    balance_state = _object(_field(state, "balances", path), path + ("balances",))
    balance_rows: JsonArrayV1 = []
    for raw_key, amount in _pair_entries(balance_state, "_balances", path + ("balances",)):
        pubkey, asset = _key_pair(raw_key, path + ("balances", "_balances"))
        if type(amount) is not int or amount <= 0:
            _fault("internal_balance_not_sparse", path + ("balances", "_balances"))
        balance_rows.append({"amount": amount, "asset": asset, "pubkey": pubkey})
    pools: JsonArrayV1 = []
    pool_rows = _array(_field(state, "pools", path), path + ("pools",))
    previous_pool_id: str | None = None
    for index, row in enumerate(pool_rows):
        pair = _array(row, path + ("pools", index))
        if len(pair) != 2 or type(pair[0]) is not str:
            _fault("internal_pool_pair_projection_failed", path + ("pools", index))
        pool_id = pair[0]
        if previous_pool_id is not None and pool_id <= previous_pool_id:
            _fault("noncanonical_internal_pool_order", path + ("pools", index))
        previous_pool_id = pool_id
        pool = _pool_public(pair[1], path + ("pools", index, 1))
        if _field(pool, "pool_id", path + ("pools", index, 1)) != pool_id:
            _fault("internal_pool_key_mismatch", path + ("pools", index, 0))
        pools.append(pool)
    lp = _object(_field(state, "lp_balances", path), path + ("lp_balances",))
    lp_balances, lp_mint, lp_risk = _internal_lp_public(lp, path + ("lp_balances",))
    nonce_state = _object(_field(state, "nonces", path), path + ("nonces",))
    nonces: JsonArrayV1 = []
    for pubkey_value, nonce in _pair_entries(nonce_state, "_last", path + ("nonces",)):
        if type(pubkey_value) is not str:
            _fault("internal_nonce_key_projection_failed", path + ("nonces", "_last"))
        nonces.append({"last_nonce": nonce, "pubkey": pubkey_value})
    return {
        "balances": balance_rows,
        "fee_accumulator": _field(state, "fee_accumulator", path),
        "lp_balances": lp_balances,
        "lp_duration_risk": lp_risk,
        "lp_mint_timestamps": lp_mint,
        "nonces": nonces,
        "oracle": _field(state, "oracle", path),
        "perps": _field(state, "perps", path),
        "pools": pools,
        "vault": _field(state, "vault", path),
        "version": 4,
    }


def _semantic_state(state: JsonObjectV1) -> JsonObjectV1:
    return {
        "balances": state["balances"],
        "fee_accumulator": state["fee_accumulator"],
        "lp_balances": {
            "balances": state["lp_balances"],
            "duration_risk": state["lp_duration_risk"],
            "mint_timestamps": state["lp_mint_timestamps"],
        },
        "nonces": state["nonces"],
        "oracle": state["oracle"],
        "perps": state["perps"],
        "pools": state["pools"],
        "vault": state["vault"],
    }


def _state_root(raw: bytes) -> str:
    return sha256_hex(domain_sep_bytes("dex_snapshot", version=4) + raw)


def _same_component(
    expected: JsonProjectionV1,
    observed: JsonProjectionV1,
    code: str,
    path: FieldPathV1,
) -> None:
    if _canonical(expected, path) != _canonical(observed, path):
        _fault(code, path)


def _public_entries(
    state: JsonObjectV1,
    field_name: str,
    key_names: tuple[str, ...],
) -> tuple[tuple[tuple[str, ...], JsonObjectV1], ...]:
    rows = _array(state[field_name], ("state", field_name))
    return tuple(
        (
            _sequence_key(row, key_names, ("state", field_name, index)),
            _object(row, ("state", field_name, index)),
        )
        for index, row in enumerate(rows)
    )


def _find_public(
    entries: tuple[tuple[tuple[str, ...], JsonObjectV1], ...],
    key: tuple[str, ...],
) -> JsonObjectV1 | None:
    for observed_key, row in entries:
        if observed_key == key:
            return row
    return None


def _all_keys(
    *entry_sets: tuple[tuple[tuple[str, ...], JsonObjectV1], ...],
) -> tuple[tuple[str, ...], ...]:
    return tuple(sorted({key for entries in entry_sets for key, _row in entries}))


def _balance_write_projection(
    pre_state: JsonObjectV1,
    post_state: JsonObjectV1,
) -> JsonArrayV1:
    pre = _public_entries(pre_state, "balances", ("pubkey", "asset"))
    post = _public_entries(post_state, "balances", ("pubkey", "asset"))
    result: JsonArrayV1 = []
    for key in _all_keys(pre, post):
        old_row = _find_public(pre, key)
        new_row = _find_public(post, key)
        old_value = 0 if old_row is None else old_row["amount"]
        new_value = 0 if new_row is None else new_row["amount"]
        if old_value != new_value:
            result.append(
                {
                    "expected_old": old_value,
                    "key": [key[0], key[1]],
                    "replacement": None if new_value == 0 else new_value,
                }
            )
    return result


def _pool_write_projection(
    pre_state: JsonObjectV1,
    post_state: JsonObjectV1,
) -> JsonArrayV1:
    pre = _public_entries(pre_state, "pools", ("pool_id",))
    post = _public_entries(post_state, "pools", ("pool_id",))
    result: JsonArrayV1 = []
    for key in _all_keys(pre, post):
        old_row = _find_public(pre, key)
        new_row = _find_public(post, key)
        if old_row != new_row:
            result.append({"expected": old_row, "pool_id": key[0], "replacement": new_row})
    return result


def _normalized_patch_pool(value: JsonProjectionV1, path: FieldPathV1) -> JsonObjectV1:
    return _pool_public(value, path)


def _observed_pool_writes(patch: JsonObjectV1) -> JsonArrayV1:
    rows = _array(patch["pool_writes"], ("patch", "pool_writes"))
    result: JsonArrayV1 = []
    previous: str | None = None
    for index, row in enumerate(rows):
        item = _object(row, ("patch", "pool_writes", index))
        pool_id = item["pool_id"]
        if type(pool_id) is not str or (previous is not None and pool_id <= previous):
            _fault("noncanonical_pool_write_order", ("patch", "pool_writes", index))
        previous = pool_id
        expected = item["expected"]
        replacement = item["replacement"]
        result.append(
            {
                "expected": None
                if expected is None
                else _normalized_patch_pool(expected, ("patch", "pool_writes", index, "expected")),
                "pool_id": pool_id,
                "replacement": None
                if replacement is None
                else _normalized_patch_pool(
                    replacement,
                    ("patch", "pool_writes", index, "replacement"),
                ),
            }
        )
    return result


def _lp_position(
    state: JsonObjectV1,
    key: tuple[str, str],
) -> JsonObjectV1:
    balance_entries = _public_entries(state, "lp_balances", ("pubkey", "pool_id"))
    mint_entries = _public_entries(state, "lp_mint_timestamps", ("pubkey", "pool_id"))
    risk_entries = _public_entries(state, "lp_duration_risk", ("pubkey", "pool_id"))
    balance = _find_public(balance_entries, key)
    mint = _find_public(mint_entries, key)
    risk = _find_public(risk_entries, key)
    return {
        "balance": 0 if balance is None else balance["amount"],
        "churn_tier": 0 if risk is None else risk["churn_tier"],
        "last_churn_update_timestamp": None
        if risk is None
        else risk["last_churn_update_timestamp"],
        "last_mint_timestamp": None if mint is None else mint["last_mint_timestamp"],
        "last_remove_timestamp": None if risk is None else risk["last_remove_timestamp"],
    }


def _lp_keys(state: JsonObjectV1) -> tuple[tuple[str, str], ...]:
    entries = (
        _public_entries(state, "lp_balances", ("pubkey", "pool_id")),
        _public_entries(state, "lp_mint_timestamps", ("pubkey", "pool_id")),
        _public_entries(state, "lp_duration_risk", ("pubkey", "pool_id")),
    )
    return cast(tuple[tuple[str, str], ...], _all_keys(*entries))


def _lp_write_projection(
    pre_state: JsonObjectV1,
    post_state: JsonObjectV1,
) -> JsonArrayV1:
    result: JsonArrayV1 = []
    for key in tuple(sorted(set(_lp_keys(pre_state)) | set(_lp_keys(post_state)))):
        old_value = _lp_position(pre_state, key)
        new_value = _lp_position(post_state, key)
        if old_value != new_value:
            result.append(
                {
                    "expected": old_value,
                    "key": [key[0], key[1]],
                    "replacement": new_value,
                }
            )
    return result


def _fee_write_projection(
    pre_state: JsonObjectV1,
    post_state: JsonObjectV1,
) -> JsonProjectionV1:
    old_value = pre_state["fee_accumulator"]
    new_value = post_state["fee_accumulator"]
    if old_value == new_value:
        return None
    return {"expected": old_value, "replacement": new_value}


def _check_patch(
    pre_state: JsonObjectV1,
    post_state: JsonObjectV1,
    patch: JsonObjectV1,
) -> None:
    _same_component(
        _balance_write_projection(pre_state, post_state),
        patch["balance_writes"],
        "incomplete_balance_patch",
        ("patch", "balance_writes"),
    )
    _same_component(
        _pool_write_projection(pre_state, post_state),
        _observed_pool_writes(patch),
        "incomplete_pool_patch",
        ("patch", "pool_writes"),
    )
    _same_component(
        _lp_write_projection(pre_state, post_state),
        patch["lp_writes"],
        "incomplete_lp_patch",
        ("patch", "lp_writes"),
    )
    _same_component(
        _fee_write_projection(pre_state, post_state),
        patch["fee_accumulator_write"],
        "incomplete_fee_patch",
        ("patch", "fee_accumulator_write"),
    )
    for field_name in ("vault_write", "oracle_write", "perps_write"):
        if patch[field_name] is not None:
            _fault("unsupported_optional_module_write", ("patch", field_name))


def _nonce_entries(state: JsonObjectV1) -> tuple[tuple[str, int], ...]:
    rows = _public_entries(state, "nonces", ("pubkey",))
    return tuple((key[0], cast(int, row["last_nonce"])) for key, row in rows)


def _nonce_at(entries: tuple[tuple[str, int], ...], pubkey: str) -> int:
    for key, value in entries:
        if key == pubkey:
            return value
    return 0


def _expected_nonce_advances(
    pre_state: JsonObjectV1,
    post_state: JsonObjectV1,
) -> JsonArrayV1:
    pre = _nonce_entries(pre_state)
    post = _nonce_entries(post_state)
    keys = tuple(sorted({key for key, _value in pre + post}))
    result: JsonArrayV1 = []
    for pubkey in keys:
        old_value = _nonce_at(pre, pubkey)
        new_value = _nonce_at(post, pubkey)
        if old_value == new_value:
            continue
        if new_value <= old_value:
            _fault("nonce_transition_not_monotone", ("replay", "nonce_advances"))
        result.append({"expected_last": old_value, "new_last": new_value, "pubkey": pubkey})
    return result


def _expected_nullifiers(binding: BoundObservationV1) -> JsonArrayV1:
    records: list[tuple[str, str]] = []
    for index, raw in enumerate(binding.binding.command_bytes):
        command = _command(binding.binding.command_kind, raw, index)
        pubkey = command["sender_pubkey"]
        intent_id = command["intent_id"]
        if type(pubkey) is not str or type(intent_id) is not str:
            _fault("command_identity_projection_failed", ("binding", "command_bytes", index))
        records.append((pubkey, intent_id))
    records.sort()
    if len(records) != len(set(records)):
        _fault("duplicate_command_identity", ("binding", "command_bytes"))
    return [{"intent_id": intent_id, "pubkey": pubkey} for pubkey, intent_id in records]


def _nonce_table_hash(state: JsonObjectV1) -> str:
    payload = canonical_json_bytes([[pubkey, nonce] for pubkey, nonce in _nonce_entries(state)])
    return sha256_hex(domain_sep_bytes("fcis_nonce_table", version=1) + payload)


def _check_replay(
    pre_state: JsonObjectV1,
    post_state: JsonObjectV1,
    replay: JsonObjectV1,
    binding: BoundObservationV1,
    expected_nonce_hash: str,
) -> None:
    _same_component(
        _expected_nonce_advances(pre_state, post_state),
        replay["nonce_advances"],
        "replay_nonce_advances_mismatch",
        ("replay", "nonce_advances"),
    )
    _same_component(
        _expected_nullifiers(binding),
        replay["nullifiers"],
        "replay_nullifiers_mismatch",
        ("replay", "nullifiers"),
    )
    if _nonce_table_hash(post_state) != expected_nonce_hash:
        _fault("next_nonce_table_hash_mismatch", ("next_nonce_table_hash",))


def _optional_admitted_array(
    value: JsonObjectV1,
    name: str,
    path: FieldPathV1,
) -> JsonArrayV1:
    """Project one schema-declared optional list after closed admission."""

    if name not in value:
        return []
    return _array(value[name], path + (name,))


def _enum_label(
    raw: JsonProjectionV1,
    tag: StateEnumTagV1,
    labels: tuple[str, ...],
    path: FieldPathV1,
) -> str:
    parts = _array(raw, path)
    expected_tag = state_enum_tag_ordinal_v1(tag)
    if len(parts) != 3 or parts[0] != "zenodex/fcis-authority-state/v1":
        _fault("enum_metadata_mismatch", path)
    if parts[1] != expected_tag:
        _fault("enum_tag_mismatch", path + (1,))
    ordinal = parts[2]
    if type(ordinal) is not int or not 0 <= ordinal < len(labels):
        _fault("enum_member_ordinal_mismatch", path + (2,))
    return labels[ordinal]


def _fee_allocation_projection(observation: ObservationValueV1) -> JsonProjectionV1:
    allocation = observation.fee_allocation
    if allocation is None:
        return None
    return {
        "buyback_amount": allocation.buyback_amount,
        "dust_carried": allocation.dust_carried,
        "rewards_amount": allocation.rewards_amount,
        "treasury_amount": allocation.treasury_amount,
    }


def _require_exact_accept_shape(observation: ObservationValueV1) -> None:
    if observation.rejection is not None:
        _fault("accepted_observation_carries_rejection", ("exact", "rejection"))
    for name in (
        "next_state_snapshot_root",
        "next_nonce_table_hash",
        "support_root",
    ):
        if object.__getattribute__(observation, name) is None:
            _fault("accepted_observation_missing_digest", ("exact", name))
    for name in ("settlement_bytes", "next_state_snapshot_bytes", "total_swap_fees"):
        if object.__getattribute__(observation, name) is None:
            _fault("accepted_observation_missing_value", ("exact", name))


def _require_exact_reject_shape(observation: ObservationValueV1) -> None:
    if observation.rejection is None:
        _fault("rejected_observation_missing_rejection", ("exact", "rejection"))
    for name in (
        "next_state_snapshot_bytes",
        "next_state_snapshot_root",
        "next_nonce_table_hash",
        "settlement_bytes",
        "support_root",
        "total_swap_fees",
        "fee_allocation",
    ):
        if object.__getattribute__(observation, name) is not None:
            _fault("rejection_carries_committable_value", ("exact", name))
    for name in (
        "bundle_bytes",
        "commit_plan_bytes",
        "effects_bytes",
        "outbox_bytes",
        "patch_bytes",
        "replay_bytes",
    ):
        _require_absent_bytes(object.__getattribute__(observation, name), ("exact", name))
    if observation.bundle_root.status is not EvidenceFieldStatusV1.ABSENT:
        _fault("rejection_carries_bundle_root", ("exact", "bundle_root"))
    if observation.outbox_identities.status is not EvidenceFieldStatusV1.ABSENT:
        _fault("rejection_carries_outbox_identities", ("exact", "outbox_identities"))


def _common_receipt_fields(
    receipt: JsonObjectV1,
    pair: ObservationPairV1,
    path: FieldPathV1,
) -> None:
    exact = pair.exact.observation
    expected = {
        "algorithm_id": FCIS_STEP_EVALUATOR_ALGORITHM_ID_V1,
        "algorithm_version": FCIS_STEP_EVALUATOR_ALGORITHM_VERSION_V1,
        "budget_hash": BUDGET_HASH_V1,
        "codec_version": FCIS_AUTHORITY_CODEC_VERSION_V1,
        "execution_context_hash": _production_context_hash(pair.exact.binding.context_bytes),
        "pre_state_root": pair.exact.binding.pre_state_root,
        "schema_version": FCIS_AUTHORITY_SCHEMA_VERSION_V1,
    }
    for name, value in expected.items():
        if _field(receipt, name, path) != value:
            _fault("receipt_lineage_mismatch", path + (name,))
    if exact.algorithm_id != expected["algorithm_id"]:
        _fault("exact_algorithm_id_mismatch", ("exact", "algorithm_id"))
    if exact.algorithm_version != expected["algorithm_version"]:
        _fault("exact_algorithm_version_mismatch", ("exact", "algorithm_version"))
    if exact.codec_version != expected["codec_version"]:
        _fault("exact_codec_version_mismatch", ("exact", "codec_version"))
    if exact.schema_version != expected["schema_version"]:
        _fault("exact_schema_version_mismatch", ("exact", "schema_version"))


def _check_accept_receipt(
    receipt: JsonObjectV1,
    pair: ObservationPairV1,
    settlement_raw: bytes,
    patch_raw: bytes,
    plan_raw: bytes,
    next_root: str,
) -> None:
    path: FieldPathV1 = ("exact", "receipt_bytes", "binding")
    binding = _object(_field(receipt, "binding", ("exact", "receipt_bytes")), path)
    _common_receipt_fields(binding, pair, path)
    exact = pair.exact.observation
    expected = {
        "command_or_batch_root": _command_root(settlement_raw, pair.exact),
        "commit_plan_root": _claim_root(FCIS_COMMIT_PLAN_SCHEMA_ID_V1, plan_raw),
        "next_state_root": next_root,
        "patch_root": _claim_root(FCIS_DEX_PATCH_SCHEMA_ID_V1, patch_raw),
        "snapshot_commitment": next_root,
        "snapshot_version": exact.snapshot_version,
        "support_root": exact.support_root,
        "support_root_version": exact.support_root_version,
    }
    for name, value in expected.items():
        if _field(binding, name, path) != value:
            _fault("accept_receipt_binding_mismatch", path + (name,))


def _event_payload(event: JsonProjectionV1, path: FieldPathV1) -> JsonArrayV1:
    value = _object(event, path)
    names = (
        "asset0",
        "asset1",
        "created_at",
        "curve_params",
        "curve_tag",
        "fee_bps",
        "pool_id",
        "status",
        "type",
    )
    return [[name, _field(value, name, path)] for name in names]


def _effect_identity(
    receipt_root: str,
    effect_index: int,
    payload_bytes: bytes,
) -> str:
    kind = OutboxEffectKindV1.CANONICAL_EVENT.value.encode("utf-8")
    preimage = (
        domain_sep_bytes(_EFFECT_IDENTITY_DOMAIN_V1, version=1)
        + _raw32(receipt_root)
        + _u32(effect_index)
        + _u32(len(kind))
        + kind
        + _u64(len(payload_bytes))
        + payload_bytes
    )
    return sha256_hex(preimage)


def _idempotency_key(receipt_root: str, effect_index: int, identity: str) -> str:
    return sha256_hex(
        domain_sep_bytes(_IDEMPOTENCY_DOMAIN_V1, version=1)
        + _raw32(receipt_root)
        + _u32(effect_index)
        + _raw32(identity)
    )


def _check_outbox(
    settlement: JsonObjectV1,
    outbox: JsonObjectV1,
    receipt_root: str,
    observation: ObservationValueV1,
) -> None:
    events = _optional_admitted_array(settlement, "events", ("settlement",))
    records = _array(_field(outbox, "records", ("outbox",)), ("outbox", "records"))
    if len(records) != len(events):
        _fault("outbox_event_cardinality_mismatch", ("outbox", "records"))
    identities = observation.outbox_identities
    if identities.status is not EvidenceFieldStatusV1.PRESENT or identities.value is None:
        _fault("accepted_outbox_identities_absent", ("exact", "outbox_identities"))
    if len(identities.value) != len(records):
        _fault("outbox_identity_cardinality_mismatch", ("exact", "outbox_identities"))
    identity_values = identities.value
    labels = tuple(member.value for member in OutboxEffectKindV1)
    for index, (event, raw_record, observed_identity) in enumerate(
        zip(events, records, identity_values, strict=True)
    ):
        path: FieldPathV1 = ("outbox", "records", index)
        record = _object(raw_record, path)
        if _field(record, "effect_index", path) != index:
            _fault("outbox_effect_index_mismatch", path + ("effect_index",))
        kind = _enum_label(
            _field(record, "effect_kind", path),
            StateEnumTagV1.OUTBOX_EFFECT_KIND,
            labels,
            path + ("effect_kind",),
        )
        if kind != OutboxEffectKindV1.CANONICAL_EVENT.value:
            _fault("unsupported_outbox_effect_kind", path + ("effect_kind",))
        payload = _event_payload(event, ("settlement", "events", index))
        _same_component(payload, _field(record, "payload", path), "outbox_payload_mismatch", path)
        payload_bytes = canonical_json_bytes(event)
        identity = _effect_identity(receipt_root, index, payload_bytes)
        idempotency_key = _idempotency_key(receipt_root, index, identity)
        if _field(record, "effect_identity", path) != identity:
            _fault("outbox_effect_identity_mismatch", path + ("effect_identity",))
        if _field(record, "idempotency_key", path) != idempotency_key:
            _fault("outbox_idempotency_key_mismatch", path + ("idempotency_key",))
        if (
            observed_identity.effect_index != index
            or observed_identity.effect_identity != identity
            or observed_identity.idempotency_key != idempotency_key
        ):
            _fault("outbox_identity_projection_mismatch", ("exact", "outbox_identities", index))


def _admit_accept_components(
    pair: ObservationPairV1,
) -> tuple[
    JsonObjectV1,
    JsonObjectV1,
    JsonObjectV1,
    JsonObjectV1,
    JsonObjectV1,
    JsonObjectV1,
    JsonObjectV1,
    JsonObjectV1,
    bytes,
    bytes,
    bytes,
    bytes,
]:
    exact = pair.exact.observation
    settlement_raw = cast(bytes, exact.settlement_bytes)
    patch_raw = _present_bytes(exact.patch_bytes, ("exact", "patch_bytes"))
    effects_raw = _present_bytes(exact.effects_bytes, ("exact", "effects_bytes"))
    replay_raw = _present_bytes(exact.replay_bytes, ("exact", "replay_bytes"))
    plan_raw = _present_bytes(exact.commit_plan_bytes, ("exact", "commit_plan_bytes"))
    receipt_raw = _present_bytes(exact.receipt_bytes, ("exact", "receipt_bytes"))
    outbox_raw = _present_bytes(exact.outbox_bytes, ("exact", "outbox_bytes"))
    bundle_raw = _present_bytes(exact.bundle_bytes, ("exact", "bundle_bytes"))
    settlement = _object(
        _component(
            RefinementComponentKindV1.SETTLEMENT, settlement_raw, ("exact", "settlement_bytes")
        ),
        ("settlement",),
    )
    patch = _object(
        _component(RefinementComponentKindV1.PATCH, patch_raw, ("exact", "patch_bytes")),
        ("patch",),
    )
    effects = _object(
        _component(RefinementComponentKindV1.EFFECTS, effects_raw, ("exact", "effects_bytes")),
        ("effects",),
    )
    replay = _object(
        _component(RefinementComponentKindV1.REPLAY, replay_raw, ("exact", "replay_bytes")),
        ("replay",),
    )
    plan = _object(
        _component(RefinementComponentKindV1.COMMIT_PLAN, plan_raw, ("exact", "commit_plan_bytes")),
        ("commit_plan",),
    )
    receipt = _object(
        _component(
            RefinementComponentKindV1.ACCEPT_RECEIPT, receipt_raw, ("exact", "receipt_bytes")
        ),
        ("receipt",),
    )
    outbox = _object(
        _component(RefinementComponentKindV1.OUTBOX, outbox_raw, ("exact", "outbox_bytes")),
        ("outbox",),
    )
    bundle = _object(
        _component(RefinementComponentKindV1.BUNDLE, bundle_raw, ("exact", "bundle_bytes")),
        ("bundle",),
    )
    return (
        settlement,
        patch,
        effects,
        replay,
        plan,
        receipt,
        outbox,
        bundle,
        settlement_raw,
        patch_raw,
        plan_raw,
        receipt_raw,
    )


def _check_accept_component_lineage(
    pair: ObservationPairV1,
    settlement: JsonObjectV1,
    patch: JsonObjectV1,
    effects: JsonObjectV1,
    replay: JsonObjectV1,
    plan: JsonObjectV1,
    receipt: JsonObjectV1,
    outbox: JsonObjectV1,
    bundle: JsonObjectV1,
    settlement_raw: bytes,
    patch_raw: bytes,
    plan_raw: bytes,
    receipt_raw: bytes,
    next_root: str,
) -> None:
    exact = pair.exact.observation
    _same_component(
        patch,
        _field(plan, "patch", ("commit_plan",)),
        "plan_patch_mismatch",
        ("commit_plan", "patch"),
    )
    _same_component(
        effects,
        _field(plan, "effects", ("commit_plan",)),
        "plan_effects_mismatch",
        ("commit_plan", "effects"),
    )
    _same_component(
        replay,
        _field(plan, "replay", ("commit_plan",)),
        "plan_replay_mismatch",
        ("commit_plan", "replay"),
    )
    _same_component(
        settlement,
        _field(effects, "settlement", ("effects",)),
        "effects_settlement_mismatch",
        ("effects", "settlement"),
    )
    if _field(effects, "total_swap_fees", ("effects",)) != exact.total_swap_fees:
        _fault("effects_total_fees_mismatch", ("effects", "total_swap_fees"))
    _same_component(
        _fee_allocation_projection(exact),
        _field(effects, "fee_allocation", ("effects",)),
        "effects_fee_allocation_mismatch",
        ("effects", "fee_allocation"),
    )
    decision = _object(_field(bundle, "decision", ("bundle",)), ("bundle", "decision"))
    _same_component(
        plan,
        _field(decision, "commit_plan", ("bundle", "decision")),
        "bundle_plan_mismatch",
        ("bundle", "decision", "commit_plan"),
    )
    _same_component(
        receipt,
        _field(decision, "receipt", ("bundle", "decision")),
        "bundle_receipt_mismatch",
        ("bundle", "decision", "receipt"),
    )
    _same_component(
        outbox,
        _field(bundle, "outbox_plan", ("bundle",)),
        "bundle_outbox_mismatch",
        ("bundle", "outbox_plan"),
    )
    if _field(bundle, "expected_pre_root", ("bundle",)) != pair.exact.binding.pre_state_root:
        _fault("bundle_pre_root_mismatch", ("bundle", "expected_pre_root"))
    receipt_root = _present_digest(exact.receipt_root, ("exact", "receipt_root"))
    if _claim_root(FCIS_ACCEPTANCE_RECEIPT_SCHEMA_ID_V1, receipt_raw) != receipt_root:
        _fault("receipt_root_mismatch", ("exact", "receipt_root"))
    if _field(bundle, "receipt_root", ("bundle",)) != receipt_root:
        _fault("bundle_receipt_root_mismatch", ("bundle", "receipt_root"))
    bundle_raw = _present_bytes(exact.bundle_bytes, ("exact", "bundle_bytes"))
    bundle_root = _present_digest(exact.bundle_root, ("exact", "bundle_root"))
    if _claim_root(FCIS_COMMIT_BUNDLE_SCHEMA_ID_V1, bundle_raw) != bundle_root:
        _fault("bundle_root_mismatch", ("exact", "bundle_root"))
    _check_accept_receipt(receipt, pair, settlement_raw, patch_raw, plan_raw, next_root)
    _check_outbox(settlement, outbox, receipt_root, exact)


def _accepted_evidence(pair: ObservationPairV1) -> _AcceptedEvidenceV1:
    exact = pair.exact.observation
    legacy = pair.legacy.observation
    _require_exact_accept_shape(exact)
    if legacy.next_state_snapshot_bytes is None:
        _fault("legacy_accept_missing_next_state", ("legacy", "next_state_snapshot_bytes"))
    pre_state = _public_state(pair.exact.binding.pre_state_bytes, ("binding", "pre_state_bytes"))
    legacy_state = _public_state(
        legacy.next_state_snapshot_bytes,
        ("legacy", "next_state_snapshot_bytes"),
    )
    exact_state_raw = cast(bytes, exact.next_state_snapshot_bytes)
    exact_state = _public_state(exact_state_raw, ("exact", "next_state_snapshot_bytes"))
    next_root = cast(str, exact.next_state_snapshot_root)
    if _state_root(exact_state_raw) != next_root:
        _fault("next_state_root_mismatch", ("exact", "next_state_snapshot_root"))
    (
        settlement,
        patch,
        effects,
        replay,
        plan,
        receipt,
        outbox,
        bundle,
        settlement_raw,
        patch_raw,
        plan_raw,
        receipt_raw,
    ) = _admit_accept_components(pair)
    decision = _object(_field(bundle, "decision", ("bundle",)), ("bundle", "decision"))
    internal = _field(decision, "next_state", ("bundle", "decision"))
    projected = _internal_state_public(internal, ("bundle", "decision", "next_state"))
    _same_component(
        exact_state,
        projected,
        "bundle_successor_projection_mismatch",
        ("bundle", "decision", "next_state"),
    )
    _check_patch(pre_state, exact_state, patch)
    _check_replay(
        pre_state,
        exact_state,
        replay,
        pair.exact,
        cast(str, exact.next_nonce_table_hash),
    )
    _check_accept_component_lineage(
        pair,
        settlement,
        patch,
        effects,
        replay,
        plan,
        receipt,
        outbox,
        bundle,
        settlement_raw,
        patch_raw,
        plan_raw,
        receipt_raw,
        next_root,
    )
    return _AcceptedEvidenceV1(pre_state, legacy_state, exact_state, settlement_raw)


def _check_reject_receipt(pair: ObservationPairV1) -> None:
    exact = pair.exact.observation
    legacy = pair.legacy.observation
    _require_exact_reject_shape(exact)
    receipt_raw = _present_bytes(exact.receipt_bytes, ("exact", "receipt_bytes"))
    receipt_root = _present_digest(exact.receipt_root, ("exact", "receipt_root"))
    if _claim_root(FCIS_REJECTION_RECEIPT_SCHEMA_ID_V1, receipt_raw) != receipt_root:
        _fault("rejection_receipt_root_mismatch", ("exact", "receipt_root"))
    receipt = _object(
        _component(
            RefinementComponentKindV1.REJECT_RECEIPT,
            receipt_raw,
            ("exact", "receipt_bytes"),
        ),
        ("receipt",),
    )
    _common_receipt_fields(receipt, pair, ("receipt",))
    exact_rejection = exact.rejection
    legacy_rejection = legacy.rejection
    if exact_rejection is None or legacy_rejection is None:
        _fault("rejection_pair_incomplete", ("rejection",))
    exact_rejection_value = exact_rejection
    legacy_rejection_value = legacy_rejection
    mapping = lookup_rejection_mapping_v1(
        legacy_rejection_value.code,
        legacy_rejection_value.precedence,
    )
    if mapping is None:
        _fault("undeclared_rejection_mapping", ("legacy", "rejection"))
    exact_mapping = mapping
    if (
        exact_rejection_value.code != exact_mapping.exact_code
        or exact_rejection_value.precedence != exact_mapping.exact_precedence
        or exact_rejection_value.path != legacy_rejection_value.path
        or exact_rejection_value.public_reason != legacy_rejection_value.public_reason
    ):
        _fault("rejection_mapping_mismatch", ("exact", "rejection"))
    phase_labels = tuple(member.value for member in FCISStepEvaluationPhaseV1)
    code_labels = tuple(member.value for member in FCISRejectCodeV1)
    phase = _enum_label(
        _field(receipt, "phase", ("receipt",)),
        StateEnumTagV1.FCIS_REJECTION_PHASE,
        phase_labels,
        ("receipt", "phase"),
    )
    code = _enum_label(
        _field(receipt, "code", ("receipt",)),
        StateEnumTagV1.FCIS_REJECTION_CODE,
        code_labels,
        ("receipt", "code"),
    )
    if phase != exact_mapping.exact_phase or code != exact_mapping.exact_code:
        _fault("rejection_receipt_enum_mismatch", ("receipt",))
    expected_fields = {
        "path": list(exact_rejection_value.path),
        "public_reason": exact_rejection_value.public_reason,
    }
    for name, value in expected_fields.items():
        if _field(receipt, name, ("receipt",)) != value:
            _fault("rejection_receipt_body_mismatch", ("receipt", name))


def _mismatch(
    code: str,
    path: FieldPathV1,
    legacy_value: JsonProjectionV1,
    exact_value: JsonProjectionV1,
) -> MismatchV1:
    return MismatchV1(code, path, _compact_value(legacy_value), _compact_value(exact_value))


def _compare_accept_semantics(
    pair: ObservationPairV1,
    evidence: _AcceptedEvidenceV1,
) -> MismatchV1 | None:
    legacy = pair.legacy.observation
    exact = pair.exact.observation
    legacy_semantic = _semantic_state(evidence.legacy_state)
    exact_semantic = _semantic_state(evidence.exact_state)
    for field_name in SEMANTIC_STATE_FIELD_ORDER_V1:
        if _canonical(legacy_semantic[field_name], ("state", field_name)) != _canonical(
            exact_semantic[field_name],
            ("state", field_name),
        ):
            return _mismatch(
                "state_field_mismatch",
                ("next_state", field_name),
                legacy_semantic[field_name],
                exact_semantic[field_name],
            )
    legacy_settlement_bytes = cast(bytes, legacy.settlement_bytes)
    _component(
        RefinementComponentKindV1.SETTLEMENT,
        legacy_settlement_bytes,
        ("legacy", "settlement_bytes"),
    )
    if legacy_settlement_bytes != exact.settlement_bytes:
        return MismatchV1(
            "settlement_bytes_mismatch",
            ("settlement_bytes",),
            legacy_settlement_bytes,
            evidence.settlement_bytes,
        )
    for field_name in ("total_swap_fees", "next_nonce_table_hash"):
        legacy_value = object.__getattribute__(legacy, field_name)
        exact_value = object.__getattribute__(exact, field_name)
        if legacy_value != exact_value:
            return _mismatch(
                "economic_output_mismatch",
                (field_name,),
                cast(JsonProjectionV1, legacy_value),
                cast(JsonProjectionV1, exact_value),
            )
    legacy_fee = _fee_allocation_projection(legacy)
    exact_fee = _fee_allocation_projection(exact)
    if _canonical(legacy_fee, ("fee_allocation",)) != _canonical(
        exact_fee,
        ("fee_allocation",),
    ):
        return _mismatch(
            "fee_allocation_mismatch",
            ("fee_allocation",),
            legacy_fee,
            exact_fee,
        )
    return None


def evaluate_refinement_v1(source: object) -> RefinementDecisionV1:
    """Evaluate one bounded directional legacy-to-exact refinement claim."""

    validated = revalidate_observation_pair_v1(source)
    if type(validated) is InvalidEvidenceV1:
        return validated
    try:
        deltas = _version_deltas(validated)
        legacy = validated.legacy.observation
        exact = validated.exact.observation
        if legacy.algorithm_id != LEGACY_ALGORITHM_ID_V1:
            _fault("legacy_algorithm_id_mismatch", ("legacy", "algorithm_id"))
        if exact.algorithm_id != EXACT_ALGORITHM_ID_V1:
            _fault("exact_algorithm_id_mismatch", ("exact", "algorithm_id"))
        if legacy.result_kind is not exact.result_kind:
            return _mismatch(
                "result_kind_mismatch",
                ("result_kind",),
                legacy.result_kind.value,
                exact.result_kind.value,
            )
        if exact.result_kind is ObservationResultKindV1.REJECT:
            _check_reject_receipt(validated)
            return RefinesV1(_witness(validated, deltas))
        evidence = _accepted_evidence(validated)
        mismatch = _compare_accept_semantics(validated, evidence)
        if mismatch is not None:
            return mismatch
        return RefinesV1(_witness(validated, deltas))
    except _EvidenceFault as fault:
        return InvalidEvidenceV1(fault.code, fault.path)
    except (AttributeError, KeyError, OverflowError, TypeError, UnicodeEncodeError, ValueError):
        return InvalidEvidenceV1("refinement_evaluation_invalid", ())


__all__ = ("evaluate_refinement_v1",)
