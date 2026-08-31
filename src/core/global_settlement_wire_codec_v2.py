"""Canonical codec for the strict, wire-only GlobalSettlementABI V2 records.

There is no schema discriminator for these records.  Exact closed top-level
field sets select the record type, then exact nested field sets select every
typed V2 component.  Decoding accepted records never constructs an accepted
domain witness; only context and candidate records expose safe input builders.
"""

from __future__ import annotations

import json
from collections.abc import Callable
from typing import Final, TypeVar

from .asset_lane_coordinator_values_v2 import (
    AssetLaneCoordinatorRejectCodeV2,
    AssetLaneRouteV2,
)
from .asset_lane_state_v2 import AssetLaneStateV2
from .asset_origin_registry_types_v2 import (
    ASSET_ORIGIN_REGISTRY_SCHEMA_V2,
    AssetOriginKindV2,
    AssetOriginRecordV2,
    AssetOriginRegistrationPolicyV2,
    AssetOriginRegistrationRejectCodeV2,
    AssetOriginRegistryStateV2,
)
from .asset_transfer_types_v2 import (
    AssetClassV2,
    AssetTransferPolicyV2,
    AssetTransferRejectCodeV2,
)
from .global_economic_proof_v2 import (
    EconomicCommandOccurrenceV2,
    LaneModuleTransitionJournalV2,
)
from .global_economic_refinement_outcome_v2 import GlobalEconomicRefinementRejectCodeV2
from .global_economic_state_ownership_v2 import (
    LaneStateRootV2,
    OutboxStateV2,
    OutboxStatusV2,
    ReplayStateV2,
)
from .global_economic_state_v2 import GlobalEconomicStateV2
from .global_settlement_resource_limits_v2 import (
    MAX_ASSETS_PER_ASSET_STATE_V2,
    MAX_BALANCE_ROWS_PER_ASSET_STATE_V2,
    MAX_CONSUMED_OBJECT_IDS_PER_OCCURRENCE_V2,
    MAX_CONSUMED_OCCURRENCES_PER_REFINEMENT_V2,
)
from .global_settlement_types_v2 import (
    GLOBAL_SETTLEMENT_ABI_V2,
    AssetConservationRowV2,
    AssetSupplyV2,
    EconomicAmountV2,
    EconomicEffectKindV2,
    EconomicEffectRowV2,
    ExternalOutboxEnqueueV2,
    FeeConservationRowV2,
    GlobalEconomicEffectPlanV2,
    GlobalOracleOccurrencePlanV2,
    GlobalTerminalObligationPlanV2,
    LaneIdV2,
    LaneWriteV2,
    OracleOccurrenceDeltaV2,
    OracleOccurrenceStateV2,
    TerminalObligationDeltaV2,
    TerminalObligationStatusV2,
    TerminalObligationV2,
    canonical_global_bytes_v2,
)
from .global_settlement_wire_records_v2 import (
    AssetLaneAcceptedWireV2,
    AssetLaneContextWireV2,
    AssetLaneRejectedWireV2,
    AssetOriginRegistrationAcceptedWireV2,
    AssetOriginRegistrationRejectedWireV2,
    GlobalEconomicRefinementAcceptedWireV2,
    GlobalEconomicRefinementRejectedWireV2,
    GlobalEconomicStateEffectRefinementCandidateWireV2,
    GlobalEconomicStateEffectRefinementWireV2,
    ManagedAssetLifecycleAcceptedWireV2,
    ManagedAssetLifecycleRejectedWireV2,
    WireRecordV2,
    wire_record_from_domain_v2,
)
from .managed_asset_lifecycle_types_v2 import (
    MANAGED_ASSET_LIFECYCLE_MODULE_SCHEMA_V2,
    ManagedAssetLifecyclePolicyV2,
    ManagedAssetLifecycleRejectCodeV2,
    ManagedAssetLifecycleStateV2,
)

MAX_GLOBAL_SETTLEMENT_WIRE_RECORD_CODEC_BYTES_V2: Final = 1_048_576
# This transport/decode ceiling intentionally has the same numeric value as
# the rootable asset-state byte ceiling.  It does not refine
# GlobalEconomicStateV2 construction or its existing 65,536-row tables.


class GlobalSettlementWireCodecErrorV2(ValueError):
    """One deterministic malformed, noncanonical, or invalid wire failure."""


GlobalSettlementWireRecordCodecErrorV2 = GlobalSettlementWireCodecErrorV2

_T = TypeVar("_T")


def _require_wire_record_codec_bytes_v2(raw: object) -> bytes:
    """Apply the transport envelope shared by canonical encode and decode."""

    if type(raw) is not bytes:
        raise GlobalSettlementWireCodecErrorV2("wire record must be exact bytes")
    if len(raw) > MAX_GLOBAL_SETTLEMENT_WIRE_RECORD_CODEC_BYTES_V2:
        raise GlobalSettlementWireCodecErrorV2("wire record exceeds the codec byte bound")
    return raw


def _construct_v2(builder: Callable[[], _T]) -> _T:
    try:
        return builder()
    except GlobalSettlementWireCodecErrorV2:
        raise
    except (TypeError, ValueError) as exc:
        raise GlobalSettlementWireCodecErrorV2(str(exc)) from exc


def _object_from_pairs_v2(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise GlobalSettlementWireCodecErrorV2(f"duplicate field: {key}")
        result[key] = value
    return result


def _reject_float_v2(_value: str) -> object:
    raise GlobalSettlementWireCodecErrorV2("floating-point values are unsupported")


def _reject_constant_v2(value: str) -> object:
    raise GlobalSettlementWireCodecErrorV2(f"non-finite JSON value is unsupported: {value}")


def _load_canonical_object_v2(raw: bytes) -> dict[str, object]:
    raw = _require_wire_record_codec_bytes_v2(raw)
    if not raw:
        raise GlobalSettlementWireCodecErrorV2("wire record must not be empty")
    try:
        value = json.loads(
            raw.decode("utf-8"),
            object_pairs_hook=_object_from_pairs_v2,
            parse_float=_reject_float_v2,
            parse_constant=_reject_constant_v2,
        )
    except GlobalSettlementWireCodecErrorV2:
        raise
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise GlobalSettlementWireCodecErrorV2("wire record is invalid JSON") from exc
    if type(value) is not dict:
        raise GlobalSettlementWireCodecErrorV2("wire record must be an object")
    if canonical_global_bytes_v2(value) != raw:
        raise GlobalSettlementWireCodecErrorV2("wire record is not canonical")
    return value


def _expect_object_v2(value: object, *, name: str) -> dict[str, object]:
    if type(value) is not dict:
        raise GlobalSettlementWireCodecErrorV2(f"{name} must be an object")
    return value


def _expect_fields_v2(
    value: dict[str, object],
    expected: frozenset[str],
    *,
    name: str,
) -> None:
    actual = frozenset(value)
    if actual != expected:
        missing = sorted(expected - actual)
        unknown = sorted(actual - expected)
        raise GlobalSettlementWireCodecErrorV2(
            f"{name} field set mismatch; missing={missing}; unknown={unknown}"
        )


def _expect_text_v2(value: object, *, name: str) -> str:
    if type(value) is not str:
        raise GlobalSettlementWireCodecErrorV2(f"{name} must be exact text")
    return value


def _expect_optional_text_v2(value: object, *, name: str) -> str | None:
    return None if value is None else _expect_text_v2(value, name=name)


def _expect_nonnegative_integer_v2(value: object, *, name: str) -> int:
    if type(value) is not int or value < 0:
        raise GlobalSettlementWireCodecErrorV2(f"{name} must be a non-negative integer")
    return value


def _expect_integer_v2(value: object, *, name: str) -> int:
    if type(value) is not int:
        raise GlobalSettlementWireCodecErrorV2(f"{name} must be an integer")
    return value


def _expect_boolean_v2(value: object, *, name: str) -> bool:
    if type(value) is not bool:
        raise GlobalSettlementWireCodecErrorV2(f"{name} must be bool")
    return value


def _expect_array_v2(
    value: object,
    *,
    name: str,
    limit: int | None = None,
) -> list[object]:
    if type(value) is not list:
        raise GlobalSettlementWireCodecErrorV2(f"{name} must be an array")
    if limit is not None and len(value) > limit:
        raise GlobalSettlementWireCodecErrorV2(f"{name} exceeds its {limit}-item ceiling")
    return value


def _expect_object_array_v2(
    value: object,
    *,
    name: str,
    limit: int | None = None,
) -> tuple[dict[str, object], ...]:
    return tuple(
        _expect_object_v2(item, name=f"{name}[{index}]")
        for index, item in enumerate(_expect_array_v2(value, name=name, limit=limit))
    )


def _expect_text_array_v2(
    value: object,
    *,
    name: str,
    limit: int | None = None,
) -> tuple[str, ...]:
    return tuple(
        _expect_text_v2(item, name=f"{name}[{index}]")
        for index, item in enumerate(_expect_array_v2(value, name=name, limit=limit))
    )


def _decode_enum_v2(
    value: object,
    enum_type: type[_T],
    *,
    name: str,
) -> _T:
    text = _expect_text_v2(value, name=name)
    try:
        return enum_type(text)  # type: ignore[call-arg]
    except ValueError as exc:
        raise GlobalSettlementWireCodecErrorV2(f"{name} is unknown") from exc


_AMOUNT_FIELDS_V2 = frozenset({"owner", "asset", "custody_domain", "amount_atoms"})
_SUPPLY_FIELDS_V2 = frozenset({"asset", "amount_atoms"})
_EFFECT_ROW_FIELDS_V2 = frozenset({"kind", "principal", "asset", "custody_domain", "delta_atoms"})
_ASSET_CONSERVATION_FIELDS_V2 = frozenset(
    {
        "asset",
        "owned_and_custodied_pre_atoms",
        "owned_and_custodied_post_atoms",
        "supply_pre_atoms",
        "supply_post_atoms",
        "authorized_issue_atoms",
        "authorized_burn_atoms",
    }
)
_FEE_CONSERVATION_FIELDS_V2 = frozenset(
    {"asset", "fee_charged_atoms", "current_allocations_atoms", "carried_residue_atoms"}
)
_LANE_WRITE_FIELDS_V2 = frozenset({"lane_id", "pre_root", "post_root"})
_EXTERNAL_OUTBOX_FIELDS_V2 = frozenset(
    {"effect_id", "destination_id", "payload_hash", "adapter_profile_root"}
)
_EFFECT_PLAN_FIELDS_V2 = frozenset(
    {
        "schema",
        "rows",
        "asset_conservation",
        "fee_conservation",
        "lane_writes",
        "occurrence_consumptions",
        "external_outbox_enqueue",
    }
)
_OCCURRENCE_FIELDS_V2 = frozenset(
    {
        "schema",
        "chain_id",
        "deployment_root",
        "height",
        "tx_index",
        "op_index",
        "command_kind",
        "command_body_hash",
        "route_release_id",
        "subject_id",
        "grant_root",
        "nonce",
        "profile_root",
        "pre_state_root",
        "consumed_object_ids",
    }
)
_JOURNAL_FIELDS_V2 = frozenset(
    {
        "schema",
        "chain_id",
        "deployment_root",
        "profile_root",
        "writer_epoch",
        "lane_id",
        "module_release_id",
        "command_occurrence_id",
        "pre_lane_root",
        "post_lane_root",
        "effect_plan_root",
        "private_port_root",
        "receipt_root",
        "terminal_obligations_root",
        "oracle_occurrence_plan_root",
    }
)


def _decode_amount_object_v2(value: dict[str, object]) -> EconomicAmountV2:
    _expect_fields_v2(value, _AMOUNT_FIELDS_V2, name="economic amount")
    return _construct_v2(
        lambda: EconomicAmountV2(
            _expect_text_v2(value["owner"], name="economic amount owner"),
            _expect_text_v2(value["asset"], name="economic amount asset"),
            _expect_text_v2(value["custody_domain"], name="economic amount custody domain"),
            _expect_nonnegative_integer_v2(value["amount_atoms"], name="economic amount atoms"),
        )
    )


def _decode_supply_object_v2(value: dict[str, object]) -> AssetSupplyV2:
    _expect_fields_v2(value, _SUPPLY_FIELDS_V2, name="asset supply")
    return _construct_v2(
        lambda: AssetSupplyV2(
            _expect_text_v2(value["asset"], name="asset supply asset"),
            _expect_nonnegative_integer_v2(value["amount_atoms"], name="asset supply atoms"),
        )
    )


def _decode_effect_row_object_v2(value: dict[str, object]) -> EconomicEffectRowV2:
    _expect_fields_v2(value, _EFFECT_ROW_FIELDS_V2, name="economic effect row")
    return _construct_v2(
        lambda: EconomicEffectRowV2(
            _decode_enum_v2(value["kind"], EconomicEffectKindV2, name="economic effect kind"),
            _expect_text_v2(value["principal"], name="economic effect principal"),
            _expect_text_v2(value["asset"], name="economic effect asset"),
            _expect_text_v2(value["custody_domain"], name="economic effect custody domain"),
            _expect_integer_v2(value["delta_atoms"], name="economic effect delta"),
        )
    )


def _decode_asset_conservation_object_v2(
    value: dict[str, object],
) -> AssetConservationRowV2:
    _expect_fields_v2(value, _ASSET_CONSERVATION_FIELDS_V2, name="asset conservation")
    return _construct_v2(
        lambda: AssetConservationRowV2(
            _expect_text_v2(value["asset"], name="asset conservation asset"),
            _expect_nonnegative_integer_v2(
                value["owned_and_custodied_pre_atoms"], name="owned pre"
            ),
            _expect_nonnegative_integer_v2(
                value["owned_and_custodied_post_atoms"], name="owned post"
            ),
            _expect_nonnegative_integer_v2(value["supply_pre_atoms"], name="supply pre"),
            _expect_nonnegative_integer_v2(value["supply_post_atoms"], name="supply post"),
            _expect_nonnegative_integer_v2(
                value["authorized_issue_atoms"], name="authorized issue"
            ),
            _expect_nonnegative_integer_v2(value["authorized_burn_atoms"], name="authorized burn"),
        )
    )


def _decode_fee_conservation_object_v2(value: dict[str, object]) -> FeeConservationRowV2:
    _expect_fields_v2(value, _FEE_CONSERVATION_FIELDS_V2, name="fee conservation")
    return _construct_v2(
        lambda: FeeConservationRowV2(
            _expect_text_v2(value["asset"], name="fee conservation asset"),
            _expect_nonnegative_integer_v2(value["fee_charged_atoms"], name="fee charged"),
            _expect_nonnegative_integer_v2(
                value["current_allocations_atoms"], name="fee allocations"
            ),
            _expect_nonnegative_integer_v2(value["carried_residue_atoms"], name="fee residue"),
        )
    )


def _decode_lane_write_object_v2(value: dict[str, object]) -> LaneWriteV2:
    _expect_fields_v2(value, _LANE_WRITE_FIELDS_V2, name="lane write")
    return _construct_v2(
        lambda: LaneWriteV2(
            _decode_enum_v2(value["lane_id"], LaneIdV2, name="lane write lane"),
            _expect_text_v2(value["pre_root"], name="lane write pre root"),
            _expect_text_v2(value["post_root"], name="lane write post root"),
        )
    )


def _decode_external_outbox_object_v2(value: dict[str, object]) -> ExternalOutboxEnqueueV2:
    _expect_fields_v2(value, _EXTERNAL_OUTBOX_FIELDS_V2, name="external outbox")
    return _construct_v2(
        lambda: ExternalOutboxEnqueueV2(
            _expect_text_v2(value["effect_id"], name="external outbox effect id"),
            _expect_text_v2(value["destination_id"], name="external outbox destination"),
            _expect_text_v2(value["payload_hash"], name="external outbox payload hash"),
            _expect_text_v2(value["adapter_profile_root"], name="external outbox profile root"),
        )
    )


def _decode_effect_plan_object_v2(value: dict[str, object]) -> GlobalEconomicEffectPlanV2:
    _expect_fields_v2(value, _EFFECT_PLAN_FIELDS_V2, name="economic effect plan")
    if value["schema"] != GLOBAL_SETTLEMENT_ABI_V2:
        raise GlobalSettlementWireCodecErrorV2("economic effect plan schema is not V2")
    rows = _expect_object_array_v2(value["rows"], name="effect plan rows", limit=4_096)
    asset_rows = _expect_object_array_v2(
        value["asset_conservation"], name="effect plan asset conservation", limit=256
    )
    fee_rows = _expect_object_array_v2(
        value["fee_conservation"], name="effect plan fee conservation", limit=256
    )
    lane_writes = _expect_object_array_v2(value["lane_writes"], name="effect plan lanes", limit=12)
    consumptions = _expect_text_array_v2(
        value["occurrence_consumptions"], name="effect plan consumptions", limit=64
    )
    outbox = _expect_object_array_v2(
        value["external_outbox_enqueue"], name="effect plan external outbox", limit=4_096
    )
    return _construct_v2(
        lambda: GlobalEconomicEffectPlanV2(
            tuple(_decode_effect_row_object_v2(item) for item in rows),
            tuple(_decode_asset_conservation_object_v2(item) for item in asset_rows),
            tuple(_decode_fee_conservation_object_v2(item) for item in fee_rows),
            tuple(_decode_lane_write_object_v2(item) for item in lane_writes),
            consumptions,
            tuple(_decode_external_outbox_object_v2(item) for item in outbox),
        )
    )


def _decode_occurrence_object_v2(value: dict[str, object]) -> EconomicCommandOccurrenceV2:
    _expect_fields_v2(value, _OCCURRENCE_FIELDS_V2, name="occurrence")
    if value["schema"] != GLOBAL_SETTLEMENT_ABI_V2:
        raise GlobalSettlementWireCodecErrorV2("occurrence schema is not V2")
    object_ids = _expect_text_array_v2(
        value["consumed_object_ids"],
        name="occurrence consumed object ids",
        limit=MAX_CONSUMED_OBJECT_IDS_PER_OCCURRENCE_V2,
    )
    return _construct_v2(
        lambda: EconomicCommandOccurrenceV2(
            _expect_text_v2(value["chain_id"], name="occurrence chain id"),
            _expect_text_v2(value["deployment_root"], name="occurrence deployment root"),
            _expect_nonnegative_integer_v2(value["height"], name="occurrence height"),
            _expect_nonnegative_integer_v2(value["tx_index"], name="occurrence tx index"),
            _expect_nonnegative_integer_v2(value["op_index"], name="occurrence op index"),
            _expect_text_v2(value["command_kind"], name="occurrence command kind"),
            _expect_text_v2(value["command_body_hash"], name="occurrence command hash"),
            _expect_text_v2(value["route_release_id"], name="occurrence release"),
            _expect_text_v2(value["subject_id"], name="occurrence subject"),
            _expect_text_v2(value["grant_root"], name="occurrence grant"),
            _expect_nonnegative_integer_v2(value["nonce"], name="occurrence nonce"),
            _expect_text_v2(value["profile_root"], name="occurrence profile"),
            _expect_text_v2(value["pre_state_root"], name="occurrence pre-state"),
            object_ids,
        )
    )


def _decode_journal_object_v2(value: dict[str, object]) -> LaneModuleTransitionJournalV2:
    _expect_fields_v2(value, _JOURNAL_FIELDS_V2, name="module journal")
    if value["schema"] != GLOBAL_SETTLEMENT_ABI_V2:
        raise GlobalSettlementWireCodecErrorV2("module journal schema is not V2")
    return _construct_v2(
        lambda: LaneModuleTransitionJournalV2(
            _expect_text_v2(value["chain_id"], name="journal chain id"),
            _expect_text_v2(value["deployment_root"], name="journal deployment root"),
            _expect_text_v2(value["profile_root"], name="journal profile root"),
            _expect_nonnegative_integer_v2(value["writer_epoch"], name="journal writer epoch"),
            _decode_enum_v2(value["lane_id"], LaneIdV2, name="journal lane"),
            _expect_text_v2(value["module_release_id"], name="journal module release"),
            _expect_text_v2(value["command_occurrence_id"], name="journal occurrence"),
            _expect_text_v2(value["pre_lane_root"], name="journal pre root"),
            _expect_text_v2(value["post_lane_root"], name="journal post root"),
            _expect_text_v2(value["effect_plan_root"], name="journal effect root"),
            _expect_text_v2(value["private_port_root"], name="journal private root"),
            _expect_text_v2(value["receipt_root"], name="journal receipt root"),
            _expect_text_v2(value["terminal_obligations_root"], name="journal terminal root"),
            _expect_text_v2(value["oracle_occurrence_plan_root"], name="journal Oracle root"),
        )
    )


_ORACLE_STATE_FIELDS_V2 = frozenset(
    {"oracle_id", "occurrence_root", "observed_height", "finalized"}
)
_ORACLE_DELTA_FIELDS_V2 = frozenset({"oracle_id", "pre_occurrence", "post_occurrence"})
_ORACLE_PLAN_FIELDS_V2 = frozenset({"schema", "deltas"})
_TERMINAL_FIELDS_V2 = frozenset(
    {
        "obligation_id",
        "lane_id",
        "claimant",
        "asset",
        "liability_domain",
        "amount_atoms",
        "status",
    }
)
_TERMINAL_DELTA_FIELDS_V2 = frozenset({"obligation_id", "pre_obligation", "post_obligation"})
_TERMINAL_PLAN_FIELDS_V2 = frozenset({"schema", "deltas"})


def _decode_oracle_state_object_v2(value: dict[str, object]) -> OracleOccurrenceStateV2:
    _expect_fields_v2(value, _ORACLE_STATE_FIELDS_V2, name="Oracle occurrence state")
    return _construct_v2(
        lambda: OracleOccurrenceStateV2(
            _expect_text_v2(value["oracle_id"], name="Oracle id"),
            _expect_text_v2(value["occurrence_root"], name="Oracle root"),
            _expect_nonnegative_integer_v2(value["observed_height"], name="Oracle height"),
            _expect_boolean_v2(value["finalized"], name="Oracle finalized"),
        )
    )


def _decode_oracle_delta_object_v2(value: dict[str, object]) -> OracleOccurrenceDeltaV2:
    _expect_fields_v2(value, _ORACLE_DELTA_FIELDS_V2, name="Oracle occurrence delta")
    pre_value = value["pre_occurrence"]
    return _construct_v2(
        lambda: OracleOccurrenceDeltaV2(
            _expect_text_v2(value["oracle_id"], name="Oracle delta id"),
            None
            if pre_value is None
            else _decode_oracle_state_object_v2(
                _expect_object_v2(pre_value, name="Oracle delta pre-value")
            ),
            _decode_oracle_state_object_v2(
                _expect_object_v2(value["post_occurrence"], name="Oracle delta post-value")
            ),
        )
    )


def _decode_oracle_plan_object_v2(value: dict[str, object]) -> GlobalOracleOccurrencePlanV2:
    _expect_fields_v2(value, _ORACLE_PLAN_FIELDS_V2, name="Oracle plan")
    if value["schema"] != GLOBAL_SETTLEMENT_ABI_V2:
        raise GlobalSettlementWireCodecErrorV2("Oracle plan schema is not V2")
    deltas = _expect_object_array_v2(value["deltas"], name="Oracle plan deltas", limit=64)
    return _construct_v2(
        lambda: GlobalOracleOccurrencePlanV2(
            tuple(_decode_oracle_delta_object_v2(item) for item in deltas)
        )
    )


def _decode_terminal_object_v2(value: dict[str, object]) -> TerminalObligationV2:
    _expect_fields_v2(value, _TERMINAL_FIELDS_V2, name="terminal obligation")
    return _construct_v2(
        lambda: TerminalObligationV2(
            _expect_text_v2(value["obligation_id"], name="terminal id"),
            _decode_enum_v2(value["lane_id"], LaneIdV2, name="terminal lane"),
            _expect_text_v2(value["claimant"], name="terminal claimant"),
            _expect_text_v2(value["asset"], name="terminal asset"),
            _expect_text_v2(value["liability_domain"], name="terminal liability domain"),
            _expect_nonnegative_integer_v2(value["amount_atoms"], name="terminal amount"),
            _decode_enum_v2(value["status"], TerminalObligationStatusV2, name="terminal status"),
        )
    )


def _decode_terminal_delta_object_v2(value: dict[str, object]) -> TerminalObligationDeltaV2:
    _expect_fields_v2(value, _TERMINAL_DELTA_FIELDS_V2, name="terminal delta")
    pre_value = value["pre_obligation"]
    return _construct_v2(
        lambda: TerminalObligationDeltaV2(
            _expect_text_v2(value["obligation_id"], name="terminal delta id"),
            None
            if pre_value is None
            else _decode_terminal_object_v2(
                _expect_object_v2(pre_value, name="terminal delta pre-value")
            ),
            _decode_terminal_object_v2(
                _expect_object_v2(value["post_obligation"], name="terminal delta post-value")
            ),
        )
    )


def _decode_terminal_plan_object_v2(value: dict[str, object]) -> GlobalTerminalObligationPlanV2:
    _expect_fields_v2(value, _TERMINAL_PLAN_FIELDS_V2, name="terminal plan")
    if value["schema"] != GLOBAL_SETTLEMENT_ABI_V2:
        raise GlobalSettlementWireCodecErrorV2("terminal plan schema is not V2")
    deltas = _expect_object_array_v2(value["deltas"], name="terminal plan deltas", limit=64)
    return _construct_v2(
        lambda: GlobalTerminalObligationPlanV2(
            tuple(_decode_terminal_delta_object_v2(item) for item in deltas)
        )
    )


_LANE_STATE_ROOT_FIELDS_V2 = frozenset({"lane_id", "module_release_id", "enabled", "state_root"})
_REPLAY_STATE_FIELDS_V2 = frozenset({"replay_id", "occurrence_id"})
_OUTBOX_STATE_FIELDS_V2 = frozenset(
    {"effect_id", "destination_id", "payload_hash", "adapter_profile_root", "commit_id", "status"}
)
_GLOBAL_STATE_FIELDS_V2 = frozenset(
    {
        "schema",
        "chain_id",
        "deployment_root",
        "writer_epoch",
        "height",
        "profile_root",
        "lane_roots",
        "balances",
        "supplies",
        "custody",
        "liabilities",
        "reserves",
        "oracle_occurrences",
        "replay_state",
        "terminal_obligations",
        "history_root",
        "outbox",
    }
)


def _decode_lane_state_root_object_v2(value: dict[str, object]) -> LaneStateRootV2:
    _expect_fields_v2(value, _LANE_STATE_ROOT_FIELDS_V2, name="lane state root")
    return _construct_v2(
        lambda: LaneStateRootV2(
            _decode_enum_v2(value["lane_id"], LaneIdV2, name="lane state lane"),
            _expect_text_v2(value["module_release_id"], name="lane state release"),
            _expect_boolean_v2(value["enabled"], name="lane state enabled"),
            _expect_text_v2(value["state_root"], name="lane state root"),
        )
    )


def _decode_replay_state_object_v2(value: dict[str, object]) -> ReplayStateV2:
    _expect_fields_v2(value, _REPLAY_STATE_FIELDS_V2, name="replay state")
    return _construct_v2(
        lambda: ReplayStateV2(
            _expect_text_v2(value["replay_id"], name="replay id"),
            _expect_text_v2(value["occurrence_id"], name="replay occurrence"),
        )
    )


def _decode_outbox_state_object_v2(value: dict[str, object]) -> OutboxStateV2:
    _expect_fields_v2(value, _OUTBOX_STATE_FIELDS_V2, name="outbox state")
    return _construct_v2(
        lambda: OutboxStateV2(
            _expect_text_v2(value["effect_id"], name="outbox effect id"),
            _expect_text_v2(value["destination_id"], name="outbox destination"),
            _expect_text_v2(value["payload_hash"], name="outbox payload hash"),
            _expect_text_v2(value["adapter_profile_root"], name="outbox profile root"),
            _expect_text_v2(value["commit_id"], name="outbox commit id"),
            _decode_enum_v2(value["status"], OutboxStatusV2, name="outbox status"),
        )
    )


def _decode_global_state_object_v2(value: dict[str, object]) -> GlobalEconomicStateV2:
    _expect_fields_v2(value, _GLOBAL_STATE_FIELDS_V2, name="global economic state")
    if value["schema"] != GLOBAL_SETTLEMENT_ABI_V2:
        raise GlobalSettlementWireCodecErrorV2("global economic state schema is not V2")
    lane_roots = _expect_object_array_v2(value["lane_roots"], name="global lane roots", limit=12)
    balances = _expect_object_array_v2(value["balances"], name="global balances")
    supplies = _expect_object_array_v2(value["supplies"], name="global supplies")
    custody = _expect_object_array_v2(value["custody"], name="global custody")
    liabilities = _expect_object_array_v2(value["liabilities"], name="global liabilities")
    reserves = _expect_object_array_v2(value["reserves"], name="global reserves")
    oracle = _expect_object_array_v2(value["oracle_occurrences"], name="global Oracle rows")
    replay = _expect_object_array_v2(value["replay_state"], name="global replay rows")
    terminal = _expect_object_array_v2(value["terminal_obligations"], name="global terminal rows")
    outbox = _expect_object_array_v2(value["outbox"], name="global outbox rows")
    return _construct_v2(
        lambda: GlobalEconomicStateV2(
            _expect_text_v2(value["chain_id"], name="global chain id"),
            _expect_text_v2(value["deployment_root"], name="global deployment root"),
            _expect_nonnegative_integer_v2(value["writer_epoch"], name="global writer epoch"),
            _expect_nonnegative_integer_v2(value["height"], name="global height"),
            _expect_text_v2(value["profile_root"], name="global profile root"),
            tuple(_decode_lane_state_root_object_v2(item) for item in lane_roots),
            tuple(_decode_amount_object_v2(item) for item in balances),
            tuple(_decode_supply_object_v2(item) for item in supplies),
            tuple(_decode_amount_object_v2(item) for item in custody),
            tuple(_decode_amount_object_v2(item) for item in liabilities),
            tuple(_decode_amount_object_v2(item) for item in reserves),
            tuple(_decode_oracle_state_object_v2(item) for item in oracle),
            tuple(_decode_replay_state_object_v2(item) for item in replay),
            tuple(_decode_terminal_object_v2(item) for item in terminal),
            _expect_text_v2(value["history_root"], name="global history root"),
            tuple(_decode_outbox_state_object_v2(item) for item in outbox),
        )
    )


_TRANSFER_POLICY_FIELDS_V2 = frozenset(
    {
        "asset",
        "fee_owner",
        "transfer_fee_atoms",
        "enabled",
        "asset_class",
        "asset_origin_root",
        "atom_decimals",
    }
)
_MANAGED_POLICY_FIELDS_V2 = frozenset(
    {
        "asset",
        "asset_class",
        "asset_origin_root",
        "atom_decimals",
        "issue_authority_subject",
        "issue_authorization_root",
        "burn_authorization_root",
        "enabled",
    }
)
_MANAGED_STATE_FIELDS_V2 = frozenset(
    {"schema", "module_release_id", "policies", "balances", "supplies"}
)
_ORIGIN_RECORD_FIELDS_V2 = frozenset(
    {
        "asset",
        "origin_kind",
        "origin_root",
        "transfer_policy_root",
        "issue_policy_root",
        "decimals",
        "asset_class",
    }
)
_ORIGIN_POLICY_FIELDS_V2 = frozenset(
    {"authority_subject", "authority_grant_root", "allow_native", "allow_tau_originated"}
)
_ORIGIN_STATE_FIELDS_V2 = frozenset({"schema", "module_release_id", "policy", "assets"})
_ASSET_LANE_STATE_FIELDS_V2 = frozenset(
    {
        "schema",
        "module_release_id",
        "origin_registry",
        "transfer_policies",
        "managed_policies",
        "balances",
        "supplies",
    }
)


def _decode_transfer_policy_object_v2(value: dict[str, object]) -> AssetTransferPolicyV2:
    _expect_fields_v2(value, _TRANSFER_POLICY_FIELDS_V2, name="asset transfer policy")
    return _construct_v2(
        lambda: AssetTransferPolicyV2(
            _expect_text_v2(value["asset"], name="transfer policy asset"),
            _expect_text_v2(value["fee_owner"], name="transfer policy fee owner"),
            _expect_nonnegative_integer_v2(value["transfer_fee_atoms"], name="transfer policy fee"),
            _expect_boolean_v2(value["enabled"], name="transfer policy enabled"),
            _decode_enum_v2(value["asset_class"], AssetClassV2, name="transfer policy class"),
            _expect_optional_text_v2(value["asset_origin_root"], name="transfer policy origin"),
            _expect_nonnegative_integer_v2(value["atom_decimals"], name="transfer policy decimals"),
        )
    )


def _decode_managed_policy_object_v2(
    value: dict[str, object],
) -> ManagedAssetLifecyclePolicyV2:
    _expect_fields_v2(value, _MANAGED_POLICY_FIELDS_V2, name="managed asset policy")
    return _construct_v2(
        lambda: ManagedAssetLifecyclePolicyV2(
            _expect_text_v2(value["asset"], name="managed policy asset"),
            _decode_enum_v2(value["asset_class"], AssetClassV2, name="managed policy class"),
            _expect_optional_text_v2(value["asset_origin_root"], name="managed policy origin"),
            _expect_nonnegative_integer_v2(value["atom_decimals"], name="managed policy decimals"),
            _expect_optional_text_v2(
                value["issue_authority_subject"], name="managed policy issue subject"
            ),
            _expect_optional_text_v2(
                value["issue_authorization_root"], name="managed policy issue root"
            ),
            _expect_optional_text_v2(
                value["burn_authorization_root"], name="managed policy burn root"
            ),
            _expect_boolean_v2(value["enabled"], name="managed policy enabled"),
        )
    )


def _decode_managed_state_object_v2(value: dict[str, object]) -> ManagedAssetLifecycleStateV2:
    _expect_fields_v2(value, _MANAGED_STATE_FIELDS_V2, name="managed asset state")
    if value["schema"] != MANAGED_ASSET_LIFECYCLE_MODULE_SCHEMA_V2:
        raise GlobalSettlementWireCodecErrorV2("managed asset state schema is not V2")
    policies = _expect_object_array_v2(
        value["policies"], name="managed asset policies", limit=MAX_ASSETS_PER_ASSET_STATE_V2
    )
    balances = _expect_object_array_v2(
        value["balances"], name="managed asset balances", limit=MAX_BALANCE_ROWS_PER_ASSET_STATE_V2
    )
    supplies = _expect_object_array_v2(
        value["supplies"], name="managed asset supplies", limit=MAX_ASSETS_PER_ASSET_STATE_V2
    )
    return _construct_v2(
        lambda: ManagedAssetLifecycleStateV2(
            _expect_text_v2(value["module_release_id"], name="managed asset release"),
            tuple(_decode_managed_policy_object_v2(item) for item in policies),
            tuple(_decode_amount_object_v2(item) for item in balances),
            tuple(_decode_supply_object_v2(item) for item in supplies),
        )
    )


def _decode_origin_record_object_v2(value: dict[str, object]) -> AssetOriginRecordV2:
    _expect_fields_v2(value, _ORIGIN_RECORD_FIELDS_V2, name="asset origin record")
    return _construct_v2(
        lambda: AssetOriginRecordV2(
            _expect_text_v2(value["asset"], name="origin record asset"),
            _decode_enum_v2(value["origin_kind"], AssetOriginKindV2, name="origin record kind"),
            _expect_text_v2(value["origin_root"], name="origin record root"),
            _expect_text_v2(value["transfer_policy_root"], name="origin transfer root"),
            _expect_text_v2(value["issue_policy_root"], name="origin issue root"),
            _expect_nonnegative_integer_v2(value["decimals"], name="origin decimals"),
            _decode_enum_v2(value["asset_class"], AssetClassV2, name="origin class"),
        )
    )


def _decode_origin_policy_object_v2(value: dict[str, object]) -> AssetOriginRegistrationPolicyV2:
    _expect_fields_v2(value, _ORIGIN_POLICY_FIELDS_V2, name="asset origin policy")
    return _construct_v2(
        lambda: AssetOriginRegistrationPolicyV2(
            _expect_text_v2(value["authority_subject"], name="origin authority"),
            _expect_text_v2(value["authority_grant_root"], name="origin grant root"),
            _expect_boolean_v2(value["allow_native"], name="origin allow native"),
            _expect_boolean_v2(value["allow_tau_originated"], name="origin allow Tau originated"),
        )
    )


def _decode_origin_state_object_v2(value: dict[str, object]) -> AssetOriginRegistryStateV2:
    _expect_fields_v2(value, _ORIGIN_STATE_FIELDS_V2, name="asset origin state")
    if value["schema"] != ASSET_ORIGIN_REGISTRY_SCHEMA_V2:
        raise GlobalSettlementWireCodecErrorV2("asset origin state schema is not V2")
    assets = _expect_object_array_v2(
        value["assets"], name="asset origin rows", limit=MAX_ASSETS_PER_ASSET_STATE_V2
    )
    return _construct_v2(
        lambda: AssetOriginRegistryStateV2(
            _expect_text_v2(value["module_release_id"], name="asset origin release"),
            _decode_origin_policy_object_v2(
                _expect_object_v2(value["policy"], name="asset origin policy")
            ),
            tuple(_decode_origin_record_object_v2(item) for item in assets),
        )
    )


def _decode_asset_lane_state_object_v2(value: dict[str, object]) -> AssetLaneStateV2:
    _expect_fields_v2(value, _ASSET_LANE_STATE_FIELDS_V2, name="asset lane state")
    if value["schema"] != "zenodex/asset-lane-state/v2":
        raise GlobalSettlementWireCodecErrorV2("asset lane state schema is not V2")
    transfer = _expect_object_array_v2(
        value["transfer_policies"],
        name="asset lane transfer policies",
        limit=MAX_ASSETS_PER_ASSET_STATE_V2,
    )
    managed = _expect_object_array_v2(
        value["managed_policies"],
        name="asset lane managed policies",
        limit=MAX_ASSETS_PER_ASSET_STATE_V2,
    )
    balances = _expect_object_array_v2(
        value["balances"], name="asset lane balances", limit=MAX_BALANCE_ROWS_PER_ASSET_STATE_V2
    )
    supplies = _expect_object_array_v2(
        value["supplies"], name="asset lane supplies", limit=MAX_ASSETS_PER_ASSET_STATE_V2
    )
    return _construct_v2(
        lambda: AssetLaneStateV2(
            _expect_text_v2(value["module_release_id"], name="asset lane release"),
            _decode_origin_state_object_v2(
                _expect_object_v2(value["origin_registry"], name="asset lane registry")
            ),
            tuple(_decode_transfer_policy_object_v2(item) for item in transfer),
            tuple(_decode_managed_policy_object_v2(item) for item in managed),
            tuple(_decode_amount_object_v2(item) for item in balances),
            tuple(_decode_supply_object_v2(item) for item in supplies),
        )
    )


_GLOBAL_REFINEMENT_ACCEPTED_FIELDS_V2 = frozenset({"witness", "production_authority"})
_GLOBAL_REFINEMENT_REJECTED_FIELDS_V2 = frozenset(
    {
        "reject_code",
        "pre_state_root",
        "post_state_root",
        "effect_plan",
        "terminal_plan",
        "oracle_plan",
        "consumed_occurrences",
        "outbox",
        "production_authority",
    }
)
_MANAGED_ACCEPTED_FIELDS_V2 = frozenset(
    {"post_state", "effects", "module_journal", "receipt_root", "production_authority"}
)
_MANAGED_REJECTED_FIELDS_V2 = frozenset(
    {
        "code",
        "pre_state_root",
        "post_state_root",
        "effects",
        "terminal_obligations_root",
        "oracle_occurrence_plan_root",
        "production_authority",
    }
)
_ORIGIN_ACCEPTED_FIELDS_V2 = frozenset(
    {"post_state", "effects", "module_journal", "production_authority"}
)
_ORIGIN_REJECTED_FIELDS_V2 = frozenset({"code", "pre_state_root", "post_state_root", "effects"})
_ASSET_LANE_CONTEXT_FIELDS_V2 = frozenset(
    {"writer_epoch", "module_release_id", "global_pre_state_root", "occurrence"}
)
_ASSET_LANE_ACCEPTED_FIELDS_V2 = frozenset(
    {
        "route",
        "source_leaf_journal_root",
        "post_state",
        "effects",
        "module_journal",
        "receipt_root",
        "production_authority",
        "profile_authentication",
    }
)
_ASSET_LANE_REJECTED_FIELDS_V2 = frozenset(
    {
        "route",
        "code",
        "pre_state_root",
        "post_state_root",
        "effects",
        "production_authority",
        "profile_authentication",
    }
)
_REFINEMENT_CANDIDATE_FIELDS_V2 = frozenset(
    {
        "pre_state",
        "post_state",
        "effect_plan",
        "consumed_occurrences",
        "terminal_plan",
        "oracle_plan",
    }
)
_REFINEMENT_FIELDS_V2 = frozenset(
    {
        "pre_state_root",
        "post_state_root",
        "effect_plan_root",
        "terminal_plan_root",
        "oracle_plan_root",
        "state_delta_root",
        "production_authority",
        "refinement_root",
    }
)

WIRE_RECORD_FIELD_SETS_V2 = {
    "GlobalEconomicRefinementAcceptedWireV2": _GLOBAL_REFINEMENT_ACCEPTED_FIELDS_V2,
    "GlobalEconomicRefinementRejectedWireV2": _GLOBAL_REFINEMENT_REJECTED_FIELDS_V2,
    "ManagedAssetLifecycleAcceptedWireV2": _MANAGED_ACCEPTED_FIELDS_V2,
    "ManagedAssetLifecycleRejectedWireV2": _MANAGED_REJECTED_FIELDS_V2,
    "AssetOriginRegistrationAcceptedWireV2": _ORIGIN_ACCEPTED_FIELDS_V2,
    "AssetOriginRegistrationRejectedWireV2": _ORIGIN_REJECTED_FIELDS_V2,
    "AssetLaneContextWireV2": _ASSET_LANE_CONTEXT_FIELDS_V2,
    "AssetLaneAcceptedWireV2": _ASSET_LANE_ACCEPTED_FIELDS_V2,
    "AssetLaneRejectedWireV2": _ASSET_LANE_REJECTED_FIELDS_V2,
    "GlobalEconomicStateEffectRefinementCandidateWireV2": _REFINEMENT_CANDIDATE_FIELDS_V2,
    "GlobalEconomicStateEffectRefinementWireV2": _REFINEMENT_FIELDS_V2,
}


def _decode_global_refinement_accepted_v2(
    value: dict[str, object],
) -> GlobalEconomicRefinementAcceptedWireV2:
    _expect_fields_v2(value, _GLOBAL_REFINEMENT_ACCEPTED_FIELDS_V2, name="global accepted")
    return _construct_v2(
        lambda: GlobalEconomicRefinementAcceptedWireV2(
            _decode_refinement_v2(_expect_object_v2(value["witness"], name="global witness")),
            _expect_text_v2(value["production_authority"], name="global accepted authority"),
        )
    )


def _decode_global_refinement_rejected_v2(
    value: dict[str, object],
) -> GlobalEconomicRefinementRejectedWireV2:
    _expect_fields_v2(value, _GLOBAL_REFINEMENT_REJECTED_FIELDS_V2, name="global rejected")
    occurrences = _expect_object_array_v2(
        value["consumed_occurrences"],
        name="global rejected occurrences",
        limit=MAX_CONSUMED_OCCURRENCES_PER_REFINEMENT_V2,
    )
    outbox = _expect_object_array_v2(value["outbox"], name="global rejected outbox")
    return _construct_v2(
        lambda: GlobalEconomicRefinementRejectedWireV2(
            _decode_enum_v2(
                value["reject_code"],
                GlobalEconomicRefinementRejectCodeV2,
                name="global reject code",
            ),
            _expect_text_v2(value["pre_state_root"], name="global rejected pre root"),
            _expect_text_v2(value["post_state_root"], name="global rejected post root"),
            _decode_effect_plan_object_v2(
                _expect_object_v2(value["effect_plan"], name="global effects")
            ),
            _decode_terminal_plan_object_v2(
                _expect_object_v2(value["terminal_plan"], name="global terminal plan")
            ),
            _decode_oracle_plan_object_v2(
                _expect_object_v2(value["oracle_plan"], name="global Oracle plan")
            ),
            tuple(_decode_occurrence_object_v2(item) for item in occurrences),
            tuple(_decode_external_outbox_object_v2(item) for item in outbox),
            _expect_text_v2(value["production_authority"], name="global rejected authority"),
        )
    )


def _decode_managed_accepted_v2(value: dict[str, object]) -> ManagedAssetLifecycleAcceptedWireV2:
    _expect_fields_v2(value, _MANAGED_ACCEPTED_FIELDS_V2, name="managed accepted")
    return _construct_v2(
        lambda: ManagedAssetLifecycleAcceptedWireV2(
            _decode_managed_state_object_v2(
                _expect_object_v2(value["post_state"], name="managed post state")
            ),
            _decode_effect_plan_object_v2(
                _expect_object_v2(value["effects"], name="managed effects")
            ),
            _decode_journal_object_v2(
                _expect_object_v2(value["module_journal"], name="managed journal")
            ),
            _expect_text_v2(value["receipt_root"], name="managed receipt root"),
            _expect_text_v2(value["production_authority"], name="managed authority"),
        )
    )


def _decode_managed_rejected_v2(value: dict[str, object]) -> ManagedAssetLifecycleRejectedWireV2:
    _expect_fields_v2(value, _MANAGED_REJECTED_FIELDS_V2, name="managed rejected")
    return _construct_v2(
        lambda: ManagedAssetLifecycleRejectedWireV2(
            _decode_enum_v2(
                value["code"], ManagedAssetLifecycleRejectCodeV2, name="managed reject code"
            ),
            _expect_text_v2(value["pre_state_root"], name="managed pre root"),
            _expect_text_v2(value["post_state_root"], name="managed post root"),
            _decode_effect_plan_object_v2(
                _expect_object_v2(value["effects"], name="managed effects")
            ),
            _expect_text_v2(value["terminal_obligations_root"], name="managed terminal root"),
            _expect_text_v2(value["oracle_occurrence_plan_root"], name="managed Oracle root"),
            _expect_text_v2(value["production_authority"], name="managed authority"),
        )
    )


def _decode_origin_accepted_v2(value: dict[str, object]) -> AssetOriginRegistrationAcceptedWireV2:
    _expect_fields_v2(value, _ORIGIN_ACCEPTED_FIELDS_V2, name="origin accepted")
    return _construct_v2(
        lambda: AssetOriginRegistrationAcceptedWireV2(
            _decode_origin_state_object_v2(
                _expect_object_v2(value["post_state"], name="origin post state")
            ),
            _decode_effect_plan_object_v2(
                _expect_object_v2(value["effects"], name="origin effects")
            ),
            _decode_journal_object_v2(
                _expect_object_v2(value["module_journal"], name="origin journal")
            ),
            _expect_text_v2(value["production_authority"], name="origin authority"),
        )
    )


def _decode_origin_rejected_v2(value: dict[str, object]) -> AssetOriginRegistrationRejectedWireV2:
    _expect_fields_v2(value, _ORIGIN_REJECTED_FIELDS_V2, name="origin rejected")
    return _construct_v2(
        lambda: AssetOriginRegistrationRejectedWireV2(
            _decode_enum_v2(
                value["code"], AssetOriginRegistrationRejectCodeV2, name="origin reject code"
            ),
            _expect_text_v2(value["pre_state_root"], name="origin pre root"),
            _expect_text_v2(value["post_state_root"], name="origin post root"),
            _decode_effect_plan_object_v2(
                _expect_object_v2(value["effects"], name="origin effects")
            ),
        )
    )


def _decode_asset_lane_context_v2(value: dict[str, object]) -> AssetLaneContextWireV2:
    _expect_fields_v2(value, _ASSET_LANE_CONTEXT_FIELDS_V2, name="asset lane context")
    occurrence_value = value["occurrence"]
    return _construct_v2(
        lambda: AssetLaneContextWireV2(
            _expect_nonnegative_integer_v2(value["writer_epoch"], name="asset lane writer epoch"),
            _expect_text_v2(value["module_release_id"], name="asset lane release"),
            _expect_text_v2(value["global_pre_state_root"], name="asset lane global pre root"),
            None
            if occurrence_value is None
            else _decode_occurrence_object_v2(
                _expect_object_v2(occurrence_value, name="asset lane occurrence")
            ),
        )
    )


def _decode_asset_lane_accepted_v2(value: dict[str, object]) -> AssetLaneAcceptedWireV2:
    _expect_fields_v2(value, _ASSET_LANE_ACCEPTED_FIELDS_V2, name="asset lane accepted")
    return _construct_v2(
        lambda: AssetLaneAcceptedWireV2(
            _decode_enum_v2(value["route"], AssetLaneRouteV2, name="asset lane route"),
            _expect_text_v2(value["source_leaf_journal_root"], name="asset lane source root"),
            _decode_asset_lane_state_object_v2(
                _expect_object_v2(value["post_state"], name="asset lane post state")
            ),
            _decode_effect_plan_object_v2(
                _expect_object_v2(value["effects"], name="asset lane effects")
            ),
            _decode_journal_object_v2(
                _expect_object_v2(value["module_journal"], name="asset lane journal")
            ),
            _expect_text_v2(value["receipt_root"], name="asset lane receipt root"),
            _expect_text_v2(value["production_authority"], name="asset lane authority"),
            _expect_text_v2(
                value["profile_authentication"], name="asset lane profile authentication"
            ),
        )
    )


def _decode_asset_lane_rejected_v2(value: dict[str, object]) -> AssetLaneRejectedWireV2:
    _expect_fields_v2(value, _ASSET_LANE_REJECTED_FIELDS_V2, name="asset lane rejected")
    code_value = _expect_text_v2(value["code"], name="asset lane reject code")
    code: object
    for enum_type in (
        AssetLaneCoordinatorRejectCodeV2,
        AssetTransferRejectCodeV2,
        ManagedAssetLifecycleRejectCodeV2,
    ):
        try:
            code = enum_type(code_value)
            break
        except ValueError:
            continue
    else:
        raise GlobalSettlementWireCodecErrorV2("asset lane reject code is unknown")
    return _construct_v2(
        lambda: AssetLaneRejectedWireV2(
            _decode_enum_v2(value["route"], AssetLaneRouteV2, name="asset lane route"),
            code,
            _expect_text_v2(value["pre_state_root"], name="asset lane pre root"),
            _expect_text_v2(value["post_state_root"], name="asset lane post root"),
            _decode_effect_plan_object_v2(
                _expect_object_v2(value["effects"], name="asset lane effects")
            ),
            _expect_text_v2(value["production_authority"], name="asset lane authority"),
            _expect_text_v2(
                value["profile_authentication"], name="asset lane profile authentication"
            ),
        )
    )


def _decode_refinement_candidate_v2(
    value: dict[str, object],
) -> GlobalEconomicStateEffectRefinementCandidateWireV2:
    _expect_fields_v2(value, _REFINEMENT_CANDIDATE_FIELDS_V2, name="refinement candidate")
    occurrences = _expect_object_array_v2(
        value["consumed_occurrences"],
        name="refinement candidate occurrences",
        limit=MAX_CONSUMED_OCCURRENCES_PER_REFINEMENT_V2,
    )
    return _construct_v2(
        lambda: GlobalEconomicStateEffectRefinementCandidateWireV2(
            _decode_global_state_object_v2(
                _expect_object_v2(value["pre_state"], name="candidate pre state")
            ),
            _decode_global_state_object_v2(
                _expect_object_v2(value["post_state"], name="candidate post state")
            ),
            _decode_effect_plan_object_v2(
                _expect_object_v2(value["effect_plan"], name="candidate effects")
            ),
            tuple(_decode_occurrence_object_v2(item) for item in occurrences),
            _decode_terminal_plan_object_v2(
                _expect_object_v2(value["terminal_plan"], name="candidate terminal plan")
            ),
            _decode_oracle_plan_object_v2(
                _expect_object_v2(value["oracle_plan"], name="candidate Oracle plan")
            ),
        )
    )


def _decode_refinement_v2(value: dict[str, object]) -> GlobalEconomicStateEffectRefinementWireV2:
    _expect_fields_v2(value, _REFINEMENT_FIELDS_V2, name="refinement")
    return _construct_v2(
        lambda: GlobalEconomicStateEffectRefinementWireV2(
            _expect_text_v2(value["pre_state_root"], name="refinement pre root"),
            _expect_text_v2(value["post_state_root"], name="refinement post root"),
            _expect_text_v2(value["effect_plan_root"], name="refinement effect root"),
            _expect_text_v2(value["terminal_plan_root"], name="refinement terminal root"),
            _expect_text_v2(value["oracle_plan_root"], name="refinement Oracle root"),
            _expect_text_v2(value["state_delta_root"], name="refinement delta root"),
            _expect_text_v2(value["production_authority"], name="refinement authority"),
            _expect_text_v2(value["refinement_root"], name="refinement root"),
        )
    )


_RECORD_DISPATCH_V2: tuple[
    tuple[frozenset[str], Callable[[dict[str, object]], WireRecordV2]], ...
] = (
    (_GLOBAL_REFINEMENT_ACCEPTED_FIELDS_V2, _decode_global_refinement_accepted_v2),
    (_GLOBAL_REFINEMENT_REJECTED_FIELDS_V2, _decode_global_refinement_rejected_v2),
    (_MANAGED_ACCEPTED_FIELDS_V2, _decode_managed_accepted_v2),
    (_MANAGED_REJECTED_FIELDS_V2, _decode_managed_rejected_v2),
    (_ORIGIN_ACCEPTED_FIELDS_V2, _decode_origin_accepted_v2),
    (_ORIGIN_REJECTED_FIELDS_V2, _decode_origin_rejected_v2),
    (_ASSET_LANE_CONTEXT_FIELDS_V2, _decode_asset_lane_context_v2),
    (_ASSET_LANE_ACCEPTED_FIELDS_V2, _decode_asset_lane_accepted_v2),
    (_ASSET_LANE_REJECTED_FIELDS_V2, _decode_asset_lane_rejected_v2),
    (_REFINEMENT_CANDIDATE_FIELDS_V2, _decode_refinement_candidate_v2),
    (_REFINEMENT_FIELDS_V2, _decode_refinement_v2),
)


def decode_global_settlement_wire_record_v2(raw: bytes) -> WireRecordV2:
    """Decode one exact canonical V2 record by its closed field set."""

    value = _load_canonical_object_v2(raw)
    actual = frozenset(value)
    matches = tuple(decoder for fields, decoder in _RECORD_DISPATCH_V2 if fields == actual)
    if len(matches) != 1:
        raise GlobalSettlementWireCodecErrorV2("wire record has no unique closed field set")
    return matches[0](value)


def encode_global_settlement_wire_record_v2(value: object) -> bytes:
    """Encode one exact V2 domain value or strict record without a type tag."""

    record = wire_record_from_domain_v2(value)
    encoded = canonical_global_bytes_v2(record.to_canonical())
    return _require_wire_record_codec_bytes_v2(encoded)


def decode_global_settlement_wire_v2(raw: bytes) -> WireRecordV2:
    return decode_global_settlement_wire_record_v2(raw)


def encode_global_settlement_wire_v2(value: object) -> bytes:
    return encode_global_settlement_wire_record_v2(value)


__all__ = [
    "MAX_GLOBAL_SETTLEMENT_WIRE_RECORD_CODEC_BYTES_V2",
    "GlobalSettlementWireCodecErrorV2",
    "GlobalSettlementWireRecordCodecErrorV2",
    "WIRE_RECORD_FIELD_SETS_V2",
    "decode_global_settlement_wire_record_v2",
    "encode_global_settlement_wire_record_v2",
    "decode_global_settlement_wire_v2",
    "encode_global_settlement_wire_v2",
]
