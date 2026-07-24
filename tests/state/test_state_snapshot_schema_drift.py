from __future__ import annotations

from dataclasses import fields

from src.core.perps import (
    PERP_CLEARINGHOUSE_2P_STATE_KEYS,
    PERP_CLEARINGHOUSE_3P_TRANSFER_STATE_KEYS,
    PERP_CLEARINGHOUSE_NP_GLOBAL_KEYS,
    PERP_ISOLATED_GLOBAL_KEYS,
)
from src.core.settlement import FillAction
from src.state.intents import IntentKind
from src.state.pools import PoolStatus
from src.state.state_admission_profile import (
    _STATE_ADMISSION_REGISTRY_V1,
    FCIS_REGISTERED_REGISTRY_IDS,
    FCIS_REQUIRED_REGISTRY_IDS,
)
from src.state.state_snapshot_schema import (
    CH2P_STATE_FIELDS_V1,
    CH3P_STATE_FIELDS_V1,
    CHNP_GLOBAL_FIELDS_V1,
    ISOLATED_GLOBAL_FIELD_NAMES_V1,
    ISOLATED_GLOBAL_FIELDS_V1,
    KNOWN_STATE_ADMISSION_SCHEMA_IDS_V1,
    SCHEMA_REGISTRATIONS_V1,
    StateEnumTagV1,
    StateRecordTagV1,
)
from src.state.state_snapshot_values import POOL_STATUS_MEMBER_VALUES_V1


def test_record_registry_is_exhaustive_ordered_and_field_exact() -> None:
    registrations = _STATE_ADMISSION_REGISTRY_V1.record_registrations
    assert tuple(registration.tag for registration in registrations) == tuple(StateRecordTagV1)
    for registration in registrations:
        source_types = (registration.source_type, *registration.additional_source_types)
        source_fields = tuple(item.name for item in fields(source_types[0]))
        assert all(
            tuple(item.name for item in fields(source_type)) == source_fields
            for source_type in source_types[1:]
        ), registration.tag
        owned_fields = tuple(item.name for item in fields(registration.owned_type))
        assert source_fields == owned_fields, registration.tag


def test_enum_registry_is_exhaustive_and_pool_status_order_is_pinned() -> None:
    registrations = _STATE_ADMISSION_REGISTRY_V1.enum_registrations
    assert tuple(registration.tag for registration in registrations) == tuple(StateEnumTagV1)
    assert registrations[0].enum_type is PoolStatus
    assert tuple(member.name for member in PoolStatus) == ("ACTIVE", "FROZEN", "DISABLED")
    assert tuple(member.value for member in PoolStatus) == POOL_STATUS_MEMBER_VALUES_V1


def test_authority_enum_tag_and_member_ordinals_are_schema_revision_pinned() -> None:
    assert tuple(StateEnumTagV1) == (
        StateEnumTagV1.POOL_STATUS,
        StateEnumTagV1.INTENT_KIND,
        StateEnumTagV1.FILL_ACTION,
    )
    assert tuple((member.name, member.value) for member in IntentKind) == (
        ("CREATE_POOL", "CREATE_POOL"),
        ("ADD_LIQUIDITY", "ADD_LIQUIDITY"),
        ("REMOVE_LIQUIDITY", "REMOVE_LIQUIDITY"),
        ("SWAP_EXACT_IN", "SWAP_EXACT_IN"),
        ("SWAP_EXACT_OUT", "SWAP_EXACT_OUT"),
        ("ROUTE_EXACT_IN", "ROUTE_EXACT_IN"),
        ("ROUTE_EXACT_OUT", "ROUTE_EXACT_OUT"),
    )
    assert tuple((member.name, member.value) for member in FillAction) == (
        ("FILL", "FILL"),
        ("REJECT", "REJECT"),
    )


def test_schema_registry_ids_are_unique_and_complete() -> None:
    base_ids = tuple(registration.schema_id for registration in SCHEMA_REGISTRATIONS_V1)
    observed = _STATE_ADMISSION_REGISTRY_V1.schema_ids
    assert base_ids == KNOWN_STATE_ADMISSION_SCHEMA_IDS_V1
    assert observed[: len(base_ids)] == base_ids
    assert observed == FCIS_REQUIRED_REGISTRY_IDS
    assert observed == FCIS_REGISTERED_REGISTRY_IDS
    assert _STATE_ADMISSION_REGISTRY_V1.schema_ids == FCIS_REGISTERED_REGISTRY_IDS
    assert len(observed) == len(set(observed))


def test_perps_key_registries_are_exact_and_canonical() -> None:
    assert ISOLATED_GLOBAL_FIELD_NAMES_V1 == tuple(
        field.name for field in ISOLATED_GLOBAL_FIELDS_V1
    )
    expectations = (
        (ISOLATED_GLOBAL_FIELDS_V1, PERP_ISOLATED_GLOBAL_KEYS),
        (CH2P_STATE_FIELDS_V1, PERP_CLEARINGHOUSE_2P_STATE_KEYS),
        (CH3P_STATE_FIELDS_V1, PERP_CLEARINGHOUSE_3P_TRANSFER_STATE_KEYS),
        (CHNP_GLOBAL_FIELDS_V1, PERP_CLEARINGHOUSE_NP_GLOBAL_KEYS),
    )
    for declared_fields, runtime_keys in expectations:
        names = tuple(field.name for field in declared_fields)
        assert names == tuple(sorted(runtime_keys))
