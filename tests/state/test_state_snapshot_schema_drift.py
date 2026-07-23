from __future__ import annotations

from dataclasses import fields

from src.core.perps import (
    PERP_CLEARINGHOUSE_2P_STATE_KEYS,
    PERP_CLEARINGHOUSE_3P_TRANSFER_STATE_KEYS,
    PERP_CLEARINGHOUSE_NP_GLOBAL_KEYS,
    PERP_ISOLATED_GLOBAL_KEYS,
)
from src.state.pools import PoolStatus
from src.state.state_admission_profile import (
    FCIS_REGISTERED_REGISTRY_IDS,
    FCIS_REQUIRED_REGISTRY_IDS,
)
from src.state.state_snapshot_schema import (
    CH2P_STATE_FIELDS_V1,
    CH3P_STATE_FIELDS_V1,
    CHNP_GLOBAL_FIELDS_V1,
    ENUM_REGISTRATIONS_V1,
    ISOLATED_GLOBAL_FIELD_NAMES_V1,
    ISOLATED_GLOBAL_FIELDS_V1,
    KNOWN_STATE_ADMISSION_SCHEMA_IDS_V1,
    RECORD_REGISTRATIONS_V1,
    SCHEMA_REGISTRATIONS_V1,
    StateEnumTagV1,
    StateRecordTagV1,
)
from src.state.state_snapshot_values import POOL_STATUS_MEMBER_VALUES_V1


def test_record_registry_is_exhaustive_ordered_and_field_exact() -> None:
    assert tuple(registration.tag for registration in RECORD_REGISTRATIONS_V1) == tuple(
        StateRecordTagV1
    )
    for registration in RECORD_REGISTRATIONS_V1:
        source_fields = tuple(item.name for item in fields(registration.source_type))
        owned_fields = tuple(item.name for item in fields(registration.owned_type))
        assert source_fields == owned_fields, registration.tag


def test_enum_registry_is_exhaustive_and_pool_status_order_is_pinned() -> None:
    assert tuple(registration.tag for registration in ENUM_REGISTRATIONS_V1) == tuple(
        StateEnumTagV1
    )
    assert ENUM_REGISTRATIONS_V1[0].enum_type is PoolStatus
    assert tuple(member.name for member in PoolStatus) == ("ACTIVE", "FROZEN", "DISABLED")
    assert tuple(member.value for member in PoolStatus) == POOL_STATUS_MEMBER_VALUES_V1


def test_schema_registry_ids_are_unique_and_complete() -> None:
    observed = tuple(registration.schema_id for registration in SCHEMA_REGISTRATIONS_V1)
    assert observed == KNOWN_STATE_ADMISSION_SCHEMA_IDS_V1
    assert observed == FCIS_REQUIRED_REGISTRY_IDS
    assert observed == FCIS_REGISTERED_REGISTRY_IDS
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
