"""C02 key-shape, canonicalization, and rotation-mutant tests."""
from __future__ import annotations

import json
from dataclasses import fields
from typing import Any

import pytest

from src.core.fcis_entitlement_key_codec_v1 import (
    canonical_sha256_entitlement_key_v1,
    encode_entitlement_key_v1,
)
from src.core.fcis_entitlement_key_v1 import (
    ENTITLEMENT_KEY_EXCLUDED_FIELDS_V1,
    ENTITLEMENT_KEY_FIELDS_V1,
    ENTITLEMENT_KEY_SCHEMA_ID_V1,
    EntitlementKeyV1,
)
from src.core.fcis_m6_profile_ids import (
    FIXED_ROLE_ORDER_ID_V1,
    SEMANTIC_ALLOCATOR_PROFILE_ID_V1,
)


def _key(
    *,
    domain: str = "protocol-fees",
    asset: str = "USDC",
) -> EntitlementKeyV1:
    return EntitlementKeyV1(
        domain,
        asset,
        SEMANTIC_ALLOCATOR_PROFILE_ID_V1,
        FIXED_ROLE_ORDER_ID_V1,
    )


def test_key_has_exact_four_fields_in_protocol_order() -> None:
    key = _key()
    field_names = tuple(field.name for field in fields(EntitlementKeyV1))
    assert field_names == ENTITLEMENT_KEY_FIELDS_V1
    assert key.canonical_fields == tuple(
        (name, getattr(key, name)) for name in ENTITLEMENT_KEY_FIELDS_V1
    )
    assert len(key.protocol_order_key) == 4


def test_excluded_dimensions_are_not_key_material() -> None:
    key = _key()
    field_names = set(ENTITLEMENT_KEY_FIELDS_V1)
    assert field_names.isdisjoint(ENTITLEMENT_KEY_EXCLUDED_FIELDS_V1)
    assert _key() == key
    assert encode_entitlement_key_v1(_key()) == encode_entitlement_key_v1(key)
    for rotated_value in (
        "buyback-v2",
        "treasury-v2",
        "rewards-v2",
        "custody-v2",
        "weights-v2",
        "agqe-surplus/v1",
    ):
        assert rotated_value not in dict(key.canonical_fields).values()


def test_representation_rotation_preserves_key_bytes() -> None:
    srgd_key = _key()
    agqe_key = _key()
    assert srgd_key == agqe_key
    assert encode_entitlement_key_v1(srgd_key) == encode_entitlement_key_v1(agqe_key)


def test_domain_is_required_key_material() -> None:
    key = _key(domain="protocol-fees")
    other_domain = _key(domain="other-fee-domain")
    encoded = encode_entitlement_key_v1(key)
    assert key != other_domain
    assert encoded != encode_entitlement_key_v1(other_domain)
    assert b"fee_distribution_domain_id" in encoded
    assert b"protocol-fees" in encoded


def test_role_permutation_is_rejected() -> None:
    with pytest.raises(ValueError, match="fixed role order"):
        EntitlementKeyV1(
            "protocol-fees",
            "USDC",
            SEMANTIC_ALLOCATOR_PROFILE_ID_V1,
            "fee-occurrence/role-order/rewards-treasury-buyback/v1",
        )


def test_semantic_profile_rotation_is_rejected() -> None:
    with pytest.raises(ValueError, match="semantic profile"):
        EntitlementKeyV1(
            "protocol-fees",
            "USDC",
            "agqe-surplus/v1",
            FIXED_ROLE_ORDER_ID_V1,
        )


@pytest.mark.parametrize(  # type: ignore[untyped-decorator]
    ("field_name", "bad_value"),
    [
        ("fee_distribution_domain_id", None),
        ("asset", True),
        ("semantic_profile_id", ["profile"]),
        ("fixed_role_order_id", {"role": "order"}),
    ],
)
def test_key_fields_fail_closed_on_non_exact_types(
    field_name: str,
    bad_value: object,
) -> None:
    kwargs: dict[str, Any] = {
        "fee_distribution_domain_id": "protocol-fees",
        "asset": "USDC",
        "semantic_profile_id": SEMANTIC_ALLOCATOR_PROFILE_ID_V1,
        "fixed_role_order_id": FIXED_ROLE_ORDER_ID_V1,
    }
    kwargs[field_name] = bad_value
    with pytest.raises(TypeError):
        EntitlementKeyV1(**kwargs)


def test_unknown_representation_field_is_rejected() -> None:
    with pytest.raises(TypeError):
        EntitlementKeyV1(  # type: ignore[call-arg]
            "protocol-fees",
            "USDC",
            SEMANTIC_ALLOCATOR_PROFILE_ID_V1,
            FIXED_ROLE_ORDER_ID_V1,
            representation_id="srgd-deficit/v1",
        )


def test_codec_requires_exact_value_and_emits_only_known_schema() -> None:
    with pytest.raises(TypeError):
        encode_entitlement_key_v1({"fee_distribution_domain_id": "protocol-fees"})
    encoded = encode_entitlement_key_v1(_key())
    decoded = json.loads(encoded)
    assert decoded == {
        "schema": ENTITLEMENT_KEY_SCHEMA_ID_V1,
        "value": {
            "asset": "USDC",
            "fee_distribution_domain_id": "protocol-fees",
            "fixed_role_order_id": FIXED_ROLE_ORDER_ID_V1,
            "semantic_profile_id": SEMANTIC_ALLOCATOR_PROFILE_ID_V1,
        },
    }
    assert canonical_sha256_entitlement_key_v1(_key()) == (
        canonical_sha256_entitlement_key_v1(_key())
    )
