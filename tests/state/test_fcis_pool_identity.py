from __future__ import annotations

import pytest

from src.state.canonical import canonical_hex_fixed_allow_0x
from src.state.fcis_pool_identity import (
    compute_pool_id,
    normalize_pool_asset_pair,
    validate_pool_id_format,
)
from src.state.pools import (
    compute_pool_id as legacy_compute_pool_id,
)
from src.state.pools import (
    normalize_pool_asset_pair as legacy_normalize_pool_asset_pair,
)

ASSET0 = "0x" + "01" * 32
ASSET1 = "0x" + "02" * 32


@pytest.mark.parametrize(
    ("curve_tag", "curve_params", "expected"),
    (
        (
            "CPMM",
            "",
            "0x87ae7deafec1b298b4a1f8e64bb2a0910e51b07812545c0e897f04e219c6f4c6",
        ),
        (
            "CUBIC_SUM_V1",
            '{"p":3,"q":5}',
            "0x18600c1f31ab858ec6c4e98c08f99cacf6ab7a84993da47b257c5906a7a6e42e",
        ),
    ),
)
def test_pool_id_matches_fixed_protocol_goldens(
    curve_tag: str,
    curve_params: str,
    expected: str,
) -> None:
    actual = compute_pool_id(
        ASSET0,
        ASSET1,
        30,
        curve_tag=curve_tag,
        curve_params=curve_params,
    )
    assert actual == expected
    assert (
        legacy_compute_pool_id(
            ASSET0,
            ASSET1,
            30,
            curve_tag=curve_tag,
            curve_params=curve_params,
        )
        == expected
    )


def test_symbolic_pool_id_matches_fixed_legacy_golden() -> None:
    expected = "0x6b0a2f303f6808faae524aa53cbbd71e216c0d8ef0e4112acb9f6c48b39cfd46"
    assert compute_pool_id("AAA", "BBB", 30) == expected
    assert legacy_compute_pool_id("AAA", "BBB", 30) == expected


@pytest.mark.parametrize(
    ("raw0", "raw1"),
    (
        ("  0X" + "01" * 32 + "  ", "0x" + "02" * 32),
        ("0x" + "01" * 32, "0X" + "02" * 32),
    ),
)
def test_asset_hex_normalization_matches_canonical_primitive(
    raw0: str,
    raw1: str,
) -> None:
    expected = (
        canonical_hex_fixed_allow_0x(raw0, nbytes=32, name="asset0"),
        canonical_hex_fixed_allow_0x(raw1, nbytes=32, name="asset1"),
    )
    assert normalize_pool_asset_pair(raw0, raw1) == expected
    assert legacy_normalize_pool_asset_pair(raw0, raw1) == expected


def test_symbolic_asset_boundary_preserves_legacy_order() -> None:
    assert normalize_pool_asset_pair("AAA", "BBB") == ("AAA", "BBB")
    with pytest.raises(ValueError, match="canonical order"):
        normalize_pool_asset_pair("BBB", "AAA")


@pytest.mark.parametrize(
    ("pool_id", "allow_symbolic"),
    (
        ("pool-local", True),
        (ASSET0, False),
    ),
)
def test_pool_id_format_accepts_declared_canonical_boundaries(
    pool_id: str,
    allow_symbolic: bool,
) -> None:
    validate_pool_id_format(pool_id, allow_symbolic=allow_symbolic)


@pytest.mark.parametrize(
    ("pool_id", "allow_symbolic"),
    (
        ("pool-local", False),
        ("0X" + "01" * 32, True),
        ("0x" + "AA" * 32, True),
        ("01" * 32, False),
        (" pool-local ", True),
    ),
)
def test_pool_id_format_rejects_noncanonical_boundaries(
    pool_id: str,
    allow_symbolic: bool,
) -> None:
    with pytest.raises(ValueError):
        validate_pool_id_format(pool_id, allow_symbolic=allow_symbolic)


class _HostileString(str):
    pass


@pytest.mark.parametrize(
    "operation",
    (
        lambda: normalize_pool_asset_pair(_HostileString(ASSET0), ASSET1),
        lambda: compute_pool_id(ASSET0, ASSET1, True),
        lambda: compute_pool_id(
            ASSET0,
            ASSET1,
            30,
            curve_tag=_HostileString("CPMM"),
        ),
        lambda: validate_pool_id_format(_HostileString(ASSET0), allow_symbolic=False),
        lambda: validate_pool_id_format(ASSET0, allow_symbolic=1),
    ),
)
def test_identity_boundary_rejects_hostile_subtypes(operation: object) -> None:
    assert callable(operation)
    with pytest.raises((TypeError, ValueError)):
        operation()
