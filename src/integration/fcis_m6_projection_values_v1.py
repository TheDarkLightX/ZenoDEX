"""Owned semantic content values for M6 application-state comparison."""

from __future__ import annotations

from dataclasses import InitVar, dataclass
from typing import Final, final
from weakref import WeakValueDictionary

from ..core.fcis_m6_global_state_projection_v1 import M6ProjectionCoverageV1
from ..state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex

M6_APPLICATION_CONTENT_SCHEMA_V1: Final = "zenodex/fcis/m6/application-content/v1"
MAX_M6_APP_STATE_BYTES_V1: Final = 6_000_000

_CONTENT_TOKEN_V1 = object()
_LOWER_HEX = frozenset("0123456789abcdef")


def _digest32(value: object, name: str) -> str:
    if (
        type(value) is not str
        or len(value) != 66
        or not value.startswith("0x")
        or any(character not in _LOWER_HEX for character in value[2:])
    ):
        raise TypeError(f"{name} must be a lowercase 0x-prefixed 32-byte digest")
    return value


def _component_registry_root_v1() -> str:
    from ..core.fcis_m6_global_state_projection_v1 import (
        M6_REQUIRED_APPLICATION_STATE_COMPONENTS_V1,
    )

    return sha256_hex(
        domain_sep_bytes("fcis_m6_application_component_registry", version=1)
        + canonical_json_bytes(
            [component.value for component in M6_REQUIRED_APPLICATION_STATE_COMPONENTS_V1]
        )
    )


M6_APPLICATION_COMPONENT_REGISTRY_ROOT_V1: Final = _component_registry_root_v1()


def _content_root_v1(coverage: M6ProjectionCoverageV1) -> str:
    return sha256_hex(
        domain_sep_bytes("fcis_m6_application_content", version=1)
        + canonical_json_bytes(
            {
                "schema": M6_APPLICATION_CONTENT_SCHEMA_V1,
                "component_registry_root": M6_APPLICATION_COMPONENT_REGISTRY_ROOT_V1,
                "coverage_root": coverage.coverage_root,
            }
        )
    )


@final
@dataclass(frozen=True, slots=True, weakref_slot=True)
class M6ApplicationContentV1:
    """Freshly derived semantic leaves plus their exact source bytes."""

    canonical_source_bytes: bytes
    coverage: M6ProjectionCoverageV1
    content_root: str
    _construction_token: InitVar[object | None] = None

    def __post_init__(self, _construction_token: object | None) -> None:
        if _construction_token is not _CONTENT_TOKEN_V1:
            raise TypeError("application content requires source decoding")
        if type(self.canonical_source_bytes) is not bytes:
            raise TypeError("canonical_source_bytes must be exact bytes")
        if not 0 < len(self.canonical_source_bytes) <= MAX_M6_APP_STATE_BYTES_V1:
            raise ValueError("canonical source bytes are outside the bound")
        if type(self.coverage) is not M6ProjectionCoverageV1:
            raise TypeError("coverage must be exact")
        self.coverage.__post_init__()
        _digest32(self.content_root, "content_root")
        if self.content_root != _content_root_v1(self.coverage):
            raise ValueError("content_root does not rederive")


_CONTENTS_V1: WeakValueDictionary[int, M6ApplicationContentV1] = WeakValueDictionary()
_CONTENT_SNAPSHOTS_V1: dict[int, tuple[object, ...]] = {}


def _content_snapshot_v1(value: M6ApplicationContentV1) -> tuple[object, ...]:
    return (
        value.canonical_source_bytes,
        value.coverage.coverage_root,
        value.content_root,
    )


def _build_content_v1(
    *,
    canonical_source_bytes: bytes,
    coverage: M6ProjectionCoverageV1,
) -> M6ApplicationContentV1:
    value = M6ApplicationContentV1(
        canonical_source_bytes=canonical_source_bytes,
        coverage=coverage,
        content_root=_content_root_v1(coverage),
        _construction_token=_CONTENT_TOKEN_V1,
    )
    _CONTENTS_V1[id(value)] = value
    _CONTENT_SNAPSHOTS_V1[id(value)] = _content_snapshot_v1(value)
    return value


def is_verified_application_content_v1(value: object) -> bool:
    if type(value) is not M6ApplicationContentV1:
        return False
    if _CONTENTS_V1.get(id(value)) is not value:
        return False
    try:
        value.__post_init__(_CONTENT_TOKEN_V1)
        return _CONTENT_SNAPSHOTS_V1.get(id(value)) == _content_snapshot_v1(value)
    except (TypeError, ValueError, ArithmeticError, OverflowError):
        return False


__all__ = (
    "MAX_M6_APP_STATE_BYTES_V1",
    "M6_APPLICATION_COMPONENT_REGISTRY_ROOT_V1",
    "M6_APPLICATION_CONTENT_SCHEMA_V1",
    "M6ApplicationContentV1",
    "is_verified_application_content_v1",
)
