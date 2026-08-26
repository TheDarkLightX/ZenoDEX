"""Fail-closed raw authority-material admission for mounted JSON HTTP APIs.

This is a pure shell-boundary classifier. It owns no signing, command,
settlement, or publication authority. Its mechanical guarantee is narrower:
valid JSON containing a recognized raw-key field cannot cross the mounted POST
choke point. Direct Python callers and alternate servers remain separate
mount/inventory obligations.
"""

from __future__ import annotations

import enum
import json
from dataclasses import dataclass

_MAX_DEPTH = 32
_MAX_NODES = 131_072
_SAFE_POSTURE_FIELD_NAMES = frozenset(
    {
        "nolivesecrets",
        "norawprivatekeyexposure",
        "rawprivatekeyimported",
        "secretscan",
        "secretscanfindingcount",
        "secretscanok",
    }
)
_RAW_KEY_NAME_FRAGMENTS = (
    "privatekey",
    "privkey",
    "secretkey",
    "seedphrase",
)
_RAW_AUTHORITY_EXACT_NAMES = frozenset(
    {
        "accesstoken",
        "apikey",
        "authtoken",
        "bearertoken",
        "mnemonic",
        "privatekey",
        "privatekeyhex",
        "privkey",
        "privkeyhex",
        "secretkey",
        "secretkeyhex",
        "seedphrase",
    }
)


class HttpAuthorityIngressRejectCodeV1(enum.Enum):
    RAW_AUTHORITY_MATERIAL_FORBIDDEN = "raw_authority_material_forbidden"
    SCAN_REFUSED = "authority_material_scan_refused"


@dataclass(frozen=True, slots=True)
class HttpAuthorityIngressAcceptedV1:
    """The bounded JSON graph contained no recognized raw-key field."""


@dataclass(frozen=True, slots=True)
class HttpAuthorityIngressDeferredV1:
    """Malformed JSON is left to the route's established decoder and error ABI."""


@dataclass(frozen=True, slots=True)
class HttpAuthorityIngressRejectedV1:
    code: HttpAuthorityIngressRejectCodeV1

    def __post_init__(self) -> None:
        if type(self.code) is not HttpAuthorityIngressRejectCodeV1:
            raise TypeError("code must be HttpAuthorityIngressRejectCodeV1")


HttpAuthorityIngressDecisionV1 = (
    HttpAuthorityIngressAcceptedV1
    | HttpAuthorityIngressDeferredV1
    | HttpAuthorityIngressRejectedV1
)


@dataclass(frozen=True, slots=True)
class _JsonObjectPairsV1:
    entries: tuple[tuple[str, object], ...]


def _owned_object_pairs_v1(pairs: list[tuple[str, object]]) -> _JsonObjectPairsV1:
    return _JsonObjectPairsV1(tuple((key, value) for key, value in pairs))


def _reject_json_constant_v1(token: str) -> None:
    raise ValueError(f"non-finite JSON constant: {token}")


def _normalized_field_name_v1(value: str) -> str:
    return "".join(character for character in value.lower() if character.isalnum())


def _is_raw_authority_field_name_v1(value: str) -> bool:
    normalized = _normalized_field_name_v1(value)
    if normalized in _SAFE_POSTURE_FIELD_NAMES:
        return False
    if normalized in _RAW_AUTHORITY_EXACT_NAMES:
        return True
    return any(fragment in normalized for fragment in _RAW_KEY_NAME_FRAGMENTS)


def _scan_refused_v1() -> HttpAuthorityIngressRejectedV1:
    return HttpAuthorityIngressRejectedV1(
        code=HttpAuthorityIngressRejectCodeV1.SCAN_REFUSED,
    )


def inspect_http_authority_ingress_v1(
    raw_body: bytes,
) -> HttpAuthorityIngressDecisionV1:
    """Classify one bounded JSON body without retaining or echoing its values."""

    if type(raw_body) is not bytes:
        return _scan_refused_v1()
    if not raw_body:
        return HttpAuthorityIngressDeferredV1()
    try:
        value = json.loads(
            raw_body,
            object_pairs_hook=_owned_object_pairs_v1,
            parse_constant=_reject_json_constant_v1,
        )
    except (json.JSONDecodeError, UnicodeDecodeError):
        return HttpAuthorityIngressDeferredV1()
    except (TypeError, ValueError, RecursionError):
        return _scan_refused_v1()

    stack: list[tuple[object, int]] = [(value, 0)]
    node_count = 0
    while stack:
        current, depth = stack.pop()
        node_count += 1
        if node_count > _MAX_NODES or depth > _MAX_DEPTH:
            return _scan_refused_v1()
        if type(current) is _JsonObjectPairsV1:
            if (
                depth == _MAX_DEPTH
                or node_count + len(stack) + len(current.entries) > _MAX_NODES
            ):
                return _scan_refused_v1()
            for key, _child in current.entries:
                if _is_raw_authority_field_name_v1(key):
                    return HttpAuthorityIngressRejectedV1(
                        code=HttpAuthorityIngressRejectCodeV1.RAW_AUTHORITY_MATERIAL_FORBIDDEN,
                    )
            for _key, child in reversed(current.entries):
                stack.append((child, depth + 1))
            continue
        if type(current) is list:
            if (
                depth == _MAX_DEPTH
                or node_count + len(stack) + len(current) > _MAX_NODES
            ):
                return _scan_refused_v1()
            for index in range(len(current) - 1, -1, -1):
                stack.append((current[index], depth + 1))
            continue
        if current is None or type(current) in {str, int, float, bool}:
            continue
        return _scan_refused_v1()

    return HttpAuthorityIngressAcceptedV1()


__all__ = [
    "HttpAuthorityIngressAcceptedV1",
    "HttpAuthorityIngressDecisionV1",
    "HttpAuthorityIngressDeferredV1",
    "HttpAuthorityIngressRejectCodeV1",
    "HttpAuthorityIngressRejectedV1",
    "inspect_http_authority_ingress_v1",
]
