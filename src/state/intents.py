"""Canonical immutable intent snapshots for TauSwap DEX.

Intents are user-authored requests collected and settled in batches.  Their
fields participate in signatures, admission decisions, and replay, so an
accepted snapshot must own its data recursively and must not retain mutable
aliases supplied by a parser or caller.
"""

from __future__ import annotations

from collections.abc import Iterator, Mapping
from dataclasses import dataclass, replace
from enum import Enum
from typing import Any, ClassVar, TypeVar, cast

from .balances import PubKey
from .canonical import (
    MAX_UVARINT_BITS,
    bounded_json_utf8_size,
    canonical_hex_fixed_allow_0x,
    canonical_json_bytes,
)

_MAX_FIELD_DEPTH = 64
_MAX_FIELD_ITEMS = 200_000
_MAX_FIELD_JSON_BYTES = 32_000
INTENT_DEADLINE_MAX_U64 = (1 << 64) - 1
_IntentT = TypeVar("_IntentT", bound="Intent")
INTENT_TRANSPORT_RESERVED_FIELDS = frozenset(
    {
        "module",
        "version",
        "kind",
        "intent_id",
        "sender_pubkey",
        "deadline",
        "salt",
        "fields",
        "signature",
        "quote_receipt",
    }
)


class IntentKind(Enum):
    """Intent type enumeration."""

    CREATE_POOL = "CREATE_POOL"
    ADD_LIQUIDITY = "ADD_LIQUIDITY"
    REMOVE_LIQUIDITY = "REMOVE_LIQUIDITY"
    SWAP_EXACT_IN = "SWAP_EXACT_IN"
    SWAP_EXACT_OUT = "SWAP_EXACT_OUT"


class _FrozenIntentObject(Mapping[str, Any]):
    """Deterministically ordered, read-only JSON object."""

    __slots__ = ("_items",)
    _items: tuple[tuple[str, Any], ...]

    def __init__(self, items: tuple[tuple[str, Any], ...]) -> None:
        object.__setattr__(self, "_items", items)

    def __setattr__(self, name: str, value: object) -> None:
        del name, value
        raise TypeError("frozen intent object is immutable")

    def __getitem__(self, key: str) -> Any:
        lo = 0
        hi = len(self._items)
        while lo < hi:
            mid = (lo + hi) // 2
            candidate, value = self._items[mid]
            if candidate < key:
                lo = mid + 1
            elif candidate > key:
                hi = mid
            else:
                return value
        raise KeyError(key)

    def __iter__(self) -> Iterator[str]:
        return (key for key, _value in self._items)

    def __len__(self) -> int:
        return len(self._items)

    def __repr__(self) -> str:
        return repr(thaw_intent_fields(self))

    def __copy__(self) -> _FrozenIntentObject:
        return self

    def __deepcopy__(self, memo: dict[int, Any]) -> _FrozenIntentObject:
        memo[id(self)] = self
        return self

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, Mapping):
            return False
        try:
            return thaw_intent_fields(self) == thaw_intent_fields(other)
        except (TypeError, ValueError):
            return False


class IntentFieldsNotOwnedError(TypeError):
    """Raised when an intent no longer carries its constructor-owned fields."""


def _require_owned_intent_fields(value: object) -> _FrozenIntentObject:
    if type(value) is not _FrozenIntentObject:
        raise IntentFieldsNotOwnedError(
            "intent.fields must be an exact owned intent snapshot"
        )
    return value


def _validate_text(
    value: str,
    *,
    path: str,
    max_len: int | None = None,
) -> str:
    if max_len is not None and len(value) > max_len:
        raise ValueError(f"{path} exceeds maximum length {max_len}")
    try:
        value.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise TypeError(f"{path} contains a surrogate code point") from exc
    return value


def _freeze_intent_value(
    value: object,
    *,
    path: str,
    depth: int,
    active_container_ids: set[int],
    item_budget: list[int],
) -> Any:
    if depth > _MAX_FIELD_DEPTH:
        raise ValueError("intent.fields nesting exceeds maximum depth")
    item_budget[0] -= 1
    if item_budget[0] < 0:
        raise ValueError("intent.fields item count exceeds maximum")

    if value is None or type(value) is bool:
        return value
    if type(value) is int:
        if value.bit_length() > MAX_UVARINT_BITS:
            raise ValueError(
                f"{path} integer exceeds {MAX_UVARINT_BITS}-bit protocol bound"
            )
        return value
    if type(value) is str:
        return _validate_text(value, path=path, max_len=_MAX_FIELD_JSON_BYTES)
    if type(value) is float:
        raise TypeError(f"{path} floats are not allowed")

    if type(value) is dict or type(value) is _FrozenIntentObject:
        container_id = id(value)
        if container_id in active_container_ids:
            raise ValueError(f"{path} contains a cycle")
        if len(value) > item_budget[0]:
            raise ValueError("intent.fields item count exceeds maximum")
        if 5 * len(value) + 1 > _MAX_FIELD_JSON_BYTES:
            raise ValueError("intent.fields canonical JSON exceeds byte maximum")
        active_container_ids.add(container_id)
        try:
            raw_items = list(value.items())
            for key, _item in raw_items:
                if type(key) is not str:
                    raise TypeError(f"{path} keys must be exactly str")
                _validate_text(
                    key,
                    path=f"{path} key",
                    max_len=_MAX_FIELD_JSON_BYTES,
                )
            frozen_items = tuple(
                (
                    cast(str, key),
                    _freeze_intent_value(
                        item,
                        path=f"{path}.{key}",
                        depth=depth + 1,
                        active_container_ids=active_container_ids,
                        item_budget=item_budget,
                    ),
                )
                for key, item in sorted(raw_items, key=lambda pair: cast(str, pair[0]))
            )
        finally:
            active_container_ids.remove(container_id)
        return _FrozenIntentObject(frozen_items)

    if type(value) in {list, tuple}:
        sequence = cast(list[Any] | tuple[Any, ...], value)
        container_id = id(value)
        if container_id in active_container_ids:
            raise ValueError(f"{path} contains a cycle")
        if len(sequence) > item_budget[0]:
            raise ValueError("intent.fields item count exceeds maximum")
        if 2 * len(sequence) + 1 > _MAX_FIELD_JSON_BYTES:
            raise ValueError("intent.fields canonical JSON exceeds byte maximum")
        active_container_ids.add(container_id)
        try:
            frozen_items = tuple(
                _freeze_intent_value(
                    item,
                    path=f"{path}[{index}]",
                    depth=depth + 1,
                    active_container_ids=active_container_ids,
                    item_budget=item_budget,
                )
                for index, item in enumerate(sequence)
            )
        finally:
            active_container_ids.remove(container_id)
        return frozen_items

    raise TypeError(
        f"{path} must contain only JSON scalars, mappings, lists, or tuples"
    )


def _freeze_intent_fields(fields: Mapping[str, Any] | None) -> _FrozenIntentObject:
    source: Mapping[str, Any] = {} if fields is None else fields
    if type(source) is not dict and type(source) is not _FrozenIntentObject:
        raise TypeError("intent.fields must be a plain dict or None")
    frozen = _freeze_intent_value(
        source,
        path="intent.fields",
        depth=0,
        active_container_ids=set(),
        item_budget=[_MAX_FIELD_ITEMS],
    )
    if not isinstance(frozen, _FrozenIntentObject):
        raise TypeError("intent.fields must freeze to an object")
    reserved = sorted(INTENT_TRANSPORT_RESERVED_FIELDS.intersection(frozen))
    if reserved:
        raise ValueError(
            f"intent.fields contains reserved transport key: {reserved[0]}"
        )
    # This is also a fail-closed parity check with the existing signing codec.
    thawed = thaw_intent_fields(frozen)
    bounded_json_utf8_size(
        thawed,
        max_bytes=_MAX_FIELD_JSON_BYTES,
        max_depth=_MAX_FIELD_DEPTH + 1,
        max_items=_MAX_FIELD_ITEMS,
    )
    canonical_json_bytes(thawed)
    return frozen


def _thaw_intent_value(value: object, *, path: str) -> Any:
    if value is None or type(value) in {bool, int, str}:
        return value
    if type(value) is dict or type(value) is _FrozenIntentObject:
        out: dict[str, Any] = {}
        for key in sorted(value):
            if type(key) is not str:
                raise TypeError(f"{path} keys must be exactly str")
            out[key] = _thaw_intent_value(value[key], path=f"{path}.{key}")
        return out
    if type(value) in {list, tuple}:
        return [
            _thaw_intent_value(item, path=f"{path}[{index}]")
            for index, item in enumerate(cast(list[Any] | tuple[Any, ...], value))
        ]
    raise TypeError(f"{path} contains a non-JSON value")


def thaw_intent_fields(fields: Mapping[str, Any]) -> dict[str, Any]:
    """Return a recursively owned JSON object for wire/signature boundaries."""

    if type(fields) is not dict and type(fields) is not _FrozenIntentObject:
        raise TypeError("intent.fields must be a plain dict or frozen intent object")
    thawed = _thaw_intent_value(fields, path="intent.fields")
    if not isinstance(thawed, dict):
        raise TypeError("intent.fields must thaw to an object")
    return thawed


def normalize_intent_wire_fields(
    fields: Mapping[str, Any] | None,
) -> dict[str, Any]:
    """Validate, canonically own, and detach an external fields object.

    This is the wire-facing counterpart to ``Intent`` construction.  It keeps
    signing callers from retaining parser-owned nested dictionaries or lists,
    and it applies the same reserved-key and JSON-domain checks as committed
    intent snapshots.
    """

    return thaw_intent_fields(_freeze_intent_fields(fields))


def _require_nonempty_str(
    value: object,
    *,
    name: str,
    max_len: int,
) -> str:
    if type(value) is not str or not value:
        raise TypeError(f"{name} must be a non-empty string")
    return _validate_text(value, path=name, max_len=max_len)


def _require_nonnegative_int(
    value: object,
    *,
    name: str,
    maximum: int | None = None,
) -> int:
    if type(value) is not int:
        raise TypeError(f"{name} must be an int")
    if value < 0:
        raise ValueError(f"{name} must be non-negative")
    if maximum is not None and value > maximum:
        raise ValueError(f"{name} exceeds maximum {maximum}")
    return value


@dataclass(frozen=True, slots=True)
class Intent:
    """Immutable, recursively owned user intent snapshot."""

    __hash__: ClassVar[Any] = None

    module: str
    version: str
    kind: IntentKind
    intent_id: str
    sender_pubkey: PubKey
    deadline: int
    salt: str | None = None
    fields: Mapping[str, Any] | None = None

    def __post_init__(self) -> None:
        if type(self.module) is not str or self.module != "TauSwap":
            raise ValueError(f"Invalid module: {self.module}")
        _require_nonempty_str(self.version, name="version", max_len=64)
        if self.version != "0.1":
            raise ValueError(f"Unsupported version: {self.version}")
        if type(self.kind) is not IntentKind:
            raise TypeError("kind must be exactly IntentKind")
        _require_nonempty_str(
            self.sender_pubkey,
            name="sender_pubkey",
            max_len=512,
        )
        _require_nonnegative_int(
            self.deadline,
            name="deadline",
            maximum=INTENT_DEADLINE_MAX_U64,
        )
        if self.salt is not None:
            _require_nonempty_str(self.salt, name="salt", max_len=4_096)
        try:
            intent_id = canonical_hex_fixed_allow_0x(
                self.intent_id,
                nbytes=32,
                name="intent_id",
            )
        except (TypeError, ValueError) as exc:
            raise ValueError(f"Invalid intent_id format: {self.intent_id}") from exc
        object.__setattr__(self, "intent_id", intent_id)
        object.__setattr__(self, "fields", _freeze_intent_fields(self.fields))

    def get_field(self, key: str, default: Any = None) -> Any:
        """Read one immutable field value."""

        if type(key) is not str:
            raise TypeError("intent field key must be exactly str")
        fields = _require_owned_intent_fields(
            object.__getattribute__(self, "fields")
        )
        return fields.get(key, default)

    def get_wire_field(self, key: str, default: Any = None) -> Any:
        """Return one present field as detached JSON-domain data.

        Committed intent fields stay recursively immutable. Consumers that
        cross into an exact plain-JSON boundary can use this method instead of
        broadening the downstream decoder to arbitrary ``Mapping`` objects.
        """

        if type(key) is not str:
            raise TypeError("intent field key must be exactly str")
        fields = _require_owned_intent_fields(
            object.__getattribute__(self, "fields")
        )
        if key not in fields:
            return default
        return _thaw_intent_value(fields[key], path=f"intent.fields.{key}")

    def with_field(self: _IntentT, key: str, value: object) -> _IntentT:
        """Return a new snapshot with one field replaced."""

        if type(key) is not str or not key:
            raise TypeError("intent field key must be a non-empty string")
        fields = thaw_intent_fields(
            _require_owned_intent_fields(
                object.__getattribute__(self, "fields")
            )
        )
        fields[key] = value
        return replace(self, fields=fields)

    def without_field(self: _IntentT, key: str) -> _IntentT:
        """Return a new snapshot without one field; absent keys are a no-op."""

        if type(key) is not str or not key:
            raise TypeError("intent field key must be a non-empty string")
        current_fields = _require_owned_intent_fields(
            object.__getattribute__(self, "fields")
        )
        if key not in current_fields:
            return self
        fields = thaw_intent_fields(current_fields)
        fields.pop(key, None)
        return replace(self, fields=fields)

    def to_wire_fields(self) -> dict[str, Any]:
        """Return a recursively detached mutable object for JSON encoding."""

        return thaw_intent_fields(
            _require_owned_intent_fields(
                object.__getattribute__(self, "fields")
            )
        )


@dataclass(frozen=True, slots=True)
class SwapIntent(Intent):
    """Validated exact-in or exact-out swap intent."""

    __hash__: ClassVar[Any] = None

    def __post_init__(self) -> None:
        Intent.__post_init__(self)
        if self.kind not in (
            IntentKind.SWAP_EXACT_IN,
            IntentKind.SWAP_EXACT_OUT,
        ):
            raise ValueError(f"Invalid kind for SwapIntent: {self.kind}")

        for name in ("pool_id", "asset_in", "asset_out"):
            value = self.get_field(name)
            if type(value) is not str or not value:
                raise ValueError(f"Missing required field: {name}")
        recipient = self.get_field("recipient", self.sender_pubkey)
        if type(recipient) is not str or not recipient:
            raise ValueError("recipient must be a non-empty string")

        if self.kind is IntentKind.SWAP_EXACT_IN:
            amount_in = self.get_field("amount_in")
            min_amount_out = self.get_field("min_amount_out")
            if type(amount_in) is not int or amount_in <= 0:
                raise ValueError("amount_in must be positive")
            if type(min_amount_out) is not int or min_amount_out < 0:
                raise ValueError("min_amount_out must be non-negative")
        else:
            amount_out = self.get_field("amount_out")
            max_amount_in = self.get_field("max_amount_in")
            if type(amount_out) is not int or amount_out <= 0:
                raise ValueError("amount_out must be positive")
            if type(max_amount_in) is not int or max_amount_in < 0:
                raise ValueError("max_amount_in must be non-negative")


@dataclass(frozen=True, slots=True)
class CreatePoolIntent(Intent):
    """Validated create-pool intent."""

    __hash__: ClassVar[Any] = None

    def __post_init__(self) -> None:
        Intent.__post_init__(self)
        if self.kind is not IntentKind.CREATE_POOL:
            raise ValueError(f"Invalid kind for CreatePoolIntent: {self.kind}")

        asset0 = self.get_field("asset0")
        asset1 = self.get_field("asset1")
        if type(asset0) is not str or type(asset1) is not str:
            raise ValueError("Missing required fields: asset0, asset1")
        if not asset0 or not asset1:
            raise ValueError("Missing required fields: asset0, asset1")
        if asset0 >= asset1:
            raise ValueError(
                f"Assets must be in canonical order: {asset0} < {asset1}"
            )

        fee_bps = self.get_field("fee_bps")
        if type(fee_bps) is not int or not 0 <= fee_bps <= 10_000:
            raise ValueError(f"fee_bps must be in [0, 10000]: {fee_bps}")
        amount0 = self.get_field("amount0")
        amount1 = self.get_field("amount1")
        if type(amount0) is not int or amount0 <= 0:
            raise ValueError("amount0 must be positive")
        if type(amount1) is not int or amount1 <= 0:
            raise ValueError("amount1 must be positive")


def require_exact_intent(value: object) -> Intent:
    """Reject behavior-changing subclasses at direct core API boundaries."""

    if type(value) not in (Intent, SwapIntent, CreatePoolIntent):
        raise TypeError("intent must be an exact ZenoDEX intent value")
    intent = cast(Intent, value)
    _require_owned_intent_fields(object.__getattribute__(intent, "fields"))
    return intent


@dataclass(frozen=True, slots=True)
class SignedIntent:
    """Immutable intent plus a canonically owned hexadecimal signature."""

    __hash__: ClassVar[Any] = None

    intent: Intent
    signature: str

    def __post_init__(self) -> None:
        require_exact_intent(self.intent)
        if type(self.signature) is not str:
            raise TypeError("signature must be a string")
        if not self.signature.startswith("0x"):
            raise ValueError(f"Invalid signature format: {self.signature}")
        try:
            signature = canonical_hex_fixed_allow_0x(
                self.signature,
                nbytes=96,
                name="signature",
            )
        except (TypeError, ValueError) as exc:
            raise ValueError(f"Invalid signature format: {self.signature}") from exc
        object.__setattr__(self, "signature", signature)
