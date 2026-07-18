"""Canonical immutable effect plans for execution-context commitments."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Final, Mapping

from src.state.canonical import (
    canonical_hex_fixed_allow_0x,
    canonical_json_bytes,
    domain_sep_bytes,
    encode_bytes,
    sha256_hex,
)

U64_MAX: Final[int] = (1 << 64) - 1
U128_MAX: Final[int] = (1 << 128) - 1
ROOT_NBYTES: Final[int] = 32
EFFECT_PLAN_SCHEMA_V1: Final[str] = "zenodex/execution_effect_plan/v1"
NATIVE_BALANCE_EFFECT_SCHEMA_V1: Final[str] = (
    "zenodex/execution_effect/native_balance_writes/v1"
)
COMMITTED_EFFECT_REFERENCE_SCHEMA_V1: Final[str] = (
    "zenodex/execution_effect/committed_reference/v1"
)


def _require_uint(value: object, *, name: str, maximum: int) -> int:
    if type(value) is not int:
        raise TypeError(f"{name} must be an int")
    if value < 0 or value > maximum:
        raise ValueError(f"{name} out of range")
    return value


def _require_text(value: object, *, name: str) -> str:
    if type(value) is not str:
        raise TypeError(f"{name} must be a str")
    if not value:
        raise ValueError(f"{name} must be non-empty")
    if "\x00" in value:
        raise ValueError(f"{name} must not contain NUL")
    return value


def _require_root(value: object, *, name: str, allow_zero: bool = False) -> str:
    if type(value) is not str:
        raise TypeError(f"{name} must be a str")
    canonical = canonical_hex_fixed_allow_0x(value, nbytes=ROOT_NBYTES, name=name)
    if type(canonical) is not str:
        raise TypeError(f"{name} canonicalizer must return a str")
    if value != canonical:
        raise ValueError(f"{name} must be canonical lowercase 0x-prefixed hex")
    if not allow_zero and canonical == "0x" + "00" * ROOT_NBYTES:
        raise ValueError(f"{name} must be non-zero")
    return canonical


def _require_canonical_principal(value: object, *, name: str) -> str:
    if type(value) is not str:
        raise TypeError(f"{name} must be a str")
    canonical = canonical_hex_fixed_allow_0x(value, nbytes=48, name=name)
    if value != canonical:
        raise ValueError(f"{name} must be canonical lowercase 0x-prefixed hex")
    return canonical


def _require_exact_fields(
    value: object,
    *,
    name: str,
    expected: set[str],
) -> Mapping[str, object]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be an object")
    if set(value) != expected:
        raise ValueError(f"{name} fields mismatch")
    return value


@dataclass(frozen=True, slots=True)
class NativeBalanceWriteV1:
    pubkey: str
    expected_amount: int
    amount: int

    def __post_init__(self) -> None:
        _require_canonical_principal(self.pubkey, name="native balance pubkey")
        _require_uint(
            self.expected_amount,
            name="native balance expected_amount",
            maximum=U128_MAX,
        )
        _require_uint(self.amount, name="native balance amount", maximum=U128_MAX)
        if self.expected_amount == self.amount:
            raise ValueError("native balance write must change the balance")

    def to_obj(self) -> dict[str, object]:
        return {
            "pubkey": self.pubkey,
            "expected_amount": str(self.expected_amount),
            "amount": str(self.amount),
        }

    @classmethod
    def from_obj(cls, value: object) -> "NativeBalanceWriteV1":
        obj = _require_exact_fields(
            value,
            name="native balance write",
            expected={"pubkey", "expected_amount", "amount"},
        )
        raw_expected_amount = obj["expected_amount"]
        raw_amount = obj["amount"]
        for field_name, raw_value in (
            ("expected_amount", raw_expected_amount),
            ("amount", raw_amount),
        ):
            if (
                type(raw_value) is not str
                or not raw_value.isascii()
                or not raw_value.isdecimal()
            ):
                raise TypeError(
                    f"native balance {field_name} must be a canonical decimal string"
                )
            if len(raw_value) > 1 and raw_value.startswith("0"):
                raise ValueError(
                    f"native balance {field_name} must not contain leading zeroes"
                )
        return cls(
            pubkey=_require_canonical_principal(
                obj["pubkey"],
                name="native balance pubkey",
            ),
            expected_amount=int(raw_expected_amount),
            amount=int(raw_amount),
        )


@dataclass(frozen=True, slots=True)
class NativeBalanceEffectV1:
    tx_index: int
    tx_hash: str
    writes: tuple[NativeBalanceWriteV1, ...]

    def __post_init__(self) -> None:
        _require_uint(self.tx_index, name="native balance tx_index", maximum=U64_MAX)
        _require_root(self.tx_hash, name="native balance tx_hash")
        if type(self.writes) is not tuple:
            raise TypeError("native balance writes must be a tuple")
        if not self.writes:
            raise ValueError("native balance writes must be non-empty")
        previous: str | None = None
        for index, write in enumerate(self.writes):
            if type(write) is not NativeBalanceWriteV1:
                raise TypeError(f"native balance writes[{index}] must be NativeBalanceWriteV1")
            if previous is not None and write.pubkey <= previous:
                raise ValueError("native balance writes must be sorted unique by pubkey")
            previous = write.pubkey

    def to_obj(self) -> dict[str, object]:
        return {
            "schema": NATIVE_BALANCE_EFFECT_SCHEMA_V1,
            "tx_index": self.tx_index,
            "tx_hash": self.tx_hash,
            "writes": [write.to_obj() for write in self.writes],
        }

    @classmethod
    def from_obj(cls, value: object) -> "NativeBalanceEffectV1":
        obj = _require_exact_fields(
            value,
            name="native balance effect",
            expected={"schema", "tx_index", "tx_hash", "writes"},
        )
        if obj["schema"] != NATIVE_BALANCE_EFFECT_SCHEMA_V1:
            raise ValueError("native balance effect schema unsupported")
        writes = obj["writes"]
        if type(writes) is not list:
            raise TypeError("native balance effect writes must be a list")
        return cls(
            tx_index=_require_uint(
                obj["tx_index"],
                name="native balance tx_index",
                maximum=U64_MAX,
            ),
            tx_hash=_require_root(obj["tx_hash"], name="native balance tx_hash"),
            writes=tuple(NativeBalanceWriteV1.from_obj(write) for write in writes),
        )


@dataclass(frozen=True, slots=True)
class CommittedEffectReferenceV1:
    effect_kind: str
    effect_id: str
    artifact_hash: str

    def __post_init__(self) -> None:
        _require_text(self.effect_kind, name="effect_kind")
        _require_text(self.effect_id, name="effect_id")
        _require_root(self.artifact_hash, name="effect artifact_hash")

    def to_obj(self) -> dict[str, object]:
        return {
            "schema": COMMITTED_EFFECT_REFERENCE_SCHEMA_V1,
            "effect_kind": self.effect_kind,
            "effect_id": self.effect_id,
            "artifact_hash": self.artifact_hash,
        }

    @classmethod
    def from_obj(cls, value: object) -> "CommittedEffectReferenceV1":
        obj = _require_exact_fields(
            value,
            name="committed effect reference",
            expected={"schema", "effect_kind", "effect_id", "artifact_hash"},
        )
        if obj["schema"] != COMMITTED_EFFECT_REFERENCE_SCHEMA_V1:
            raise ValueError("committed effect reference schema unsupported")
        return cls(
            effect_kind=_require_text(obj["effect_kind"], name="effect_kind"),
            effect_id=_require_text(obj["effect_id"], name="effect_id"),
            artifact_hash=_require_root(
                obj["artifact_hash"],
                name="effect artifact_hash",
            ),
        )


@dataclass(frozen=True, slots=True)
class ExecutionEffectPlanV1:
    chain_id: str
    height: int
    native_balance_effects: tuple[NativeBalanceEffectV1, ...]
    committed_effect_references: tuple[CommittedEffectReferenceV1, ...]

    def __post_init__(self) -> None:
        _require_text(self.chain_id, name="effect plan chain_id")
        _require_uint(self.height, name="effect plan height", maximum=U64_MAX)
        if type(self.native_balance_effects) is not tuple:
            raise TypeError("native_balance_effects must be a tuple")
        if type(self.committed_effect_references) is not tuple:
            raise TypeError("committed_effect_references must be a tuple")

        previous_tx_index: int | None = None
        for index, effect in enumerate(self.native_balance_effects):
            if type(effect) is not NativeBalanceEffectV1:
                raise TypeError(
                    f"native_balance_effects[{index}] must be NativeBalanceEffectV1"
                )
            if previous_tx_index is not None and effect.tx_index <= previous_tx_index:
                raise ValueError("native balance effects must be sorted unique by tx_index")
            previous_tx_index = effect.tx_index

        previous_reference: tuple[str, str] | None = None
        for index, reference in enumerate(self.committed_effect_references):
            if type(reference) is not CommittedEffectReferenceV1:
                raise TypeError(
                    "committed_effect_references"
                    f"[{index}] must be CommittedEffectReferenceV1"
                )
            key = (reference.effect_kind, reference.effect_id)
            if previous_reference is not None and key <= previous_reference:
                raise ValueError("committed effect references must be sorted unique")
            previous_reference = key

    def to_obj(self) -> dict[str, object]:
        return {
            "schema": EFFECT_PLAN_SCHEMA_V1,
            "chain_id": self.chain_id,
            "height": self.height,
            "native_balance_effects": [
                effect.to_obj() for effect in self.native_balance_effects
            ],
            "committed_effect_references": [
                reference.to_obj() for reference in self.committed_effect_references
            ],
        }

    @classmethod
    def from_obj(cls, value: object) -> "ExecutionEffectPlanV1":
        obj = _require_exact_fields(
            value,
            name="execution effect plan",
            expected={
                "schema",
                "chain_id",
                "height",
                "native_balance_effects",
                "committed_effect_references",
            },
        )
        if obj["schema"] != EFFECT_PLAN_SCHEMA_V1:
            raise ValueError("execution effect plan schema unsupported")
        native_effects = obj["native_balance_effects"]
        committed_references = obj["committed_effect_references"]
        if type(native_effects) is not list:
            raise TypeError("native_balance_effects must be a list")
        if type(committed_references) is not list:
            raise TypeError("committed_effect_references must be a list")
        return cls(
            chain_id=_require_text(obj["chain_id"], name="effect plan chain_id"),
            height=_require_uint(
                obj["height"],
                name="effect plan height",
                maximum=U64_MAX,
            ),
            native_balance_effects=tuple(
                NativeBalanceEffectV1.from_obj(effect) for effect in native_effects
            ),
            committed_effect_references=tuple(
                CommittedEffectReferenceV1.from_obj(reference)
                for reference in committed_references
            ),
        )


def execution_effect_plan_hash_v1(plan: ExecutionEffectPlanV1) -> str:
    if type(plan) is not ExecutionEffectPlanV1:
        raise TypeError("plan must be ExecutionEffectPlanV1")
    payload = domain_sep_bytes("execution_effect_plan", version=1) + encode_bytes(
        canonical_json_bytes(plan.to_obj())
    )
    digest = sha256_hex(payload)
    if type(digest) is not str:
        raise TypeError("sha256_hex must return a str")
    return digest
