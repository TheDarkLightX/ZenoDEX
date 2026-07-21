"""Deterministic, monotone join for parallel admission facts.

This module is a functional-core primitive. Workers operate on one immutable
execution context and return data-only bundles. The join is independent of
physical worker count, completion order, and bundle arrival order.

The admitted surface is intentionally narrower than an LVar runtime:

* facts grow by pointwise set/map union;
* duplicate identical facts are idempotent;
* different values for one fact key are a deterministic conflict;
* semantic rejection precedence follows logical partition order;
* operational worker failures, missing bundles, duplicates, and context drift
  reject with no frozen candidate;
* freezing occurs only after every expected logical partition has one bundle.

It grants no value-moving or commit authority. The sequential transition remains
normative; an imperative shell may use these frozen facts as inputs to that
transition and atomically commit only the transition's exact effect plan.
"""

from __future__ import annotations

import hashlib
import json
import re
from dataclasses import dataclass, field
from typing import Final, Iterable, Sequence

_SCHEMA_CONTEXT: Final = "zenodex.parallel_admission.context.v1"
_SCHEMA_FACT: Final = "zenodex.parallel_admission.fact.v1"
_SCHEMA_BUNDLE: Final = "zenodex.parallel_admission.worker_bundle.v1"
_SCHEMA_FACT_SET: Final = "zenodex.parallel_admission.frozen_fact_set.v1"
_SCHEMA_JOIN: Final = "zenodex.parallel_admission.join_result.v1"

MAX_LOGICAL_PARTITIONS: Final = 4096
MAX_FACTS_PER_BUNDLE: Final = 4096
MAX_FACT_KEY_BYTES: Final = 256
MAX_FACT_PAYLOAD_BYTES: Final = 1_048_576
MAX_REJECTIONS_PER_BUNDLE: Final = 4096
MAX_TOKEN_BYTES: Final = 128

_HASH_RE = re.compile(r"^sha256:[0-9a-f]{64}$")
_TOKEN_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._:/-]*$")


def _canonical_json_bytes(value: object) -> bytes:
    return json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
        allow_nan=False,
    ).encode("ascii")


def _domain_hash(domain: str, value: object) -> str:
    digest = hashlib.sha256()
    digest.update(domain.encode("ascii"))
    digest.update(b"\x00")
    digest.update(_canonical_json_bytes(value))
    return "sha256:" + digest.hexdigest()


def _payload_hash(payload: bytes) -> str:
    return "sha256:" + hashlib.sha256(payload).hexdigest()


def _require_hash(value: str, *, name: str) -> str:
    if not isinstance(value, str) or _HASH_RE.fullmatch(value) is None:
        raise ValueError(f"{name} must be canonical sha256:<64 lowercase hex>")
    return value


def _require_token(value: str, *, name: str, max_bytes: int = MAX_TOKEN_BYTES) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a string")
    if not value or len(value.encode("ascii", "strict")) > max_bytes:
        raise ValueError(f"{name} must be non-empty ASCII within {max_bytes} bytes")
    if _TOKEN_RE.fullmatch(value) is None:
        raise ValueError(f"{name} has non-canonical characters")
    return value


def _require_nonnegative_int(value: int, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    if value < 0:
        raise ValueError(f"{name} must be non-negative")
    return int(value)


def _require_partition_ids(values: Sequence[int]) -> tuple[int, ...]:
    if not isinstance(values, (tuple, list)):
        raise TypeError("expected_partition_ids must be a tuple or list")
    if not values:
        raise ValueError("expected_partition_ids must be non-empty")
    if len(values) > MAX_LOGICAL_PARTITIONS:
        raise ValueError("too many logical partitions")
    normalized = tuple(
        _require_nonnegative_int(value, name="logical partition id") for value in values
    )
    if tuple(sorted(normalized)) != normalized:
        raise ValueError("expected_partition_ids must be strictly increasing")
    if len(set(normalized)) != len(normalized):
        raise ValueError("expected_partition_ids must be unique")
    return normalized


@dataclass(frozen=True, slots=True)
class ParallelExecutionContext:
    """Authority bindings shared by every logical worker."""

    pre_state_root: str
    command_set_root: str
    execution_context_hash: str
    policy_hash: str
    module_version_digest: str
    algorithm_version_digest: str
    partition_profile_version: str
    context_hash: str = field(init=False)

    def __post_init__(self) -> None:
        for name in (
            "pre_state_root",
            "command_set_root",
            "execution_context_hash",
            "policy_hash",
            "module_version_digest",
            "algorithm_version_digest",
        ):
            _require_hash(getattr(self, name), name=name)
        _require_token(
            self.partition_profile_version,
            name="partition_profile_version",
        )
        object.__setattr__(
            self,
            "context_hash",
            _domain_hash(
                _SCHEMA_CONTEXT,
                {
                    "algorithm_version_digest": self.algorithm_version_digest,
                    "command_set_root": self.command_set_root,
                    "execution_context_hash": self.execution_context_hash,
                    "module_version_digest": self.module_version_digest,
                    "partition_profile_version": self.partition_profile_version,
                    "policy_hash": self.policy_hash,
                    "pre_state_root": self.pre_state_root,
                    "schema": _SCHEMA_CONTEXT,
                },
            ),
        )


@dataclass(frozen=True, slots=True)
class MonotoneFact:
    """One immutable fact. Its key may only acquire this exact payload."""

    key: str
    payload: bytes
    payload_hash: str = field(init=False)
    fact_hash: str = field(init=False)

    def __post_init__(self) -> None:
        _require_token(self.key, name="fact key", max_bytes=MAX_FACT_KEY_BYTES)
        if not isinstance(self.payload, bytes):
            raise TypeError("fact payload must be bytes")
        if len(self.payload) > MAX_FACT_PAYLOAD_BYTES:
            raise ValueError("fact payload too large")
        payload_hash = _payload_hash(self.payload)
        object.__setattr__(self, "payload_hash", payload_hash)
        object.__setattr__(
            self,
            "fact_hash",
            _domain_hash(
                _SCHEMA_FACT,
                {
                    "key": self.key,
                    "payload_hash": payload_hash,
                    "payload_len": len(self.payload),
                    "schema": _SCHEMA_FACT,
                },
            ),
        )


@dataclass(frozen=True, slots=True, order=True)
class SemanticRejection:
    """A core-level rejection emitted by one logical partition."""

    local_command_index: int
    code: str
    evidence_hash: str

    def __post_init__(self) -> None:
        _require_nonnegative_int(
            self.local_command_index,
            name="local_command_index",
        )
        _require_token(self.code, name="semantic rejection code")
        _require_hash(self.evidence_hash, name="semantic rejection evidence_hash")


@dataclass(frozen=True, slots=True)
class WorkerBundle:
    """Data-only result for exactly one versioned logical partition."""

    context_hash: str
    partition_profile_version: str
    logical_partition_id: int
    facts: tuple[MonotoneFact, ...] = ()
    semantic_rejections: tuple[SemanticRejection, ...] = ()
    failure_code: str | None = None
    failure_evidence_hash: str | None = None
    bundle_hash: str = field(init=False)

    def __post_init__(self) -> None:
        _require_hash(self.context_hash, name="worker context_hash")
        _require_token(
            self.partition_profile_version,
            name="worker partition_profile_version",
        )
        _require_nonnegative_int(
            self.logical_partition_id,
            name="logical_partition_id",
        )
        if not isinstance(self.facts, tuple):
            raise TypeError("worker facts must be a tuple")
        if not isinstance(self.semantic_rejections, tuple):
            raise TypeError("worker semantic_rejections must be a tuple")
        if len(self.facts) > MAX_FACTS_PER_BUNDLE:
            raise ValueError("too many worker facts")
        if len(self.semantic_rejections) > MAX_REJECTIONS_PER_BUNDLE:
            raise ValueError("too many semantic rejections")
        if any(not isinstance(fact, MonotoneFact) for fact in self.facts):
            raise TypeError("worker facts contain a non-MonotoneFact")
        if any(
            not isinstance(rejection, SemanticRejection)
            for rejection in self.semantic_rejections
        ):
            raise TypeError(
                "worker semantic_rejections contain a non-SemanticRejection"
            )

        sorted_facts = tuple(
            sorted(
                {
                    (fact.key, fact.payload): fact
                    for fact in self.facts
                }.values(),
                key=lambda fact: (fact.key, fact.payload_hash),
            )
        )
        sorted_rejections = tuple(sorted(set(self.semantic_rejections)))
        object.__setattr__(self, "facts", sorted_facts)
        object.__setattr__(
            self,
            "semantic_rejections",
            sorted_rejections,
        )

        if self.failure_code is None:
            if self.failure_evidence_hash is not None:
                raise ValueError(
                    "failure_evidence_hash requires failure_code"
                )
        else:
            _require_token(self.failure_code, name="worker failure_code")
            if self.failure_evidence_hash is None:
                raise ValueError("worker failure requires failure_evidence_hash")
            _require_hash(
                self.failure_evidence_hash,
                name="worker failure_evidence_hash",
            )
            if self.facts or self.semantic_rejections:
                raise ValueError(
                    "failed worker bundle cannot contain facts or semantic rejections"
                )

        object.__setattr__(
            self,
            "bundle_hash",
            _domain_hash(
                _SCHEMA_BUNDLE,
                {
                    "context_hash": self.context_hash,
                    "facts": [
                        {
                            "fact_hash": fact.fact_hash,
                            "key": fact.key,
                            "payload_hash": fact.payload_hash,
                        }
                        for fact in sorted_facts
                    ],
                    "failure_code": self.failure_code,
                    "failure_evidence_hash": self.failure_evidence_hash,
                    "logical_partition_id": self.logical_partition_id,
                    "partition_profile_version": self.partition_profile_version,
                    "schema": _SCHEMA_BUNDLE,
                    "semantic_rejections": [
                        {
                            "code": rejection.code,
                            "evidence_hash": rejection.evidence_hash,
                            "local_command_index": rejection.local_command_index,
                        }
                        for rejection in sorted_rejections
                    ],
                },
            ),
        )


@dataclass(frozen=True, slots=True)
class FrozenFactSet:
    """Exact monotone fixed point after all logical partitions have joined."""

    facts: tuple[MonotoneFact, ...]
    fact_root: str = field(init=False)

    def __post_init__(self) -> None:
        if not isinstance(self.facts, tuple):
            raise TypeError("frozen facts must be a tuple")
        if any(not isinstance(fact, MonotoneFact) for fact in self.facts):
            raise TypeError("frozen facts contain a non-MonotoneFact")
        ordered = tuple(sorted(self.facts, key=lambda fact: fact.key))
        if len({fact.key for fact in ordered}) != len(ordered):
            raise ValueError("frozen facts must contain unique keys")
        object.__setattr__(self, "facts", ordered)
        object.__setattr__(
            self,
            "fact_root",
            _domain_hash(
                _SCHEMA_FACT_SET,
                {
                    "facts": [
                        {
                            "fact_hash": fact.fact_hash,
                            "key": fact.key,
                            "payload_hash": fact.payload_hash,
                        }
                        for fact in ordered
                    ],
                    "schema": _SCHEMA_FACT_SET,
                },
            ),
        )


@dataclass(frozen=True, slots=True)
class JoinRejection:
    """Canonical no-candidate failure selected by the deterministic join."""

    code: str
    partition_id: int
    local_command_index: int
    evidence_hash: str
    fact_key: str | None = None

    def __post_init__(self) -> None:
        _require_token(self.code, name="join rejection code")
        if not isinstance(self.partition_id, int) or isinstance(
            self.partition_id,
            bool,
        ):
            raise TypeError("join rejection partition_id must be an int")
        if self.partition_id < -1:
            raise ValueError("join rejection partition_id must be >= -1")
        if not isinstance(self.local_command_index, int) or isinstance(
            self.local_command_index,
            bool,
        ):
            raise TypeError("join rejection local_command_index must be an int")
        if self.local_command_index < -1:
            raise ValueError(
                "join rejection local_command_index must be >= -1"
            )
        _require_hash(self.evidence_hash, name="join rejection evidence_hash")
        if self.fact_key is not None:
            _require_token(
                self.fact_key,
                name="join rejection fact_key",
                max_bytes=MAX_FACT_KEY_BYTES,
            )


@dataclass(frozen=True, slots=True)
class ParallelAdmissionJoinResult:
    """Accepted fixed point or one canonical rejection, never both."""

    ok: bool
    context_hash: str
    expected_partition_ids: tuple[int, ...]
    frozen_facts: FrozenFactSet | None
    rejection: JoinRejection | None
    join_hash: str = field(init=False)

    def __post_init__(self) -> None:
        if not isinstance(self.ok, bool):
            raise TypeError("ok must be bool")
        _require_hash(self.context_hash, name="join context_hash")
        normalized = _require_partition_ids(self.expected_partition_ids)
        object.__setattr__(self, "expected_partition_ids", normalized)
        if self.ok:
            if self.frozen_facts is None or self.rejection is not None:
                raise ValueError(
                    "accepted join requires frozen_facts and no rejection"
                )
        elif self.frozen_facts is not None or self.rejection is None:
            raise ValueError(
                "rejected join requires one rejection and no frozen_facts"
            )
        payload = {
            "context_hash": self.context_hash,
            "expected_partition_ids": list(normalized),
            "fact_root": (
                None if self.frozen_facts is None else self.frozen_facts.fact_root
            ),
            "ok": self.ok,
            "rejection": (
                None
                if self.rejection is None
                else {
                    "code": self.rejection.code,
                    "evidence_hash": self.rejection.evidence_hash,
                    "fact_key": self.rejection.fact_key,
                    "local_command_index": (
                        self.rejection.local_command_index
                    ),
                    "partition_id": self.rejection.partition_id,
                }
            ),
            "schema": _SCHEMA_JOIN,
        }
        object.__setattr__(
            self,
            "join_hash",
            _domain_hash(_SCHEMA_JOIN, payload),
        )


def _rejected(
    *,
    context: ParallelExecutionContext,
    expected_partition_ids: tuple[int, ...],
    code: str,
    evidence: object,
    partition_id: int = -1,
    local_command_index: int = -1,
    fact_key: str | None = None,
) -> ParallelAdmissionJoinResult:
    return ParallelAdmissionJoinResult(
        ok=False,
        context_hash=context.context_hash,
        expected_partition_ids=expected_partition_ids,
        frozen_facts=None,
        rejection=JoinRejection(
            code=code,
            partition_id=partition_id,
            local_command_index=local_command_index,
            evidence_hash=_domain_hash(
                "zenodex.parallel_admission.rejection_evidence.v1",
                evidence,
            ),
            fact_key=fact_key,
        ),
    )


def join_parallel_admission(
    context: ParallelExecutionContext,
    *,
    expected_partition_ids: Sequence[int],
    bundles: Iterable[WorkerBundle],
) -> ParallelAdmissionJoinResult:
    """Join one complete logical profile into an immutable monotone fixed point.

    Bundle arrival order is ignored. Physical worker count is absent from the
    input language. Every rejection returns no frozen fact candidate.
    """

    if not isinstance(context, ParallelExecutionContext):
        raise TypeError("context must be ParallelExecutionContext")
    expected = _require_partition_ids(expected_partition_ids)
    bundle_tuple = tuple(bundles)
    if any(not isinstance(bundle, WorkerBundle) for bundle in bundle_tuple):
        raise TypeError("bundles contain a non-WorkerBundle")

    by_partition: dict[int, list[WorkerBundle]] = {}
    for bundle in bundle_tuple:
        by_partition.setdefault(bundle.logical_partition_id, []).append(bundle)

    expected_set = set(expected)
    actual_set = set(by_partition)
    missing = sorted(expected_set - actual_set)
    extra = sorted(actual_set - expected_set)
    duplicate = sorted(
        partition_id
        for partition_id, partition_bundles in by_partition.items()
        if len(partition_bundles) != 1
    )
    if missing or extra or duplicate:
        implicated = missing + extra + duplicate
        return _rejected(
            context=context,
            expected_partition_ids=expected,
            code="PARTITION_SET_INVALID",
            partition_id=min(implicated) if implicated else -1,
            evidence={
                "duplicate": duplicate,
                "extra": extra,
                "missing": missing,
            },
        )

    ordered_bundles = tuple(by_partition[partition_id][0] for partition_id in expected)

    for bundle in ordered_bundles:
        if bundle.context_hash != context.context_hash:
            return _rejected(
                context=context,
                expected_partition_ids=expected,
                code="CONTEXT_MISMATCH",
                partition_id=bundle.logical_partition_id,
                evidence={
                    "expected_context_hash": context.context_hash,
                    "observed_context_hash": bundle.context_hash,
                },
            )
        if (
            bundle.partition_profile_version
            != context.partition_profile_version
        ):
            return _rejected(
                context=context,
                expected_partition_ids=expected,
                code="PARTITION_PROFILE_MISMATCH",
                partition_id=bundle.logical_partition_id,
                evidence={
                    "expected_partition_profile_version": (
                        context.partition_profile_version
                    ),
                    "observed_partition_profile_version": (
                        bundle.partition_profile_version
                    ),
                },
            )
        if bundle.failure_code is not None:
            return _rejected(
                context=context,
                expected_partition_ids=expected,
                code="WORKER_FAILURE",
                partition_id=bundle.logical_partition_id,
                evidence={
                    "failure_code": bundle.failure_code,
                    "failure_evidence_hash": bundle.failure_evidence_hash,
                },
            )

    semantic_candidates = [
        (
            bundle.logical_partition_id,
            rejection.local_command_index,
            rejection.code,
            rejection.evidence_hash,
        )
        for bundle in ordered_bundles
        for rejection in bundle.semantic_rejections
    ]
    if semantic_candidates:
        (
            partition_id,
            local_command_index,
            rejection_code,
            rejection_evidence_hash,
        ) = min(semantic_candidates)
        return _rejected(
            context=context,
            expected_partition_ids=expected,
            code="SEMANTIC_REJECTION",
            partition_id=partition_id,
            local_command_index=local_command_index,
            evidence={
                "semantic_code": rejection_code,
                "semantic_evidence_hash": rejection_evidence_hash,
            },
        )

    values_by_key: dict[str, dict[bytes, set[int]]] = {}
    facts_by_key_and_payload: dict[tuple[str, bytes], MonotoneFact] = {}
    for bundle in ordered_bundles:
        for fact in bundle.facts:
            values_by_key.setdefault(fact.key, {}).setdefault(
                fact.payload,
                set(),
            ).add(bundle.logical_partition_id)
            facts_by_key_and_payload[(fact.key, fact.payload)] = fact

    conflicts = [
        (
            key,
            tuple(
                sorted(
                    (
                        _payload_hash(payload),
                        tuple(sorted(producers)),
                    )
                    for payload, producers in payloads.items()
                )
            ),
        )
        for key, payloads in values_by_key.items()
        if len(payloads) > 1
    ]
    if conflicts:
        fact_key, value_rows = min(conflicts, key=lambda row: row[0])
        first_partition = min(
            partition
            for _value_hash, producers in value_rows
            for partition in producers
        )
        return _rejected(
            context=context,
            expected_partition_ids=expected,
            code="FACT_CONFLICT",
            partition_id=first_partition,
            fact_key=fact_key,
            evidence={
                "fact_key": fact_key,
                "values": [
                    {
                        "payload_hash": value_hash,
                        "producer_partitions": list(producers),
                    }
                    for value_hash, producers in value_rows
                ],
            },
        )

    frozen = FrozenFactSet(
        facts=tuple(
            facts_by_key_and_payload[(key, next(iter(payloads)))]
            for key, payloads in sorted(values_by_key.items())
        )
    )
    return ParallelAdmissionJoinResult(
        ok=True,
        context_hash=context.context_hash,
        expected_partition_ids=expected,
        frozen_facts=frozen,
        rejection=None,
    )
