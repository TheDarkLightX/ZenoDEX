"""Owned task values and closed decode edges for the signed project workflow."""

from dataclasses import dataclass, fields, is_dataclass
from enum import Enum
from typing import cast

from .authority import Action, Delegation
from .codec import _array, _integer, _object, _parse, _string, decode_scope, encode
from .model import Candidate, LacunaError, Scope


def plain(value: object) -> object:
    """Render internal diagnostics; input admission uses exact decoders below."""
    if isinstance(value, Enum):
        return value.value
    if is_dataclass(value) and not isinstance(value, type):
        return {f.name: plain(getattr(value, f.name)) for f in fields(value)}
    if type(value) is tuple or type(value) is list:
        return [plain(item) for item in value]
    if type(value) is dict:
        return {key: plain(item) for key, item in value.items()}
    if value is None or type(value) in (str, int, bool):
        return value
    raise LacunaError("JSON_TYPE")


def sha_field(value: object) -> str:
    text = _string(value)
    if len(text) != 64 or any(c not in "0123456789abcdef" for c in text):
        raise LacunaError("INVALID_DIGEST")
    return text


@dataclass(frozen=True, slots=True)
class RuntimeSpec:
    adapter: str
    inputs: tuple[int, ...]
    observations: tuple[str, ...]

    def __post_init__(self) -> None:
        if self.adapter not in ("RELATION", "RESTRICTED_PIPELINE", "SIGNAL_MIGRATION"):
            raise LacunaError("UNALLOWLISTED_SOURCE")
        if type(self.inputs) is not tuple or len(self.inputs) > 256 or any(
            type(i) is not int or i < 0 or i > 255 for i in self.inputs
        ):
            raise LacunaError("INVALID_RUNTIME_INPUTS")
        if type(self.observations) is not tuple or any(type(o) is not str for o in self.observations):
            raise LacunaError("MODEL_OMISSION")
        if len(self.observations) > 32 or len(self.observations) != len(set(self.observations)):
            raise LacunaError("MODEL_OMISSION")
        if self.adapter == "RELATION" and (self.inputs or self.observations):
            raise LacunaError("INVALID_RUNTIME_INPUTS")


@dataclass(frozen=True, slots=True)
class Task:
    scope: Scope
    runtime: RuntimeSpec
    delegates: tuple[Delegation, ...]
    tau_sha256: str | None
    esso_sha256: str | None

    def __post_init__(self) -> None:
        if type(self.scope) is not Scope or type(self.runtime) is not RuntimeSpec:
            raise LacunaError("JSON_TYPE")
        if type(self.delegates) is not tuple or len(self.delegates) > 16 or any(
            type(d) is not Delegation for d in self.delegates
        ):
            raise LacunaError("MALFORMED_APPROVAL")
        if len({d.public_key for d in self.delegates}) != len(self.delegates):
            raise LacunaError("MALFORMED_APPROVAL")
        if any(d.scope_root != self.scope.root for d in self.delegates):
            raise LacunaError("UNAUTHORIZED")
        for pin in (self.tau_sha256, self.esso_sha256):
            if pin is not None:
                sha_field(pin)
        if self.esso_sha256 is not None and self.runtime.adapter != "SIGNAL_MIGRATION":
            raise LacunaError("UNSUPPORTED_ESSO_PROFILE")


def task_value(task: Task) -> dict[str, object]:
    return cast(dict[str, object], plain(task))


def decode_task(value: object) -> Task:
    item = _object(value, frozenset({"scope", "runtime", "delegates", "tau_sha256", "esso_sha256"}))
    runtime = _object(item["runtime"], frozenset({"adapter", "inputs", "observations"}))
    delegates = []
    for raw in _array(item["delegates"]):
        grant = _object(raw, frozenset({"public_key", "scope_root", "actions"}))
        try:
            actions = tuple(Action(_string(a)) for a in _array(grant["actions"]))
        except ValueError as exc:
            raise LacunaError("MALFORMED_APPROVAL") from exc
        delegates.append(Delegation(sha_field(grant["public_key"]), sha_field(grant["scope_root"]), actions))
    return Task(
        decode_scope(encode(item["scope"])),
        RuntimeSpec(_string(runtime["adapter"]), tuple(_integer(i) for i in _array(runtime["inputs"])),
                    tuple(_string(o) for o in _array(runtime["observations"]))),
        tuple(delegates),
        None if item["tau_sha256"] is None else sha_field(item["tau_sha256"]),
        None if item["esso_sha256"] is None else sha_field(item["esso_sha256"]),
    )


def payload_object(raw: bytes, names: set[str]) -> dict[str, object]:
    result = _object(_parse(raw), frozenset(names))
    if encode(result) != raw:
        raise LacunaError("NONCANONICAL_PAYLOAD")
    return result


@dataclass(frozen=True, slots=True)
class ProjectState:
    project_id: str
    revision: str
    scope_revision: str
    task: Task
    survivors: tuple[int, ...]
    candidate: Candidate | None
    cancelled: bool
    answers: tuple[tuple[str, str, str, str], ...]
    completion: bytes | None


def retired_requirements(previous: Scope, successor: Scope) -> tuple[str, ...]:
    """Changing the meaning of a row invalidates index-based preservation."""
    changed_domain = (previous.contexts, previous.outcomes, previous.assumptions) != (
        successor.contexts, successor.outcomes, successor.assumptions,
    )
    remaining = {r.name: r for r in successor.protected}
    return tuple(sorted(r.name for r in previous.protected
                        if changed_domain or remaining.get(r.name) != r))
