from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from typing import Any, Literal, Mapping

FIRE_INTERVAL_CERT_SCHEMA = "zenodex/fire-interval-certificate/v1"
_EVIDENCE_LEVELS = frozenset({"proved", "contract", "implemented", "tested_discovery", "hypothesis"})

FireRule = Literal["const", "exact_param", "source_bound", "add", "sub", "mul", "min", "max"]


def _require_int(name: str, value: object) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    return int(value)


def _require_sha256_prefixed(name: str, value: object) -> str:
    if not isinstance(value, str) or not value.startswith("sha256:"):
        raise ValueError(f"{name} must be a sha256:... string")
    digest = value.removeprefix("sha256:")
    if len(digest) != 64:
        raise ValueError(f"{name} must be a sha256:... string")
    try:
        int(digest, 16)
    except ValueError as exc:
        raise ValueError(f"{name} must be a sha256:... string") from exc
    return value


def _require_evidence_level(name: str, value: object) -> str:
    if not isinstance(value, str) or not value:
        raise TypeError(f"{name} must be a non-empty string")
    if value not in _EVIDENCE_LEVELS:
        raise ValueError(f"{name} has unsupported evidence level: {value}")
    return value


def _require_nonempty_str(name: str, value: object) -> str:
    if not isinstance(value, str) or not value:
        raise TypeError(f"{name} must be a non-empty string")
    return value


@dataclass(frozen=True)
class FireInterval:
    lower: int
    upper: int

    def __post_init__(self) -> None:
        lower = _require_int("lower", self.lower)
        upper = _require_int("upper", self.upper)
        if lower > upper:
            raise ValueError(f"invalid interval [{lower}, {upper}]")

    def to_dict(self) -> dict[str, int]:
        return {"lower": int(self.lower), "upper": int(self.upper)}

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "FireInterval":
        if not isinstance(payload, Mapping):
            raise TypeError("interval payload must be a mapping")
        return cls(lower=_require_int("lower", payload["lower"]), upper=_require_int("upper", payload["upper"]))


@dataclass(frozen=True)
class FireInstanceGateClaims:
    param_ok: str
    authorization_ok: str
    nonce_ok: str
    maturity_ok: str
    window_ok: str

    def __post_init__(self) -> None:
        object.__setattr__(self, "param_ok", _require_evidence_level("param_ok", self.param_ok))
        object.__setattr__(self, "authorization_ok", _require_evidence_level("authorization_ok", self.authorization_ok))
        object.__setattr__(self, "nonce_ok", _require_evidence_level("nonce_ok", self.nonce_ok))
        object.__setattr__(self, "maturity_ok", _require_evidence_level("maturity_ok", self.maturity_ok))
        object.__setattr__(self, "window_ok", _require_evidence_level("window_ok", self.window_ok))

    def to_dict(self) -> dict[str, str]:
        return {
            "param_ok": self.param_ok,
            "authorization_ok": self.authorization_ok,
            "nonce_ok": self.nonce_ok,
            "maturity_ok": self.maturity_ok,
            "window_ok": self.window_ok,
        }

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "FireInstanceGateClaims":
        if not isinstance(payload, Mapping):
            raise TypeError("instance gate claims payload must be a mapping")
        return cls(
            param_ok=payload["param_ok"],
            authorization_ok=payload["authorization_ok"],
            nonce_ok=payload["nonce_ok"],
            maturity_ok=payload["maturity_ok"],
            window_ok=payload["window_ok"],
        )


@dataclass(frozen=True)
class FireCertNode:
    rule: FireRule
    lower: int
    upper: int
    value: int | None = None
    name: str | None = None
    children: tuple["FireCertNode", ...] = ()

    def __post_init__(self) -> None:
        _require_int("lower", self.lower)
        _require_int("upper", self.upper)
        if self.lower > self.upper:
            raise ValueError(f"invalid claimed interval [{self.lower}, {self.upper}]")
        if self.rule not in {"const", "exact_param", "source_bound", "add", "sub", "mul", "min", "max"}:
            raise ValueError(f"unsupported rule: {self.rule}")
        if self.rule == "const":
            if self.value is None:
                raise ValueError("const node requires value")
            _require_int("value", self.value)
            if self.name is not None:
                raise ValueError("const node must not have name")
            if self.children:
                raise ValueError("const node must not have children")
        elif self.rule in {"exact_param", "source_bound"}:
            if not isinstance(self.name, str) or not self.name:
                raise ValueError(f"{self.rule} node requires non-empty name")
            if self.value is not None:
                raise ValueError(f"{self.rule} node must not have value")
            if self.children:
                raise ValueError(f"{self.rule} node must not have children")
        else:
            if self.value is not None or self.name is not None:
                raise ValueError(f"{self.rule} node must not have value or name")
            if len(self.children) != 2:
                raise ValueError(f"{self.rule} node requires two children")

    @property
    def interval(self) -> FireInterval:
        return FireInterval(self.lower, self.upper)

    def to_dict(self) -> dict[str, Any]:
        payload: dict[str, Any] = {
            "rule": self.rule,
            "lower": int(self.lower),
            "upper": int(self.upper),
            "children": [child.to_dict() for child in self.children],
        }
        if self.value is not None:
            payload["value"] = int(self.value)
        if self.name is not None:
            payload["name"] = self.name
        return payload

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "FireCertNode":
        if not isinstance(payload, Mapping):
            raise TypeError("node payload must be a mapping")
        raw_children = payload.get("children", ())
        if not isinstance(raw_children, (list, tuple)):
            raise TypeError("children must be a sequence")
        return cls(
            rule=_require_nonempty_str("rule", payload["rule"]),
            lower=_require_int("lower", payload["lower"]),
            upper=_require_int("upper", payload["upper"]),
            value=None if "value" not in payload else _require_int("value", payload["value"]),
            name=None if "name" not in payload else _require_nonempty_str("name", payload["name"]),
            children=tuple(cls.from_dict(child) for child in raw_children),
        )


@dataclass(frozen=True)
class FireCertEnv:
    exact_values: Mapping[str, int]
    source_bounds: Mapping[str, FireInterval]

    def exact(self, name: str) -> int:
        if name not in self.exact_values:
            raise KeyError(f"missing exact value: {name}")
        return _require_int(name, self.exact_values[name])

    def source_bound(self, name: str) -> FireInterval:
        if name not in self.source_bounds:
            raise KeyError(f"missing source bound: {name}")
        bound = self.source_bounds[name]
        if not isinstance(bound, FireInterval):
            raise TypeError(f"source bound {name} must be a FireInterval")
        return bound


@dataclass(frozen=True)
class FireIntervalCertificate:
    root: FireCertNode
    instance_gate_claims: FireInstanceGateClaims | None = None
    schema: str = FIRE_INTERVAL_CERT_SCHEMA

    def __post_init__(self) -> None:
        if self.schema != FIRE_INTERVAL_CERT_SCHEMA:
            raise ValueError("fire interval certificate schema mismatch")
        if not isinstance(self.root, FireCertNode):
            raise TypeError("root must be a FireCertNode")
        if self.instance_gate_claims is not None and not isinstance(self.instance_gate_claims, FireInstanceGateClaims):
            raise TypeError("instance_gate_claims must be a FireInstanceGateClaims")

    def to_dict(self) -> dict[str, Any]:
        payload = {"schema": self.schema, "root": self.root.to_dict()}
        if self.instance_gate_claims is not None:
            payload["instance_gate_claims"] = self.instance_gate_claims.to_dict()
        return payload

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "FireIntervalCertificate":
        if not isinstance(payload, Mapping):
            raise TypeError("certificate payload must be a mapping")
        claims_payload = payload.get("instance_gate_claims")
        return cls(
            schema=_require_nonempty_str("schema", payload["schema"]),
            root=FireCertNode.from_dict(payload["root"]),
            instance_gate_claims=(
                None if claims_payload is None else FireInstanceGateClaims.from_dict(claims_payload)
            ),
        )


def fire_cert_sha256(certificate: FireIntervalCertificate) -> str:
    payload = json.dumps(certificate.to_dict(), sort_keys=True, separators=(",", ":")).encode("utf-8")
    return "sha256:" + hashlib.sha256(payload).hexdigest()


def _product_interval(left: FireInterval, right: FireInterval) -> FireInterval:
    candidates = (
        left.lower * right.lower,
        left.lower * right.upper,
        left.upper * right.lower,
        left.upper * right.upper,
    )
    return FireInterval(lower=min(candidates), upper=max(candidates))


def _derive_binary_interval(rule: FireRule, left: FireInterval, right: FireInterval) -> FireInterval:
    if rule == "add":
        return FireInterval(lower=left.lower + right.lower, upper=left.upper + right.upper)
    if rule == "sub":
        return FireInterval(lower=left.lower - right.upper, upper=left.upper - right.lower)
    if rule == "mul":
        return _product_interval(left, right)
    if rule == "min":
        return FireInterval(lower=min(left.lower, right.lower), upper=min(left.upper, right.upper))
    if rule == "max":
        return FireInterval(lower=max(left.lower, right.lower), upper=max(left.upper, right.upper))
    raise ValueError(f"unsupported binary rule: {rule}")


def _verify_node(node: FireCertNode, env: FireCertEnv, *, path: str) -> tuple[bool, str | None, FireInterval | None]:
    try:
        if node.rule == "const":
            if node.value is None:
                raise ValueError("const node missing value")
            derived = FireInterval(lower=node.value, upper=node.value)
        elif node.rule == "exact_param":
            if node.name is None:
                raise ValueError("exact_param node missing name")
            value = env.exact(node.name)
            derived = FireInterval(lower=value, upper=value)
        elif node.rule == "source_bound":
            if node.name is None:
                raise ValueError("source_bound node missing name")
            derived = env.source_bound(node.name)
        else:
            left = node.children[0]
            right = node.children[1]
            ok, err, left_interval = _verify_node(left, env, path=f"{path}.0")
            if not ok:
                return False, err, None
            ok, err, right_interval = _verify_node(right, env, path=f"{path}.1")
            if not ok:
                return False, err, None
            if left_interval is None or right_interval is None:
                raise ValueError("verified child node did not return interval")
            derived = _derive_binary_interval(node.rule, left_interval, right_interval)
    except (AssertionError, KeyError, TypeError, ValueError) as exc:
        return False, f"{path}:{exc}", None

    if derived.lower != node.lower or derived.upper != node.upper:
        return (
            False,
            f"{path}:claimed interval [{node.lower}, {node.upper}] != derived [{derived.lower}, {derived.upper}]",
            None,
        )
    return True, None, derived


def verify_interval_certificate(
    certificate: FireIntervalCertificate,
    env: FireCertEnv,
) -> tuple[bool, str | None, FireInterval | None]:
    if not isinstance(certificate, FireIntervalCertificate):
        raise TypeError("certificate must be a FireIntervalCertificate")
    if not isinstance(env, FireCertEnv):
        raise TypeError("env must be a FireCertEnv")
    return _verify_node(certificate.root, env, path="root")


def verify_instance_gate_claims(
    certificate: FireIntervalCertificate,
    *,
    expected: FireInstanceGateClaims | None = None,
    require_present: bool = False,
) -> tuple[bool, str | None, FireInstanceGateClaims | None]:
    if not isinstance(certificate, FireIntervalCertificate):
        raise TypeError("certificate must be a FireIntervalCertificate")
    claims = certificate.instance_gate_claims
    if claims is None:
        if require_present:
            return False, "instance_gate_claims_missing", None
        return True, None, None
    if expected is not None and claims != expected:
        return False, "instance_gate_claims_mismatch", claims
    return True, None, claims


def const_node(value: int) -> FireCertNode:
    value = _require_int("value", value)
    return FireCertNode(rule="const", lower=value, upper=value, value=value)


def exact_param_node(name: str, value: int) -> FireCertNode:
    value = _require_int(name, value)
    return FireCertNode(rule="exact_param", name=name, lower=value, upper=value)


def source_bound_node(name: str, bound: FireInterval) -> FireCertNode:
    if not isinstance(bound, FireInterval):
        raise TypeError("bound must be a FireInterval")
    return FireCertNode(rule="source_bound", name=name, lower=bound.lower, upper=bound.upper)


def binary_node(rule: FireRule, left: FireCertNode, right: FireCertNode) -> FireCertNode:
    if rule not in {"add", "sub", "mul", "min", "max"}:
        raise ValueError(f"binary node does not support rule: {rule}")
    if not isinstance(left, FireCertNode) or not isinstance(right, FireCertNode):
        raise TypeError("binary node children must be FireCertNode values")
    interval = _derive_binary_interval(rule, left.interval, right.interval)
    return FireCertNode(rule=rule, lower=interval.lower, upper=interval.upper, children=(left, right))


__all__ = [
    "FIRE_INTERVAL_CERT_SCHEMA",
    "FireCertEnv",
    "FireCertNode",
    "FireInstanceGateClaims",
    "FireInterval",
    "FireIntervalCertificate",
    "FireRule",
    "_require_evidence_level",
    "_require_sha256_prefixed",
    "binary_node",
    "const_node",
    "exact_param_node",
    "fire_cert_sha256",
    "source_bound_node",
    "verify_instance_gate_claims",
    "verify_interval_certificate",
]
