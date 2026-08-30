from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping

from ..integration.bls_intent_signing import bls_pubkey_hex_from_privkey
from ..state.canonical import canonical_json_bytes, sha256_hex
from .autotrader_client_policy_surface import (
    AutoTraderClientPolicySurface,
    autotrader_client_policy_surface_from_dict,
)
from .autotrader_local_guard_evaluator import (
    AutoTraderLocalGuardEvaluation,
    AutoTraderLocalGuardInputs,
    autotrader_local_guard_evaluation_from_dict,
    evaluate_autotrader_local_guards,
)
from .policy_artifacts import G2Basic, _parse_privkey_to_int, _require_bls

AUTOTRADER_CLIENT_POLICY_BUNDLE_SCHEMA = "zenodex/autotrader-client-policy-bundle/v1"
DEFAULT_CLIENT_POLICY_BUNDLE_COMPILER_VERSION = "autotrader-client-policy-bundle/v1"


def _require_text(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a string")
    text = value.strip()
    if not text:
        raise ValueError(f"{name} must be non-empty")
    return text


def _require_mapping(value: object, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be an object")
    return value


def _require_isoish_timestamp(value: object, *, name: str) -> str:
    text = _require_text(value, name=name)
    if "T" not in text:
        raise ValueError(f"{name} must be an ISO-like timestamp")
    return text


@dataclass(frozen=True)
class AutoTraderClientPolicyBundle:
    bundle_name: str
    built_at: str
    compiler_version: str
    client_policy_surface: AutoTraderClientPolicySurface
    local_guard_evaluation: AutoTraderLocalGuardEvaluation | None = None
    signature: str | None = None
    signer_pubkey: str | None = None

    def __post_init__(self) -> None:
        object.__setattr__(self, "bundle_name", _require_text(self.bundle_name, name="bundle_name"))
        object.__setattr__(self, "built_at", _require_isoish_timestamp(self.built_at, name="built_at"))
        object.__setattr__(
            self,
            "compiler_version",
            _require_text(self.compiler_version, name="compiler_version"),
        )
        if not isinstance(self.client_policy_surface, AutoTraderClientPolicySurface):
            raise TypeError("client_policy_surface must be an AutoTraderClientPolicySurface")
        if self.local_guard_evaluation is not None:
            if not isinstance(self.local_guard_evaluation, AutoTraderLocalGuardEvaluation):
                raise TypeError("local_guard_evaluation must be an AutoTraderLocalGuardEvaluation")
            if self.local_guard_evaluation.strategy_id != self.client_policy_surface.strategy.strategy_id:
                raise ValueError("local guard evaluation strategy_id mismatch")
        if (self.signature is None) != (self.signer_pubkey is None):
            raise ValueError("signature and signer_pubkey must either both be present or both be absent")
        if self.signature is not None:
            object.__setattr__(self, "signature", _require_text(self.signature, name="signature"))
            signer_pubkey = _require_text(self.signer_pubkey, name="signer_pubkey")
            if signer_pubkey != self.client_policy_surface.strategy.owner_pubkey:
                raise ValueError("bundle signer pubkey mismatch")
            object.__setattr__(self, "signer_pubkey", signer_pubkey)

    @property
    def strategy_id(self) -> str:
        return self.client_policy_surface.strategy.strategy_id

    @property
    def strategy_hash(self) -> str:
        return self.client_policy_surface.strategy.strategy_hash_hex()

    @property
    def owner_pubkey(self) -> str:
        return self.client_policy_surface.strategy.owner_pubkey

    def local_guard_evaluation_hash_hex(self) -> str | None:
        if self.local_guard_evaluation is None:
            return None
        return sha256_hex(canonical_json_bytes(self.local_guard_evaluation.to_dict()))

    def to_unsigned_dict(self) -> dict[str, Any]:
        return {
            "schema": AUTOTRADER_CLIENT_POLICY_BUNDLE_SCHEMA,
            "bundle_name": self.bundle_name,
            "built_at": self.built_at,
            "compiler_version": self.compiler_version,
            "strategy_id": self.strategy_id,
            "strategy_hash": self.strategy_hash,
            "owner_pubkey": self.owner_pubkey,
            "client_policy_surface_hash": self.client_policy_surface.client_policy_surface_hash_hex(),
            "client_policy_surface": self.client_policy_surface.to_dict(),
            "local_guard_evaluation_hash": self.local_guard_evaluation_hash_hex(),
            "local_guard_evaluation": (
                None if self.local_guard_evaluation is None else self.local_guard_evaluation.to_dict()
            ),
        }

    def to_dict(self) -> dict[str, Any]:
        payload = self.to_unsigned_dict()
        payload["client_policy_bundle_hash"] = self.client_policy_bundle_hash_hex()
        payload["signer_pubkey"] = self.signer_pubkey
        payload["signature"] = self.signature
        return payload

    def to_json_bytes(self) -> bytes:
        return canonical_json_bytes(self.to_unsigned_dict())

    def client_policy_bundle_hash_hex(self) -> str:
        return sha256_hex(self.to_json_bytes())


def build_autotrader_client_policy_bundle(
    *,
    bundle_name: str,
    built_at: str,
    client_policy_surface: AutoTraderClientPolicySurface,
    local_guard_evaluation: AutoTraderLocalGuardEvaluation | None = None,
    local_guard_inputs: AutoTraderLocalGuardInputs | None = None,
    compiler_version: str = DEFAULT_CLIENT_POLICY_BUNDLE_COMPILER_VERSION,
) -> AutoTraderClientPolicyBundle:
    if not isinstance(client_policy_surface, AutoTraderClientPolicySurface):
        raise TypeError("client_policy_surface must be an AutoTraderClientPolicySurface")
    if local_guard_evaluation is not None and local_guard_inputs is not None:
        raise ValueError("provide local_guard_evaluation or local_guard_inputs, not both")
    effective_guard_evaluation = local_guard_evaluation
    if local_guard_inputs is not None:
        if not isinstance(local_guard_inputs, AutoTraderLocalGuardInputs):
            raise TypeError("local_guard_inputs must be an AutoTraderLocalGuardInputs")
        effective_guard_evaluation = evaluate_autotrader_local_guards(
            strategy=client_policy_surface.strategy,
            inputs=local_guard_inputs,
        )
    return AutoTraderClientPolicyBundle(
        bundle_name=bundle_name,
        built_at=built_at,
        compiler_version=compiler_version,
        client_policy_surface=client_policy_surface,
        local_guard_evaluation=effective_guard_evaluation,
        signature=None,
        signer_pubkey=None,
    )


def sign_autotrader_client_policy_bundle(
    bundle: AutoTraderClientPolicyBundle,
    *,
    privkey: str | int | bytes | bytearray,
) -> AutoTraderClientPolicyBundle:
    if not isinstance(bundle, AutoTraderClientPolicyBundle):
        raise TypeError("bundle must be an AutoTraderClientPolicyBundle")
    _require_bls()
    sk = _parse_privkey_to_int(privkey)
    signer_pubkey = "0x" + bls_pubkey_hex_from_privkey(sk)
    if signer_pubkey != bundle.owner_pubkey:
        raise ValueError("signer pubkey does not match client policy owner")
    signature = "0x" + G2Basic.Sign(sk, bundle.to_json_bytes()).hex()
    return AutoTraderClientPolicyBundle(
        bundle_name=bundle.bundle_name,
        built_at=bundle.built_at,
        compiler_version=bundle.compiler_version,
        client_policy_surface=bundle.client_policy_surface,
        local_guard_evaluation=bundle.local_guard_evaluation,
        signature=signature,
        signer_pubkey=signer_pubkey,
    )


def verify_autotrader_client_policy_bundle_signature(bundle: AutoTraderClientPolicyBundle) -> bool:
    if bundle.signature is None or bundle.signer_pubkey is None:
        return False
    if G2Basic is None:
        return False
    if not bundle.signer_pubkey.startswith("0x"):
        return False
    try:
        pk = bytes.fromhex(bundle.signer_pubkey[2:])
        sig = bytes.fromhex(bundle.signature[2:] if bundle.signature.startswith("0x") else bundle.signature)
    except ValueError:
        return False
    return bool(G2Basic.Verify(pk, bundle.to_json_bytes(), sig))


def autotrader_client_policy_bundle_from_dict(data: Mapping[str, Any]) -> AutoTraderClientPolicyBundle:
    doc = _require_mapping(data, name="client policy bundle")
    schema = doc.get("schema")
    if schema is not None and schema != AUTOTRADER_CLIENT_POLICY_BUNDLE_SCHEMA:
        raise ValueError("unsupported client policy bundle schema")
    surface_raw = _require_mapping(doc.get("client_policy_surface"), name="client_policy_surface")
    surface = autotrader_client_policy_surface_from_dict(surface_raw)
    local_guard_evaluation = None
    local_guard_evaluation_raw = doc.get("local_guard_evaluation")
    if local_guard_evaluation_raw is not None:
        local_guard_evaluation = autotrader_local_guard_evaluation_from_dict(
            _require_mapping(local_guard_evaluation_raw, name="local_guard_evaluation")
        )
    bundle = AutoTraderClientPolicyBundle(
        bundle_name=_require_text(doc.get("bundle_name"), name="bundle_name"),
        built_at=_require_text(doc.get("built_at"), name="built_at"),
        compiler_version=_require_text(
            doc.get("compiler_version", DEFAULT_CLIENT_POLICY_BUNDLE_COMPILER_VERSION),
            name="compiler_version",
        ),
        client_policy_surface=surface,
        local_guard_evaluation=local_guard_evaluation,
        signature=doc.get("signature"),
        signer_pubkey=doc.get("signer_pubkey"),
    )
    strategy_id = _require_text(doc.get("strategy_id"), name="strategy_id")
    if strategy_id != bundle.strategy_id:
        raise ValueError("client policy bundle strategy_id mismatch")
    strategy_hash = _require_text(doc.get("strategy_hash"), name="strategy_hash")
    if strategy_hash != bundle.strategy_hash:
        raise ValueError("client policy bundle strategy_hash mismatch")
    owner_pubkey = _require_text(doc.get("owner_pubkey"), name="owner_pubkey")
    if owner_pubkey != bundle.owner_pubkey:
        raise ValueError("client policy bundle owner_pubkey mismatch")
    surface_hash = _require_text(doc.get("client_policy_surface_hash"), name="client_policy_surface_hash")
    if surface_hash != bundle.client_policy_surface.client_policy_surface_hash_hex():
        raise ValueError("client policy bundle surface hash mismatch")
    expected_guard_hash = doc.get("local_guard_evaluation_hash")
    actual_guard_hash = bundle.local_guard_evaluation_hash_hex()
    if expected_guard_hash != actual_guard_hash:
        raise ValueError("client policy bundle guard evaluation hash mismatch")
    bundle_hash = _require_text(doc.get("client_policy_bundle_hash"), name="client_policy_bundle_hash")
    if bundle_hash != bundle.client_policy_bundle_hash_hex():
        raise ValueError("client policy bundle hash mismatch")
    return bundle


def load_autotrader_client_policy_bundle_file(
    path: str | Path,
    *,
    require_signature: bool = True,
) -> AutoTraderClientPolicyBundle:
    obj = json.loads(Path(path).expanduser().resolve().read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise ValueError("client policy bundle file must be a JSON object")
    bundle = autotrader_client_policy_bundle_from_dict(obj)
    if require_signature and not verify_autotrader_client_policy_bundle_signature(bundle):
        raise ValueError("client policy bundle signature verification failed")
    return bundle


__all__ = [
    "AUTOTRADER_CLIENT_POLICY_BUNDLE_SCHEMA",
    "DEFAULT_CLIENT_POLICY_BUNDLE_COMPILER_VERSION",
    "AutoTraderClientPolicyBundle",
    "autotrader_client_policy_bundle_from_dict",
    "build_autotrader_client_policy_bundle",
    "load_autotrader_client_policy_bundle_file",
    "sign_autotrader_client_policy_bundle",
    "verify_autotrader_client_policy_bundle_signature",
]
