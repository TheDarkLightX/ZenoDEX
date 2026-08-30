from __future__ import annotations

import hashlib
from dataclasses import dataclass
from typing import Any, Mapping

from ..integration.bls_intent_signing import bls_pubkey_hex_from_privkey
from ..state.canonical import canonical_json_bytes
from .strategy_ir import AUTOTRADER_TAU_POLICY_SPECS, StrategyIR, strategy_ir_from_dict

try:
    from py_ecc.bls import G2Basic

    _BLS_AVAILABLE = True
except ImportError:  # pragma: no cover - optional dependency
    G2Basic = None
    _BLS_AVAILABLE = False

try:
    from py_ecc.optimized_bls12_381 import curve_order as _BLS12_381_CURVE_ORDER
except ImportError:  # pragma: no cover - optional dependency
    _BLS12_381_CURVE_ORDER = None


POLICY_ARTIFACT_SCHEMA = "zenodex/strategy-policy-artifact/v1"
TAU_POLICY_BUNDLE_SCHEMA = "zenodex/strategy-policy-bundle/v1"
SOURCE_ARTIFACT_SCHEMA = "zenodex/strategy-source-artifact/v1"
DEFAULT_DECISION_MODEL_VERSION = "autotrader-binary-v1"
EVIDENCE_RANK = {"O0": 0, "O1": 1, "O2": 2, "O3": 3, "O4": 4, "O5": 5}


def _require_mapping(value: object, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be an object")
    return value


def _require_text(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a string")
    text = value.strip()
    if not text:
        raise ValueError(f"{name} must be non-empty")
    return text


def _require_bool(value: object, *, name: str) -> bool:
    if not isinstance(value, bool):
        raise TypeError(f"{name} must be a bool")
    return value


def _canonical_json_bytes(value: Mapping[str, Any]) -> bytes:
    return canonical_json_bytes(dict(value))


def _sha256_hex(value: bytes) -> str:
    return "0x" + hashlib.sha256(value).hexdigest()


def _parse_privkey_to_int(privkey: str | int | bytes | bytearray) -> int:
    if isinstance(privkey, int):
        sk = int(privkey)
    elif isinstance(privkey, (bytes, bytearray)):
        raw = bytes(privkey)
        if len(raw) != 32:
            raise ValueError("privkey bytes must be length 32")
        sk = int.from_bytes(raw, byteorder="big", signed=False)
    elif isinstance(privkey, str):
        text = privkey.strip()
        if not text:
            raise ValueError("privkey must be non-empty")
        if text.lower().startswith("0x"):
            text = text[2:]
        if len(text) == 64 and all(ch in "0123456789abcdefABCDEF" for ch in text):
            sk = int.from_bytes(bytes.fromhex(text), byteorder="big", signed=False)
        elif text.isdigit():
            sk = int(text, 10)
        else:
            raise ValueError("privkey must be 32-byte hex or a positive integer string")
    else:
        raise TypeError("privkey must be str|int|bytes")
    if sk <= 0:
        raise ValueError("privkey must be positive")
    if _BLS12_381_CURVE_ORDER is not None and sk >= int(_BLS12_381_CURVE_ORDER):
        raise ValueError("privkey out of range (must be < BLS12-381 curve order)")
    return sk


def _require_bls() -> None:
    if not _BLS_AVAILABLE:
        raise ValueError("py_ecc.bls is required for policy artifact signing")


@dataclass(frozen=True)
class StrategySourceArtifact:
    source_form: str
    strategy: StrategyIR
    source_text_hash: str | None = None

    def __post_init__(self) -> None:
        object.__setattr__(self, "source_form", _require_text(self.source_form, name="source_form"))
        if not isinstance(self.strategy, StrategyIR):
            raise TypeError("strategy must be a StrategyIR")
        if self.source_text_hash is not None:
            object.__setattr__(
                self,
                "source_text_hash",
                _require_text(self.source_text_hash, name="source_text_hash"),
            )

    def to_unsigned_dict(self) -> dict[str, Any]:
        return {
            "schema": SOURCE_ARTIFACT_SCHEMA,
            "source_form": self.source_form,
            "strategy": self.strategy.to_dict(),
            "strategy_hash": self.strategy.strategy_hash_hex(),
            "owner_pubkey": self.strategy.owner_pubkey,
            "source_text_hash": self.source_text_hash,
        }

    def to_dict(self) -> dict[str, Any]:
        payload = self.to_unsigned_dict()
        payload["source_artifact_hash"] = self.source_artifact_hash_hex()
        return payload

    def to_json_bytes(self) -> bytes:
        return _canonical_json_bytes(self.to_unsigned_dict())

    def source_artifact_hash_hex(self) -> str:
        return _sha256_hex(self.to_json_bytes())


@dataclass(frozen=True)
class TauPolicyBundle:
    strategy_hash: str
    owner_pubkey: str
    source_artifact_hash: str
    required_spec_ids: tuple[str, ...]
    compile_contract_tau_receipt: Mapping[str, Any]
    compilation_witness_tau_receipt: Mapping[str, Any]
    decision_model_version: str = DEFAULT_DECISION_MODEL_VERSION
    evidence_class: str = "O3"

    def __post_init__(self) -> None:
        object.__setattr__(self, "strategy_hash", _require_text(self.strategy_hash, name="strategy_hash"))
        object.__setattr__(self, "owner_pubkey", _require_text(self.owner_pubkey, name="owner_pubkey"))
        object.__setattr__(
            self,
            "source_artifact_hash",
            _require_text(self.source_artifact_hash, name="source_artifact_hash"),
        )
        object.__setattr__(
            self,
            "decision_model_version",
            _require_text(self.decision_model_version, name="decision_model_version"),
        )
        evidence_class = _require_text(self.evidence_class, name="evidence_class")
        if evidence_class not in EVIDENCE_RANK:
            raise ValueError("evidence_class must be one of O0..O5")
        object.__setattr__(self, "evidence_class", evidence_class)
        normalized_specs: list[str] = []
        seen: set[str] = set()
        for raw in self.required_spec_ids:
            spec = _require_text(raw, name="required_spec_ids")
            if spec in seen:
                continue
            seen.add(spec)
            normalized_specs.append(spec)
        if tuple(normalized_specs) != AUTOTRADER_TAU_POLICY_SPECS:
            raise ValueError("required_spec_ids must equal the canonical autotrader Tau bundle")
        object.__setattr__(self, "required_spec_ids", tuple(normalized_specs))
        receipt = _require_mapping(self.compile_contract_tau_receipt, name="compile_contract_tau_receipt")
        object.__setattr__(self, "compile_contract_tau_receipt", dict(receipt))
        witness_receipt = _require_mapping(
            self.compilation_witness_tau_receipt,
            name="compilation_witness_tau_receipt",
        )
        object.__setattr__(self, "compilation_witness_tau_receipt", dict(witness_receipt))

    def to_unsigned_dict(self) -> dict[str, Any]:
        return {
            "schema": TAU_POLICY_BUNDLE_SCHEMA,
            "strategy_hash": self.strategy_hash,
            "owner_pubkey": self.owner_pubkey,
            "source_artifact_hash": self.source_artifact_hash,
            "required_spec_ids": list(self.required_spec_ids),
            "compile_contract_tau_receipt": dict(self.compile_contract_tau_receipt),
            "compilation_witness_tau_receipt": dict(self.compilation_witness_tau_receipt),
            "decision_model_version": self.decision_model_version,
            "evidence_class": self.evidence_class,
        }

    def to_dict(self) -> dict[str, Any]:
        payload = self.to_unsigned_dict()
        payload["tau_policy_bundle_hash"] = self.tau_policy_bundle_hash_hex()
        return payload

    def to_json_bytes(self) -> bytes:
        return _canonical_json_bytes(self.to_unsigned_dict())

    def tau_policy_bundle_hash_hex(self) -> str:
        return _sha256_hex(self.to_json_bytes())


@dataclass(frozen=True)
class StrategyPolicyArtifact:
    strategy: StrategyIR
    source_artifact_hash: str
    tau_policy_bundle_hash: str
    decision_model_version: str = DEFAULT_DECISION_MODEL_VERSION
    signature: str | None = None

    def __post_init__(self) -> None:
        if not isinstance(self.strategy, StrategyIR):
            raise TypeError("strategy must be a StrategyIR")
        object.__setattr__(
            self,
            "source_artifact_hash",
            _require_text(self.source_artifact_hash, name="source_artifact_hash"),
        )
        object.__setattr__(
            self,
            "tau_policy_bundle_hash",
            _require_text(self.tau_policy_bundle_hash, name="tau_policy_bundle_hash"),
        )
        object.__setattr__(
            self,
            "decision_model_version",
            _require_text(self.decision_model_version, name="decision_model_version"),
        )
        if self.signature is not None:
            object.__setattr__(self, "signature", _require_text(self.signature, name="signature"))

    def to_unsigned_dict(self) -> dict[str, Any]:
        return {
            "schema": POLICY_ARTIFACT_SCHEMA,
            "strategy": self.strategy.to_dict(),
            "strategy_hash": self.strategy.strategy_hash_hex(),
            "owner_pubkey": self.strategy.owner_pubkey,
            "source_artifact_hash": self.source_artifact_hash,
            "tau_policy_bundle_hash": self.tau_policy_bundle_hash,
            "decision_model_version": self.decision_model_version,
        }

    def to_dict(self) -> dict[str, Any]:
        payload = self.to_unsigned_dict()
        payload["policy_artifact_hash"] = self.policy_artifact_hash_hex()
        payload["signature"] = self.signature
        return payload

    def to_json_bytes(self) -> bytes:
        return _canonical_json_bytes(self.to_unsigned_dict())

    def policy_artifact_hash_hex(self) -> str:
        return _sha256_hex(self.to_json_bytes())


def build_tau_policy_bundle(
    *,
    strategy: StrategyIR,
    compile_contract_tau_receipt: Mapping[str, Any],
    source_artifact: StrategySourceArtifact | None = None,
    compilation_witness_tau_receipt: Mapping[str, Any] | None = None,
    decision_model_version: str = DEFAULT_DECISION_MODEL_VERSION,
) -> TauPolicyBundle:
    if not isinstance(strategy, StrategyIR):
        raise TypeError("strategy must be a StrategyIR")
    effective_source_artifact = source_artifact
    if effective_source_artifact is None:
        effective_source_artifact = build_strategy_source_artifact(
            strategy=strategy,
            source_form="compiled_strategy_ir",
        )
    if not isinstance(effective_source_artifact, StrategySourceArtifact):
        raise TypeError("source_artifact must be a StrategySourceArtifact")
    if effective_source_artifact.strategy.strategy_hash_hex() != strategy.strategy_hash_hex():
        raise ValueError("source artifact strategy hash mismatch")
    effective_compilation_witness = compilation_witness_tau_receipt
    if effective_compilation_witness is None:
        from .tau_policy_adapter import build_compilation_witness_tau_policy_receipt

        effective_compilation_witness = build_compilation_witness_tau_policy_receipt(
            strategy=strategy,
            source_artifact=effective_source_artifact,
            compile_contract_tau_receipt=compile_contract_tau_receipt,
        ).to_dict()
    return TauPolicyBundle(
        strategy_hash=strategy.strategy_hash_hex(),
        owner_pubkey=strategy.owner_pubkey,
        source_artifact_hash=effective_source_artifact.source_artifact_hash_hex(),
        required_spec_ids=AUTOTRADER_TAU_POLICY_SPECS,
        compile_contract_tau_receipt=compile_contract_tau_receipt,
        compilation_witness_tau_receipt=effective_compilation_witness,
        decision_model_version=decision_model_version,
    )


def build_strategy_policy_artifact(
    *,
    strategy: StrategyIR,
    tau_policy_bundle: TauPolicyBundle,
    source_artifact: StrategySourceArtifact | None = None,
    decision_model_version: str = DEFAULT_DECISION_MODEL_VERSION,
) -> StrategyPolicyArtifact:
    if not isinstance(tau_policy_bundle, TauPolicyBundle):
        raise TypeError("tau_policy_bundle must be a TauPolicyBundle")
    if tau_policy_bundle.strategy_hash != strategy.strategy_hash_hex():
        raise ValueError("tau policy bundle strategy hash mismatch")
    if tau_policy_bundle.owner_pubkey != strategy.owner_pubkey:
        raise ValueError("tau policy bundle owner mismatch")
    if tau_policy_bundle.decision_model_version != decision_model_version:
        raise ValueError("decision model version mismatch")
    if source_artifact is not None:
        if not isinstance(source_artifact, StrategySourceArtifact):
            raise TypeError("source_artifact must be a StrategySourceArtifact")
        if source_artifact.source_artifact_hash_hex() != tau_policy_bundle.source_artifact_hash:
            raise ValueError("source artifact hash mismatch")
    return StrategyPolicyArtifact(
        strategy=strategy,
        source_artifact_hash=tau_policy_bundle.source_artifact_hash,
        tau_policy_bundle_hash=tau_policy_bundle.tau_policy_bundle_hash_hex(),
        decision_model_version=decision_model_version,
        signature=None,
    )


def sign_strategy_policy_artifact(
    artifact: StrategyPolicyArtifact,
    *,
    privkey: str | int | bytes | bytearray,
) -> StrategyPolicyArtifact:
    if not isinstance(artifact, StrategyPolicyArtifact):
        raise TypeError("artifact must be a StrategyPolicyArtifact")
    _require_bls()
    sk_int = _parse_privkey_to_int(privkey)
    pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    if pubkey != artifact.strategy.owner_pubkey:
        raise ValueError("signer pubkey does not match artifact owner")
    msg_hash = hashlib.sha256(artifact.to_json_bytes()).digest()
    if G2Basic is None:  # pragma: no cover - mirrors _require_bls()
        raise RuntimeError("py_ecc.bls.G2Basic unavailable after BLS availability check")
    signature = "0x" + G2Basic.Sign(sk_int, msg_hash).hex()
    return StrategyPolicyArtifact(
        strategy=artifact.strategy,
        source_artifact_hash=artifact.source_artifact_hash,
        tau_policy_bundle_hash=artifact.tau_policy_bundle_hash,
        decision_model_version=artifact.decision_model_version,
        signature=signature,
    )


def verify_strategy_policy_artifact_signature(artifact: StrategyPolicyArtifact) -> bool:
    if artifact.signature is None:
        return False
    if not _BLS_AVAILABLE:
        return False
    try:
        if G2Basic is None:
            return False
        pubkey_bytes = bytes.fromhex(artifact.strategy.owner_pubkey.removeprefix("0x"))
        sig_bytes = bytes.fromhex(artifact.signature.removeprefix("0x"))
        msg_hash = hashlib.sha256(artifact.to_json_bytes()).digest()
    except ValueError:
        return False
    return bool(G2Basic.Verify(pubkey_bytes, msg_hash, sig_bytes))


def tau_policy_bundle_from_dict(data: Mapping[str, Any]) -> TauPolicyBundle:
    doc = _require_mapping(data, name="tau policy bundle")
    if doc.get("schema") != TAU_POLICY_BUNDLE_SCHEMA:
        raise ValueError(f"unsupported tau policy bundle schema: {doc.get('schema')!r}")
    bundle = TauPolicyBundle(
        strategy_hash=_require_text(doc.get("strategy_hash"), name="strategy_hash"),
        owner_pubkey=_require_text(doc.get("owner_pubkey"), name="owner_pubkey"),
        source_artifact_hash=_require_text(doc.get("source_artifact_hash"), name="source_artifact_hash"),
        required_spec_ids=tuple(doc.get("required_spec_ids", ()) or ()),
        compile_contract_tau_receipt=doc.get("compile_contract_tau_receipt", {}),
        compilation_witness_tau_receipt=doc.get("compilation_witness_tau_receipt", {}),
        decision_model_version=doc.get("decision_model_version", DEFAULT_DECISION_MODEL_VERSION),
        evidence_class=doc.get("evidence_class", "O3"),
    )
    bundle_hash = _require_text(doc.get("tau_policy_bundle_hash"), name="tau_policy_bundle_hash")
    if bundle_hash != bundle.tau_policy_bundle_hash_hex():
        raise ValueError("tau policy bundle hash mismatch")
    return bundle


def strategy_policy_artifact_from_dict(data: Mapping[str, Any]) -> StrategyPolicyArtifact:
    doc = _require_mapping(data, name="policy artifact")
    if doc.get("schema") != POLICY_ARTIFACT_SCHEMA:
        raise ValueError(f"unsupported policy artifact schema: {doc.get('schema')!r}")
    strategy_raw = _require_mapping(doc.get("strategy"), name="policy artifact.strategy")
    strategy = strategy_ir_from_dict(strategy_raw)
    artifact = StrategyPolicyArtifact(
        strategy=strategy,
        source_artifact_hash=_require_text(doc.get("source_artifact_hash"), name="source_artifact_hash"),
        tau_policy_bundle_hash=_require_text(
            doc.get("tau_policy_bundle_hash"), name="tau_policy_bundle_hash"
        ),
        decision_model_version=doc.get("decision_model_version", DEFAULT_DECISION_MODEL_VERSION),
        signature=doc.get("signature"),
    )
    strategy_hash = _require_text(doc.get("strategy_hash"), name="strategy_hash")
    if strategy_hash != strategy.strategy_hash_hex():
        raise ValueError("policy artifact strategy_hash mismatch")
    owner_pubkey = _require_text(doc.get("owner_pubkey"), name="owner_pubkey")
    if owner_pubkey != strategy.owner_pubkey:
        raise ValueError("policy artifact owner_pubkey mismatch")
    artifact_hash = _require_text(doc.get("policy_artifact_hash"), name="policy_artifact_hash")
    if artifact_hash != artifact.policy_artifact_hash_hex():
        raise ValueError("policy artifact hash mismatch")
    return artifact


def build_strategy_source_artifact(
    *,
    strategy: StrategyIR,
    source_form: str,
    source_text: str | None = None,
) -> StrategySourceArtifact:
    if not isinstance(strategy, StrategyIR):
        raise TypeError("strategy must be a StrategyIR")
    source_text_hash = None
    if source_text is not None:
        if not isinstance(source_text, str):
            raise TypeError("source_text must be a string")
        source_text_hash = _sha256_hex(source_text.encode("utf-8"))
    return StrategySourceArtifact(
        source_form=source_form,
        strategy=strategy,
        source_text_hash=source_text_hash,
    )


def strategy_source_artifact_from_dict(data: Mapping[str, Any]) -> StrategySourceArtifact:
    doc = _require_mapping(data, name="source artifact")
    if doc.get("schema") != SOURCE_ARTIFACT_SCHEMA:
        raise ValueError(f"unsupported source artifact schema: {doc.get('schema')!r}")
    strategy_raw = _require_mapping(doc.get("strategy"), name="source artifact.strategy")
    strategy = strategy_ir_from_dict(strategy_raw)
    artifact = StrategySourceArtifact(
        source_form=_require_text(doc.get("source_form"), name="source_form"),
        strategy=strategy,
        source_text_hash=doc.get("source_text_hash"),
    )
    strategy_hash = _require_text(doc.get("strategy_hash"), name="strategy_hash")
    if strategy_hash != strategy.strategy_hash_hex():
        raise ValueError("source artifact strategy_hash mismatch")
    owner_pubkey = _require_text(doc.get("owner_pubkey"), name="owner_pubkey")
    if owner_pubkey != strategy.owner_pubkey:
        raise ValueError("source artifact owner_pubkey mismatch")
    artifact_hash = _require_text(doc.get("source_artifact_hash"), name="source_artifact_hash")
    if artifact_hash != artifact.source_artifact_hash_hex():
        raise ValueError("source artifact hash mismatch")
    return artifact
