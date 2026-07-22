"""
DEX execution adapter for Tau Net-style transactions.

This is an imperative-shell wrapper around the functional core:
- Parses ops["2"] intents and ops["3"] settlement (+ optional proof payload).
- Verifies per-intent signatures (optional, but recommended for batch settlement).
- Validates and applies the settlement against the current `DexState`.
"""

from __future__ import annotations

import hashlib
import re
from collections.abc import Mapping, Sequence
from dataclasses import dataclass, replace
from typing import Any, Dict, List, Optional, Tuple, TypeGuard

from ..core.batch_clearing import apply_settlement_pure, compute_settlement
from ..core.dex import DexConfig, DexState, reject_settlement_public_boundary_error
from ..core.dex_intent_auth_message import build_dex_intent_signing_dict_v1
from ..core.fees import split_fee_with_dust_carry
from ..core.intent_normal_form import IntentNormalFormError, require_normal_form
from ..core.quote_receipts import verify_route_quote_receipt
from ..core.settlement import Settlement
from ..core.settlement_normal_form import normalize_settlement_op_for_commitment
from ..core.uniform_batch_clearing import (
    UNIFORM_BATCH_POLICY_V2_ID,
    UNIFORM_BATCH_POLICY_V3_ID,
    UniformBatchCertificateV1,
    build_uniform_batch_settlement_v1,
)
from ..core.uniform_batch_optimality import (
    verify_uniform_batch_bound_optimality_certificate_v1,
    verify_uniform_batch_v2_bounded_grid_optimality_certificate_v1,
    verify_uniform_batch_v3_exact_out_grid_optimality_certificate_v1,
)
from ..state.canonical import (
    CANONICAL_ENCODING_VERSION,
    bounded_json_utf8_size,
    canonical_json_bytes,
    domain_sep_bytes,
    sha256_hex,
)
from ..state.immutable_collections import deep_thaw_json
from ..state.intents import Intent, IntentKind
from ..state.nonces import NonceTable, validate_and_apply_intent_nonce_batch
from ..state.state_root import compute_state_root
from ..state.support_root import compute_support_state_root_for_batch
from .lp_position_age_gate import (
    LPDurationRiskPolicy,
    apply_lp_mint_timestamps_after_settlement,
    validate_lp_settlement_age_gate,
)
from .operations import (
    SettlementEnvelope,
    SignedIntentEnvelope,
    canonicalize_authenticated_intent_for_execution,
    create_settlement_operation,
    parse_settlement_envelope,
    parse_signed_intents,
)
from .proof_mining_context import ProofMiningContext, build_proof_mining_context
from .proof_verifier import (
    MisconfiguredProofVerifier,
    ProofVerifier,
    ProofVerifierConfig,
    make_proof_verifier,
)
from .settlement_end_to_end_certificate_packet import SettlementEndToEndCertificateInputs
from .settlement_strong_certificate import (
    SettlementProofFlags,
    derive_verified_replay_bound_certificate_flags,
)
from .tau_gate import TauGateConfig
from .validation import validate_operations
from .zeno_oracle_routing_authorization import check_protected_swap_oracle_authorization
from .zeno_oracle_settlement_authorization import check_critical_settlement_oracle_authorization

G2Basic: Any | None

try:
    from py_ecc.bls import G2Basic as _PyEccG2Basic

    G2Basic = _PyEccG2Basic
    _BLS_AVAILABLE = True
except ImportError:  # pragma: no cover - optional dependency
    G2Basic = None
    _BLS_AVAILABLE = False

_HEX_CHARS_RE = re.compile(r"^[0-9a-fA-F]+$")

_FAULT_STAGES = (
    "after_raw_validation",
    "after_intent_parse",
    "after_settlement_parse",
    "after_preconditions",
    "after_signature_verification",
    "after_nonce_validation",
    "after_settlement_compute",
    "after_settlement_validation",
    "after_proof_verification",
    "after_apply_pure",
)


def _format_error_details(**kwargs: Any) -> str:
    parts: list[str] = []
    for key, value in kwargs.items():
        if value is None:
            continue
        parts.append(f"{key}={value!r}")
    return ", ".join(parts)


def _quote_receipt_error(reason: str, **kwargs: Any) -> str:
    details = _format_error_details(**kwargs)
    if not details:
        return reason
    return f"{reason}: {details}"


def _quote_receipt_intent_context(intent: Intent) -> dict[str, Any]:
    return {
        "intent_id": intent.intent_id,
        "quote_hash": intent.get_field("quote_receipt_hash"),
        "leg_index": intent.get_field("quote_receipt_leg_index"),
        "pool_id": intent.get_field("pool_id"),
        "asset_in": intent.get_field("asset_in"),
        "asset_out": intent.get_field("asset_out"),
    }


def _is_quote_receipt_array(value: object) -> TypeGuard[Sequence[Any]]:
    return isinstance(value, Sequence) and not isinstance(value, (str, bytes, bytearray))


def _validate_and_apply_nonce_batch(
    *, nonces: NonceTable, intents: list[Intent]
) -> tuple[bool, str | None, NonceTable | None]:
    return validate_and_apply_intent_nonce_batch(
        nonces=nonces,
        intents=intents,
        require_all_nonces=True,
    )


@dataclass(frozen=True)
class DexFaultInjectionConfig:
    """
    Test-only fault injection for fail-closed anomaly coverage.

    `fail_at_stage` must be one of the stable stage ids in `_FAULT_STAGES`.
    """

    fail_at_stage: Optional[str] = None

    def __post_init__(self) -> None:
        stage = self.fail_at_stage
        if stage is None:
            return
        if stage not in _FAULT_STAGES:
            raise ValueError(f"unknown fault injection stage: {stage}")


@dataclass(frozen=True)
class DexEngineConfig:
    # Settlement handling:
    # - If `allow_missing_settlement` is True and ops["3"] is absent, we compute it locally.
    allow_missing_settlement: bool = False
    # If True and ops["3"] is present, it must match the locally computed settlement (fail-closed).
    #
    # This prevents malicious "conservation-only" settlements from stealing funds when the settlement
    # is treated as untrusted input.
    require_settlement_match: bool = True
    # Production swap ordering posture for deterministic, high-A/B batch clearing.
    swap_ordering: str = "greedy_ab_refined"

    # Intent signature policy:
    # - If `require_intent_signatures` is True, each intent must carry a per-intent signature,
    #   unless `allow_unsigned_intents_if_tx_sender_matches` is True and the outer tx sender
    #   matches the intent sender (user-submitted intents).
    # - If `require_intent_signatures` is False, per-intent signatures are ignored and all intents
    #   must be submitted by their declared sender at the outer tx layer (tx_sender_pubkey).
    require_intent_signatures: bool = True
    allow_unsigned_intents_if_tx_sender_matches: bool = True
    # Tau adapter policy: authenticate the original payload, then project BLS
    # identities into the committed-state spelling used by Tau snapshots.
    canonicalize_authenticated_bls_principals: bool = False
    # Strict profiles require quote receipts as an inner canonical JSON string.
    # A pre-decoded object cannot prove which byte spelling crossed the boundary.
    require_canonical_quote_receipt_transport: bool = False

    # DoS limits (applied before expensive hashing/signature verification):
    max_intents: int = 256
    max_intent_bytes: int = 32_000
    max_total_intent_bytes: int = 256_000
    max_intent_entry_bytes: int = 40_000
    max_total_intent_entry_bytes: int = 300_000

    # Settlement / proof DoS limits:
    max_settlement_op_bytes: int = 512_000
    max_settlement_bytes: int = 512_000
    max_settlement_fills: int = 512

    # Proof policy:
    proof_config: ProofVerifierConfig = ProofVerifierConfig()
    require_proof_when_present: bool = (
        False  # if True: reject txs with intents unless proof is present
    )

    # Signature replay protection:
    # Bind per-intent signatures to a specific chain/network deployment.
    chain_id: str = "tau-net-alpha"

    # External tool policy:
    # - Proof verification and Tau gating may run external executables and rely on wall-clock timeouts.
    # - Default is fail-closed (disabled) to avoid accidental nondeterminism in consensus-like contexts.
    allow_external_tools: bool = False
    # If True, structurally disallow external tools even if `allow_external_tools` is set.
    consensus_mode: bool = True

    # Optional Tau gate (swap transition checks against Tau specs).
    tau_gate_config: Optional[TauGateConfig] = None
    # Optional replay-bound settlement certificate gate. When enabled, the
    # engine derives the compact settlement summary from the computed settlement
    # order plus supplied price history and fails closed if the certificate
    # bundle does not pass.
    require_settlement_certificate: bool = False
    settlement_certificate_proof_flags: Optional[SettlementProofFlags] = None
    settlement_certificate_price_history: Optional[Tuple[int, int, int]] = None
    require_settlement_end_to_end_certificate: bool = False
    settlement_end_to_end_certificate_inputs: Optional[SettlementEndToEndCertificateInputs] = None
    # Optional production bridge: require quote-receipt-bound swaps to carry a
    # typed ZenoOracle authorization binding the actual protected quote value.
    require_oracle_authorization_for_protected_swaps: bool = False
    # Optional production bridge: require critical batch settlements to carry a
    # typed ZenoOracle authorization binding the exact settlement, pre-state,
    # and price_curr value consumed by the settlement certificate lane.
    require_oracle_authorization_for_critical_settlements: bool = False
    allow_uniform_batch_certificate: bool = False
    # Optional strict UPBA production posture. When enabled, supported
    # single-pool swap families must use UPBA, and UPBA settlements must carry
    # bound audited-set optimality evidence.
    require_uniform_batch_certificate_for_supported_swaps: bool = False
    require_uniform_batch_optimality_certificate: bool = False
    require_uniform_batch_v2_bounded_grid_optimality: bool = False
    require_uniform_batch_v3_exact_out_grid_optimality: bool = False

    # Optional LP duration-risk gate. When positive, REMOVE_LIQUIDITY burns must
    # be at least this old according to runtime-tracked LP mint timestamps.
    min_lp_position_age_seconds: int = 0
    # Optional accepted-lifecycle churn policy. When set, the effective LP age
    # floor grows with committed LP churn metadata and decays over quiet periods.
    lp_duration_risk_policy: Optional[LPDurationRiskPolicy] = None

    # Optional fee split params (applied after any successful settlement).
    dex_config: DexConfig = DexConfig()

    # Test-only anomaly hook. Must not be enabled in production/testnet configs.
    enable_test_fault_injection: bool = False
    fault_injection: Optional[DexFaultInjectionConfig] = None

    def __post_init__(self) -> None:
        if (
            self.require_settlement_certificate
            and self.settlement_end_to_end_certificate_inputs is None
        ):
            raise ValueError(
                "require_settlement_certificate=True requires settlement_end_to_end_certificate_inputs"
            )
        if (
            self.require_settlement_end_to_end_certificate
            and self.settlement_end_to_end_certificate_inputs is None
        ):
            raise ValueError(
                "require_settlement_end_to_end_certificate=True requires settlement_end_to_end_certificate_inputs"
            )

        if self.settlement_certificate_proof_flags is not None and not isinstance(
            self.settlement_certificate_proof_flags, SettlementProofFlags
        ):
            raise TypeError(
                "settlement_certificate_proof_flags must be a SettlementProofFlags instance"
            )
        if self.settlement_end_to_end_certificate_inputs is not None and not isinstance(
            self.settlement_end_to_end_certificate_inputs, SettlementEndToEndCertificateInputs
        ):
            raise TypeError(
                "settlement_end_to_end_certificate_inputs must be a SettlementEndToEndCertificateInputs instance"
            )

        if self.settlement_certificate_price_history is not None:
            price_history = self.settlement_certificate_price_history
            if not isinstance(price_history, tuple) or len(price_history) != 3:
                raise ValueError(
                    "settlement_certificate_price_history must be a 3-tuple: (price_pp, price_prev, price_curr)"
                )
            for idx, value in enumerate(price_history):
                if not isinstance(value, int) or isinstance(value, bool):
                    raise ValueError(f"settlement_certificate_price_history[{idx}] must be an int")

        if not isinstance(self.min_lp_position_age_seconds, int) or isinstance(
            self.min_lp_position_age_seconds, bool
        ):
            raise TypeError("min_lp_position_age_seconds must be an int")
        if self.min_lp_position_age_seconds < 0:
            raise ValueError("min_lp_position_age_seconds must be non-negative")
        if self.lp_duration_risk_policy is not None and not isinstance(
            self.lp_duration_risk_policy, LPDurationRiskPolicy
        ):
            raise TypeError("lp_duration_risk_policy must be an LPDurationRiskPolicy")
        if type(self.require_canonical_quote_receipt_transport) is not bool:
            raise TypeError("require_canonical_quote_receipt_transport must be a bool")
        if not isinstance(self.allow_uniform_batch_certificate, bool):
            raise TypeError("allow_uniform_batch_certificate must be a bool")
        if not isinstance(self.require_uniform_batch_certificate_for_supported_swaps, bool):
            raise TypeError("require_uniform_batch_certificate_for_supported_swaps must be a bool")
        if not isinstance(self.require_uniform_batch_optimality_certificate, bool):
            raise TypeError("require_uniform_batch_optimality_certificate must be a bool")
        if not isinstance(self.require_uniform_batch_v2_bounded_grid_optimality, bool):
            raise TypeError("require_uniform_batch_v2_bounded_grid_optimality must be a bool")
        if not isinstance(self.require_uniform_batch_v3_exact_out_grid_optimality, bool):
            raise TypeError("require_uniform_batch_v3_exact_out_grid_optimality must be a bool")
        if (
            self.require_uniform_batch_certificate_for_supported_swaps
            or self.require_uniform_batch_optimality_certificate
            or self.require_uniform_batch_v2_bounded_grid_optimality
            or self.require_uniform_batch_v3_exact_out_grid_optimality
        ) and not self.allow_uniform_batch_certificate:
            raise ValueError(
                "strict UPBA requirements require allow_uniform_batch_certificate=True"
            )


def make_strict_upba_engine_config(**overrides: Any) -> DexEngineConfig:
    """Build the strict UPBA profile for supported single-pool swap families."""

    params: Dict[str, Any] = dict(overrides)
    dex_config = params.get("dex_config")
    if isinstance(dex_config, DexConfig):
        params["dex_config"] = replace(
            dex_config,
            settlement_validation="strong_proof_carrying",
            allow_snapshot_bound_quote_bindings=False,
        )
    params.update(
        {
            "allow_missing_settlement": False,
            "require_settlement_match": True,
            "require_intent_signatures": True,
            "require_canonical_quote_receipt_transport": True,
            "allow_external_tools": False,
            "consensus_mode": True,
            "allow_uniform_batch_certificate": True,
            "require_uniform_batch_certificate_for_supported_swaps": True,
            "require_uniform_batch_optimality_certificate": True,
            "require_uniform_batch_v2_bounded_grid_optimality": True,
            "require_uniform_batch_v3_exact_out_grid_optimality": True,
        }
    )
    return DexEngineConfig(**params)


def strict_upba_engine_config_facts_v0(config: DexEngineConfig) -> dict[str, Any]:
    """Expose the strict UPBA profile facts used by release/audit tooling."""

    return {
        "allow_missing_settlement": config.allow_missing_settlement,
        "require_settlement_match": config.require_settlement_match,
        "require_intent_signatures": config.require_intent_signatures,
        "require_canonical_quote_receipt_transport": (
            config.require_canonical_quote_receipt_transport
        ),
        "allow_external_tools": config.allow_external_tools,
        "consensus_mode": config.consensus_mode,
        "settlement_validation": config.dex_config.settlement_validation,
        "allow_snapshot_bound_quote_bindings": config.dex_config.allow_snapshot_bound_quote_bindings,
        "allow_uniform_batch_certificate": config.allow_uniform_batch_certificate,
        "require_uniform_batch_certificate_for_supported_swaps": (
            config.require_uniform_batch_certificate_for_supported_swaps
        ),
        "require_uniform_batch_optimality_certificate": config.require_uniform_batch_optimality_certificate,
        "require_uniform_batch_v2_bounded_grid_optimality": (
            config.require_uniform_batch_v2_bounded_grid_optimality
        ),
        "require_uniform_batch_v3_exact_out_grid_optimality": (
            config.require_uniform_batch_v3_exact_out_grid_optimality
        ),
    }


@dataclass(frozen=True)
class DexTxResult:
    ok: bool
    state: Optional[DexState] = None
    settlement: Optional[Settlement] = None
    error: Optional[str] = None
    proof_mining_context: Optional[ProofMiningContext] = None


class _InjectedFault(RuntimeError):
    def __init__(self, stage: str) -> None:
        super().__init__(f"fault injected: {stage}")
        self.stage = stage


def _hex_to_bytes_allow_0x(
    hex_str: str, *, name: str, expected_nbytes: Optional[int] = None
) -> bytes:
    if not isinstance(hex_str, str):
        raise TypeError(f"{name} must be a string")
    s = hex_str[2:] if hex_str.lower().startswith("0x") else hex_str
    if not s:
        raise ValueError(f"{name} must be non-empty hex")

    if expected_nbytes is not None:
        if (
            not isinstance(expected_nbytes, int)
            or isinstance(expected_nbytes, bool)
            or expected_nbytes <= 0
        ):
            raise ValueError("expected_nbytes must be a positive int")
        expected_hex_len = 2 * expected_nbytes
        if len(s) != expected_hex_len:
            raise ValueError(
                f"{name} must be {expected_nbytes} bytes (hex length {expected_hex_len})"
            )

    if len(s) % 2 != 0:
        raise ValueError(f"{name} must have an even number of hex chars")
    if not _HEX_CHARS_RE.fullmatch(s):
        raise ValueError(f"{name} must be valid hex")
    try:
        out = bytes.fromhex(s)
    except ValueError as exc:
        raise ValueError(f"{name} must be valid hex") from exc
    if expected_nbytes is not None and len(out) != expected_nbytes:
        raise ValueError(f"{name} must decode to exactly {expected_nbytes} bytes")
    return out


def _pubkey_bytes48_or_none(value: Optional[str], *, name: str) -> Optional[bytes]:
    if value is None:
        return None
    try:
        return _hex_to_bytes_allow_0x(value, name=name, expected_nbytes=48)
    except (TypeError, ValueError):
        return None


def _intent_signing_dict(intent: Intent) -> Dict[str, Any]:
    return build_dex_intent_signing_dict_v1(intent)


def _settlement_commitment_dict(settlement: Settlement) -> Dict[str, Any]:
    """
    Canonical, deterministic settlement dict for batch commitments.

    This intentionally excludes metadata fields that do not affect state transition:
    - settlement.batch_ref
    - settlement.events
    - fill.reason

    It also omits any per-fill optional fields that are `None`, so proofs do not
    depend on whether an encoder used explicit `null` vs omitted keys.
    """
    op = create_settlement_operation(settlement).get("3")
    if not isinstance(op, dict):
        raise TypeError("internal error: settlement operation must be an object")

    out: Dict[str, Any] = {k: v for k, v in op.items() if k not in ("batch_ref", "events")}

    fills = out.get("fills")
    if not isinstance(fills, list):
        raise TypeError("internal error: settlement.fills must be a list")
    compact_fills: List[Dict[str, Any]] = []
    for fill in fills:
        if not isinstance(fill, dict):
            raise TypeError("internal error: settlement fill must be an object")
        compact_fills.append({k: v for k, v in fill.items() if v is not None and k != "reason"})
    out["fills"] = compact_fills

    return out


def _settlement_rewrite_normal_form_dict(settlement: Settlement) -> Dict[str, Any]:
    """
    Algebraic-rewrite canonicalization for semantic settlement equivalence.

    This quotient form is used for settlement equality checks so list ordering,
    duplicate deltas, and omitted-vs-null optional fields cannot create false
    mismatches for semantically equivalent transitions.
    """
    op = create_settlement_operation(settlement).get("3")
    if not isinstance(op, dict):
        raise TypeError("internal error: settlement operation must be an object")
    return normalize_settlement_op_for_commitment(op)


def _verify_intent_signature_bytes(
    *, sender_pubkey_hex: str, signature_hex: str, signing_payload_bytes: bytes, chain_id: str
) -> Tuple[bool, Optional[str]]:
    if not _BLS_AVAILABLE:
        return False, "py_ecc (BLS) not available"
    if G2Basic is None:
        return False, "py_ecc.bls.G2Basic unavailable"
    try:
        pubkey_bytes = _hex_to_bytes_allow_0x(
            sender_pubkey_hex, name="sender_pubkey", expected_nbytes=48
        )
        sig_bytes = _hex_to_bytes_allow_0x(signature_hex, name="signature", expected_nbytes=96)

        msg = domain_sep_bytes(f"dex_intent_sig:{chain_id}", version=1) + signing_payload_bytes
        msg_hash = hashlib.sha256(msg).digest()
        ok = bool(G2Basic.Verify(pubkey_bytes, msg_hash, sig_bytes))
        if not ok:
            return False, "invalid intent signature"
        return True, None
    except Exception as exc:
        return False, f"intent signature verification error: {exc}"


def _verify_all_intent_signatures(
    intents: List[SignedIntentEnvelope],
    *,
    require: bool,
    tx_sender_pubkey: Optional[str],
    allow_tx_sender_bypass: bool,
    signing_payloads: List[bytes],
    chain_id: str,
) -> Tuple[bool, Optional[str]]:
    if len(intents) != len(signing_payloads):
        return False, "internal error: signing payload mismatch"
    if not intents:
        return True, None

    if not require:
        # No per-intent signatures: require that intents are submitted by their
        # declared sender at the outer tx layer (tx_sender_pubkey).
        #
        # This mode is intentionally restrictive: it prevents third-party batch
        # settlement unless per-intent signatures are enabled.
        if not allow_tx_sender_bypass:
            return False, "unsigned intents disabled (tx sender binding required)"
        sender_b = _pubkey_bytes48_or_none(tx_sender_pubkey, name="tx_sender_pubkey")
        if sender_b is None:
            return False, "tx_sender_pubkey must be a 48-byte hex pubkey for unsigned intents"
        for env in intents:
            intent_b = _pubkey_bytes48_or_none(
                env.intent.sender_pubkey, name="intent.sender_pubkey"
            )
            if intent_b is None or intent_b != sender_b:
                return False, f"intent sender mismatch: {env.intent.intent_id}"
        return True, None

    for env, signing_payload in zip(intents, signing_payloads, strict=True):
        if env.signature is None:
            if allow_tx_sender_bypass:
                sender_b = _pubkey_bytes48_or_none(tx_sender_pubkey, name="tx_sender_pubkey")
                intent_b = _pubkey_bytes48_or_none(
                    env.intent.sender_pubkey, name="intent.sender_pubkey"
                )
                if sender_b is not None and intent_b is not None and intent_b == sender_b:
                    continue
            return False, f"missing intent signature: {env.intent.intent_id}"
        if not _BLS_AVAILABLE:
            return False, "py_ecc (BLS) not available"
        ok, err = _verify_intent_signature_bytes(
            sender_pubkey_hex=env.intent.sender_pubkey,
            signature_hex=env.signature,
            signing_payload_bytes=signing_payload,
            chain_id=chain_id,
        )
        if not ok:
            return False, f"intent signature invalid: {env.intent.intent_id}: {err or 'rejected'}"
    return True, None


def _verify_proof_if_present(
    verifier: ProofVerifier,
    *,
    intents: List[SignedIntentEnvelope],
    settlement_env: Optional[SettlementEnvelope],
    require_proof: bool,
    verifier_enforcing: bool,
    pre_state_commitment: str,
    batch_commitment: str,
    max_verifier_payload_bytes: int,
) -> Tuple[bool, Optional[str]]:
    proof: object = settlement_env.proof if settlement_env else None
    if proof is None:
        if require_proof and intents:
            return False, "missing required proof"
        return True, None
    if not isinstance(proof, Mapping):
        return False, "proof must be an object"

    if verifier_enforcing and isinstance(verifier, MisconfiguredProofVerifier):
        _ok, v_err = verifier.verify({"schema": "zenodex_proof", "schema_version": 1})
        return False, v_err or "proof verifier misconfigured"

    if not verifier_enforcing:
        if require_proof and intents:
            return False, "proof required but verification disabled"
        # Proof is present but verification is disabled; ignore it (do not treat as authoritative).
        return True, None

    # Fail-closed binding: require the proof payload to commit to the exact
    # pre-state and batch encoding we compute locally.
    proof_pre = proof.get("pre_state_commitment")
    if proof_pre is None:
        return False, "proof missing pre_state_commitment"
    if proof_pre != pre_state_commitment:
        return False, "proof pre_state_commitment mismatch"

    proof_batch = proof.get("batch_commitment")
    if proof_batch is None:
        return False, "proof missing batch_commitment"
    if proof_batch != batch_commitment:
        return False, "proof batch_commitment mismatch"

    # Keep the verifier payload intentionally small: verifiers should validate the proof against
    # committed public inputs (commitments), not re-parse an entire batch (which can be large).
    payload: Dict[str, Any] = {
        "schema": "zenodex_proof",
        "schema_version": 1,
        "proof": proof,
        "pre_state_commitment": pre_state_commitment,
        "batch_commitment": batch_commitment,
    }
    try:
        bounded_json_utf8_size(payload, max_bytes=max_verifier_payload_bytes)
    except ValueError:
        return False, "proof payload too large"
    except TypeError:
        return False, "invalid proof payload encoding"
    ok, err = verifier.verify(payload)
    if not ok:
        return False, f"proof rejected: {err or 'invalid'}"
    return True, None


def _clean_error(message: Any, *, max_len: int = 200) -> str:
    out = " ".join(str(message).strip().split())
    return out if len(out) <= max_len else out[:max_len]


def _fault_stage(config: DexEngineConfig, stage: str) -> None:
    fault = config.fault_injection
    if fault is None:
        return
    if fault.fail_at_stage == stage:
        raise _InjectedFault(stage)


def _validate_external_tool_policy(config: DexEngineConfig) -> Optional[str]:
    tau_gate_enabled = bool(config.tau_gate_config and config.tau_gate_config.enabled)
    proof_verifier_enabled = bool(config.proof_config.enabled)
    if config.consensus_mode and (tau_gate_enabled or proof_verifier_enabled):
        return "external tools not permitted in consensus_mode"
    if (tau_gate_enabled or proof_verifier_enabled) and not config.allow_external_tools:
        return "external tools disabled (set DexEngineConfig.allow_external_tools=True)"
    return None


def _validate_raw_settlement_op(config: DexEngineConfig, raw_settlement_op: Any) -> Optional[str]:
    if raw_settlement_op is None:
        return None
    if not isinstance(raw_settlement_op, dict):
        return "operations['3'] must be an object"
    try:
        bounded_json_utf8_size(raw_settlement_op, max_bytes=config.max_settlement_op_bytes)
    except ValueError:
        return "settlement operation too large"
    except Exception as exc:
        return f"invalid settlement operation: {exc}"

    raw_fills = raw_settlement_op.get("fills")
    if isinstance(raw_fills, list) and len(raw_fills) > config.max_settlement_fills:
        return f"too many settlement fills: {len(raw_fills)} > {config.max_settlement_fills}"
    return None


def _v3_exact_out_grid_bounds(evidence: Mapping[str, Any]) -> Tuple[int, int]:
    allowed = {"max_price_num", "max_price_den"}
    extras = sorted(set(evidence) - allowed)
    if extras:
        raise ValueError(f"uniform batch v3 exact-out grid evidence has unknown field {extras[0]}")
    missing = sorted(allowed - set(evidence))
    if missing:
        raise ValueError(f"uniform batch v3 exact-out grid evidence missing {missing[0]}")
    max_price_num = evidence["max_price_num"]
    max_price_den = evidence["max_price_den"]
    if not isinstance(max_price_num, int) or isinstance(max_price_num, bool):
        raise ValueError("uniform batch v3 exact-out grid max_price_num must be an int")
    if not isinstance(max_price_den, int) or isinstance(max_price_den, bool):
        raise ValueError("uniform batch v3 exact-out grid max_price_den must be an int")
    return max_price_num, max_price_den


def _validate_raw_intent_ops(config: DexEngineConfig, raw_intents: Any) -> Optional[str]:
    if isinstance(raw_intents, list) and len(raw_intents) > config.max_intents:
        return f"too many intents: {len(raw_intents)} > {config.max_intents}"
    if not isinstance(raw_intents, list):
        return None

    total_raw_bytes = 0
    for i, entry in enumerate(raw_intents):
        try:
            total_raw_bytes += bounded_json_utf8_size(
                entry, max_bytes=config.max_intent_entry_bytes
            )
        except ValueError:
            return f"intent operation too large: index {i}"
        except Exception as exc:
            return f"invalid intent operation: {exc}"
        if total_raw_bytes > config.max_total_intent_entry_bytes:
            return "total intent operation too large"
    return None


def _validate_intent_preconditions(
    *,
    intents: List[Intent],
    settlement: Optional[Settlement],
    block_timestamp: int,
) -> Optional[str]:
    if not intents and settlement is not None:
        return "settlement provided without intents"
    for intent in intents:
        if int(intent.deadline) < int(block_timestamp):
            return f"Intent expired: {intent.intent_id}"
    return None


def _validate_intent_against_quote_receipt(
    intent: Intent, receipt: Mapping[str, Any]
) -> Optional[str]:
    if intent.kind.value not in {"SWAP_EXACT_IN", "SWAP_EXACT_OUT"}:
        return _quote_receipt_error(
            "quote receipt only supported for swap intents",
            **_quote_receipt_intent_context(intent),
            intent_kind=intent.kind.value,
        )

    body = receipt.get("body")
    if not isinstance(body, Mapping):
        return _quote_receipt_error(
            "invalid quote receipt body", **_quote_receipt_intent_context(intent)
        )
    kind = str(body.get("kind", "")).strip().lower()
    expected_kind = "exact_in" if intent.kind.value == "SWAP_EXACT_IN" else "exact_out"
    if kind != expected_kind:
        return _quote_receipt_error(
            "quote receipt kind mismatch",
            **_quote_receipt_intent_context(intent),
            expected_kind=expected_kind,
            receipt_kind=kind,
        )

    pool_id = intent.get_field("pool_id")
    asset_in = intent.get_field("asset_in")
    asset_out = intent.get_field("asset_out")
    if (
        not isinstance(pool_id, str)
        or not isinstance(asset_in, str)
        or not isinstance(asset_out, str)
    ):
        return _quote_receipt_error(
            "invalid quote receipt-bound swap fields",
            **_quote_receipt_intent_context(intent),
        )

    pools = body.get("pools")
    if not isinstance(pools, Mapping):
        return _quote_receipt_error(
            "invalid quote receipt pools", **_quote_receipt_intent_context(intent)
        )
    quote_pool_fp = intent.get_field("quote_pool_fingerprint")
    if quote_pool_fp is not None:
        if not isinstance(quote_pool_fp, str) or not quote_pool_fp:
            return _quote_receipt_error(
                "invalid quote_pool_fingerprint", **_quote_receipt_intent_context(intent)
            )
        if pools.get(pool_id) != quote_pool_fp:
            return _quote_receipt_error(
                "quote receipt pool fingerprint mismatch",
                **_quote_receipt_intent_context(intent),
                quoted_pool_fingerprint=quote_pool_fp,
                receipt_pool_fingerprint=pools.get(pool_id),
            )

    legs = body.get("legs")
    if not _is_quote_receipt_array(legs) or not legs:
        return _quote_receipt_error(
            "invalid quote receipt legs", **_quote_receipt_intent_context(intent)
        )

    leg_index_raw = intent.get_field("quote_receipt_leg_index")
    candidate_legs: list[tuple[int, Any]]
    if leg_index_raw is not None:
        if (
            not isinstance(leg_index_raw, int)
            or isinstance(leg_index_raw, bool)
            or leg_index_raw < 0
        ):
            return _quote_receipt_error(
                "invalid quote_receipt_leg_index", **_quote_receipt_intent_context(intent)
            )
        if leg_index_raw >= len(legs):
            return _quote_receipt_error(
                "quote receipt leg index out of range",
                **_quote_receipt_intent_context(intent),
                receipt_leg_count=len(legs),
            )
        candidate_legs = [(int(leg_index_raw), legs[int(leg_index_raw)])]
    else:
        candidate_legs = list(enumerate(legs))

    saw_multi_hop_match = False
    for _leg_index, leg in candidate_legs:
        if not isinstance(leg, Mapping):
            continue
        hops = leg.get("hops")
        if _is_quote_receipt_array(hops) and len(hops) != 1:
            for raw_hop in hops:
                if not isinstance(raw_hop, Mapping):
                    continue
                hop_pool_id = str(raw_hop.get("pool_id", "")).strip()
                hop_asset_in = str(raw_hop.get("asset_in", "")).strip()
                hop_asset_out = str(raw_hop.get("asset_out", "")).strip()
                if (
                    hop_pool_id == pool_id
                    and hop_asset_in == asset_in
                    and hop_asset_out == asset_out
                ):
                    saw_multi_hop_match = True
                    if leg_index_raw is not None:
                        return _quote_receipt_error(
                            "quote receipt multi-hop leg unsupported for direct intent binding",
                            **_quote_receipt_intent_context(intent),
                            hop_count=len(hops),
                        )
            continue
        if not _is_quote_receipt_array(hops) or len(hops) != 1:
            continue
        hop = hops[0]
        if not isinstance(hop, Mapping):
            continue

        hop_pool_id = str(hop.get("pool_id", "")).strip()
        hop_asset_in = str(hop.get("asset_in", "")).strip()
        hop_asset_out = str(hop.get("asset_out", "")).strip()
        if hop_pool_id != pool_id or hop_asset_in != asset_in or hop_asset_out != asset_out:
            continue

        hop_amount_in = hop.get("amount_in")
        hop_amount_out = hop.get("amount_out")
        if not isinstance(hop_amount_in, int) or isinstance(hop_amount_in, bool):
            continue
        if not isinstance(hop_amount_out, int) or isinstance(hop_amount_out, bool):
            continue

        if intent.kind.value == "SWAP_EXACT_IN":
            amount_in = intent.get_field("amount_in")
            min_amount_out = intent.get_field("min_amount_out", 0)
            if not isinstance(amount_in, int) or isinstance(amount_in, bool):
                return _quote_receipt_error(
                    "invalid amount_in for quote receipt binding",
                    **_quote_receipt_intent_context(intent),
                )
            if (
                not isinstance(min_amount_out, int)
                or isinstance(min_amount_out, bool)
                or min_amount_out < 0
            ):
                return _quote_receipt_error(
                    "invalid min_amount_out for quote receipt binding",
                    **_quote_receipt_intent_context(intent),
                )
            if int(amount_in) == int(hop_amount_in) and int(min_amount_out) <= int(hop_amount_out):
                return None
            return _quote_receipt_error(
                "exact-in quote receipt leg mismatch",
                **_quote_receipt_intent_context(intent),
                quoted_amount_in=int(hop_amount_in),
                quoted_amount_out=int(hop_amount_out),
                amount_in=int(amount_in),
                min_amount_out=int(min_amount_out),
            )

        amount_out = intent.get_field("amount_out")
        max_amount_in = intent.get_field("max_amount_in")
        if not isinstance(amount_out, int) or isinstance(amount_out, bool):
            return _quote_receipt_error(
                "invalid amount_out for quote receipt binding",
                **_quote_receipt_intent_context(intent),
            )
        if (
            not isinstance(max_amount_in, int)
            or isinstance(max_amount_in, bool)
            or max_amount_in < 0
        ):
            return _quote_receipt_error(
                "invalid max_amount_in for quote receipt binding",
                **_quote_receipt_intent_context(intent),
            )
        if int(amount_out) == int(hop_amount_out) and int(max_amount_in) >= int(hop_amount_in):
            return None
        return _quote_receipt_error(
            "exact-out quote receipt leg mismatch",
            **_quote_receipt_intent_context(intent),
            quoted_amount_in=int(hop_amount_in),
            quoted_amount_out=int(hop_amount_out),
            amount_out=int(amount_out),
            max_amount_in=int(max_amount_in),
        )

    if saw_multi_hop_match:
        return _quote_receipt_error(
            "quote receipt multi-hop leg unsupported for direct intent binding",
            **_quote_receipt_intent_context(intent),
        )
    if leg_index_raw is not None:
        return _quote_receipt_error(
            "intent does not match quote receipt leg", **_quote_receipt_intent_context(intent)
        )
    return _quote_receipt_error(
        "intent does not match quote receipt", **_quote_receipt_intent_context(intent)
    )


def _validate_quote_receipt_witnesses(
    *,
    signed_intents: List[SignedIntentEnvelope],
    pools: Dict[str, Any],
) -> Optional[str]:
    grouped_by_hash: Dict[str, List[SignedIntentEnvelope]] = {}
    for env in signed_intents:
        quote_hash = env.intent.get_field("quote_receipt_hash")
        receipt = env.quote_receipt
        if quote_hash is not None and receipt is None:
            return _quote_receipt_error(
                "missing quote receipt witness", **_quote_receipt_intent_context(env.intent)
            )
        if receipt is None:
            continue
        if quote_hash is None:
            return _quote_receipt_error(
                "quote receipt provided without quote_receipt_hash",
                **_quote_receipt_intent_context(env.intent),
                witness_hash=receipt.get("receipt_hash") if isinstance(receipt, Mapping) else None,
            )
        if not isinstance(quote_hash, str) or not quote_hash:
            return _quote_receipt_error(
                "invalid quote_receipt_hash", **_quote_receipt_intent_context(env.intent)
            )
        ok, receipt_verify_err = verify_route_quote_receipt(receipt, pools_by_id=pools)
        if not ok:
            return _quote_receipt_error(
                "invalid quote receipt",
                **_quote_receipt_intent_context(env.intent),
                verifier_error=(receipt_verify_err or "rejected"),
            )
        if receipt.get("receipt_hash") != quote_hash:
            return _quote_receipt_error(
                "quote receipt hash mismatch",
                **_quote_receipt_intent_context(env.intent),
                witness_hash=receipt.get("receipt_hash"),
            )
        leg_index = env.intent.get_field("quote_receipt_leg_index")
        if not isinstance(leg_index, int) or isinstance(leg_index, bool) or leg_index < 0:
            return _quote_receipt_error(
                "missing quote_receipt_leg_index",
                **_quote_receipt_intent_context(env.intent),
                guidance="direct quote-bound intents must bind exactly one receipt leg",
            )
        grouped_by_hash.setdefault(str(quote_hash), []).append(env)
        intent_receipt_err = _validate_intent_against_quote_receipt(env.intent, receipt)
        if intent_receipt_err is not None:
            return intent_receipt_err

    for quote_hash, envs in grouped_by_hash.items():
        receipt = envs[0].quote_receipt
        body = receipt.get("body") if isinstance(receipt, Mapping) else None
        legs = body.get("legs") if isinstance(body, Mapping) else None
        if not _is_quote_receipt_array(legs) or not legs:
            return f"invalid quote receipt legs: {envs[0].intent.intent_id}"

        observed_leg_indices: List[int] = []
        seen_leg_indices: set[int] = set()
        duplicate_leg_indices: set[int] = set()
        for env in envs:
            leg_index = env.intent.get_field("quote_receipt_leg_index")
            if not isinstance(leg_index, int) or isinstance(leg_index, bool) or leg_index < 0:
                return _quote_receipt_error(
                    "missing quote_receipt_leg_index",
                    **_quote_receipt_intent_context(env.intent),
                    guidance="direct quote-bound intents must bind exactly one receipt leg",
                )
            normalized_leg_index = int(leg_index)
            observed_leg_indices.append(normalized_leg_index)
            if normalized_leg_index in seen_leg_indices:
                duplicate_leg_indices.add(normalized_leg_index)
            else:
                seen_leg_indices.add(normalized_leg_index)

        if duplicate_leg_indices:
            return _quote_receipt_error(
                "duplicate quote receipt leg binding",
                quote_hash=quote_hash,
                duplicate_leg_indices=sorted(duplicate_leg_indices),
                intent_ids=[env.intent.intent_id for env in envs],
            )

        required_leg_indices = set(range(len(legs)))
        if set(observed_leg_indices) != required_leg_indices:
            return _quote_receipt_error(
                "incomplete quote receipt leg coverage",
                quote_hash=quote_hash,
                expected_leg_indices=sorted(required_leg_indices),
                observed_leg_indices=sorted(observed_leg_indices),
                intent_ids=[env.intent.intent_id for env in envs],
            )
    return None


def _validate_protected_swap_oracle_authorizations(
    *,
    signed_intents: List[SignedIntentEnvelope],
    block_timestamp: int,
    require_authorization: bool,
) -> Optional[str]:
    for env in signed_intents:
        auth = env.intent.get_field("oracle_authorization")
        if auth is None and not require_authorization:
            continue
        if env.intent.kind.value not in {"SWAP_EXACT_IN", "SWAP_EXACT_OUT"}:
            if auth is not None:
                return _quote_receipt_error(
                    "oracle authorization only supported for swap intents",
                    **_quote_receipt_intent_context(env.intent),
                )
            continue
        quote_hash = env.intent.get_field("quote_receipt_hash")
        if auth is None:
            if quote_hash is not None or env.quote_receipt is not None:
                return _quote_receipt_error(
                    "oracle_authorization_required",
                    **_quote_receipt_intent_context(env.intent),
                )
            continue
        if not isinstance(auth, Mapping):
            return _quote_receipt_error(
                "oracle_authorization must be an object",
                **_quote_receipt_intent_context(env.intent),
            )
        if env.quote_receipt is None:
            return _quote_receipt_error(
                "oracle authorization requires quote receipt witness",
                **_quote_receipt_intent_context(env.intent),
            )
        try:
            result = check_protected_swap_oracle_authorization(
                authorization_payload=auth,
                intent=env.intent,
                receipt=env.quote_receipt,
                now_epoch=int(block_timestamp),
            )
        except Exception as exc:
            return _quote_receipt_error(
                f"oracle_authorization_rejected: {_clean_error(exc)}",
                **_quote_receipt_intent_context(env.intent),
            )
        if not bool(result.get("typed_ok", False)):
            errors = (
                result.get("typed_errors")
                or result.get("opaque_errors")
                or ["typed authorization rejected"]
            )
            return _quote_receipt_error(
                "oracle_authorization_rejected: " + "; ".join(str(err) for err in errors),
                **_quote_receipt_intent_context(env.intent),
            )
    return None


def _validate_critical_settlement_oracle_authorization(
    *,
    settlement: Optional[Settlement],
    settlement_env: Optional[SettlementEnvelope],
    state: DexState,
    block_timestamp: int,
    price_history: Optional[Tuple[int, int, int]],
    require_authorization: bool,
) -> Optional[str]:
    auth = getattr(settlement_env, "oracle_authorization", None) if settlement_env else None
    if settlement is None:
        if auth is not None:
            return "critical_settlement_oracle_authorization_rejected: settlement missing"
        return None
    if auth is None:
        if require_authorization:
            return "critical_settlement_oracle_authorization_required"
        return None
    if not isinstance(auth, Mapping):
        return "critical settlement oracle_authorization must be an object"
    if price_history is None:
        return (
            "critical settlement oracle authorization requires settlement_certificate_price_history"
        )
    try:
        pre_state_hash = compute_state_root(
            balances=state.balances,
            pools=state.pools,
            lp_balances=state.lp_balances,
            nonces=state.nonces,
        )
    except Exception as exc:
        return f"critical_settlement_oracle_authorization_rejected: invalid pre-state root: {_clean_error(exc)}"
    try:
        result = check_critical_settlement_oracle_authorization(
            authorization_payload=auth,
            settlement=settlement,
            pre_state_hash=pre_state_hash,
            price_history=price_history,
            now_epoch=int(block_timestamp),
        )
    except Exception as exc:
        return f"critical_settlement_oracle_authorization_rejected: {_clean_error(exc)}"
    if not bool(result.get("typed_ok", False)):
        errors = (
            result.get("typed_errors")
            or result.get("opaque_errors")
            or ["typed authorization rejected"]
        )
        return "critical_settlement_oracle_authorization_rejected: " + "; ".join(
            str(err) for err in errors
        )
    return None


def _sanitize_intents_after_quote_receipt_validation(intents: List[Intent]) -> List[Intent]:
    """
    Strip transport-only quote receipt witness fields after engine-side witness
    validation. The strong validator should only consume the stale-snapshot
    marker (`quote_pool_fingerprint`) and not raw receipt transport metadata.
    """
    out: List[Intent] = []
    for intent in intents:
        fields = deep_thaw_json(intent.fields or {})
        fields.pop("quote_receipt_hash", None)
        fields.pop("quote_receipt_leg_index", None)
        fields.pop("oracle_authorization", None)
        out.append(
            Intent(
                module=intent.module,
                version=intent.version,
                kind=intent.kind,
                intent_id=intent.intent_id,
                sender_pubkey=intent.sender_pubkey,
                deadline=intent.deadline,
                salt=intent.salt,
                fields=fields,
            )
        )
    return out


def _is_supported_uniform_batch_swap_family(intents: List[Intent]) -> bool:
    """Return true for the current scoped UPBA single-pool swap families."""

    if not intents:
        return False
    pool_id: Optional[str] = None
    asset_pair: Optional[frozenset[str]] = None
    kind: Optional[IntentKind] = None
    for intent in intents:
        if intent.kind not in (IntentKind.SWAP_EXACT_IN, IntentKind.SWAP_EXACT_OUT):
            return False
        if kind is None:
            kind = intent.kind
        elif intent.kind != kind:
            return False
        try:
            current_pool_id = str(intent.get_field("pool_id"))
            asset_in = str(intent.get_field("asset_in"))
            asset_out = str(intent.get_field("asset_out"))
        except (TypeError, ValueError):
            return False
        if asset_in == asset_out:
            return False
        if intent.kind == IntentKind.SWAP_EXACT_IN:
            amount_in = intent.get_field("amount_in")
            min_amount_out = intent.get_field("min_amount_out")
            if not isinstance(amount_in, int) or isinstance(amount_in, bool) or amount_in <= 0:
                return False
            if (
                not isinstance(min_amount_out, int)
                or isinstance(min_amount_out, bool)
                or min_amount_out < 0
            ):
                return False
        else:
            amount_out = intent.get_field("amount_out")
            max_amount_in = intent.get_field("max_amount_in")
            if not isinstance(amount_out, int) or isinstance(amount_out, bool) or amount_out <= 0:
                return False
            if (
                not isinstance(max_amount_in, int)
                or isinstance(max_amount_in, bool)
                or max_amount_in < 0
            ):
                return False
        current_pair = frozenset((asset_in, asset_out))
        if pool_id is None:
            pool_id = current_pool_id
            asset_pair = current_pair
            continue
        if current_pool_id != pool_id or current_pair != asset_pair:
            return False
    return True


def _build_signing_payloads(
    signed_intents: List[SignedIntentEnvelope],
    *,
    max_intent_bytes: int,
    max_total_intent_bytes: int,
) -> Tuple[List[Dict[str, Any]], List[bytes]]:
    signing_dicts: List[Dict[str, Any]] = []
    signing_payloads: List[bytes] = []
    total_bytes = 0
    for env in signed_intents:
        signing_dict = _intent_signing_dict(env.intent)
        signing_dicts.append(signing_dict)
        try:
            bounded_json_utf8_size(signing_dict, max_bytes=max_intent_bytes)
            payload = canonical_json_bytes(signing_dict)
        except ValueError as exc:
            raise ValueError(f"intent signing payload too large: {env.intent.intent_id}") from exc
        except Exception as exc:
            raise ValueError(f"invalid intent signing payload: {env.intent.intent_id}") from exc
        if len(payload) > max_intent_bytes:
            raise ValueError(f"intent signing payload too large: {env.intent.intent_id}")
        signing_payloads.append(payload)
        total_bytes += len(payload)
        if total_bytes > max_total_intent_bytes:
            raise ValueError("total intent payload too large")
    return signing_dicts, signing_payloads


def apply_ops(
    *,
    config: DexEngineConfig,
    state: DexState,
    operations: Dict[str, Any],
    block_timestamp: int,
    tx_sender_pubkey: Optional[str] = None,
) -> DexTxResult:
    """
    Apply DEX operations to the current state.

    `tx_sender_pubkey` is the outer transaction sender (already verified by Tau Net);
    it is used only for signature policy (bypass for user-submitted intents).
    """
    try:
        if config.fault_injection is not None and not bool(config.enable_test_fault_injection):
            return DexTxResult(ok=False, error="fault injection disabled")

        err = _validate_external_tool_policy(config)
        if err is not None:
            return DexTxResult(ok=False, error=err)

        err = _validate_raw_settlement_op(config, operations.get("3"))
        if err is not None:
            return DexTxResult(ok=False, error=err)

        err = _validate_raw_intent_ops(config, operations.get("2"))
        if err is not None:
            return DexTxResult(ok=False, error=err)
        _fault_stage(config, "after_raw_validation")

        try:
            if config.require_canonical_quote_receipt_transport:
                signed_intents = parse_signed_intents(
                    operations,
                    require_canonical_quote_receipt_transport=True,
                )
            else:
                # Preserve the historical one-argument call path for non-strict
                # builders and test doubles. Only strict profiles need the new
                # canonical-carrier policy argument.
                signed_intents = parse_signed_intents(operations)
        except ValueError as exc:
            return DexTxResult(ok=False, error=f"invalid intents: {_clean_error(exc)}")
        if len(signed_intents) > config.max_intents:
            return DexTxResult(
                ok=False, error=f"too many intents: {len(signed_intents)} > {config.max_intents}"
            )
        _fault_stage(config, "after_intent_parse")

        try:
            settlement_env = parse_settlement_envelope(operations)
        except ValueError as exc:
            return DexTxResult(ok=False, error=f"invalid settlement: {_clean_error(exc)}")
        settlement_supplied = settlement_env is not None
        settlement = settlement_env.settlement if settlement_env else None
        proof = settlement_env.proof if settlement_env else None
        uniform_batch_certificate = (
            getattr(settlement_env, "uniform_batch_certificate", None) if settlement_env else None
        )
        uniform_batch_optimality_certificate = (
            getattr(settlement_env, "uniform_batch_optimality_certificate", None)
            if settlement_env
            else None
        )
        uniform_batch_v2_bounded_grid = (
            getattr(settlement_env, "uniform_batch_v2_bounded_grid", None)
            if settlement_env
            else None
        )
        uniform_batch_v3_exact_out_grid = (
            getattr(settlement_env, "uniform_batch_v3_exact_out_grid", None)
            if settlement_env
            else None
        )
        if uniform_batch_optimality_certificate is not None and uniform_batch_certificate is None:
            return DexTxResult(
                ok=False,
                error="uniform batch optimality certificate requires uniform batch certificate",
            )
        if uniform_batch_v2_bounded_grid is not None and uniform_batch_certificate is None:
            return DexTxResult(
                ok=False,
                error="uniform batch v2 bounded-grid evidence requires uniform batch certificate",
            )
        if uniform_batch_v3_exact_out_grid is not None and uniform_batch_certificate is None:
            return DexTxResult(
                ok=False,
                error="uniform batch v3 exact-out grid evidence requires uniform batch certificate",
            )
        if (
            uniform_batch_v2_bounded_grid is not None
            and uniform_batch_optimality_certificate is None
        ):
            return DexTxResult(
                ok=False,
                error="uniform batch v2 bounded-grid evidence requires optimality certificate",
            )
        if (
            uniform_batch_v3_exact_out_grid is not None
            and uniform_batch_optimality_certificate is None
        ):
            return DexTxResult(
                ok=False,
                error="uniform batch v3 exact-out grid evidence requires optimality certificate",
            )
        if (
            uniform_batch_v2_bounded_grid is not None
            and uniform_batch_v3_exact_out_grid is not None
        ):
            return DexTxResult(
                ok=False,
                error="uniform batch bounded-grid evidence provided twice",
            )
        proof_scheme: Optional[str] = None
        if proof is not None:
            scheme_raw = proof.get("scheme")
            if isinstance(scheme_raw, str) and scheme_raw:
                proof_scheme = scheme_raw
            try:
                bounded_json_utf8_size(proof, max_bytes=config.proof_config.max_proof_bytes)
            except ValueError:
                return DexTxResult(ok=False, error="proof payload too large")
            except TypeError:
                return DexTxResult(ok=False, error="invalid proof payload encoding")
        _fault_stage(config, "after_settlement_parse")

        signed_payload_intents = [env.intent for env in signed_intents]
        err = _validate_intent_preconditions(
            intents=signed_payload_intents,
            settlement=settlement,
            block_timestamp=block_timestamp,
        )
        if err is not None:
            return DexTxResult(ok=False, error=err)
        _fault_stage(config, "after_preconditions")

        try:
            signing_dicts, signing_payloads = _build_signing_payloads(
                signed_intents,
                max_intent_bytes=config.max_intent_bytes,
                max_total_intent_bytes=config.max_total_intent_bytes,
            )
        except ValueError as exc:
            return DexTxResult(ok=False, error=str(exc))

        ok, err = _verify_all_intent_signatures(
            signed_intents,
            require=config.require_intent_signatures,
            tx_sender_pubkey=tx_sender_pubkey,
            allow_tx_sender_bypass=config.allow_unsigned_intents_if_tx_sender_matches,
            signing_payloads=signing_payloads,
            chain_id=config.chain_id,
        )
        if not ok:
            return DexTxResult(ok=False, error=err)
        _fault_stage(config, "after_signature_verification")

        err = _validate_quote_receipt_witnesses(signed_intents=signed_intents, pools=state.pools)
        if err is not None:
            return DexTxResult(ok=False, error=err)
        err = _validate_protected_swap_oracle_authorizations(
            signed_intents=signed_intents,
            block_timestamp=block_timestamp,
            require_authorization=bool(config.require_oracle_authorization_for_protected_swaps),
        )
        if err is not None:
            return DexTxResult(ok=False, error=err)
        if config.canonicalize_authenticated_bls_principals:
            try:
                execution_intents = [
                    canonicalize_authenticated_intent_for_execution(intent)
                    for intent in signed_payload_intents
                ]
            except (TypeError, ValueError) as exc:
                return DexTxResult(
                    ok=False,
                    error=f"invalid authenticated intent identity: {_clean_error(exc)}",
                )
        else:
            execution_intents = signed_payload_intents
        if (
            proof_scheme
            in {
                "recompute_batch_v1",
                "recompute_batch_v2",
                "recompute_batch_v3",
                "recompute_batch_v4",
            }
            and execution_intents != signed_payload_intents
        ):
            return DexTxResult(
                ok=False,
                error=(
                    "proof-bearing intents must use canonical BLS principal spellings; "
                    "recompute proof v1-v4 do not bind an identity execution profile"
                ),
            )
        validation_intents = _sanitize_intents_after_quote_receipt_validation(execution_intents)
        if (
            config.require_uniform_batch_certificate_for_supported_swaps
            and uniform_batch_certificate is None
            and _is_supported_uniform_batch_swap_family(validation_intents)
        ):
            return DexTxResult(
                ok=False, error="uniform batch certificate required for supported swaps"
            )

        next_nonces: Optional[NonceTable] = None
        if execution_intents:
            ok, err, next_nonces = _validate_and_apply_nonce_batch(
                nonces=state.nonces,
                intents=execution_intents,
            )
            if not ok:
                return DexTxResult(ok=False, error=err or "nonce policy rejected")
        _fault_stage(config, "after_nonce_validation")

        # Compute settlement deterministically and (optionally) require an exact match.
        computed_settlement: Optional[Settlement] = None
        if execution_intents:
            if uniform_batch_certificate is not None:
                if not config.allow_uniform_batch_certificate:
                    return DexTxResult(ok=False, error="uniform batch certificate not enabled")
                if config.dex_config.protocol_fee_share_bps > 0:
                    return DexTxResult(
                        ok=False,
                        error="uniform batch certificate cannot be used when protocol fees are enabled",
                    )
                try:
                    cert = UniformBatchCertificateV1.from_obj(uniform_batch_certificate)
                except Exception as exc:
                    return DexTxResult(
                        ok=False,
                        error=f"uniform batch certificate rejected: {_clean_error(exc)}",
                    )
                pool = state.pools.get(cert.pool_id)
                if pool is None:
                    return DexTxResult(
                        ok=False,
                        error=f"uniform batch certificate pool not found: {cert.pool_id}",
                    )
                if (
                    config.require_uniform_batch_optimality_certificate
                    and uniform_batch_optimality_certificate is None
                ):
                    return DexTxResult(
                        ok=False, error="uniform batch optimality certificate required"
                    )
                if (
                    config.require_uniform_batch_v2_bounded_grid_optimality
                    and cert.policy_id == UNIFORM_BATCH_POLICY_V2_ID
                    and uniform_batch_v2_bounded_grid is None
                ):
                    return DexTxResult(
                        ok=False,
                        error="uniform batch v2 bounded-grid evidence required",
                    )
                if (
                    config.require_uniform_batch_v3_exact_out_grid_optimality
                    and cert.policy_id == UNIFORM_BATCH_POLICY_V3_ID
                    and uniform_batch_v3_exact_out_grid is None
                ):
                    return DexTxResult(
                        ok=False,
                        error="uniform batch v3 exact-out grid evidence required",
                    )
                if (
                    uniform_batch_v2_bounded_grid is not None
                    and cert.policy_id != UNIFORM_BATCH_POLICY_V2_ID
                ):
                    return DexTxResult(
                        ok=False,
                        error="uniform batch v2 bounded-grid evidence requires v2 uniform batch certificate",
                    )
                if (
                    uniform_batch_v3_exact_out_grid is not None
                    and cert.policy_id != UNIFORM_BATCH_POLICY_V3_ID
                ):
                    return DexTxResult(
                        ok=False,
                        error="uniform batch v3 exact-out grid evidence requires v3 uniform batch certificate",
                    )
                if uniform_batch_optimality_certificate is not None:
                    if uniform_batch_v2_bounded_grid is not None:
                        try:
                            optimality_result = (
                                verify_uniform_batch_v2_bounded_grid_optimality_certificate_v1(
                                    optimality_certificate=uniform_batch_optimality_certificate,
                                    uniform_batch_certificate=cert,
                                    intents=validation_intents,
                                    pool=pool,
                                    balances=state.balances,
                                    max_price_num=uniform_batch_v2_bounded_grid["max_price_num"],
                                    max_price_den=uniform_batch_v2_bounded_grid["max_price_den"],
                                    fill_vectors=uniform_batch_v2_bounded_grid["fill_vectors"],
                                    expected_table_root=uniform_batch_v2_bounded_grid.get(
                                        "table_root"
                                    ),
                                )
                            )
                        except KeyError as exc:
                            return DexTxResult(
                                ok=False,
                                error=(
                                    "uniform batch optimality certificate rejected: "
                                    f"uniform batch v2 bounded-grid evidence missing {str(exc)}"
                                ),
                            )
                    elif uniform_batch_v3_exact_out_grid is not None:
                        try:
                            max_price_num, max_price_den = _v3_exact_out_grid_bounds(
                                uniform_batch_v3_exact_out_grid
                            )
                            optimality_result = (
                                verify_uniform_batch_v3_exact_out_grid_optimality_certificate_v1(
                                    optimality_certificate=uniform_batch_optimality_certificate,
                                    uniform_batch_certificate=cert,
                                    intents=validation_intents,
                                    pool=pool,
                                    balances=state.balances,
                                    max_price_num=max_price_num,
                                    max_price_den=max_price_den,
                                )
                            )
                        except ValueError as exc:
                            return DexTxResult(
                                ok=False,
                                error=(
                                    "uniform batch optimality certificate rejected: "
                                    f"{_clean_error(exc)}"
                                ),
                            )
                    else:
                        optimality_result = verify_uniform_batch_bound_optimality_certificate_v1(
                            optimality_certificate=uniform_batch_optimality_certificate,
                            uniform_batch_certificate=cert,
                        )
                    if not optimality_result.ok:
                        return DexTxResult(
                            ok=False,
                            error=(
                                "uniform batch optimality certificate rejected: "
                                f"{optimality_result.error or 'invalid certificate'}"
                            ),
                        )
                try:
                    computed_settlement = build_uniform_batch_settlement_v1(
                        intents=validation_intents,
                        pool=pool,
                        balances=state.balances,
                        certificate=cert,
                    )
                except Exception as exc:
                    return DexTxResult(
                        ok=False,
                        error=f"uniform batch certificate rejected: {_clean_error(exc)}",
                    )
            else:
                computed_settlement = compute_settlement(
                    intents=execution_intents,
                    pools=state.pools,
                    balances=state.balances,
                    lp_balances=state.lp_balances,
                    swap_ordering=str(config.swap_ordering),
                    protocol_fee_share_bps=config.dex_config.protocol_fee_share_bps,
                    protocol_fee_recipient_pubkey=config.dex_config.protocol_fee_recipient_pubkey,
                )

            if settlement is None:
                if not config.allow_missing_settlement:
                    return DexTxResult(ok=False, error="missing settlement")
                settlement = computed_settlement
            elif config.require_settlement_match:
                try:
                    expected = _settlement_rewrite_normal_form_dict(computed_settlement)
                    got = _settlement_rewrite_normal_form_dict(settlement)
                except (TypeError, ValueError):
                    return DexTxResult(ok=False, error="invalid settlement payload for comparison")
                if got != expected:
                    return DexTxResult(ok=False, error="settlement mismatch")
                settlement = computed_settlement
        _fault_stage(config, "after_settlement_compute")

        if settlement is not None and settlement_supplied:
            reject_error = reject_settlement_public_boundary_error(config.dex_config, settlement)
            if reject_error is not None:
                return DexTxResult(ok=False, error=reject_error)
        if settlement is not None:
            err = validate_lp_settlement_age_gate(
                settlement=settlement,
                intents=execution_intents,
                lp_balances=state.lp_balances,
                block_timestamp=block_timestamp,
                min_lp_position_age_seconds=config.min_lp_position_age_seconds,
                duration_risk_policy=config.lp_duration_risk_policy,
            )
            if err is not None:
                return DexTxResult(ok=False, error=err)

        err = _validate_critical_settlement_oracle_authorization(
            settlement=settlement,
            settlement_env=settlement_env,
            state=state,
            block_timestamp=block_timestamp,
            price_history=config.settlement_certificate_price_history,
            require_authorization=bool(
                config.require_oracle_authorization_for_critical_settlements
            ),
        )
        if err is not None:
            return DexTxResult(ok=False, error=err)

        verifier = make_proof_verifier(config.proof_config)
        verifier_enforcing = bool(config.proof_config.enabled)
        pre_state_commitment = "0x0"
        batch_commitment = "0x0"
        proof_preverified = False
        effective_settlement_end_to_end_inputs = config.settlement_end_to_end_certificate_inputs
        using_end_to_end_certificate = bool(
            config.require_settlement_end_to_end_certificate
            or config.require_settlement_certificate
        )

        if proof is not None and verifier_enforcing:
            if settlement is None:
                return DexTxResult(ok=False, error="proof requires settlement")
            try:
                require_normal_form(execution_intents, strict_lp_order=True)
            except IntentNormalFormError as exc:
                return DexTxResult(
                    ok=False, error=f"intents not in normal form: {_clean_error(exc)}"
                )

            try:
                if proof_scheme in ("recompute_batch_v3", "recompute_batch_v4"):
                    pre_state_commitment = compute_support_state_root_for_batch(
                        intents=execution_intents,
                        balances=state.balances,
                        pools=state.pools,
                        lp_balances=state.lp_balances,
                        nonces=state.nonces,
                    )
                else:
                    pre_state_commitment = compute_state_root(
                        balances=state.balances,
                        pools=state.pools,
                        lp_balances=state.lp_balances,
                        nonces=state.nonces,
                    )
            except Exception as exc:
                return DexTxResult(ok=False, error=f"invalid state for commitment: {exc}")

            try:
                if proof_scheme == "recompute_batch_v4":
                    op3 = create_settlement_operation(settlement).get("3")
                    if not isinstance(op3, dict):
                        raise TypeError("settlement operation must be an object")
                    settlement_obj_for_commit = normalize_settlement_op_for_commitment(op3)
                else:
                    settlement_obj_for_commit = _settlement_commitment_dict(settlement)
            except Exception as exc:
                return DexTxResult(
                    ok=False, error=f"invalid settlement payload for commitment: {exc}"
                )
            try:
                bounded_json_utf8_size(
                    settlement_obj_for_commit, max_bytes=config.max_settlement_bytes
                )
            except ValueError:
                return DexTxResult(ok=False, error="settlement payload too large")
            except Exception as exc:
                return DexTxResult(ok=False, error=f"invalid settlement payload: {exc}")

            batch_payload = {
                "schema": "zenodex_batch",
                "schema_version": 1,
                "canonical_encoding_version": CANONICAL_ENCODING_VERSION,
                "intents": signing_dicts,
                "settlement": settlement_obj_for_commit,
            }
            try:
                bounded_json_utf8_size(
                    batch_payload,
                    max_bytes=(config.max_total_intent_bytes + config.max_settlement_bytes + 8192),
                )
                batch_commitment = sha256_hex(
                    domain_sep_bytes("dex_batch", version=1) + canonical_json_bytes(batch_payload)
                )
            except ValueError:
                return DexTxResult(ok=False, error="batch payload too large")
            except Exception as exc:
                return DexTxResult(ok=False, error=f"invalid batch payload: {exc}")

        if (
            settlement is not None
            and using_end_to_end_certificate
            and effective_settlement_end_to_end_inputs is not None
            and verifier_enforcing
        ):
            if proof is None:
                return DexTxResult(
                    ok=False,
                    error="settlement certificate requires proof when proof verification is enabled",
                )
            ok, err = _verify_proof_if_present(
                verifier,
                intents=signed_intents,
                settlement_env=settlement_env,
                require_proof=True,
                verifier_enforcing=verifier_enforcing,
                pre_state_commitment=pre_state_commitment,
                batch_commitment=batch_commitment,
                max_verifier_payload_bytes=config.proof_config.max_proof_bytes,
            )
            if not ok:
                return DexTxResult(ok=False, error=err)
            proof_preverified = True
            effective_settlement_end_to_end_inputs = replace(
                effective_settlement_end_to_end_inputs,
                proof_flags=derive_verified_replay_bound_certificate_flags(
                    effective_settlement_end_to_end_inputs.proof_flags,
                    proof_ok=True,
                    binding_ok=True,
                ),
            )
        ok, err = validate_operations(
            intents=validation_intents,
            settlement=settlement,
            balances=state.balances,
            pools=state.pools,
            lp_balances=state.lp_balances,
            block_timestamp=block_timestamp,
            tau_gate_config=config.tau_gate_config,
            settlement_validation=config.dex_config.settlement_validation,
            swap_ordering=str(config.swap_ordering),
            quote_bindings_validated=True,
            require_settlement_certificate=bool(config.require_settlement_certificate),
            settlement_proof_flags=config.settlement_certificate_proof_flags,
            settlement_price_history=config.settlement_certificate_price_history,
            require_settlement_end_to_end_certificate=bool(
                config.require_settlement_end_to_end_certificate
            ),
            settlement_end_to_end_certificate_inputs=effective_settlement_end_to_end_inputs,
            uniform_batch_certificate=uniform_batch_certificate,
            protocol_fee_share_bps=config.dex_config.protocol_fee_share_bps,
            protocol_fee_recipient_pubkey=config.dex_config.protocol_fee_recipient_pubkey,
        )
        if not ok:
            return DexTxResult(ok=False, error=err or "operations invalid")
        _fault_stage(config, "after_settlement_validation")

        if not proof_preverified:
            ok, err = _verify_proof_if_present(
                verifier,
                intents=signed_intents,
                settlement_env=settlement_env,
                require_proof=config.require_proof_when_present,
                verifier_enforcing=verifier_enforcing,
                pre_state_commitment=pre_state_commitment,
                batch_commitment=batch_commitment,
                max_verifier_payload_bytes=config.proof_config.max_proof_bytes,
            )
            if not ok:
                return DexTxResult(ok=False, error=err)
        _fault_stage(config, "after_proof_verification")
        if settlement is None:
            # No DEX ops; state unchanged.
            return DexTxResult(ok=True, state=state, settlement=None)

        next_balances, next_pools, next_lp = apply_settlement_pure(
            settlement=settlement,
            balances=state.balances,
            pools=state.pools,
            lp_balances=state.lp_balances,
        )
        err = apply_lp_mint_timestamps_after_settlement(
            lp_balances=next_lp,
            settlement=settlement,
            block_timestamp=block_timestamp,
            duration_risk_policy=config.lp_duration_risk_policy,
        )
        if err is not None:
            return DexTxResult(ok=False, error=err)
        _fault_stage(config, "after_apply_pure")

        # Optional fee split accounting (dust carry). This is a local/accounting module
        # and does not mutate balances/pools unless a future module consumes it.
        next_fee_state = state.fee_accumulator
        if config.dex_config.fee_split_params is not None:
            total_fees = sum(int(fill.fee_paid or 0) for fill in settlement.fills)
            _fee_split, next_fee_state = split_fee_with_dust_carry(
                fee_amount=total_fees,
                params=config.dex_config.fee_split_params,
                state=state.fee_accumulator,
            )

        next_state = DexState(
            balances=next_balances,
            pools=next_pools,
            lp_balances=next_lp,
            nonces=next_nonces or state.nonces,
            vault=state.vault,
            oracle=state.oracle,
            fee_accumulator=next_fee_state,
            perps=state.perps,
        )
        proof_mining_context: Optional[ProofMiningContext] = None
        if proof is not None and verifier_enforcing:
            try:
                proof_mining_context = build_proof_mining_context(
                    chain_id=config.chain_id,
                    prev_state_hash=pre_state_commitment,
                    batch_hash=batch_commitment,
                    proof=proof,
                    next_state=next_state,
                    proof_scheme=proof_scheme,
                )
            except Exception as exc:
                return DexTxResult(ok=False, error=f"invalid proof mining context: {exc}")
        return DexTxResult(
            ok=True,
            state=next_state,
            settlement=settlement,
            proof_mining_context=proof_mining_context,
        )
    except _InjectedFault as exc:
        return DexTxResult(ok=False, error=str(exc))
    except Exception:
        return DexTxResult(ok=False, error="internal error")
