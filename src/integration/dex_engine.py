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
from dataclasses import dataclass
from typing import Any, Dict, List, Mapping, Optional, Tuple

from ..core.batch_clearing import apply_settlement_pure, compute_settlement
from ..core.dex import DexConfig, DexState
from ..core.fees import split_fee_with_dust_carry
from ..core.intent_normal_form import IntentNormalFormError, require_normal_form
from ..core.settlement import Settlement
from ..core.settlement_normal_form import normalize_settlement_op_for_commitment
from ..state.canonical import (
    CANONICAL_ENCODING_VERSION,
    bounded_json_utf8_size,
    canonical_json_bytes,
    domain_sep_bytes,
    sha256_hex,
)
from ..state.intents import Intent
from ..state.state_root import compute_state_root
from ..state.support_root import compute_support_state_root_for_batch
from .operations import (
    SignedIntentEnvelope,
    SettlementEnvelope,
    create_settlement_operation,
    parse_settlement_envelope,
    parse_signed_intents,
)
from .proof_verifier import MisconfiguredProofVerifier, ProofVerifier, ProofVerifierConfig, make_proof_verifier
from .tau_gate import TauGateConfig
from .validation import validate_operations


try:
    from py_ecc.bls import G2Basic

    _BLS_AVAILABLE = True
except Exception:  # pragma: no cover - optional dependency
    G2Basic = None  # type: ignore[assignment]
    _BLS_AVAILABLE = False

_HEX_CHARS_RE = re.compile(r"^[0-9a-fA-F]+$")


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

    # Intent signature policy:
    # - If `require_intent_signatures` is True, each intent must carry a per-intent signature,
    #   unless `allow_unsigned_intents_if_tx_sender_matches` is True and the outer tx sender
    #   matches the intent sender (user-submitted intents).
    # - If `require_intent_signatures` is False, per-intent signatures are ignored and all intents
    #   must be submitted by their declared sender at the outer tx layer (tx_sender_pubkey).
    require_intent_signatures: bool = True
    allow_unsigned_intents_if_tx_sender_matches: bool = True

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
    require_proof_when_present: bool = False  # if True: reject txs with intents unless proof is present

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

    # Optional fee split params (applied after any successful settlement).
    dex_config: DexConfig = DexConfig()


@dataclass(frozen=True)
class DexTxResult:
    ok: bool
    state: Optional[DexState] = None
    settlement: Optional[Settlement] = None
    error: Optional[str] = None


def _hex_to_bytes_allow_0x(hex_str: str, *, name: str, expected_nbytes: Optional[int] = None) -> bytes:
    if not isinstance(hex_str, str):
        raise TypeError(f"{name} must be a string")
    s = hex_str[2:] if hex_str.startswith("0x") else hex_str
    if not s:
        raise ValueError(f"{name} must be non-empty hex")

    if expected_nbytes is not None:
        if not isinstance(expected_nbytes, int) or isinstance(expected_nbytes, bool) or expected_nbytes <= 0:
            raise ValueError("expected_nbytes must be a positive int")
        expected_hex_len = 2 * expected_nbytes
        if len(s) != expected_hex_len:
            raise ValueError(f"{name} must be {expected_nbytes} bytes (hex length {expected_hex_len})")

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
    if not isinstance(value, str):
        return None
    try:
        return _hex_to_bytes_allow_0x(value, name=name, expected_nbytes=48)
    except Exception:
        return None


def _intent_signing_dict(intent: Intent) -> Dict[str, Any]:
    fields = intent.fields or {}
    if not isinstance(fields, dict):
        raise TypeError("intent.fields must be a dict")
    # Defend against accidental mutation/aliasing: signing must be computed over a
    # stable snapshot of the intent fields.
    fields = dict(fields)

    d: Dict[str, Any] = {
        "module": intent.module,
        "version": intent.version,
        "kind": intent.kind.value,
        "intent_id": intent.intent_id,
        "sender_pubkey": intent.sender_pubkey,
        "deadline": intent.deadline,
        "fields": fields,
    }
    if intent.salt is not None:
        d["salt"] = intent.salt
    return d


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


def _verify_intent_signature_bytes(
    *, sender_pubkey_hex: str, signature_hex: str, signing_payload_bytes: bytes, chain_id: str
) -> Tuple[bool, Optional[str]]:
    if not _BLS_AVAILABLE:
        return False, "py_ecc (BLS) not available"
    try:
        pubkey_bytes = _hex_to_bytes_allow_0x(sender_pubkey_hex, name="sender_pubkey", expected_nbytes=48)
        sig_bytes = _hex_to_bytes_allow_0x(signature_hex, name="signature", expected_nbytes=96)

        msg = domain_sep_bytes(f"dex_intent_sig:{chain_id}", version=1) + signing_payload_bytes
        msg_hash = hashlib.sha256(msg).digest()
        ok = bool(G2Basic.Verify(pubkey_bytes, msg_hash, sig_bytes))  # type: ignore[attr-defined]
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
            intent_b = _pubkey_bytes48_or_none(env.intent.sender_pubkey, name="intent.sender_pubkey")
            if intent_b is None or intent_b != sender_b:
                return False, f"intent sender mismatch: {env.intent.intent_id}"
        return True, None

    for env, signing_payload in zip(intents, signing_payloads):
        if env.signature is None:
            if allow_tx_sender_bypass:
                sender_b = _pubkey_bytes48_or_none(tx_sender_pubkey, name="tx_sender_pubkey")
                intent_b = _pubkey_bytes48_or_none(env.intent.sender_pubkey, name="intent.sender_pubkey")
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
    proof = settlement_env.proof if settlement_env else None
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
    except Exception:
        return False, "invalid proof payload encoding"
    ok, err = verifier.verify(payload)
    if not ok:
        return False, f"proof rejected: {err or 'invalid'}"
    return True, None


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
        tau_gate_enabled = bool(config.tau_gate_config and config.tau_gate_config.enabled)
        proof_verifier_enabled = bool(config.proof_config.enabled)
        if config.consensus_mode and (tau_gate_enabled or proof_verifier_enabled):
            return DexTxResult(ok=False, error="external tools not permitted in consensus_mode")
        if (tau_gate_enabled or proof_verifier_enabled) and not config.allow_external_tools:
            return DexTxResult(
                ok=False,
                error="external tools disabled (set DexEngineConfig.allow_external_tools=True)",
            )

        raw_settlement_op = operations.get("3")
        if raw_settlement_op is not None:
            if not isinstance(raw_settlement_op, dict):
                return DexTxResult(ok=False, error="operations['3'] must be an object")
            try:
                bounded_json_utf8_size(raw_settlement_op, max_bytes=config.max_settlement_op_bytes)
            except ValueError:
                return DexTxResult(ok=False, error="settlement operation too large")
            except Exception as exc:
                return DexTxResult(ok=False, error=f"invalid settlement operation: {exc}")

            raw_fills = raw_settlement_op.get("fills")
            if isinstance(raw_fills, list) and len(raw_fills) > config.max_settlement_fills:
                return DexTxResult(
                    ok=False,
                    error=f"too many settlement fills: {len(raw_fills)} > {config.max_settlement_fills}",
                )

        raw_intents = operations.get("2")
        if isinstance(raw_intents, list) and len(raw_intents) > config.max_intents:
            return DexTxResult(ok=False, error=f"too many intents: {len(raw_intents)} > {config.max_intents}")
        if isinstance(raw_intents, list):
            # Apply DoS guards to the raw intent entries *before* parsing, to avoid large
            # copies during normalization (dict comprehensions) inside parsing logic.
            total_raw_bytes = 0
            for i, entry in enumerate(raw_intents):
                try:
                    total_raw_bytes += bounded_json_utf8_size(entry, max_bytes=config.max_intent_entry_bytes)
                except ValueError:
                    return DexTxResult(ok=False, error=f"intent operation too large: index {i}")
                except Exception as exc:
                    return DexTxResult(ok=False, error=f"invalid intent operation: {exc}")
                if total_raw_bytes > config.max_total_intent_entry_bytes:
                    return DexTxResult(ok=False, error="total intent operation too large")

        def _clean_error(s: str, *, max_len: int = 200) -> str:
            out = " ".join(str(s).strip().split())
            return out if len(out) <= max_len else out[:max_len]

        try:
            signed_intents = parse_signed_intents(operations)
        except ValueError as exc:
            return DexTxResult(ok=False, error=f"invalid intents: {_clean_error(exc)}")
        except Exception:
            return DexTxResult(ok=False, error="invalid intents")
        if len(signed_intents) > config.max_intents:
            return DexTxResult(ok=False, error=f"too many intents: {len(signed_intents)} > {config.max_intents}")

        signing_dicts: List[Dict[str, Any]] = []
        signing_payloads: List[bytes] = []
        total_bytes = 0
        for env in signed_intents:
            d = _intent_signing_dict(env.intent)
            signing_dicts.append(d)
            try:
                bounded_json_utf8_size(d, max_bytes=config.max_intent_bytes)
                b = canonical_json_bytes(d)
            except ValueError:
                return DexTxResult(ok=False, error=f"intent signing payload too large: {env.intent.intent_id}")
            except Exception:
                return DexTxResult(ok=False, error=f"invalid intent signing payload: {env.intent.intent_id}")
            if len(b) > config.max_intent_bytes:
                return DexTxResult(ok=False, error=f"intent signing payload too large: {env.intent.intent_id}")
            signing_payloads.append(b)
            total_bytes += len(b)
            if total_bytes > config.max_total_intent_bytes:
                return DexTxResult(ok=False, error="total intent payload too large")

        intents = [env.intent for env in signed_intents]
        try:
            settlement_env = parse_settlement_envelope(operations)
        except ValueError as exc:
            return DexTxResult(ok=False, error=f"invalid settlement: {_clean_error(exc)}")
        except Exception:
            return DexTxResult(ok=False, error="invalid settlement")
        settlement = settlement_env.settlement if settlement_env else None
        proof = settlement_env.proof if settlement_env else None
        proof_scheme: Optional[str] = None
        if not intents and settlement is not None:
            return DexTxResult(ok=False, error="settlement provided without intents")
        if proof is not None:
            if not isinstance(settlement_env.proof, Mapping):
                return DexTxResult(ok=False, error="proof must be an object")
            scheme_raw = proof.get("scheme")
            if isinstance(scheme_raw, str) and scheme_raw:
                proof_scheme = scheme_raw
            try:
                bounded_json_utf8_size(proof, max_bytes=config.proof_config.max_proof_bytes)
            except ValueError:
                return DexTxResult(ok=False, error="proof payload too large")
            except Exception:
                return DexTxResult(ok=False, error="invalid proof payload encoding")

        # Compute settlement deterministically and (optionally) require an exact match.
        computed_settlement: Optional[Settlement] = None
        if intents:
            computed_settlement = compute_settlement(
                intents=intents,
                pools=state.pools,
                balances=state.balances,
                lp_balances=state.lp_balances,
            )

            if settlement is None:
                if not config.allow_missing_settlement:
                    return DexTxResult(ok=False, error="missing settlement")
                settlement = computed_settlement
            elif config.require_settlement_match:
                try:
                    if proof_scheme == "recompute_batch_v4":
                        expected_op3 = create_settlement_operation(computed_settlement).get("3")
                        got_op3 = create_settlement_operation(settlement).get("3")
                        if not isinstance(expected_op3, dict) or not isinstance(got_op3, dict):
                            raise TypeError("settlement operation must be an object")
                        expected = normalize_settlement_op_for_commitment(expected_op3)
                        got = normalize_settlement_op_for_commitment(got_op3)
                    else:
                        expected = _settlement_commitment_dict(computed_settlement)
                        got = _settlement_commitment_dict(settlement)
                except Exception:
                    return DexTxResult(ok=False, error="invalid settlement payload for comparison")
                if got != expected:
                    return DexTxResult(ok=False, error="settlement mismatch")
                settlement = computed_settlement

        verifier = make_proof_verifier(config.proof_config)
        verifier_enforcing = bool(config.proof_config.enabled)

        ok, err = validate_operations(
            intents=intents,
            settlement=settlement,
            balances=state.balances,
            pools=state.pools,
            lp_balances=state.lp_balances,
            block_timestamp=block_timestamp,
            tau_gate_config=config.tau_gate_config,
        )
        if not ok:
            return DexTxResult(ok=False, error=err or "operations invalid")

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

        pre_state_commitment = "0x0"
        batch_commitment = "0x0"
        if proof is not None and verifier_enforcing:
            try:
                require_normal_form(intents, strict_lp_order=False)
            except IntentNormalFormError as exc:
                return DexTxResult(ok=False, error=f"intents not in normal form: {_clean_error(exc)}")

            try:
                scheme = proof.get("scheme") if isinstance(proof, Mapping) else None
                if scheme in ("recompute_batch_v3", "recompute_batch_v4"):
                    pre_state_commitment = compute_support_state_root_for_batch(
                        intents=intents,
                        balances=state.balances,
                        pools=state.pools,
                        lp_balances=state.lp_balances,
                    )
                else:
                    pre_state_commitment = compute_state_root(
                        balances=state.balances,
                        pools=state.pools,
                        lp_balances=state.lp_balances,
                    )
            except Exception as exc:
                return DexTxResult(ok=False, error=f"invalid state for commitment: {exc}")

            try:
                if scheme == "recompute_batch_v4":
                    op3 = create_settlement_operation(settlement).get("3")
                    if not isinstance(op3, dict):
                        raise TypeError("settlement operation must be an object")
                    settlement_obj_for_commit = normalize_settlement_op_for_commitment(op3)
                else:
                    settlement_obj_for_commit = _settlement_commitment_dict(settlement)
            except Exception as exc:
                return DexTxResult(ok=False, error=f"invalid settlement payload for commitment: {exc}")
            try:
                bounded_json_utf8_size(settlement_obj_for_commit, max_bytes=config.max_settlement_bytes)
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
        if settlement is None:
            # No DEX ops; state unchanged.
            return DexTxResult(ok=True, state=state, settlement=None)

        next_balances, next_pools, next_lp = apply_settlement_pure(
            settlement=settlement,
            balances=state.balances,
            pools=state.pools,
            lp_balances=state.lp_balances,
        )

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
            vault=state.vault,
            oracle=state.oracle,
            fee_accumulator=next_fee_state,
        )
        return DexTxResult(ok=True, state=next_state, settlement=settlement)
    except Exception as exc:
        return DexTxResult(ok=False, error="internal error")
