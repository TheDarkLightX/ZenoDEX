"""Per-endpoint handlers for the DEX dispatch registry.

Each handler is a free function ``(obj, ctx) -> (status, body)``. Handlers
are registered with ``_register`` at module import time so the
``DEX_ENDPOINT_REGISTRY`` in ``api_server_dex_dispatch.py`` is populated
before any HTTP request is served.

Behavior preservation is the only contract: each handler MUST return a
``(status, body)`` tuple that matches byte-for-byte what the legacy
``_maybe_handle_dex_api`` block at the cited line range returned. Tests in
``tests/integration/test_api_server_dex_api.py`` validate via the live
server; the dispatch seam in ``api_server.py`` is invisible to clients.

Import strategy: ``src.core.*`` and ``src.integration.*`` modules are
imported at top of file (eager). The exception is
``src.integration.api_server`` itself — that creates a cycle since
api_server imports api_server_dex_dispatch which imports this module.
Those (2) imports stay lazy inside the handler bodies that need them.
"""

from __future__ import annotations

import json
import os
import urllib.error
import urllib.parse
import urllib.request
from dataclasses import replace
from pathlib import Path
from typing import Any, Mapping, Optional, Sequence

from src.core.batch_clearing import apply_settlement_pure, compute_settlement
from src.core.dex_intent_auth_message import build_dex_intent_signing_dict_v1
from src.core.pokayoke_swap_guardrails import (
    SwapGuardrailContext,
    decide_swap_guardrails,
)
from src.core.pokayoke_swap_suggest import (
    suggest_amount_in_exact_in_cpmm,
    suggest_amount_in_for_impact_lt_bps,
    suggest_amount_in_for_required_slippage_le_bps,
)
from src.core.price_impact_preview import price_impact_preview
from src.core.proof_mining_claims import build_proof_mining_claim
from src.core.quote_receipts import verify_route_quote_receipt
from src.core.settlement_normal_form import normalize_settlement_op_for_commitment
from src.core.slippage_advisor import slippage_advice_exact_in_cpmm
from src.integration._dex_api_helpers import (
    EndpointSchema,
    IntFieldSpec,
    exact_out_split_quote_from_dict,
    parse_int_kwargs,
    parse_pools,
)
from src.integration.api_server_dex_dispatch import (
    DexRequestContext,
    DexResponse,
    _register,
)
from src.integration.api_server_settlement_parsers import (
    _parse_settlement_feature_extension_inputs_payload,
)
from src.integration.dex_snapshot import snapshot_from_state, state_from_snapshot
from src.integration.exact_in_route_certificate import (
    verify_exact_in_route_guarded_quote_packet_payload,
    verify_exact_in_route_oracle_contract_payload,
    verify_exact_in_route_rank_projection_packet_payload,
    verify_exact_in_route_true_key_interpretation_packet_payload,
)
from src.integration.lp_position_age_gate import apply_lp_mint_timestamps_after_settlement
from src.integration.operations import create_settlement_operation, parse_intents
from src.integration.proof_mining_claimability import (
    evaluate_proof_mining_claimability,
)
from src.integration.proof_mining_context import (
    build_proof_mining_context,
    proof_mining_context_to_obj,
)
from src.integration.settlement_feature_extension_packet import (
    build_settlement_feature_extension_packet,
    verify_settlement_feature_extension_packet_payload,
)
from src.integration.settlement_price_attestation import (
    build_settlement_spot_price_attestation,
    verify_settlement_spot_price_attestation_payload,
)
from src.integration.settlement_price_provenance import (
    SettlementSpotPriceEntry,
    SettlementSpotPricePacket,
    build_settlement_spot_price_packet,
    verify_settlement_spot_price_packet_payload,
)
from src.integration.zeno_ledger_v0 import hash_v0
from src.state.balances import BalanceTable
from src.state.nonces import validate_and_apply_intent_nonce_batch
from src.state.support_root import compute_support_state_root_for_batch


# ----------------------------------------------------------------------
# /api/dex/impact_preview
# Legacy: src/integration/api_server.py:1443-1490
# ----------------------------------------------------------------------
def _handle_impact_preview(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
    """No try/except: the dispatcher's catch-all converts any raised
    exception to ``(400, {"ok": False, "error": "impact_preview_error",
    "details": "request failed"})`` via the registered default_error_code.
    """
    reserve_in = int(obj.get("reserve_in", 0))
    reserve_out = int(obj.get("reserve_out", 0))
    amount_in = int(obj.get("amount_in", 0))
    fee_bps = int(obj.get("fee_bps", 0))
    pending_same_dir = int(obj.get("pending_volume_same_direction", 0))
    confidence_bps = int(obj.get("confidence_bps", 9500))

    preview = price_impact_preview(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_in=amount_in,
        fee_bps=fee_bps,
        pending_volume_same_direction=pending_same_dir,
        confidence_bps=confidence_bps,
    )
    return 200, {
        "ok": True,
        "preview": {
            "amount_out_isolated": int(preview.amount_out_isolated),
            "fee_amount": int(preview.fee_amount),
            "price_impact_bps": int(preview.price_impact_bps),
            "effective_price_e8": int(preview.effective_price_e8),
            "spot_price_e8": int(preview.spot_price_e8),
            "amount_out_best_case": int(preview.amount_out_best_case),
            "amount_out_worst_case": int(preview.amount_out_worst_case),
            "recommended_min_out": int(preview.recommended_min_out),
            "pending_volume_same_direction": int(preview.pending_volume_same_direction),
            "confidence_bps": int(preview.confidence_bps),
            "pending_volume_at_confidence": int(preview.pending_volume_at_confidence),
            "amount_out_at_confidence": int(preview.amount_out_at_confidence),
        },
    }


# ----------------------------------------------------------------------
# /api/dex/slippage_advice
# Legacy: src/integration/api_server.py:1492-1617
# ----------------------------------------------------------------------
def _handle_slippage_advice(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
    try:
        reserve_in = int(obj.get("reserve_in", 0))
        reserve_out = int(obj.get("reserve_out", 0))
        amount_in = int(obj.get("amount_in", 0))
        fee_bps = int(obj.get("fee_bps", 0))
        pending_same_dir = int(obj.get("pending_volume_same_direction", 0))
        confidence_bps = int(obj.get("confidence_bps", 9500))
        max_attacker_amount_in = int(obj.get("max_attacker_amount_in", 5000))
        user_slippage_bps_raw = obj.get("user_slippage_bps", None)
        user_slippage_bps: int | None
        if user_slippage_bps_raw is None:
            user_slippage_bps = None
        else:
            user_slippage_bps = int(user_slippage_bps_raw)

        raw_opts = obj.get("slippage_options_bps")
        slippage_options_bps: list[int] | None
        if isinstance(raw_opts, list):
            collected_opts: list[int] = []
            for x in raw_opts:
                try:
                    collected_opts.append(int(x))
                except Exception:
                    continue
            slippage_options_bps = collected_opts
        else:
            slippage_options_bps = None

        advice = slippage_advice_exact_in_cpmm(
            reserve_in=reserve_in,
            reserve_out=reserve_out,
            fee_bps=fee_bps,
            amount_in=amount_in,
            pending_volume_same_direction=pending_same_dir,
            confidence_bps=confidence_bps,
            slippage_options_bps=slippage_options_bps,
            max_attacker_amount_in=max_attacker_amount_in,
        )

        pokayoke = None
        if user_slippage_bps is not None:
            inner_ctx = SwapGuardrailContext(
                price_impact_bps=int(advice.price_impact_bps),
                slippage_advice_status=str(advice.status),
                required_slippage_bps=int(advice.required_slippage_bps),
                recommended_slippage_bps_revert_safe=(
                    int(advice.recommended_slippage_bps_revert_safe)
                    if advice.recommended_slippage_bps_revert_safe is not None
                    else None
                ),
                recommended_slippage_bps_mev_safe=(
                    int(advice.recommended_slippage_bps_mev_safe)
                    if advice.recommended_slippage_bps_mev_safe is not None
                    else None
                ),
                recommended_slippage_bps=(
                    int(advice.recommended_slippage_bps) if advice.recommended_slippage_bps is not None else None
                ),
            )
            decision = decide_swap_guardrails(ctx=inner_ctx, user_slippage_bps=int(user_slippage_bps))
            pokayoke = {
                "action": str(decision.action),
                "reasons": list(decision.reasons),
                "messages": list(decision.messages),
                "typed_confirm_phrase": decision.typed_confirm_phrase,
            }
        return 200, {
            "ok": True,
            "advice": {
                "best_amount_out": int(advice.best_amount_out),
                "price_impact_bps": int(advice.price_impact_bps),
                "amount_out_at_confidence": int(advice.amount_out_at_confidence),
                "pending_volume_at_confidence": int(advice.pending_volume_at_confidence),
                "confidence_bps": int(advice.confidence_bps),
                "required_slippage_bps": int(advice.required_slippage_bps),
                "recommended_slippage_bps_revert_safe": (
                    int(advice.recommended_slippage_bps_revert_safe)
                    if advice.recommended_slippage_bps_revert_safe is not None
                    else None
                ),
                "recommended_slippage_bps_mev_safe": (
                    int(advice.recommended_slippage_bps_mev_safe)
                    if advice.recommended_slippage_bps_mev_safe is not None
                    else None
                ),
                "recommended_slippage_bps": (
                    int(advice.recommended_slippage_bps)
                    if advice.recommended_slippage_bps is not None
                    else None
                ),
                "status": str(advice.status),
                "pokayoke": pokayoke,
                "options": [
                    {
                        "slippage_bps": int(o.slippage_bps),
                        "min_amount_out": int(o.min_amount_out),
                        "is_revert_safe_at_confidence": bool(o.is_revert_safe_at_confidence),
                        "sandwich_status": str(o.sandwich_status),
                        "sandwich_max_profit": int(o.sandwich_max_profit),
                        "sandwich_attacker_amount_in": int(o.sandwich_attacker_amount_in),
                        "sandwich_victim_amount_out": int(o.sandwich_victim_amount_out),
                        "sandwich_scanned_max_attacker_amount_in": int(o.sandwich_scanned_max_attacker_amount_in),
                    }
                    for o in advice.options
                ],
            },
        }
    except Exception:
        return 400, {"ok": False, "error": "slippage_advice_error", "details": "request failed"}


# ----------------------------------------------------------------------
# /api/dex/pokayoke_swap_suggest
# Legacy: src/integration/api_server.py:1619-1732
# ----------------------------------------------------------------------
def _handle_pokayoke_swap_suggest(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
    try:
        reserve_in = int(obj.get("reserve_in", 0))
        reserve_out = int(obj.get("reserve_out", 0))
        amount_in = int(obj.get("amount_in", 0))
        fee_bps = int(obj.get("fee_bps", 0))
        pending_same_dir = int(obj.get("pending_volume_same_direction", 0))
        confidence_bps = int(obj.get("confidence_bps", 9500))

        user_slippage_bps_raw = obj.get("user_slippage_bps", None)
        user_slippage_bps: int | None
        if user_slippage_bps_raw is None:
            user_slippage_bps = None
        else:
            user_slippage_bps = int(user_slippage_bps_raw)

        raw_opts = obj.get("slippage_options_bps")
        opts: list[int] = []
        if isinstance(raw_opts, list):
            for x in raw_opts:
                try:
                    v = int(x)
                except Exception:
                    continue
                if v < 0 or v > 10_000:
                    continue
                opts.append(int(v))
        max_opt = max(opts) if opts else None

        impact_5 = suggest_amount_in_for_impact_lt_bps(
            reserve_in=reserve_in,
            reserve_out=reserve_out,
            fee_bps=fee_bps,
            amount_in=amount_in,
            target_impact_bps=500,
            window=256,
        )
        impact_1 = suggest_amount_in_for_impact_lt_bps(
            reserve_in=reserve_in,
            reserve_out=reserve_out,
            fee_bps=fee_bps,
            amount_in=amount_in,
            target_impact_bps=100,
            window=256,
        )

        req_user = (
            suggest_amount_in_for_required_slippage_le_bps(
                reserve_in=reserve_in,
                reserve_out=reserve_out,
                fee_bps=fee_bps,
                amount_in=amount_in,
                pending_volume_same_direction=pending_same_dir,
                confidence_bps=confidence_bps,
                target_required_slippage_bps=int(user_slippage_bps),
                window=256,
            )
            if user_slippage_bps is not None
            else None
        )
        req_max_opt = (
            suggest_amount_in_for_required_slippage_le_bps(
                reserve_in=reserve_in,
                reserve_out=reserve_out,
                fee_bps=fee_bps,
                amount_in=amount_in,
                pending_volume_same_direction=pending_same_dir,
                confidence_bps=confidence_bps,
                target_required_slippage_bps=int(max_opt),
                window=256,
            )
            if max_opt is not None
            else None
        )

        def _as_obj(sugg: Any) -> Any:
            if sugg is None:
                return None
            return {
                "kind": str(sugg.kind),
                "target_bps": int(sugg.target_bps),
                "suggested_amount_in": int(sugg.suggested_amount_in) if sugg.suggested_amount_in is not None else None,
                "status": str(sugg.status),
                "eval_count": int(sugg.eval_count),
                "baseline_value_bps": int(sugg.baseline_value_bps),
                "suggested_value_bps": int(sugg.suggested_value_bps) if sugg.suggested_value_bps is not None else None,
            }

        return 200, {
            "ok": True,
            "suggestions": {
                "impact_lt_500_bps": _as_obj(impact_5),
                "impact_lt_100_bps": _as_obj(impact_1),
                "required_slippage_le_user_bps": _as_obj(req_user),
                "required_slippage_le_max_option_bps": _as_obj(req_max_opt),
            },
        }
    except Exception:
        return 400, {"ok": False, "error": "pokayoke_swap_suggest_error", "details": "request failed"}


# ----------------------------------------------------------------------
# /api/dex/pokayoke_swap_suggest_heavy
# Legacy: src/integration/api_server.py:1734-1828
# ----------------------------------------------------------------------
def _handle_pokayoke_swap_suggest_heavy(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
    try:
        reserve_in = int(obj.get("reserve_in", 0))
        reserve_out = int(obj.get("reserve_out", 0))
        amount_in = int(obj.get("amount_in", 0))
        fee_bps = int(obj.get("fee_bps", 0))
        pending_same_dir = int(obj.get("pending_volume_same_direction", 0))
        confidence_bps = int(obj.get("confidence_bps", 9500))

        user_slippage_bps_raw = obj.get("user_slippage_bps", None)
        if user_slippage_bps_raw is None:
            raise ValueError("user_slippage_bps is required")
        user_slippage_bps = int(user_slippage_bps_raw)

        raw_opts = obj.get("slippage_options_bps")
        opts: list[int] | None
        if isinstance(raw_opts, list):
            opts = []
            for x in raw_opts:
                try:
                    v = int(x)
                except Exception:
                    continue
                if v < 0 or v > 10_000:
                    continue
                opts.append(int(v))
        else:
            opts = None

        max_attacker_amount_in_raw = obj.get("max_attacker_amount_in", 2000)
        max_attacker_amount_in = int(max_attacker_amount_in_raw)
        if max_attacker_amount_in < 0 or max_attacker_amount_in > 50_000:
            raise ValueError("max_attacker_amount_in must be in [0, 50_000]")

        max_evals_raw = obj.get("max_evals", 16)
        max_evals = int(max_evals_raw)
        if max_evals <= 0 or max_evals > 64:
            raise ValueError("max_evals must be in [1, 64]")

        raw_targets = obj.get("target_actions")
        targets: tuple[str, ...]
        if isinstance(raw_targets, list):
            cleaned: list[str] = []
            for x in raw_targets:
                s = str(x or "").strip().lower()
                if s in {"confirm", "allow"} and s not in cleaned:
                    cleaned.append(s)
            targets = tuple(cleaned) if cleaned else ("confirm", "allow")
        else:
            targets = ("confirm", "allow")

        rows = suggest_amount_in_exact_in_cpmm(
            reserve_in=reserve_in,
            reserve_out=reserve_out,
            fee_bps=fee_bps,
            amount_in=amount_in,
            pending_volume_same_direction=pending_same_dir,
            confidence_bps=confidence_bps,
            slippage_options_bps=opts,
            max_attacker_amount_in=max_attacker_amount_in,
            user_slippage_bps=user_slippage_bps,
            max_evals=max_evals,
            target_actions=targets,
        )

        def _as_obj(sugg: Any) -> Any:
            return {
                "target_action": str(sugg.target_action),
                "suggested_amount_in": int(sugg.suggested_amount_in) if sugg.suggested_amount_in is not None else None,
                "status": str(sugg.status),
                "eval_count": int(sugg.eval_count),
                "baseline_action": str(sugg.baseline_action),
                "suggested_action": str(sugg.suggested_action) if sugg.suggested_action is not None else None,
                "baseline_reasons": [str(x) for x in (sugg.baseline_reasons or ())],
                "suggested_reasons": [str(x) for x in (sugg.suggested_reasons or ())] if sugg.suggested_reasons is not None else None,
            }

        return 200, {"ok": True, "suggestions": [_as_obj(s) for s in rows]}
    except Exception:
        return 400, {"ok": False, "error": "pokayoke_swap_suggest_heavy_error", "details": "request failed"}


# ----------------------------------------------------------------------
# /api/dex/proof_mining_status
# Legacy: src/integration/api_server.py:1830-1873
# ----------------------------------------------------------------------
def _canonical_asset_id(value: Any, *, name: str) -> str:
    text = str(value or "").strip().lower()
    if text.startswith("0x"):
        text = text[2:]
    if len(text) != 64 or any(ch not in "0123456789abcdef" for ch in text):
        raise ValueError(f"{name} must be a canonical 32-byte hex asset")
    return "0x" + text


def _canonical_pubkey_48(value: Any, *, name: str) -> str:
    text = str(value or "").strip().lower()
    if text.startswith("0x"):
        text = text[2:]
    if len(text) != 96 or any(ch not in "0123456789abcdef" for ch in text):
        raise ValueError(f"{name} must be a canonical 48-byte hex pubkey")
    return "0x" + text


def _copy_balances_for_template(source: BalanceTable) -> BalanceTable:
    copied = BalanceTable()
    for (pubkey, asset), amount in source.get_all_balances().items():
        copied.set(str(pubkey), str(asset), int(amount))
    return copied


def _load_latest_writer_snapshot_from_url_for_template(url: str) -> Mapping[str, Any]:
    url_text = str(url).strip()
    parsed = urllib.parse.urlparse(url_text)
    if parsed.scheme not in {"http", "https"} or not parsed.netloc:
        raise ValueError("writer snapshot URL must be absolute http or https")
    req = urllib.request.Request(url_text, headers={"Accept": "application/json"})
    # URL scheme and host are validated above.
    with urllib.request.urlopen(req, timeout=2.0) as resp:  # nosec B310
        payload = json.loads(resp.read().decode("utf-8"))
    if not isinstance(payload, Mapping) or payload.get("ok") is not True:
        raise ValueError("writer snapshot endpoint returned non-ok payload")
    snapshot_obj = payload.get("snapshot")
    if not isinstance(snapshot_obj, Mapping):
        raise ValueError("writer snapshot endpoint missing snapshot object")
    return snapshot_obj


def _load_latest_writer_snapshot_from_file_for_template(data_dir_raw: Any) -> Mapping[str, Any]:
    data_dir = Path(str(data_dir_raw)).resolve()
    live_state_path = data_dir / "live_state.json"
    live_state = json.loads(live_state_path.read_text(encoding="utf-8"))
    if not isinstance(live_state, Mapping):
        raise ValueError("live_state.json must decode to an object")
    rel = live_state.get("latest_snapshot_path")
    if not isinstance(rel, str) or not rel:
        raise ValueError("live_state.latest_snapshot_path missing")
    snapshot_path = Path(rel)
    if not snapshot_path.is_absolute():
        snapshot_path = data_dir / snapshot_path
    snapshot_path = snapshot_path.resolve()
    try:
        snapshot_path.relative_to(data_dir)
    except ValueError as exc:
        raise ValueError("live_state.latest_snapshot_path escapes writer data dir") from exc
    snapshot_obj = json.loads(snapshot_path.read_text(encoding="utf-8"))
    if not isinstance(snapshot_obj, Mapping):
        raise ValueError("latest snapshot must decode to an object")
    if snapshot_obj.get("schema") == "zenodex/tau_app_state/v1":
        dex_state = snapshot_obj.get("dex_state")
        if not isinstance(dex_state, Mapping):
            raise ValueError("tau app state dex_state must be an object")
        return dex_state
    return snapshot_obj


def _load_latest_writer_snapshot_for_template(ctx: DexRequestContext) -> Mapping[str, Any]:
    data_dir_raw = getattr(ctx.server, "local_testnet_writer_data_dir", None)
    if data_dir_raw is not None:
        return _load_latest_writer_snapshot_from_file_for_template(data_dir_raw)

    snapshot_url = os.environ.get(
        "ZENO_LEDGER_WRITER_SNAPSHOT_URL",
        "http://zeno-ledger-writer:8787/api/dex/snapshot",
    ).strip()
    if snapshot_url:
        try:
            return _load_latest_writer_snapshot_from_url_for_template(snapshot_url)
        except (OSError, ValueError, urllib.error.URLError, TimeoutError, json.JSONDecodeError):
            pass

    data_dir_raw = os.environ.get("ZENO_LEDGER_WRITER_DATA_DIR", "/app/data/local-testnet/node-writer")
    return _load_latest_writer_snapshot_from_file_for_template(data_dir_raw)


def _template_batch_commitment(signing_dicts: Sequence[Mapping[str, Any]], settlement_op: Mapping[str, Any]) -> str:
    from src.state.canonical import (
        CANONICAL_ENCODING_VERSION,
        canonical_json_bytes,
        domain_sep_bytes,
        sha256_hex,
    )

    payload = {
        "schema": "zenodex_batch",
        "schema_version": 1,
        "canonical_encoding_version": CANONICAL_ENCODING_VERSION,
        "intents": [dict(row) for row in signing_dicts],
        "settlement": dict(settlement_op),
    }
    return str(sha256_hex(domain_sep_bytes("dex_batch", version=1) + canonical_json_bytes(payload)))


def _template_stable_digest(payload: Mapping[str, Any]) -> str:
    from src.state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex

    return str(
        sha256_hex(
            domain_sep_bytes("proof_mining_payout_template_defaults", version=1)
            + canonical_json_bytes(dict(payload))
        )
    )


def _template_non_negative_int(value: Any, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise ValueError(f"{name} must be a non-negative int")
    return int(value)


def _template_block_timestamp(obj: Mapping[str, Any], intent: Mapping[str, Any]) -> int:
    raw = obj.get("block_timestamp")
    if raw is not None:
        return _template_non_negative_int(raw, name="block_timestamp")
    created_at = intent.get("created_at")
    if isinstance(created_at, int) and not isinstance(created_at, bool) and created_at >= 0:
        return int(created_at)
    raise ValueError("block_timestamp or intent.created_at required")


def _handle_proof_mining_payout_template(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
    if os.environ.get("ZENODEX_ENV", "").strip().lower() not in {"local", "test", "local-testnet", ""}:
        return 403, {"ok": False, "error": "local_testnet_only"}
    try:
        sender = _canonical_pubkey_48(obj.get("tx_sender_pubkey"), name="tx_sender_pubkey")
        signed_intent = obj.get("signed_intent")
        if not isinstance(signed_intent, Mapping):
            return 400, {"ok": False, "error": "bad_signed_intent"}
        raw_intent = signed_intent.get("intent", signed_intent)
        if not isinstance(raw_intent, Mapping):
            return 400, {"ok": False, "error": "bad_intent"}
        intent = dict(raw_intent)
        signature = signed_intent.get("signature", intent.get("signature"))
        if not isinstance(signature, str) or not signature:
            return 400, {"ok": False, "error": "missing_signature"}
        intent["signature"] = signature
        if str(intent.get("sender_pubkey", "")).lower() != sender:
            return 400, {"ok": False, "error": "sender_mismatch"}
        intent_for_proof = {k: v for k, v in intent.items() if k != "signature"}

        chain_id = str(obj.get("chain_id") or os.environ.get("TAU_DEX_CHAIN_ID") or "zeno-ledger-localtest-v0")
        try:
            tx_block_timestamp = _template_block_timestamp(obj, intent)
        except ValueError:
            return 400, {"ok": False, "error": "bad_block_timestamp"}
        snapshot_obj = obj.get("pre_state_snapshot")
        if snapshot_obj is None:
            snapshot_obj = _load_latest_writer_snapshot_for_template(ctx)
        if not isinstance(snapshot_obj, Mapping):
            return 400, {"ok": False, "error": "bad_pre_state_snapshot"}
        state = state_from_snapshot(snapshot_obj)

        faucet_mint = obj.get("faucet_mint", [])
        if faucet_mint is None:
            faucet_mint = []
        if not isinstance(faucet_mint, list):
            return 400, {"ok": False, "error": "bad_faucet_mint"}
        balances = _copy_balances_for_template(state.balances)
        for index, entry in enumerate(faucet_mint):
            if not isinstance(entry, Mapping):
                return 400, {"ok": False, "error": "bad_faucet_mint_entry", "index": index}
            pubkey = _canonical_pubkey_48(entry.get("pubkey", sender), name=f"faucet_mint[{index}].pubkey")
            asset = _canonical_asset_id(entry.get("asset"), name=f"faucet_mint[{index}].asset")
            amount = entry.get("amount")
            if not isinstance(amount, int) or isinstance(amount, bool) or amount <= 0:
                return 400, {"ok": False, "error": "bad_faucet_mint_amount", "index": index}
            balances.set(pubkey, asset, int(balances.get(pubkey, asset)) + int(amount))
        proof_state = replace(state, balances=balances)

        operations_without_proof = {"5": [intent_for_proof]}
        intents = parse_intents(operations_without_proof)
        settlement = compute_settlement(
            intents=intents,
            pools=proof_state.pools,
            balances=proof_state.balances,
            lp_balances=proof_state.lp_balances,
        )
        settlement_op = create_settlement_operation(settlement)["6"]
        settlement_op_for_proof = json.loads(json.dumps(settlement_op))
        signing_dicts = [build_dex_intent_signing_dict_v1(intent_obj) for intent_obj in intents]
        settlement_commit = normalize_settlement_op_for_commitment(settlement_op)
        pre_state_commitment = compute_support_state_root_for_batch(
            intents=intents,
            balances=proof_state.balances,
            pools=proof_state.pools,
            lp_balances=proof_state.lp_balances,
            nonces=proof_state.nonces,
        )
        batch_commitment = _template_batch_commitment(signing_dicts, settlement_commit)
        proof = {
            "scheme": "recompute_batch_v4",
            "pre_state_commitment": pre_state_commitment,
            "batch_commitment": batch_commitment,
            "pre_state_snapshot": snapshot_from_state(proof_state).data,
            "operations": {"5": [intent_for_proof], "6": settlement_op_for_proof},
        }
        settlement_op["proof"] = proof

        next_balances, next_pools, next_lp = apply_settlement_pure(
            settlement=settlement,
            balances=proof_state.balances,
            pools=proof_state.pools,
            lp_balances=proof_state.lp_balances,
        )
        lp_age_err = apply_lp_mint_timestamps_after_settlement(
            lp_balances=next_lp,
            settlement=settlement,
            block_timestamp=tx_block_timestamp,
            duration_risk_policy=None,
        )
        if lp_age_err is not None:
            return 400, {"ok": False, "error": "lp_duration_risk_update_failed", "details": lp_age_err}
        nonce_ok, nonce_err, next_nonces = validate_and_apply_intent_nonce_batch(
            nonces=proof_state.nonces,
            intents=intents,
            require_all_nonces=True,
        )
        if not nonce_ok or next_nonces is None:
            return 400, {"ok": False, "error": "bad_intent_nonce", "details": nonce_err or "nonce rejected"}
        next_state = replace(
            proof_state,
            balances=next_balances,
            pools=next_pools,
            lp_balances=next_lp,
            nonces=next_nonces,
        )
        context = build_proof_mining_context(
            chain_id=chain_id,
            prev_state_hash=pre_state_commitment,
            batch_hash=batch_commitment,
            proof=proof,
            next_state=next_state,
            proof_scheme="recompute_batch_v4",
        )

        reward_pool = os.environ.get("TAU_DEX_PROOF_MINING_POOL_PUBKEY", "").strip()
        if not reward_pool:
            reward_pool = str(obj.get("reward_pool_pubkey", "")).strip()
        reward_pool = _canonical_pubkey_48(reward_pool, name="reward_pool_pubkey")
        reward_asset = obj.get("reward_asset_id")
        if reward_asset is None:
            reward_asset = os.environ.get("TAU_DEX_PROOF_MINING_REWARD_ASSET_ID", "").strip()
        if not reward_asset:
            token_symbol = os.environ.get("TAU_DEX_TOKEN_SYMBOL", "ZDEX").strip() or "ZDEX"
            reward_asset = hash_v0("testnet_bundle_token_asset", {"chain_id": chain_id, "symbol": token_symbol})
        reward_asset = _canonical_asset_id(reward_asset, name="reward_asset_id")
        reward_pool_before = int(state.balances.get(reward_pool, reward_asset))
        if reward_pool_before <= 0:
            return 409, {
                "ok": False,
                "error": "reward_pool_unfunded",
                "reward_pool_pubkey": reward_pool,
                "reward_asset_id": reward_asset,
            }

        base_reward = int(obj.get("base_reward", 8))
        epoch = int(obj.get("epoch", 1))
        proposal_slot = int(obj.get("proposal_slot", 0))
        prover_id = int(obj.get("prover_id", 1))
        improvement_u64 = int(obj.get("improvement_u64", 1))
        default_id_digest = _template_stable_digest(
            {
                "chain_id": chain_id,
                "sender": sender,
                "block_timestamp": tx_block_timestamp,
                "intent": intent_for_proof,
                "signature": signature,
                "faucet_mint": faucet_mint,
                "pre_state_commitment": context.prev_state_hash,
                "batch_hash": context.batch_hash,
                "witness_hash": context.witness_hash,
                "dex_hash_after": context.dex_hash_after,
                "reward_pool_pubkey": reward_pool,
                "reward_asset_id": reward_asset,
                "reward_pool_before": reward_pool_before,
                "base_reward": base_reward,
                "epoch": epoch,
                "proposal_slot": proposal_slot,
                "prover_id": prover_id,
                "improvement_u64": improvement_u64,
            }
        )
        job_digest = str(obj.get("job_digest") or f"local-proof-mining:{default_id_digest}")
        round_id = str(obj.get("round_id") or f"local-proof-mining-round:{default_id_digest}")
        claim = build_proof_mining_claim(
            round_obj={
                "schema": "zenodex/improvement_bounty_round/v1",
                "ok": True,
                "job_digest": job_digest,
                "winner": {
                    "miner_id": sender,
                    "witness_sha256": context.witness_hash,
                    "improvement_u64": improvement_u64,
                },
                "candidates": [],
                "argmax_certificate": None,
            },
            round_id=round_id,
            reward_pool_before=reward_pool_before,
            base_reward=base_reward,
            epoch=epoch,
            proposal_slot=proposal_slot,
            prover_id=prover_id,
            chain_id=chain_id,
            prev_state_hash=context.prev_state_hash,
            batch_hash=context.batch_hash,
            dex_hash_after=context.dex_hash_after,
        )
        tx = {
            "tx_id": str(obj.get("tx_id") or f"proof-mining-payout:{claim['claim_hash']}"),
            "tx_sender_pubkey": sender,
            "block_timestamp": tx_block_timestamp,
            "operations": {
                **({"7": {"mint": faucet_mint}} if faucet_mint else {}),
                "5": [intent],
                "6": settlement_op,
                "10": {
                    "module": "ZenoProofMining",
                    "action": "submit_proof",
                    "claim": claim,
                    "recipient_pubkey": sender,
                },
            },
        }
        status_request = {
            "app_state_json": json.dumps(
                {
                    "schema": "zenodex/tau_app_state/v1",
                    "version": 1,
                    "proof_mining": None,
                },
                separators=(",", ":"),
                sort_keys=True,
            ),
            "chain_balances": {
                reward_pool: {
                    reward_asset: reward_pool_before,
                },
            },
            "claim": claim,
            "proof_mining_context": proof_mining_context_to_obj(context),
            "tx_sender_pubkey": sender,
            "expected_proposal_hash": claim["body"]["proposal_hash"],
            "reward_pool_pubkey": reward_pool,
        }
        return 200, {
            "ok": True,
            "tx": tx,
            "status_request": status_request,
            "reward_pool_pubkey": reward_pool,
            "reward_asset_id": reward_asset,
            "reward_pool_before": reward_pool_before,
        }
    except Exception as exc:
        return 400, {"ok": False, "error": "proof_mining_payout_template_error", "details": str(exc)}


def _handle_proof_mining_status(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
    claim_artifact = obj.get("claim")
    chain_balances = obj.get("chain_balances", {})
    tx_sender_pubkey = str(obj.get("tx_sender_pubkey", ""))
    expected_proposal_hash = str(obj.get("expected_proposal_hash", ""))
    proof_mining_context = obj.get("proof_mining_context")
    app_state_json = obj.get("app_state_json", "")
    if not isinstance(claim_artifact, dict):
        return 400, {"ok": False, "error": "bad_claim"}
    if not isinstance(chain_balances, dict):
        return 400, {"ok": False, "error": "bad_chain_balances"}
    if proof_mining_context is not None and not isinstance(proof_mining_context, dict):
        return 400, {"ok": False, "error": "bad_proof_mining_context"}
    if not isinstance(app_state_json, str):
        return 400, {"ok": False, "error": "bad_app_state_json"}
    if not tx_sender_pubkey:
        return 400, {"ok": False, "error": "missing_tx_sender_pubkey"}
    if not expected_proposal_hash:
        return 400, {"ok": False, "error": "missing_expected_proposal_hash"}
    try:
        reward_pool_pubkey = (
            os.environ.get("TAU_DEX_PROOF_MINING_POOL_PUBKEY", "").strip()
            or str(obj.get("reward_pool_pubkey", "")).strip()
            or None
        )
        status = evaluate_proof_mining_claimability(
            reward_pool_pubkey=reward_pool_pubkey,
            app_state_json=app_state_json,
            chain_balances=chain_balances,
            claim_artifact=claim_artifact,
            tx_sender_pubkey=tx_sender_pubkey,
            expected_proposal_hash=expected_proposal_hash,
            proof_mining_context_obj=proof_mining_context,
        )
        return 200, {"ok": True, "status": status.to_public_dict()}
    except Exception:
        return 400, {"ok": False, "error": "proof_mining_status_error", "details": "request failed"}


_register("/api/dex/impact_preview", _handle_impact_preview, default_error_code="impact_preview_error")
_register("/api/dex/slippage_advice", _handle_slippage_advice, default_error_code="slippage_advice_error")
_register("/api/dex/pokayoke_swap_suggest", _handle_pokayoke_swap_suggest, default_error_code="pokayoke_swap_suggest_error")
_register("/api/dex/pokayoke_swap_suggest_heavy", _handle_pokayoke_swap_suggest_heavy, default_error_code="pokayoke_swap_suggest_heavy_error")
_register("/api/dex/proof_mining_payout_template", _handle_proof_mining_payout_template, default_error_code="proof_mining_payout_template_error")
_register("/api/dex/proof_mining_status", _handle_proof_mining_status, default_error_code="proof_mining_status_error")


# ======================================================================
# PR2 Batch 1 — verify_exact_in_route_* and verify_quote_receipt.
# These are all variations on "parse a dict-shaped payload, call a
# verifier, return {ok, error}". A factory pattern replaces the
# copy-paste.
# ======================================================================
def _make_simple_verifier(
    *,
    payload_key: str,
    importer: Any,
    error_code: str,
) -> Any:
    """Build a handler for the (payload_key -> importer() -> ok/err) shape.

    ``importer`` is a zero-arg callable that returns the verifier
    function from a lazy import. This preserves the legacy import-cycle
    guard (imports happen only when the endpoint is invoked).
    """

    def _handler(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
        payload = obj.get(payload_key)
        if not isinstance(payload, dict):
            return 400, {"ok": False, "error": f"bad_{payload_key}"}
        try:
            verifier = importer()
            ok, err = verifier(payload)
            return 200, {"ok": bool(ok), "error": err}
        except Exception:
            return 400, {"ok": False, "error": error_code, "details": "request failed"}

    return _handler


def _import_verify_exact_in_route_oracle_contract_payload() -> Any:

    return verify_exact_in_route_oracle_contract_payload


def _import_verify_exact_in_route_guarded_quote_packet_payload() -> Any:

    return verify_exact_in_route_guarded_quote_packet_payload


def _import_verify_exact_in_route_rank_projection_packet_payload() -> Any:

    return verify_exact_in_route_rank_projection_packet_payload


def _import_verify_exact_in_route_true_key_interpretation_packet_payload() -> Any:

    return verify_exact_in_route_true_key_interpretation_packet_payload


_register(
    "/api/dex/verify_exact_in_route_oracle_contract",
    _make_simple_verifier(
        payload_key="contract",
        importer=_import_verify_exact_in_route_oracle_contract_payload,
        error_code="verify_exact_in_route_oracle_contract_error",
    ),
)
_register(
    "/api/dex/verify_exact_in_route_guarded_quote_packet",
    _make_simple_verifier(
        payload_key="packet",
        importer=_import_verify_exact_in_route_guarded_quote_packet_payload,
        error_code="verify_exact_in_route_guarded_quote_packet_error",
    ),
)
_register(
    "/api/dex/verify_exact_in_route_rank_projection_packet",
    _make_simple_verifier(
        payload_key="packet",
        importer=_import_verify_exact_in_route_rank_projection_packet_payload,
        error_code="verify_exact_in_route_rank_projection_packet_error",
    ),
)
_register(
    "/api/dex/verify_exact_in_route_true_key_interpretation_packet",
    _make_simple_verifier(
        payload_key="packet",
        importer=_import_verify_exact_in_route_true_key_interpretation_packet_payload,
        error_code="verify_exact_in_route_true_key_interpretation_packet_error",
    ),
)


# /api/dex/verify_quote_receipt — same shape but takes `expected_quote_epoch`
# and pools as extra inputs, so it can't use the simple factory.
def _handle_verify_quote_receipt(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
    rec = obj.get("receipt")
    if not isinstance(rec, dict):
        return 400, {"ok": False, "error": "bad_receipt"}
    expected_quote_epoch = obj.get("expected_quote_epoch")
    if expected_quote_epoch is not None:
        if (
            not isinstance(expected_quote_epoch, int)
            or isinstance(expected_quote_epoch, bool)
            or expected_quote_epoch < 0
        ):
            return 400, {"ok": False, "error": "bad_expected_quote_epoch"}
    try:
        pools_by_id = parse_pools(obj)
        ok, err = verify_route_quote_receipt(
            rec,
            pools_by_id=pools_by_id,
            expected_quote_epoch=(None if expected_quote_epoch is None else int(expected_quote_epoch)),
        )
        return 200, {"ok": bool(ok), "error": str(err)}
    except Exception:
        return 400, {"ok": False, "error": "verify_error", "details": "request failed"}


_register("/api/dex/verify_quote_receipt", _handle_verify_quote_receipt)


# ======================================================================
# PR2 Batch 2 — verify_exact_out_many_pool_* and verify_exact_out_route_*.
# Policy-aware verifier shape: returns {"ok": True} or {"ok": True,
# "quote_policy": "..."} on success; on failure, includes the default
# error text and optionally the quote_policy.
# ======================================================================
def _make_policy_verifier(
    *,
    payload_key: str,
    importer: Any,
    error_code: str,
    default_error: str,
    quote_policy: Optional[str] = None,
) -> Any:
    """Build a handler for policy-aware verify endpoints.

    Matches the legacy shape exactly:
      success: {"ok": True} + optional {"quote_policy": policy}
      failure: {"ok": False, "error": err or default_error} + optional {"quote_policy"}
      exception: 400, {"ok": False, "error": error_code, "details": "request failed"}
    """

    def _handler(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
        payload = obj.get(payload_key)
        if not isinstance(payload, dict):
            return 400, {"ok": False, "error": f"bad_{payload_key}"}
        try:
            verifier = importer()
            ok, err = verifier(payload)
            if ok:
                body: dict[str, Any] = {"ok": True}
                if quote_policy is not None:
                    body["quote_policy"] = quote_policy
                return 200, body
            else:
                fail_body: dict[str, Any] = {"ok": False, "error": err or default_error}
                if quote_policy is not None:
                    fail_body["quote_policy"] = quote_policy
                return 200, fail_body
        except Exception:
            return 400, {"ok": False, "error": error_code, "details": "request failed"}

    return _handler


def _import_exact_out_route_certificate(name: str) -> Any:
    """Lazy import of any verifier from src.integration.exact_out_route_certificate."""

    def _importer() -> Any:
        import importlib  # pylint: disable=import-outside-toplevel

        module = importlib.import_module("src.integration.exact_out_route_certificate")
        return getattr(module, name)

    return _importer


# (endpoint_path, payload_key, verifier_fn_name, error_code, default_error, quote_policy)
_EXACT_OUT_POLICY_VERIFIERS: tuple[tuple[str, str, str, str, str, Optional[str]], ...] = (
    (
        "/api/dex/verify_exact_out_many_pool_guarded_quote_packet",
        "packet",
        "verify_exact_out_many_pool_guarded_quote_packet_payload",
        "verify_exact_out_many_pool_guarded_quote_packet_error",
        "guarded quote packet verification failed",
        None,
    ),
    (
        "/api/dex/verify_exact_out_many_pool_certified_winner_packet",
        "packet",
        "verify_exact_out_many_pool_certified_winner_packet_payload",
        "verify_exact_out_many_pool_certified_winner_packet_error",
        "certified winner packet verification failed",
        None,
    ),
    (
        "/api/dex/verify_exact_out_many_pool_repaired_advisory_quote_packet",
        "packet",
        "verify_exact_out_many_pool_repaired_advisory_quote_packet_payload",
        "verify_exact_out_many_pool_repaired_advisory_quote_packet_error",
        "repaired advisory quote packet verification failed",
        None,
    ),
    (
        "/api/dex/verify_exact_out_many_pool_repaired_full_domain_certified_packet",
        "packet",
        "verify_exact_out_many_pool_repaired_full_domain_certified_packet_payload",
        "verify_exact_out_many_pool_repaired_full_domain_certified_packet_error",
        "repaired full-domain certified packet verification failed",
        "repaired_full_domain_certified_v1",
    ),
    (
        "/api/dex/verify_exact_out_many_pool_repaired_key_cover_packet",
        "packet",
        "verify_exact_out_many_pool_repaired_key_cover_packet_payload",
        "verify_exact_out_many_pool_repaired_key_cover_packet_error",
        "repaired key-cover packet verification failed",
        "repaired_key_cover_v1",
    ),
    (
        "/api/dex/verify_exact_out_many_pool_repaired_key_cover_interpretation_packet",
        "packet",
        "verify_exact_out_many_pool_repaired_key_cover_interpretation_packet_payload",
        "verify_exact_out_many_pool_repaired_key_cover_interpretation_packet_error",
        "repaired key-cover interpretation packet verification failed",
        "repaired_key_cover_interpretation_v1",
    ),
    (
        "/api/dex/verify_exact_out_many_pool_certified_advisory_packet",
        "packet",
        "verify_exact_out_many_pool_certified_advisory_packet_payload",
        "verify_exact_out_many_pool_certified_advisory_packet_error",
        "certified advisory packet verification failed",
        None,
    ),
    (
        "/api/dex/verify_exact_out_many_pool_repaired_replacement_shadow_packet",
        "packet",
        "verify_exact_out_many_pool_repaired_replacement_shadow_packet_payload",
        "verify_exact_out_many_pool_repaired_replacement_shadow_packet_error",
        "repaired replacement shadow packet verification failed",
        None,
    ),
    (
        "/api/dex/verify_exact_out_many_pool_default_packet",
        "packet",
        "verify_exact_out_many_pool_default_packet_payload",
        "verify_exact_out_many_pool_default_packet_error",
        "default packet verification failed",
        "certified_advisory_v1",
    ),
    (
        "/api/dex/verify_exact_out_many_pool_bounded_advisory_quote_packet",
        "packet",
        "verify_exact_out_many_pool_bounded_advisory_quote_packet_payload",
        "verify_exact_out_many_pool_bounded_advisory_quote_packet_error",
        "bounded advisory quote packet verification failed",
        None,
    ),
    (
        "/api/dex/verify_exact_out_many_pool_bounded_workaround_packet",
        "packet",
        "verify_exact_out_many_pool_bounded_workaround_packet_payload",
        "verify_exact_out_many_pool_bounded_workaround_packet_error",
        "bounded workaround packet verification failed",
        None,
    ),
    (
        "/api/dex/verify_exact_out_many_pool_repaired_selected_domain_oracle_contract",
        "contract",
        "verify_exact_out_many_pool_repaired_selected_domain_oracle_contract_payload",
        "verify_exact_out_many_pool_repaired_selected_domain_oracle_contract_error",
        "repaired selected-domain oracle contract verification failed",
        "repaired_selected_domain_v1",
    ),
    (
        "/api/dex/verify_exact_out_many_pool_candidate_domain_contract",
        "contract",
        "verify_exact_out_many_pool_candidate_domain_contract_payload",
        "verify_exact_out_many_pool_candidate_domain_contract_error",
        "candidate domain contract verification failed",
        None,
    ),
    (
        "/api/dex/verify_exact_out_many_pool_prefilter_contract",
        "contract",
        "verify_exact_out_many_pool_prefilter_contract_payload",
        "verify_exact_out_many_pool_prefilter_contract_error",
        "prefilter contract verification failed",
        None,
    ),
    (
        "/api/dex/verify_exact_out_many_pool_repaired_prefilter_contract",
        "contract",
        "verify_exact_out_many_pool_repaired_prefilter_contract_payload",
        "verify_exact_out_many_pool_repaired_prefilter_contract_error",
        "repaired prefilter contract verification failed",
        None,
    ),
    (
        "/api/dex/verify_exact_out_many_pool_oracle_contract",
        "contract",
        "verify_exact_out_many_pool_oracle_contract_payload",
        "verify_exact_out_many_pool_oracle_contract_error",
        "oracle contract verification failed",
        None,
    ),
    (
        "/api/dex/verify_exact_out_many_pool_audited_bounds_contract",
        "contract",
        "verify_exact_out_many_pool_audited_bounds_contract_payload",
        "verify_exact_out_many_pool_audited_bounds_contract_error",
        "audited bounds contract verification failed",
        None,
    ),
    (
        "/api/dex/verify_exact_out_many_pool_adaptive_liveness_packet",
        "packet",
        "verify_exact_out_many_pool_adaptive_liveness_packet_payload",
        "verify_exact_out_many_pool_adaptive_liveness_packet_error",
        "adaptive liveness packet verification failed",
        "adaptive_liveness_v1",
    ),
)

for _path, _key, _fn_name, _err_code, _default_err, _policy in _EXACT_OUT_POLICY_VERIFIERS:
    _register(
        _path,
        _make_policy_verifier(
            payload_key=_key,
            importer=_import_exact_out_route_certificate(_fn_name),
            error_code=_err_code,
            default_error=_default_err,
            quote_policy=_policy,
        ),
    )


# verify_exact_out_route_certificate uses a different response shape:
# returns {"ok": bool, "error": "ok"|err} (always populates "error" with
# string "ok" on success). Custom handler.
def _handle_verify_exact_out_route_certificate(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
    certificate = obj.get("certificate")
    if not isinstance(certificate, dict):
        return 400, {"ok": False, "error": "bad_certificate"}
    try:
        from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
            verify_exact_out_route_canonical_certificate_payload,
        )

        ok, err = verify_exact_out_route_canonical_certificate_payload(certificate)
        return 200, {"ok": bool(ok), "error": ("ok" if ok else str(err))}
    except Exception:
        return 400, {"ok": False, "error": "verify_exact_out_certificate_error", "details": "request failed"}


_register("/api/dex/verify_exact_out_route_certificate", _handle_verify_exact_out_route_certificate)


# ======================================================================
# PR2 Batch 3 — verify_settlement_spot_price_packet,
# verify_settlement_feature_extension_packet,
# verify_settlement_spot_price_attestation,
# build_settlement_spot_price_attestation,
# build_exact_out_route_certificate,
# audit_exact_out_two_pool_canonicality,
# audit_exact_out_many_pool_canonicality
# ======================================================================
def _import_verify_settlement_spot_price_packet_payload() -> Any:

    return verify_settlement_spot_price_packet_payload


_register(
    "/api/dex/verify_settlement_spot_price_packet",
    _make_simple_verifier(
        payload_key="packet",
        importer=_import_verify_settlement_spot_price_packet_payload,
        error_code="verify_settlement_spot_price_packet_error",
    ),
)


def _handle_verify_settlement_feature_extension_packet(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
    """2-input verify: takes both feature_extension_inputs and packet."""
    feature_extension_inputs_obj = obj.get("feature_extension_inputs")
    packet_obj = obj.get("packet")
    if not isinstance(packet_obj, dict):
        return 400, {"ok": False, "error": "bad_packet"}
    try:
        ok, err = verify_settlement_feature_extension_packet_payload(
            inputs_payload=feature_extension_inputs_obj,
            packet_payload=packet_obj,
        )
        return 200, {"ok": bool(ok), "error": err}
    except Exception:
        return 400, {"ok": False, "error": "verify_settlement_feature_extension_packet_error", "details": "request failed"}


_register("/api/dex/verify_settlement_feature_extension_packet", _handle_verify_settlement_feature_extension_packet)


def _handle_verify_settlement_spot_price_attestation(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
    """Verify a spot-price attestation against a freshness window + signer allowlist."""
    attestation_obj = obj.get("attestation")
    consumer_now_epoch = obj.get("consumer_now_epoch")
    max_attestation_age_epochs = obj.get("max_attestation_age_epochs")
    allowed_signers_obj = obj.get("allowed_signers")
    if not isinstance(attestation_obj, dict):
        return 400, {"ok": False, "error": "bad_attestation"}
    if not isinstance(consumer_now_epoch, int) or isinstance(consumer_now_epoch, bool) or consumer_now_epoch < 0:
        return 400, {"ok": False, "error": "bad_consumer_now_epoch"}
    if (
        not isinstance(max_attestation_age_epochs, int)
        or isinstance(max_attestation_age_epochs, bool)
        or max_attestation_age_epochs < 0
    ):
        return 400, {"ok": False, "error": "bad_max_attestation_age_epochs"}
    if allowed_signers_obj is not None and not isinstance(allowed_signers_obj, dict):
        return 400, {"ok": False, "error": "bad_allowed_signers"}
    try:
        ok, err = verify_settlement_spot_price_attestation_payload(
            payload=attestation_obj,
            consumer_now_epoch=int(consumer_now_epoch),
            max_attestation_age_epochs=int(max_attestation_age_epochs),
            allowed_signers=allowed_signers_obj,
        )
        return 200, {"ok": bool(ok), "error": err}
    except Exception:
        return 400, {"ok": False, "error": "verify_settlement_spot_price_attestation_error", "details": "request failed"}


_register("/api/dex/verify_settlement_spot_price_attestation", _handle_verify_settlement_spot_price_attestation)


def _handle_build_settlement_spot_price_attestation(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
    """Sign a settlement spot-price packet into an attestation."""
    packet_obj = obj.get("packet")
    signer_privkey = obj.get("signer_privkey")
    if not isinstance(packet_obj, dict):
        return 400, {"ok": False, "error": "bad_packet"}
    if isinstance(signer_privkey, bool) or not isinstance(signer_privkey, (str, int)):
        return 400, {"ok": False, "error": "bad_signer_privkey"}
    try:
        packet = SettlementSpotPricePacket.from_dict(packet_obj)
        attestation = build_settlement_spot_price_attestation(
            packet=packet,
            signer_privkey=signer_privkey,
        )
        return 200, {"ok": True, "attestation": attestation.to_dict()}
    except Exception:
        return 400, {"ok": False, "error": "build_settlement_spot_price_attestation_error", "details": "request failed"}


_register("/api/dex/build_settlement_spot_price_attestation", _handle_build_settlement_spot_price_attestation)


def _handle_build_exact_out_route_certificate(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
    """Combine exact-out quote payloads into a canonical certificate."""
    quotes_obj = obj.get("quotes")
    if not isinstance(quotes_obj, list) or not quotes_obj:
        return 400, {"ok": False, "error": "bad_quotes"}
    try:
        from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
            build_exact_out_route_canonical_certificate,
        )

        quotes = tuple(exact_out_split_quote_from_dict(quote_obj) for quote_obj in quotes_obj)
        certificate = build_exact_out_route_canonical_certificate(quotes)
        return 200, {"ok": True, "certificate": certificate.to_dict()}
    except Exception:
        return 400, {"ok": False, "error": "bad_exact_out_certificate_request", "details": "request failed"}


_register("/api/dex/build_exact_out_route_certificate", _handle_build_exact_out_route_certificate)


def _handle_audit_exact_out_two_pool_canonicality(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
    try:
        pools_by_id = parse_pools(obj)
        if len(pools_by_id) != 2:
            return 400, {"ok": False, "error": "expected_exactly_two_pools"}
        asset_in = str(obj.get("asset_in", "")).strip()
        asset_out = str(obj.get("asset_out", "")).strip()
        amount_out_total = obj.get("amount_out_total")
        brute_force_max = obj.get("brute_force_max")
        if not asset_in or not asset_out or asset_in == asset_out:
            return 400, {"ok": False, "error": "bad_assets"}
        if not isinstance(amount_out_total, int) or isinstance(amount_out_total, bool) or amount_out_total <= 0:
            return 400, {"ok": False, "error": "bad_amount_out_total"}
        if brute_force_max is not None and (
            not isinstance(brute_force_max, int) or isinstance(brute_force_max, bool) or brute_force_max < 0
        ):
            return 400, {"ok": False, "error": "bad_brute_force_max"}

        from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
            audit_exact_out_two_pool_runtime_canonicality,
        )

        pools = list(pools_by_id.values())
        audit = audit_exact_out_two_pool_runtime_canonicality(
            pools[0],
            pools[1],
            asset_in=asset_in,
            asset_out=asset_out,
            amount_out_total=int(amount_out_total),
            brute_force_max=(None if brute_force_max is None else int(brute_force_max)),
        )
        return 200, {"ok": True, "audit": audit.to_dict()}
    except Exception:
        return 400, {"ok": False, "error": "audit_exact_out_two_pool_canonicality_error", "details": "request failed"}


_register("/api/dex/audit_exact_out_two_pool_canonicality", _handle_audit_exact_out_two_pool_canonicality)


# Step 6 declarative schema. Replaces the inline int_fields tuple loop.
# Use this as a template for migrating other handlers and as the single
# source of truth for OpenAPI / JSON-Schema generation.
_AUDIT_MANY_POOL_SCHEMA = EndpointSchema(
    summary="Audit canonicality of many-pool exact-out runtime quote against the canonical winner.",
    requires_pools=True,
    requires_assets=True,
    int_fields=(
        IntFieldSpec(name="amount_out_total", minimum=1, description="Target output amount."),
        IntFieldSpec(name="max_legs", default=3, minimum=1),
        IntFieldSpec(name="max_candidate_pools", default=5, minimum=1),
        IntFieldSpec(name="max_candidates", default=12, minimum=1),
        IntFieldSpec(name="max_iters", default=4096, minimum=1),
        IntFieldSpec(name="window", default=64, minimum=0),
        IntFieldSpec(name="brute_force_max", default=512, minimum=0),
        IntFieldSpec(name="max_full_domain_pools", default=8, minimum=1),
        IntFieldSpec(name="max_enumerated_candidates", default=20_000, minimum=1),
    ),
)


def _handle_audit_exact_out_many_pool_canonicality(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
    """Demonstrates the Step 6 declarative-schema pattern.

    No try/except: the dispatcher catches ``BadFieldError`` (raised by
    ``parse_int_kwargs`` on validation failure) and converts to
    ``(400, {"ok": False, "error": f"bad_{field}"})``. Any other
    ``Exception`` becomes ``(400, default_error_code, details="request
    failed")`` via the registered ``default_error_code``.
    """
    pools_by_id = parse_pools(obj)
    asset_in = str(obj.get("asset_in", "")).strip()
    asset_out = str(obj.get("asset_out", "")).strip()
    if not asset_in or not asset_out or asset_in == asset_out:
        return 400, {"ok": False, "error": "bad_assets"}
    validated = parse_int_kwargs(obj, _AUDIT_MANY_POOL_SCHEMA.int_fields)

    from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
        audit_exact_out_many_pool_runtime_canonicality,
    )

    audit = audit_exact_out_many_pool_runtime_canonicality(
        list(pools_by_id.values()),
        asset_in=asset_in,
        asset_out=asset_out,
        **validated,
    )
    return 200, {"ok": True, "audit": audit.to_dict()}


_register(
    "/api/dex/audit_exact_out_many_pool_canonicality",
    _handle_audit_exact_out_many_pool_canonicality,
    default_error_code="audit_exact_out_many_pool_canonicality_error",
    schema=_AUDIT_MANY_POOL_SCHEMA,
)


# ======================================================================
# PR2 Batch 4 — build/guard/quote_exact_in_route_* endpoints.
# All 6 share an identical input-validation block (asset_in, asset_out,
# amount_in, split_search_profile, enable_mixed_direct_twohop_split,
# optional binding_ok). Extract that block, then per-endpoint dispatch
# differs only in (importer, response_builder, has_binding_ok, has_bridge).
# ======================================================================
def _validate_exact_in_route_inputs(
    obj: Mapping[str, Any],
    *,
    needs_binding_ok: bool,
) -> DexResponse | dict[str, Any]:
    """Return a parsed kwargs dict on success or a ``DexResponse`` on failure.

    The two return shapes are distinguishable by ``isinstance(result, tuple)``
    (DexResponse is ``Tuple[int, Mapping[str, Any]]``). This gives mypy a
    narrowable union without a sentinel ``None`` second element.
    """
    asset_in = str(obj.get("asset_in", "")).strip()
    asset_out = str(obj.get("asset_out", "")).strip()
    amount_in = obj.get("amount_in")
    split_search_profile = str(obj.get("split_search_profile", "adaptive_v6")).strip()
    enable_mixed_direct_twohop_split = obj.get("enable_mixed_direct_twohop_split", False)
    if not asset_in or not asset_out or asset_in == asset_out:
        return 400, {"ok": False, "error": "bad_assets"}
    if not isinstance(amount_in, int) or isinstance(amount_in, bool) or amount_in <= 0:
        return 400, {"ok": False, "error": "bad_amount_in"}
    if not split_search_profile:
        return 400, {"ok": False, "error": "bad_split_search_profile"}
    if not isinstance(enable_mixed_direct_twohop_split, bool):
        return 400, {"ok": False, "error": "bad_enable_mixed_direct_twohop_split"}
    out: dict[str, Any] = {
        "asset_in": asset_in,
        "asset_out": asset_out,
        "amount_in": int(amount_in),
        "split_search_profile": split_search_profile,
        "enable_mixed_direct_twohop_split": bool(enable_mixed_direct_twohop_split),
    }
    if needs_binding_ok:
        binding_ok = obj.get("binding_ok", 1)
        if not isinstance(binding_ok, int) or isinstance(binding_ok, bool) or binding_ok not in {0, 1}:
            return 400, {"ok": False, "error": "bad_binding_ok"}
        out["binding_ok"] = int(binding_ok)
    return out


def _handle_build_exact_in_route_oracle_contract(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
    try:
        pools_by_id = parse_pools(obj)
        kwargs = _validate_exact_in_route_inputs(obj, needs_binding_ok=True)
        if isinstance(kwargs, tuple):
            return kwargs

        from src.integration.exact_in_route_certificate import (  # pylint: disable=import-outside-toplevel
            build_exact_in_route_oracle_contract,
        )

        contract = build_exact_in_route_oracle_contract(pools_by_id=pools_by_id, **kwargs)
        return 200, {
            "ok": True,
            "contract_schema": "zenodex/exact-in-route-oracle-contract/v1",
            "verify_contract_endpoint": "/api/dex/verify_exact_in_route_oracle_contract",
            "contract": contract.to_dict(),
        }
    except Exception:
        return 400, {"ok": False, "error": "build_exact_in_route_oracle_contract_error", "details": "request failed"}


_register("/api/dex/build_exact_in_route_oracle_contract", _handle_build_exact_in_route_oracle_contract)


def _handle_guard_exact_in_route_canonicality(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
    try:
        pools_by_id = parse_pools(obj)
        kwargs = _validate_exact_in_route_inputs(obj, needs_binding_ok=True)
        if isinstance(kwargs, tuple):
            return kwargs

        from src.integration.exact_in_route_certificate import (  # pylint: disable=import-outside-toplevel
            guard_exact_in_route_runtime_canonicality,
        )

        ok, err_msg, contract = guard_exact_in_route_runtime_canonicality(pools_by_id=pools_by_id, **kwargs)
        return 200, {"ok": bool(ok), "contract": contract.to_dict(), "error": err_msg}
    except Exception:
        return 400, {"ok": False, "error": "guard_exact_in_route_canonicality_error", "details": "request failed"}


_register("/api/dex/guard_exact_in_route_canonicality", _handle_guard_exact_in_route_canonicality)


def _handle_quote_exact_in_route_guarded(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
    try:
        from src.integration._dex_api_helpers import (
            parse_pools,  # pylint: disable=import-outside-toplevel
        )
        from src.integration.api_server import (
            _check_routing_oracle_adapter_bridge,  # pylint: disable=import-outside-toplevel
        )

        pools_by_id = parse_pools(obj)
        kwargs = _validate_exact_in_route_inputs(obj, needs_binding_ok=True)
        if isinstance(kwargs, tuple):
            return kwargs

        bridge_err = _check_routing_oracle_adapter_bridge(
            body=obj,
            path="/api/dex/quote_exact_in_route_guarded",
            asset_in=kwargs["asset_in"],
            asset_out=kwargs["asset_out"],
            amount_in=kwargs["amount_in"],
            split_search_profile=kwargs["split_search_profile"],
            enable_mixed_direct_twohop_split=kwargs["enable_mixed_direct_twohop_split"],
            binding_ok=kwargs["binding_ok"],
        )
        if bridge_err is not None:
            return 400, {"ok": False, "error": "rejected", "detail": bridge_err}

        from src.integration.exact_in_route_certificate import (  # pylint: disable=import-outside-toplevel
            quote_exact_in_route_guarded,
        )

        quote, err_msg, contract = quote_exact_in_route_guarded(pools_by_id=pools_by_id, **kwargs)
        response: dict[str, Any] = {"ok": quote is not None, "contract": contract.to_dict(), "error": err_msg}
        if quote is not None:
            response["quote"] = contract.to_dict()["runtime_quote"]
        return 200, response
    except Exception:
        return 400, {"ok": False, "error": "quote_exact_in_route_guarded_error", "details": "request failed"}


_register("/api/dex/quote_exact_in_route_guarded", _handle_quote_exact_in_route_guarded)


def _handle_build_exact_in_route_guarded_quote_packet(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
    try:
        pools_by_id = parse_pools(obj)
        kwargs = _validate_exact_in_route_inputs(obj, needs_binding_ok=True)
        if isinstance(kwargs, tuple):
            return kwargs

        from src.integration.exact_in_route_certificate import (  # pylint: disable=import-outside-toplevel
            build_exact_in_route_guarded_quote_packet,
        )

        packet = build_exact_in_route_guarded_quote_packet(pools_by_id=pools_by_id, **kwargs)
        packet_dict = packet.to_dict()
        response: dict[str, Any] = {
            "ok": True,
            "packet_schema": "zenodex/exact-in-route-guarded-quote-packet/v1",
            "verify_packet_endpoint": "/api/dex/verify_exact_in_route_guarded_quote_packet",
            "packet": packet_dict,
        }
        if not packet.guard_ok:
            response["guard_ok"] = False
            response["error"] = str(packet.error or "exact_in_runtime_not_canonical")
        return 200, response
    except Exception:
        return 400, {"ok": False, "error": "build_exact_in_route_guarded_quote_packet_error", "details": "request failed"}


_register("/api/dex/build_exact_in_route_guarded_quote_packet", _handle_build_exact_in_route_guarded_quote_packet)


def _handle_build_exact_in_route_rank_projection_packet(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
    try:
        pools_by_id = parse_pools(obj)
        kwargs = _validate_exact_in_route_inputs(obj, needs_binding_ok=False)
        if isinstance(kwargs, tuple):
            return kwargs

        from src.integration.exact_in_route_certificate import (  # pylint: disable=import-outside-toplevel
            build_exact_in_route_rank_projection_packet_for_pools,
        )

        packet = build_exact_in_route_rank_projection_packet_for_pools(pools_by_id=pools_by_id, **kwargs)
        if packet is None:
            return 200, {"ok": False, "error": "no_route_candidates"}
        return 200, {
            "ok": True,
            "packet_schema": "zenodex/exact-in-route-rank-projection-packet/v1",
            "verify_packet_endpoint": "/api/dex/verify_exact_in_route_rank_projection_packet",
            "packet": packet.to_dict(),
        }
    except Exception:
        return 400, {"ok": False, "error": "build_exact_in_route_rank_projection_packet_error", "details": "request failed"}


_register("/api/dex/build_exact_in_route_rank_projection_packet", _handle_build_exact_in_route_rank_projection_packet)


def _handle_build_exact_in_route_true_key_interpretation_packet(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
    try:
        pools_by_id = parse_pools(obj)
        kwargs = _validate_exact_in_route_inputs(obj, needs_binding_ok=False)
        if isinstance(kwargs, tuple):
            return kwargs

        from src.integration.exact_in_route_certificate import (  # pylint: disable=import-outside-toplevel
            build_exact_in_route_true_key_interpretation_packet_for_pools,
        )

        packet = build_exact_in_route_true_key_interpretation_packet_for_pools(pools_by_id=pools_by_id, **kwargs)
        if packet is None:
            return 200, {"ok": False, "error": "no_route_candidates"}
        return 200, {
            "ok": True,
            "packet_schema": "zenodex/exact-in-route-true-key-interpretation-packet/v1",
            "verify_packet_endpoint": "/api/dex/verify_exact_in_route_true_key_interpretation_packet",
            "packet": packet.to_dict(),
        }
    except Exception:
        return 400, {"ok": False, "error": "build_exact_in_route_true_key_interpretation_packet_error", "details": "request failed"}


_register("/api/dex/build_exact_in_route_true_key_interpretation_packet", _handle_build_exact_in_route_true_key_interpretation_packet)


# ======================================================================
# PR2 Batch 5 — build_exact_out_many_pool_*_contract endpoints.
# Six contract-builder endpoints share an identical skeleton:
#   parse_pools → assets → int_fields → call → respond.
# Variance: int_field set, module function/schema names, response extras
# (contract_ok flag, quote_endpoint).
# ======================================================================
def _int_field_specs_from_tuples(
    tuples: Sequence[tuple[str, Any, int]],
) -> tuple[IntFieldSpec, ...]:
    """Convert the legacy ``(name, default, minimum)`` tuple form into
    ``IntFieldSpec`` instances for use with ``parse_int_kwargs`` and the
    OpenAPI generator. ``default=None`` means the field is required."""
    return tuple(IntFieldSpec(name=n, default=d, minimum=m) for n, d, m in tuples)


def _make_exact_out_many_pool_contract_builder(
    *,
    field_specs: Sequence[IntFieldSpec],
    module_function_name: str,
    module_schema_name: str,
    verify_endpoint: str,
    error_code: str,
    include_contract_ok: bool = False,
    quote_endpoint: Optional[str] = None,
) -> Any:
    """Factory for the build_exact_out_many_pool_*_contract endpoint shape.

    ``field_specs`` is a sequence of ``IntFieldSpec`` validated by
    ``parse_int_kwargs`` (raises ``BadFieldError`` on invalid input which
    the dispatcher converts to ``(400, {"ok": False, "error":
    f"bad_{field}"})`` matching the legacy ad-hoc shape).

    No try/except in the handler body: the dispatcher's catch-all uses
    the spec's registered ``default_error_code``.
    """
    # The two response variants (include_contract_ok / quote_endpoint /
    # neither) preserve legacy key ordering exactly. Resolved once at
    # factory time, not per request, to avoid the per-request dict
    # rebuild on the hot path.
    def _response(contract_dict: Mapping[str, Any], schema: str) -> dict[str, Any]:
        if quote_endpoint is not None:
            return {
                "ok": True,
                "contract": contract_dict,
                "contract_schema": schema,
                "quote_endpoint": quote_endpoint,
                "verify_contract_endpoint": verify_endpoint,
            }
        if include_contract_ok:
            return {
                "ok": True,
                "contract": contract_dict,
                "contract_ok": bool(contract_dict["contract_ok"]),
                "contract_schema": schema,
                "verify_contract_endpoint": verify_endpoint,
            }
        return {
            "ok": True,
            "contract": contract_dict,
            "contract_schema": schema,
            "verify_contract_endpoint": verify_endpoint,
        }

    def _handler(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
        pools_by_id = parse_pools(obj)
        asset_in = str(obj.get("asset_in", "")).strip()
        asset_out = str(obj.get("asset_out", "")).strip()
        if not asset_in or not asset_out or asset_in == asset_out:
            return 400, {"ok": False, "error": "bad_assets"}

        int_kwargs = parse_int_kwargs(obj, field_specs)

        import importlib  # pylint: disable=import-outside-toplevel
        module = importlib.import_module("src.integration.exact_out_route_certificate")
        builder = getattr(module, module_function_name)
        schema = getattr(module, module_schema_name)

        contract = builder(
            list(pools_by_id.values()),
            asset_in=asset_in,
            asset_out=asset_out,
            **int_kwargs,
        )
        return 200, _response(contract.to_dict(), schema)

    return _handler


_BUILD_EXACT_OUT_CONTRACT_SPECS: tuple[tuple[str, dict[str, Any]], ...] = (
    (
        "/api/dex/build_exact_out_many_pool_candidate_domain_contract",
        {
            "field_defaults": [
                ("amount_out_total", None, 1),
                ("max_legs", 3, 1),
                ("max_candidate_pools", 5, 1),
                ("max_enumerated_candidates", 20_000, 1),
            ],
            "module_function_name": "build_exact_out_many_pool_candidate_domain_contract",
            "module_schema_name": "EXACT_OUT_MANY_POOL_CANDIDATE_DOMAIN_CONTRACT_SCHEMA",
            "verify_endpoint": "/api/dex/verify_exact_out_many_pool_candidate_domain_contract",
            "error_code": "build_exact_out_many_pool_candidate_domain_contract_error",
        },
    ),
    (
        "/api/dex/build_exact_out_many_pool_prefilter_contract",
        {
            "field_defaults": [
                ("amount_out_total", None, 1),
                ("max_legs", 3, 1),
                ("max_candidate_pools", 5, 1),
            ],
            "module_function_name": "build_exact_out_many_pool_prefilter_contract",
            "module_schema_name": "EXACT_OUT_MANY_POOL_PREFILTER_CONTRACT_SCHEMA",
            "verify_endpoint": "/api/dex/verify_exact_out_many_pool_prefilter_contract",
            "error_code": "build_exact_out_many_pool_prefilter_contract_error",
        },
    ),
    (
        "/api/dex/build_exact_out_many_pool_repaired_prefilter_contract",
        {
            "field_defaults": [
                ("amount_out_total", None, 1),
                ("max_legs", 3, 1),
                ("max_candidate_pools", 5, 1),
                ("max_full_domain_pools", 8, 1),
                ("max_enumerated_candidates", 20_000, 1),
            ],
            "module_function_name": "build_exact_out_many_pool_repaired_prefilter_contract",
            "module_schema_name": "EXACT_OUT_MANY_POOL_REPAIRED_PREFILTER_CONTRACT_SCHEMA",
            "verify_endpoint": "/api/dex/verify_exact_out_many_pool_repaired_prefilter_contract",
            "error_code": "build_exact_out_many_pool_repaired_prefilter_contract_error",
        },
    ),
    (
        "/api/dex/build_exact_out_many_pool_repaired_selected_domain_oracle_contract",
        {
            "field_defaults": [
                ("amount_out_total", None, 1),
                ("max_legs", 3, 1),
                ("max_candidate_pools", 5, 1),
                ("max_candidates", 12, 1),
                ("max_iters", 4096, 1),
                ("window", 64, 0),
                ("brute_force_max", 512, 0),
                ("max_full_domain_pools", 8, 1),
                ("max_enumerated_candidates", 20_000, 1),
            ],
            "module_function_name": "build_exact_out_many_pool_repaired_selected_domain_oracle_contract",
            "module_schema_name": "EXACT_OUT_MANY_POOL_REPAIRED_SELECTED_DOMAIN_ORACLE_CONTRACT_SCHEMA",
            "verify_endpoint": "/api/dex/verify_exact_out_many_pool_repaired_selected_domain_oracle_contract",
            "error_code": "build_exact_out_many_pool_repaired_selected_domain_oracle_contract_error",
            "quote_endpoint": "/api/dex/quote_exact_out_many_pool_repaired_selected_domain",
        },
    ),
    (
        "/api/dex/build_exact_out_many_pool_oracle_contract",
        {
            "field_defaults": [
                ("amount_out_total", None, 1),
                ("max_legs", 3, 1),
                ("max_candidate_pools", 5, 1),
                ("max_candidates", 12, 1),
                ("max_iters", 4096, 1),
                ("window", 64, 0),
                ("brute_force_max", 512, 0),
                ("max_enumerated_candidates", 20_000, 1),
            ],
            "module_function_name": "build_exact_out_many_pool_oracle_contract",
            "module_schema_name": "EXACT_OUT_MANY_POOL_ORACLE_CONTRACT_SCHEMA",
            "verify_endpoint": "/api/dex/verify_exact_out_many_pool_oracle_contract",
            "error_code": "build_exact_out_many_pool_oracle_contract_error",
            "include_contract_ok": True,
        },
    ),
    (
        "/api/dex/build_exact_out_many_pool_audited_bounds_contract",
        {
            "field_defaults": [
                ("amount_out_total", None, 1),
                ("max_legs", 3, 1),
                ("max_candidate_pools", 5, 1),
                ("max_candidates", 12, 1),
                ("max_iters", 4096, 1),
                ("window", 64, 0),
                ("brute_force_max", 512, 0),
                ("max_full_domain_pools", 8, 1),
                ("max_enumerated_candidates", 20_000, 1),
            ],
            "module_function_name": "build_exact_out_many_pool_audited_bounds_contract",
            "module_schema_name": "EXACT_OUT_MANY_POOL_AUDITED_BOUNDS_CONTRACT_SCHEMA",
            "verify_endpoint": "/api/dex/verify_exact_out_many_pool_audited_bounds_contract",
            "error_code": "build_exact_out_many_pool_audited_bounds_contract_error",
        },
    ),
)

for _path, _spec in _BUILD_EXACT_OUT_CONTRACT_SPECS:
    # Convert the legacy tuple form to IntFieldSpec for the factory + the
    # registered EndpointSchema. The schema gives us OpenAPI for every
    # contract builder for free.
    _field_specs = _int_field_specs_from_tuples(_spec["field_defaults"])
    _handler_fn = _make_exact_out_many_pool_contract_builder(
        field_specs=_field_specs,
        module_function_name=_spec["module_function_name"],
        module_schema_name=_spec["module_schema_name"],
        verify_endpoint=_spec["verify_endpoint"],
        error_code=_spec["error_code"],
        include_contract_ok=_spec.get("include_contract_ok", False),
        quote_endpoint=_spec.get("quote_endpoint"),
    )
    _register(
        _path,
        _handler_fn,
        default_error_code=_spec["error_code"],
        schema=EndpointSchema(requires_pools=True, requires_assets=True, int_fields=_field_specs),
    )


# ======================================================================
# PR2 Batch 6 — build_exact_out_many_pool_*_packet endpoints (10 of them).
# Share the same 9-int-field validation as the contract builders but each
# has slightly different response shape:
#   - "ok_true": response.ok is always True (only valid for endpoints
#     that don't surface packet_ok)
#   - "ok_packet_ok": response.ok = bool(packet.packet_ok), error on False
#   - "ok_true_unless_packet_ok": response.ok = True initially, flipped to
#     False + error appended if packet.packet_ok is False
# Some also include extra response fields (e.g. liveness_ok) and a
# quote_policy tag.
# ======================================================================
_PACKET_BUILDER_DEFAULT_FIELDS: list[tuple[str, Any, int]] = [
    ("amount_out_total", None, 1),
    ("max_legs", 3, 1),
    ("max_candidate_pools", 5, 1),
    ("max_candidates", 12, 1),
    ("max_iters", 4096, 1),
    ("window", 64, 0),
    ("brute_force_max", 512, 0),
    ("max_full_domain_pools", 8, 1),
    ("max_enumerated_candidates", 20_000, 1),
]


def _make_exact_out_many_pool_packet_builder(
    *,
    field_specs: Sequence[IntFieldSpec],
    module_function_name: str,
    module_schema_name: str,
    verify_endpoint: str,
    error_code: str,
    quote_policy: Optional[str] = None,
    response_mode: str = "ok_packet_ok",
    fallback_error: Optional[str] = None,
    extra_response_field: Optional[tuple[str, str]] = None,
) -> Any:
    """Factory for build_exact_out_many_pool_*_packet endpoints.

    See ``_make_exact_out_many_pool_contract_builder`` for the validation
    contract. ``response_mode`` controls the shape of the success response:

      - ``ok_true``: response always has ``ok=True`` (only valid when the
        packet has no failure mode tied to ``packet_ok``).
      - ``ok_packet_ok``: ``response.ok = bool(packet.packet_ok)``; on
        ``False``, adds the ``error`` key using ``packet.error`` if
        present, else ``fallback_error``.
      - ``ok_true_unless_packet_ok``: ``response.ok = True`` initially;
        on ``packet_ok=False``, flipped to ``False`` and ``error`` set.
        Matches the legacy ``advisory_quote_packet`` shape.

    ``extra_response_field``: ``(response_key, packet_attr_name)``. The
    bool value of ``getattr(packet, packet_attr_name)`` is added to the
    response under ``response_key``. Used by ``adaptive_liveness_packet``
    to expose ``liveness_ok``.

    No try/except: the dispatcher catch-all uses the registered
    ``default_error_code``. ``BadFieldError`` from ``parse_int_kwargs``
    is converted to ``(400, "bad_{field}")`` by the dispatcher.
    """
    if response_mode not in {"ok_true", "ok_packet_ok", "ok_true_unless_packet_ok"}:
        raise ValueError(f"unknown response_mode: {response_mode}")

    def _handler(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
        pools_by_id = parse_pools(obj)
        asset_in = str(obj.get("asset_in", "")).strip()
        asset_out = str(obj.get("asset_out", "")).strip()
        if not asset_in or not asset_out or asset_in == asset_out:
            return 400, {"ok": False, "error": "bad_assets"}

        int_kwargs = parse_int_kwargs(obj, field_specs)

        import importlib  # pylint: disable=import-outside-toplevel
        module = importlib.import_module("src.integration.exact_out_route_certificate")
        builder = getattr(module, module_function_name)
        schema = getattr(module, module_schema_name)

        packet = builder(
            list(pools_by_id.values()),
            asset_in=asset_in,
            asset_out=asset_out,
            **int_kwargs,
        )

        if response_mode == "ok_true":
            response: dict[str, Any] = {
                "ok": True,
                "packet": packet.to_dict(),
                "packet_schema": schema,
                "verify_packet_endpoint": verify_endpoint,
            }
            if quote_policy is not None:
                response["quote_policy"] = quote_policy
        elif response_mode == "ok_packet_ok":
            response = {
                "ok": bool(packet.packet_ok),
                "packet": packet.to_dict(),
                "packet_schema": schema,
                "verify_packet_endpoint": verify_endpoint,
            }
            if quote_policy is not None:
                response["quote_policy"] = quote_policy
            if not packet.packet_ok and fallback_error is not None:
                response["error"] = str(getattr(packet, "error", None) or fallback_error)
        else:  # ok_true_unless_packet_ok
            response = {
                "ok": True,
                "packet": packet.to_dict(),
                "packet_schema": schema,
                "verify_packet_endpoint": verify_endpoint,
            }
            if quote_policy is not None:
                response["quote_policy"] = quote_policy
            if not packet.packet_ok:
                response["ok"] = False
                response["error"] = str(packet.error or fallback_error or "packet_not_ok")

        if extra_response_field is not None:
            response_key, packet_attr = extra_response_field
            response[response_key] = bool(getattr(packet, packet_attr))

        return 200, response

    return _handler


_BUILD_EXACT_OUT_PACKET_SPECS: tuple[tuple[str, dict[str, Any]], ...] = (
    (
        "/api/dex/build_exact_out_many_pool_repaired_advisory_quote_packet",
        {
            "field_defaults": _PACKET_BUILDER_DEFAULT_FIELDS,
            "module_function_name": "build_exact_out_many_pool_repaired_advisory_quote_packet",
            "module_schema_name": "EXACT_OUT_MANY_POOL_REPAIRED_ADVISORY_QUOTE_PACKET_SCHEMA",
            "verify_endpoint": "/api/dex/verify_exact_out_many_pool_repaired_advisory_quote_packet",
            "error_code": "build_exact_out_many_pool_repaired_advisory_quote_packet_error",
            "response_mode": "ok_true_unless_packet_ok",
            "fallback_error": "many_pool_repaired_prefilter_contract_not_ok",
        },
    ),
    (
        "/api/dex/build_exact_out_many_pool_repaired_full_domain_certified_packet",
        {
            "field_defaults": _PACKET_BUILDER_DEFAULT_FIELDS,
            "module_function_name": "build_exact_out_many_pool_repaired_full_domain_certified_packet",
            "module_schema_name": "EXACT_OUT_MANY_POOL_REPAIRED_FULL_DOMAIN_CERTIFIED_PACKET_SCHEMA",
            "verify_endpoint": "/api/dex/verify_exact_out_many_pool_repaired_full_domain_certified_packet",
            "error_code": "build_exact_out_many_pool_repaired_full_domain_certified_packet_error",
            "response_mode": "ok_packet_ok",
            "fallback_error": "many_pool_repaired_advisory_not_full_domain_canonical",
            "quote_policy": "repaired_full_domain_certified_v1",
        },
    ),
    (
        "/api/dex/build_exact_out_many_pool_repaired_key_cover_packet",
        {
            "field_defaults": _PACKET_BUILDER_DEFAULT_FIELDS,
            "module_function_name": "build_exact_out_many_pool_repaired_key_cover_packet",
            "module_schema_name": "EXACT_OUT_MANY_POOL_REPAIRED_KEY_COVER_PACKET_SCHEMA",
            "verify_endpoint": "/api/dex/verify_exact_out_many_pool_repaired_key_cover_packet",
            "error_code": "build_exact_out_many_pool_repaired_key_cover_packet_error",
            "response_mode": "ok_packet_ok",
            "fallback_error": "many_pool_repaired_selected_domain_not_key_cover_complete",
            "quote_policy": "repaired_key_cover_v1",
        },
    ),
    (
        "/api/dex/build_exact_out_many_pool_repaired_key_cover_interpretation_packet",
        {
            "field_defaults": _PACKET_BUILDER_DEFAULT_FIELDS,
            "module_function_name": "build_exact_out_many_pool_repaired_key_cover_interpretation_packet",
            "module_schema_name": "EXACT_OUT_MANY_POOL_REPAIRED_KEY_COVER_INTERPRETATION_PACKET_SCHEMA",
            "verify_endpoint": "/api/dex/verify_exact_out_many_pool_repaired_key_cover_interpretation_packet",
            "error_code": "build_exact_out_many_pool_repaired_key_cover_interpretation_packet_error",
            "response_mode": "ok_packet_ok",
            "fallback_error": "many_pool_repaired_key_cover_witness_interpretation_inconsistent",
            "quote_policy": "repaired_key_cover_interpretation_v1",
        },
    ),
    (
        "/api/dex/build_exact_out_many_pool_bounded_advisory_quote_packet",
        {
            "field_defaults": _PACKET_BUILDER_DEFAULT_FIELDS,
            "module_function_name": "build_exact_out_many_pool_bounded_advisory_quote_packet",
            "module_schema_name": "EXACT_OUT_MANY_POOL_BOUNDED_ADVISORY_QUOTE_PACKET_SCHEMA",
            "verify_endpoint": "/api/dex/verify_exact_out_many_pool_bounded_advisory_quote_packet",
            "error_code": "build_exact_out_many_pool_bounded_advisory_quote_packet_error",
            "response_mode": "ok_packet_ok",
            "fallback_error": "many_pool_bounded_advisory_unavailable",
        },
    ),
    (
        "/api/dex/build_exact_out_many_pool_certified_advisory_packet",
        {
            "field_defaults": _PACKET_BUILDER_DEFAULT_FIELDS,
            "module_function_name": "build_exact_out_many_pool_certified_advisory_packet",
            "module_schema_name": "EXACT_OUT_MANY_POOL_CERTIFIED_ADVISORY_PACKET_SCHEMA",
            "verify_endpoint": "/api/dex/verify_exact_out_many_pool_certified_advisory_packet",
            "error_code": "build_exact_out_many_pool_certified_advisory_packet_error",
            "response_mode": "ok_packet_ok",
            "fallback_error": "many_pool_certified_advisory_packet_not_ok",
        },
    ),
    (
        "/api/dex/build_exact_out_many_pool_repaired_replacement_shadow_packet",
        {
            "field_defaults": _PACKET_BUILDER_DEFAULT_FIELDS,
            "module_function_name": "build_exact_out_many_pool_repaired_replacement_shadow_packet",
            "module_schema_name": "EXACT_OUT_MANY_POOL_REPAIRED_REPLACEMENT_SHADOW_PACKET_SCHEMA",
            "verify_endpoint": "/api/dex/verify_exact_out_many_pool_repaired_replacement_shadow_packet",
            "error_code": "build_exact_out_many_pool_repaired_replacement_shadow_packet_error",
            "response_mode": "ok_packet_ok",
            # No fallback_error: legacy never sets an error key on packet_ok=False here.
        },
    ),
    (
        "/api/dex/build_exact_out_many_pool_default_packet",
        {
            "field_defaults": _PACKET_BUILDER_DEFAULT_FIELDS,
            "module_function_name": "build_exact_out_many_pool_default_packet",
            "module_schema_name": "EXACT_OUT_MANY_POOL_CERTIFIED_ADVISORY_PACKET_SCHEMA",
            "verify_endpoint": "/api/dex/verify_exact_out_many_pool_default_packet",
            "error_code": "build_exact_out_many_pool_default_packet_error",
            "response_mode": "ok_packet_ok",
            "fallback_error": "many_pool_default_packet_not_ok",
            "quote_policy": "certified_advisory_v1",
        },
    ),
    (
        "/api/dex/build_exact_out_many_pool_bounded_workaround_packet",
        {
            "field_defaults": _PACKET_BUILDER_DEFAULT_FIELDS,
            "module_function_name": "build_exact_out_many_pool_bounded_workaround_packet",
            "module_schema_name": "EXACT_OUT_MANY_POOL_BOUNDED_WORKAROUND_PACKET_SCHEMA",
            "verify_endpoint": "/api/dex/verify_exact_out_many_pool_bounded_workaround_packet",
            "error_code": "build_exact_out_many_pool_bounded_workaround_packet_error",
            "response_mode": "ok_true",
        },
    ),
    (
        "/api/dex/build_exact_out_many_pool_adaptive_liveness_packet",
        {
            "field_defaults": _PACKET_BUILDER_DEFAULT_FIELDS,
            "module_function_name": "build_exact_out_many_pool_adaptive_liveness_packet",
            "module_schema_name": "EXACT_OUT_MANY_POOL_ADAPTIVE_LIVENESS_PACKET_SCHEMA",
            "verify_endpoint": "/api/dex/verify_exact_out_many_pool_adaptive_liveness_packet",
            "error_code": "build_exact_out_many_pool_adaptive_liveness_packet_error",
            "response_mode": "ok_packet_ok",
            "quote_policy": "adaptive_liveness_v1",
            "extra_response_field": ("liveness_ok", "liveness_ok"),
        },
    ),
)

for _path, _spec in _BUILD_EXACT_OUT_PACKET_SPECS:
    _field_specs = _int_field_specs_from_tuples(_spec["field_defaults"])
    _handler_fn = _make_exact_out_many_pool_packet_builder(
        field_specs=_field_specs,
        module_function_name=_spec["module_function_name"],
        module_schema_name=_spec["module_schema_name"],
        verify_endpoint=_spec["verify_endpoint"],
        error_code=_spec["error_code"],
        quote_policy=_spec.get("quote_policy"),
        response_mode=_spec.get("response_mode", "ok_packet_ok"),
        fallback_error=_spec.get("fallback_error"),
        extra_response_field=_spec.get("extra_response_field"),
    )
    _register(
        _path,
        _handler_fn,
        default_error_code=_spec["error_code"],
        schema=EndpointSchema(requires_pools=True, requires_assets=True, int_fields=_field_specs),
    )


# ======================================================================
# PR2 Batch 7 — guarded family (guard/quote/build) + certified_winner_packet.
# These have heavier custom response shapes that extract specific fields
# from the contract.audit payload, so per-endpoint handlers preserve
# byte-identical behavior.
# ======================================================================
_GUARD_FAMILY_INT_FIELDS: list[tuple[str, Any, int]] = [
    ("amount_out_total", None, 1),
    ("max_legs", 3, 1),
    ("max_candidate_pools", 5, 1),
    ("max_candidates", 12, 1),
    ("max_iters", 4096, 1),
    ("window", 64, 0),
    ("brute_force_max", 512, 0),
    ("max_enumerated_candidates", 20_000, 1),
]


def _validate_guard_family_inputs(obj: Mapping[str, Any]) -> DexResponse | dict[str, Any]:
    """Return parsed kwargs dict on success or ``DexResponse`` on failure."""
    asset_in = str(obj.get("asset_in", "")).strip()
    asset_out = str(obj.get("asset_out", "")).strip()
    if not asset_in or not asset_out or asset_in == asset_out:
        return 400, {"ok": False, "error": "bad_assets"}
    int_kwargs: dict[str, int] = {}
    for name, default, minimum in _GUARD_FAMILY_INT_FIELDS:
        raw_value = obj.get(name, default)
        if not isinstance(raw_value, int) or isinstance(raw_value, bool) or raw_value < int(minimum):
            return 400, {"ok": False, "error": f"bad_{name}"}
        int_kwargs[name] = int(raw_value)
    return {"asset_in": asset_in, "asset_out": asset_out, **int_kwargs}


def _handle_guard_exact_out_many_pool_canonicality(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
    try:
        pools_by_id = parse_pools(obj)
        inputs = _validate_guard_family_inputs(obj)
        if isinstance(inputs, tuple):
            return inputs

        from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
            EXACT_OUT_MANY_POOL_ORACLE_CONTRACT_SCHEMA,
            guard_exact_out_many_pool_runtime_canonicality,
        )

        ok, err_msg, contract = guard_exact_out_many_pool_runtime_canonicality(
            list(pools_by_id.values()),
            **inputs,
        )
        contract_dict = contract.to_dict()
        audit_payload = contract_dict["audit"]
        payload = {
            "ok": bool(ok),
            "contract": contract_dict,
            "contract_ok": bool(contract_dict["contract_ok"]),
            "contract_schema": EXACT_OUT_MANY_POOL_ORACLE_CONTRACT_SCHEMA,
            "build_contract_endpoint": "/api/dex/build_exact_out_many_pool_oracle_contract",
            "verify_contract_endpoint": "/api/dex/verify_exact_out_many_pool_oracle_contract",
            "runtime_projected_path": audit_payload["runtime_projected_path"],
            "canonical_winner_projected_path": audit_payload["canonical_winner_projected_path"],
            "runtime_matches_canonical_projected_path": audit_payload["runtime_matches_canonical_projected_path"],
            "projection_cover_available": audit_payload["projection_cover_available"],
            "projection_cover_holds": audit_payload["projection_cover_holds"],
        }
        if ok:
            payload["quote"] = dict(audit_payload["runtime_quote"])
        else:
            payload["error"] = str(err_msg or "many_pool_runtime_not_canonical")
            payload["runtime_quote"] = dict(audit_payload["runtime_quote"])
            payload["canonical_winner_quote"] = dict(audit_payload["canonical_winner_quote"])
        return 200, payload
    except Exception:
        return 400, {"ok": False, "error": "guard_exact_out_many_pool_canonicality_error", "details": "request failed"}


_register("/api/dex/guard_exact_out_many_pool_canonicality", _handle_guard_exact_out_many_pool_canonicality)


def _handle_quote_exact_out_many_pool_guarded(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
    try:
        from src.integration._dex_api_helpers import (
            parse_pools,  # pylint: disable=import-outside-toplevel
        )
        from src.integration.api_server import (
            _check_routing_exact_out_oracle_adapter_bridge,  # pylint: disable=import-outside-toplevel
        )

        pools_by_id = parse_pools(obj)
        inputs = _validate_guard_family_inputs(obj)
        if isinstance(inputs, tuple):
            return inputs

        bridge_err = _check_routing_exact_out_oracle_adapter_bridge(
            body=obj,
            path="/api/dex/quote_exact_out_many_pool_guarded",
            **inputs,
        )
        if bridge_err is not None:
            return 400, {"ok": False, "error": "rejected", "detail": bridge_err}

        from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
            EXACT_OUT_MANY_POOL_GUARDED_QUOTE_PACKET_SCHEMA,
            EXACT_OUT_MANY_POOL_ORACLE_CONTRACT_SCHEMA,
            quote_exact_out_many_pool_guarded,
        )

        quote, err_msg, contract = quote_exact_out_many_pool_guarded(
            list(pools_by_id.values()),
            **inputs,
        )
        contract_dict = contract.to_dict()
        audit_payload = contract_dict["audit"]
        if quote is not None:
            return 200, {
                "ok": True,
                "quote": dict(audit_payload["runtime_quote"]),
                "contract": contract_dict,
                "contract_ok": bool(contract_dict["contract_ok"]),
                "contract_schema": EXACT_OUT_MANY_POOL_ORACLE_CONTRACT_SCHEMA,
                "packet_schema": EXACT_OUT_MANY_POOL_GUARDED_QUOTE_PACKET_SCHEMA,
                "build_contract_endpoint": "/api/dex/build_exact_out_many_pool_oracle_contract",
                "verify_contract_endpoint": "/api/dex/verify_exact_out_many_pool_oracle_contract",
                "build_packet_endpoint": "/api/dex/build_exact_out_many_pool_guarded_quote_packet",
                "verify_packet_endpoint": "/api/dex/verify_exact_out_many_pool_guarded_quote_packet",
                "runtime_projected_path": audit_payload["runtime_projected_path"],
                "canonical_winner_projected_path": audit_payload["canonical_winner_projected_path"],
                "runtime_matches_canonical_projected_path": audit_payload["runtime_matches_canonical_projected_path"],
                "projection_cover_available": audit_payload["projection_cover_available"],
                "projection_cover_holds": audit_payload["projection_cover_holds"],
            }
        return 200, {
            "ok": False,
            "error": str(err_msg or "many_pool_runtime_not_canonical"),
            "runtime_quote": dict(audit_payload["runtime_quote"]),
            "canonical_winner_quote": dict(audit_payload["canonical_winner_quote"]),
            "contract": contract_dict,
            "contract_ok": bool(contract_dict["contract_ok"]),
            "contract_schema": EXACT_OUT_MANY_POOL_ORACLE_CONTRACT_SCHEMA,
            "packet_schema": EXACT_OUT_MANY_POOL_GUARDED_QUOTE_PACKET_SCHEMA,
            "build_contract_endpoint": "/api/dex/build_exact_out_many_pool_oracle_contract",
            "verify_contract_endpoint": "/api/dex/verify_exact_out_many_pool_oracle_contract",
            "build_packet_endpoint": "/api/dex/build_exact_out_many_pool_guarded_quote_packet",
            "verify_packet_endpoint": "/api/dex/verify_exact_out_many_pool_guarded_quote_packet",
            "runtime_projected_path": audit_payload["runtime_projected_path"],
            "canonical_winner_projected_path": audit_payload["canonical_winner_projected_path"],
            "runtime_matches_canonical_projected_path": audit_payload["runtime_matches_canonical_projected_path"],
            "projection_cover_available": audit_payload["projection_cover_available"],
            "projection_cover_holds": audit_payload["projection_cover_holds"],
        }
    except Exception:
        return 400, {"ok": False, "error": "quote_exact_out_many_pool_guarded_error", "details": "request failed"}


_register("/api/dex/quote_exact_out_many_pool_guarded", _handle_quote_exact_out_many_pool_guarded)


def _handle_build_exact_out_many_pool_guarded_quote_packet(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
    """Uses packet.guard_ok (not packet_ok) as the success flag; adds guard_ok=False on failure."""
    try:
        pools_by_id = parse_pools(obj)
        inputs = _validate_guard_family_inputs(obj)
        if isinstance(inputs, tuple):
            return inputs

        from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
            EXACT_OUT_MANY_POOL_GUARDED_QUOTE_PACKET_SCHEMA,
            build_exact_out_many_pool_guarded_quote_packet,
        )

        packet = build_exact_out_many_pool_guarded_quote_packet(
            list(pools_by_id.values()),
            **inputs,
        )
        packet_dict = packet.to_dict()
        response: dict[str, Any] = {
            "ok": True,
            "packet": packet_dict,
            "packet_schema": EXACT_OUT_MANY_POOL_GUARDED_QUOTE_PACKET_SCHEMA,
            "verify_packet_endpoint": "/api/dex/verify_exact_out_many_pool_guarded_quote_packet",
        }
        if not packet.guard_ok:
            response["guard_ok"] = False
            response["error"] = str(packet.error or "many_pool_runtime_not_canonical")
        return 200, response
    except Exception:
        return 400, {"ok": False, "error": "build_exact_out_many_pool_guarded_quote_packet_error", "details": "request failed"}


_register("/api/dex/build_exact_out_many_pool_guarded_quote_packet", _handle_build_exact_out_many_pool_guarded_quote_packet)


# build_exact_out_many_pool_certified_winner_packet uses the standard 9-field
# packet builder shape with response_mode="ok_true". Fits the existing factory.
_certified_winner_field_specs = _int_field_specs_from_tuples(_PACKET_BUILDER_DEFAULT_FIELDS)
_register(
    "/api/dex/build_exact_out_many_pool_certified_winner_packet",
    _make_exact_out_many_pool_packet_builder(
        field_specs=_certified_winner_field_specs,
        module_function_name="build_exact_out_many_pool_certified_winner_packet",
        module_schema_name="EXACT_OUT_MANY_POOL_CERTIFIED_WINNER_PACKET_SCHEMA",
        verify_endpoint="/api/dex/verify_exact_out_many_pool_certified_winner_packet",
        error_code="build_exact_out_many_pool_certified_winner_packet_error",
        response_mode="ok_true",
    ),
    default_error_code="build_exact_out_many_pool_certified_winner_packet_error",
    schema=EndpointSchema(requires_pools=True, requires_assets=True, int_fields=_certified_winner_field_specs),
)


# ======================================================================
# PR2 Batch 8 — small settlement builders + repaired_full_domain_certified
# quote endpoint.
# ======================================================================
def _handle_build_settlement_feature_extension_packet(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
    feature_extension_inputs_obj = obj.get("feature_extension_inputs")
    try:

        feature_extension_inputs = _parse_settlement_feature_extension_inputs_payload(feature_extension_inputs_obj)
        packet = build_settlement_feature_extension_packet(feature_extension_inputs)
        return 200, {"ok": True, "packet": packet.to_dict()}
    except Exception:
        return 400, {"ok": False, "error": "build_settlement_feature_extension_packet_error", "details": "request failed"}


_register("/api/dex/build_settlement_feature_extension_packet", _handle_build_settlement_feature_extension_packet)


def _handle_build_settlement_spot_price_packet(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
    entries_obj = obj.get("entries")
    now_epoch = obj.get("now_epoch")
    max_staleness_epochs = obj.get("max_staleness_epochs")
    cross_module_sync_required = obj.get("cross_module_sync_required", False)
    cross_module_sync_contract = obj.get("cross_module_sync_contract")
    if not isinstance(entries_obj, list) or not entries_obj:
        return 400, {"ok": False, "error": "bad_entries"}
    if not isinstance(now_epoch, int) or isinstance(now_epoch, bool) or now_epoch < 0:
        return 400, {"ok": False, "error": "bad_now_epoch"}
    if not isinstance(max_staleness_epochs, int) or isinstance(max_staleness_epochs, bool) or max_staleness_epochs < 0:
        return 400, {"ok": False, "error": "bad_max_staleness_epochs"}
    if not isinstance(cross_module_sync_required, bool):
        return 400, {"ok": False, "error": "bad_cross_module_sync_required"}
    if cross_module_sync_contract is not None and not isinstance(cross_module_sync_contract, dict):
        return 400, {"ok": False, "error": "bad_cross_module_sync_contract"}
    try:
        entries = tuple(SettlementSpotPriceEntry.from_dict(entry) for entry in entries_obj)
        packet = build_settlement_spot_price_packet(
            entries=entries,
            now_epoch=int(now_epoch),
            max_staleness_epochs=int(max_staleness_epochs),
            cross_module_sync_required=bool(cross_module_sync_required),
            cross_module_sync_contract=cross_module_sync_contract,
        )
        return 200, {"ok": True, "packet": packet.to_dict()}
    except Exception:
        return 400, {"ok": False, "error": "build_settlement_spot_price_packet_error", "details": "request failed"}


_register("/api/dex/build_settlement_spot_price_packet", _handle_build_settlement_spot_price_packet)


def _handle_quote_exact_out_many_pool_repaired_full_domain_certified(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
    try:
        pools_by_id = parse_pools(obj)
        asset_in = str(obj.get("asset_in", "")).strip()
        asset_out = str(obj.get("asset_out", "")).strip()
        if not asset_in or not asset_out or asset_in == asset_out:
            return 400, {"ok": False, "error": "bad_assets"}
        int_kwargs: dict[str, int] = {}
        for name, default, minimum in _PACKET_BUILDER_DEFAULT_FIELDS:
            raw_value = obj.get(name, default)
            if not isinstance(raw_value, int) or isinstance(raw_value, bool) or raw_value < int(minimum):
                return 400, {"ok": False, "error": f"bad_{name}"}
            int_kwargs[name] = int(raw_value)

        from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
            EXACT_OUT_MANY_POOL_REPAIRED_FULL_DOMAIN_CERTIFIED_PACKET_SCHEMA,
            quote_exact_out_many_pool_repaired_full_domain_certified,
        )

        quote, err_msg, packet = quote_exact_out_many_pool_repaired_full_domain_certified(
            list(pools_by_id.values()),
            asset_in=asset_in,
            asset_out=asset_out,
            **int_kwargs,
        )
        payload = {
            "ok": bool(quote is not None),
            "packet": packet.to_dict(),
            "packet_schema": EXACT_OUT_MANY_POOL_REPAIRED_FULL_DOMAIN_CERTIFIED_PACKET_SCHEMA,
            "quote_policy": "repaired_full_domain_certified_v1",
            "build_packet_endpoint": "/api/dex/build_exact_out_many_pool_repaired_full_domain_certified_packet",
            "verify_packet_endpoint": "/api/dex/verify_exact_out_many_pool_repaired_full_domain_certified_packet",
            "runtime_quote": packet.repaired_packet.to_dict()["runtime_quote"],
            "full_domain_canonical_quote": packet.to_dict()["full_domain_canonical_quote"],
            "repaired_matches_full_canonical": bool(packet.repaired_matches_full_canonical),
            "full_domain_candidate_count": int(packet.full_domain_candidate_count),
            "full_domain_feasible_pool_ids": [str(pool_id) for pool_id in packet.full_domain_feasible_pool_ids],
        }
        if quote is not None:
            payload["quote"] = packet.to_dict()["repaired_quote"]
        else:
            payload["error"] = str(err_msg or "many_pool_repaired_advisory_not_full_domain_canonical")
        return 200, payload
    except Exception:
        return 400, {"ok": False, "error": "quote_exact_out_many_pool_repaired_full_domain_certified_error", "details": "request failed"}


_register("/api/dex/quote_exact_out_many_pool_repaired_full_domain_certified", _handle_quote_exact_out_many_pool_repaired_full_domain_certified)
