"""Proof-mining payout-template assembly helpers."""

from __future__ import annotations

import json
from dataclasses import dataclass, replace
from typing import Any, Mapping, Sequence, cast

from src.core.batch_clearing import apply_settlement_pure, compute_settlement
from src.core.dex_intent_auth_message import build_dex_intent_signing_dict_v1
from src.core.proof_mining_claims import build_proof_mining_claim
from src.core.settlement_normal_form import normalize_settlement_op_for_commitment
from src.integration import dex_dispatch_proof_mining_snapshots as _snapshot_helpers
from src.integration.dex_dispatch_proof_mining_reward import (
    ProofMiningRewardConfig,
    canonical_asset_id,
    canonical_pubkey_48,
)
from src.integration.dex_dispatch_proof_mining_snapshots import (
    _load_latest_writer_snapshot_for_template,
)
from src.integration.dex_snapshot import snapshot_from_state, state_from_snapshot
from src.integration.lp_position_age_gate import apply_lp_mint_timestamps_after_settlement
from src.integration.operations import create_settlement_operation, parse_intents
from src.integration.proof_mining_context import (
    build_proof_mining_context,
    proof_mining_context_to_obj,
)
from src.state.balances import NATIVE_ASSET, BalanceTable
from src.state.nonces import validate_and_apply_intent_nonce_batch
from src.state.support_root import compute_support_state_root_for_batch

BOUNDARY_DOMAIN_ERRORS: tuple[type[Exception], ...] = (TypeError, ValueError, ArithmeticError)
DexResponse = tuple[int, Mapping[str, Any]]
urllib = _snapshot_helpers.urllib


class _TemplateReject(Exception):
    def __init__(self, status: int, body: Mapping[str, Any]) -> None:
        self.status = status
        self.body = dict(body)
        super().__init__(str(body.get("error", "template_rejected")))

    @property
    def response(self) -> DexResponse:
        return self.status, self.body


@dataclass(frozen=True)
class _TemplateIntent:
    intent: dict[str, Any]
    intent_for_proof: dict[str, Any]
    signature: str


@dataclass(frozen=True)
class _TemplateProofBundle:
    proof: dict[str, Any]
    settlement: Any
    settlement_op: dict[str, Any]
    context: Any


@dataclass(frozen=True)
class _TemplateProofParts:
    intents: Any
    proof: dict[str, Any]
    settlement: Any
    settlement_op: dict[str, Any]
    pre_state_commitment: str
    batch_commitment: str


@dataclass(frozen=True)
class _TemplateAssembly:
    obj: Mapping[str, Any]
    sender: str
    chain_id: str
    tx_block_timestamp: int
    template_intent: _TemplateIntent
    faucet_mint: list[Any]
    bundle: _TemplateProofBundle
    reward: ProofMiningRewardConfig


def _copy_balances_for_template(source: BalanceTable) -> BalanceTable:
    copied = BalanceTable()
    for (pubkey, asset), amount in source.get_all_balances().items():
        copied.set(str(pubkey), str(asset), int(amount))
    return copied


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


def _template_intent(obj: Mapping[str, Any], *, sender: str) -> _TemplateIntent:
    signed_intent = obj.get("signed_intent")
    if not isinstance(signed_intent, Mapping):
        raise _TemplateReject(400, {"ok": False, "error": "bad_signed_intent"})
    raw_intent = signed_intent.get("intent", signed_intent)
    if not isinstance(raw_intent, Mapping):
        raise _TemplateReject(400, {"ok": False, "error": "bad_intent"})

    intent = dict(raw_intent)
    signature = signed_intent.get("signature", intent.get("signature"))
    if not isinstance(signature, str) or not signature:
        raise _TemplateReject(400, {"ok": False, "error": "missing_signature"})
    intent["signature"] = signature
    if str(intent.get("sender_pubkey", "")).lower() != sender:
        raise _TemplateReject(400, {"ok": False, "error": "sender_mismatch"})
    return _TemplateIntent(
        intent=intent,
        intent_for_proof={k: v for k, v in intent.items() if k != "signature"},
        signature=signature,
    )


def _template_state(obj: Mapping[str, Any], ctx: Any) -> Any:
    snapshot_obj = obj.get("pre_state_snapshot")
    if snapshot_obj is None:
        snapshot_obj = _load_latest_writer_snapshot_for_template(ctx)
    if not isinstance(snapshot_obj, Mapping):
        raise _TemplateReject(400, {"ok": False, "error": "bad_pre_state_snapshot"})
    return state_from_snapshot(snapshot_obj)


def _template_faucet_mint(obj: Mapping[str, Any]) -> list[Any]:
    faucet_mint = obj.get("faucet_mint", [])
    if faucet_mint is None:
        return []
    if not isinstance(faucet_mint, list):
        raise _TemplateReject(400, {"ok": False, "error": "bad_faucet_mint"})
    return faucet_mint


def _template_state_with_faucet(state: Any, faucet_mint: list[Any], *, sender: str) -> Any:
    balances = _copy_balances_for_template(state.balances)
    for index, entry in enumerate(faucet_mint):
        if not isinstance(entry, Mapping):
            raise _TemplateReject(400, {"ok": False, "error": "bad_faucet_mint_entry", "index": index})
        pubkey = canonical_pubkey_48(entry.get("pubkey", sender), name=f"faucet_mint[{index}].pubkey")
        asset = canonical_asset_id(entry.get("asset"), name=f"faucet_mint[{index}].asset")
        amount = entry.get("amount")
        if not isinstance(amount, int) or isinstance(amount, bool) or amount <= 0:
            raise _TemplateReject(400, {"ok": False, "error": "bad_faucet_mint_amount", "index": index})
        balances.set(pubkey, asset, int(balances.get(pubkey, asset)) + int(amount))
    return replace(state, balances=balances)


def _template_state_with_native_reward_pool(state: Any, reward: ProofMiningRewardConfig) -> Any:
    balances = _copy_balances_for_template(state.balances)
    current = int(balances.get(reward.pool_pubkey, NATIVE_ASSET))
    if current not in (0, int(reward.pool_before)):
        raise _TemplateReject(
            400,
            {
                "ok": False,
                "error": "reward_pool_native_balance_mismatch",
                "reward_pool_pubkey": reward.pool_pubkey,
            },
        )
    balances.set(reward.pool_pubkey, NATIVE_ASSET, int(reward.pool_before))
    return replace(state, balances=balances)


def _settlement_operation_payload_for_template(settlement: Any) -> dict[str, Any]:
    operation = create_settlement_operation(settlement)
    if len(operation) != 1:
        raise ValueError("settlement operation must contain exactly one entry")
    payload = next(iter(operation.values()))
    if not isinstance(payload, Mapping):
        raise TypeError("settlement operation payload must be a mapping")
    return dict(payload)


def _template_proof_parts(proof_state: Any, template_intent: _TemplateIntent) -> _TemplateProofParts:
    operations_without_proof = {"2": [template_intent.intent_for_proof]}
    intents = parse_intents(operations_without_proof)
    settlement = compute_settlement(
        intents=intents,
        pools=proof_state.pools,
        balances=proof_state.balances,
        lp_balances=proof_state.lp_balances,
    )
    settlement_op = _settlement_operation_payload_for_template(settlement)
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
        "operations": {
            "2": [template_intent.intent_for_proof],
            "3": settlement_op_for_proof,
            "5": [template_intent.intent_for_proof],
        },
    }
    settlement_op["proof"] = proof
    return _TemplateProofParts(
        intents=intents,
        proof=proof,
        settlement=settlement,
        settlement_op=settlement_op,
        pre_state_commitment=pre_state_commitment,
        batch_commitment=batch_commitment,
    )


def _template_next_state(proof_state: Any, parts: _TemplateProofParts, *, tx_block_timestamp: int) -> Any:
    next_balances, next_pools, next_lp = apply_settlement_pure(
        settlement=parts.settlement,
        balances=proof_state.balances,
        pools=proof_state.pools,
        lp_balances=proof_state.lp_balances,
    )
    lp_age_err = apply_lp_mint_timestamps_after_settlement(
        lp_balances=next_lp,
        settlement=parts.settlement,
        block_timestamp=tx_block_timestamp,
        duration_risk_policy=None,
    )
    if lp_age_err is not None:
        raise _TemplateReject(
            400,
            {"ok": False, "error": "lp_duration_risk_update_failed", "details": lp_age_err},
        )
    nonce_ok, nonce_err, next_nonces = validate_and_apply_intent_nonce_batch(
        nonces=proof_state.nonces,
        intents=parts.intents,
        require_all_nonces=True,
    )
    if not nonce_ok or next_nonces is None:
        raise _TemplateReject(
            400,
            {"ok": False, "error": "bad_intent_nonce", "details": nonce_err or "nonce rejected"},
        )
    return replace(
        proof_state,
        balances=next_balances,
        pools=next_pools,
        lp_balances=next_lp,
        nonces=next_nonces,
    )


def _template_proof_bundle(
    *,
    proof_state: Any,
    template_intent: _TemplateIntent,
    tx_block_timestamp: int,
    chain_id: str,
) -> _TemplateProofBundle:
    parts = _template_proof_parts(proof_state, template_intent)
    next_state = _template_next_state(
        proof_state,
        parts,
        tx_block_timestamp=tx_block_timestamp,
    )
    context = build_proof_mining_context(
        chain_id=chain_id,
        prev_state_hash=parts.pre_state_commitment,
        batch_hash=parts.batch_commitment,
        proof=parts.proof,
        next_state=next_state,
        proof_scheme="recompute_batch_v4",
    )
    return _TemplateProofBundle(
        proof=parts.proof,
        settlement=parts.settlement,
        settlement_op=parts.settlement_op,
        context=context,
    )


def _template_default_digest(assembly: _TemplateAssembly) -> str:
    return _template_stable_digest(
        {
            "chain_id": assembly.chain_id,
            "sender": assembly.sender,
            "block_timestamp": assembly.tx_block_timestamp,
            "intent": assembly.template_intent.intent_for_proof,
            "signature": assembly.template_intent.signature,
            "faucet_mint": assembly.faucet_mint,
            "pre_state_commitment": assembly.bundle.context.prev_state_hash,
            "batch_hash": assembly.bundle.context.batch_hash,
            "witness_hash": assembly.bundle.context.witness_hash,
            "dex_hash_after": assembly.bundle.context.dex_hash_after,
            "reward_pool_pubkey": assembly.reward.pool_pubkey,
            "reward_asset_id": assembly.reward.asset_id,
            "reward_pool_before": assembly.reward.pool_before,
            "base_reward": assembly.reward.base_reward,
            "epoch": assembly.reward.epoch,
            "proposal_slot": assembly.reward.proposal_slot,
            "prover_id": assembly.reward.prover_id,
            "improvement_u64": assembly.reward.improvement_u64,
        }
    )


def _template_claim(assembly: _TemplateAssembly, default_id_digest: str) -> Mapping[str, Any]:
    job_digest = str(assembly.obj.get("job_digest") or f"local-proof-mining:{default_id_digest}")
    round_id = str(assembly.obj.get("round_id") or f"local-proof-mining-round:{default_id_digest}")
    return cast(
        Mapping[str, Any],
        build_proof_mining_claim(
            round_obj={
                "schema": "zenodex/improvement_bounty_round/v1",
                "ok": True,
                "job_digest": job_digest,
                "winner": {
                    "miner_id": assembly.sender,
                    "witness_sha256": assembly.bundle.context.witness_hash,
                    "improvement_u64": assembly.reward.improvement_u64,
                },
                "candidates": [],
                "argmax_certificate": None,
            },
            round_id=round_id,
            reward_pool_before=assembly.reward.pool_before,
            base_reward=assembly.reward.base_reward,
            epoch=assembly.reward.epoch,
            proposal_slot=assembly.reward.proposal_slot,
            prover_id=assembly.reward.prover_id,
            chain_id=assembly.chain_id,
            prev_state_hash=assembly.bundle.context.prev_state_hash,
            batch_hash=assembly.bundle.context.batch_hash,
            dex_hash_after=assembly.bundle.context.dex_hash_after,
        ),
    )


def _template_response(assembly: _TemplateAssembly, claim: Mapping[str, Any]) -> Mapping[str, Any]:
    tx = {
        "tx_id": str(assembly.obj.get("tx_id") or f"proof-mining-payout:{claim['claim_hash']}"),
        "tx_sender_pubkey": assembly.sender,
        "operations": {
            **({"7": {"mint": assembly.faucet_mint}} if assembly.faucet_mint else {}),
            "5": [assembly.template_intent.intent],
            "6": assembly.bundle.settlement_op,
            "10": {
                "module": "ZenoProofMining",
                "action": "submit_proof",
                "claim": claim,
                "recipient_pubkey": assembly.sender,
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
            assembly.reward.pool_pubkey: {
                assembly.reward.asset_id: assembly.reward.pool_before,
            },
        },
        "claim": claim,
        "proof_mining_context": proof_mining_context_to_obj(assembly.bundle.context),
        "tx_sender_pubkey": assembly.sender,
        "expected_proposal_hash": claim["body"]["proposal_hash"],
        "reward_pool_pubkey": assembly.reward.pool_pubkey,
        "reward_asset_id": assembly.reward.asset_id,
    }
    return {
        "ok": True,
        "tx": tx,
        "execution_context_requirements": {
            "block_time_seconds": assembly.tx_block_timestamp,
        },
        "status_request": status_request,
        "reward_pool_pubkey": assembly.reward.pool_pubkey,
        "reward_asset_id": assembly.reward.asset_id,
        "reward_pool_before": assembly.reward.pool_before,
    }


def _template_success_body(assembly: _TemplateAssembly) -> Mapping[str, Any]:
    default_id_digest = _template_default_digest(assembly)
    claim = _template_claim(assembly, default_id_digest)
    return _template_response(assembly, claim)
