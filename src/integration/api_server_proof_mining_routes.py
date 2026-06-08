from __future__ import annotations

import os
from dataclasses import dataclass
from typing import Callable, Mapping


WriteJson = Callable[[int, object], None]

_PROOF_MINING_STATUS_ENDPOINT = "/api/dex/proof_mining_status"


@dataclass(frozen=True)
class _ProofMiningStatusRequest:
    claim_artifact: dict[str, object]
    chain_balances: dict[str, object]
    tx_sender_pubkey: str
    expected_proposal_hash: str
    app_state_json: str


class BadRequest(Exception):
    def __init__(self, error: str) -> None:
        super().__init__(error)
        self.error = error


def _parse_request(obj: dict[str, object]) -> _ProofMiningStatusRequest:
    claim_artifact = _claim_artifact(obj.get("claim"))
    chain_balances = _chain_balances(obj.get("chain_balances", {}))
    _reject_proof_mining_context(obj)
    app_state_json = _app_state_json(obj.get("app_state_json", ""))
    tx_sender_pubkey = _required_text(obj.get("tx_sender_pubkey", ""), "missing_tx_sender_pubkey")
    expected_proposal_hash = _required_text(
        obj.get("expected_proposal_hash", ""),
        "missing_expected_proposal_hash",
    )
    return _ProofMiningStatusRequest(
        claim_artifact=claim_artifact,
        chain_balances=chain_balances,
        tx_sender_pubkey=tx_sender_pubkey,
        expected_proposal_hash=expected_proposal_hash,
        app_state_json=app_state_json,
    )


def _claim_artifact(value: object) -> dict[str, object]:
    if not isinstance(value, dict):
        raise BadRequest("bad_claim")
    return value


def _chain_balances(value: object) -> dict[str, object]:
    if not isinstance(value, dict):
        raise BadRequest("bad_chain_balances")
    return value


def _reject_proof_mining_context(obj: dict[str, object]) -> None:
    if "proof_mining_context" in obj:
        raise BadRequest("proof_mining_context_not_accepted")


def _app_state_json(value: object) -> str:
    if not isinstance(value, str):
        raise BadRequest("bad_app_state_json")
    return value


def _required_text(value: object, error: str) -> str:
    text = str(value)
    if not text:
        raise BadRequest(error)
    return text


def _reward_pool_pubkey_from_env(environ: Mapping[str, str] | None = None) -> str | None:
    env = os.environ if environ is None else environ
    return str(env.get("TAU_DEX_PROOF_MINING_POOL_PUBKEY", "")).strip() or None


def _handle_proof_mining_status(obj: dict[str, object], write_json: WriteJson) -> None:
    try:
        request = _parse_request(obj)
    except BadRequest as exc:
        write_json(400, {"ok": False, "error": exc.error})
        return

    try:
        from src.integration.proof_mining_claimability import (  # pylint: disable=import-outside-toplevel
            evaluate_proof_mining_claimability,
        )

        status = evaluate_proof_mining_claimability(
            reward_pool_pubkey=_reward_pool_pubkey_from_env(),
            app_state_json=request.app_state_json,
            chain_balances=request.chain_balances,
            claim_artifact=request.claim_artifact,
            tx_sender_pubkey=request.tx_sender_pubkey,
            expected_proposal_hash=request.expected_proposal_hash,
            proof_mining_context_obj=None,
        )
        write_json(200, {"ok": True, "status": status.to_public_dict()})
    except Exception:
        write_json(400, {"ok": False, "error": "proof_mining_status_error", "details": "request failed"})


def maybe_handle_proof_mining_route(
    *,
    path: str,
    obj: dict[str, object],
    write_json: WriteJson,
) -> bool:
    if path != _PROOF_MINING_STATUS_ENDPOINT:
        return False
    _handle_proof_mining_status(obj, write_json)
    return True
