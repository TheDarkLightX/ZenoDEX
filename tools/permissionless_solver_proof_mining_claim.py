#!/usr/bin/env python3
"""Build a proof-mining-compatible claim from a verified permissionless solver round."""

from __future__ import annotations

import argparse
import json
import os
import sys
from pathlib import Path
from typing import Any, Mapping

# Allow `python3 tools/...` from repo root without needing `-m`.
_REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
if _REPO_ROOT not in sys.path:
    sys.path.insert(0, _REPO_ROOT)

from src.core.proof_mining_claims import (  # noqa: E402
    DEFAULT_MIN_VERIFIER_DOMAIN_DIVERSITY,
    DEFAULT_MIN_VERIFIER_QUORUM,
    MAX_EPOCH,
    MAX_PROPOSAL_SLOT,
    MAX_PROVER_ID,
    U32_MAX,
    build_proof_mining_claim,
    explicit_proposal_hash,
    fallback_proposal_hash,
    proof_mining_claim_hash,
    schedule_reward_amount,
    validate_proof_mining_claim_artifact,
)


def _require_mapping(value: Any, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be an object")
    return value


def _load_json(path: Path) -> Mapping[str, Any]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    return _require_mapping(obj, name=str(path))


def _parse_verifier_arg(value: str) -> dict[str, int]:
    parts = str(value).split(":")
    if len(parts) != 2:
        raise argparse.ArgumentTypeError("--verifier must use verifier_id:domain_id")
    try:
        verifier_id = int(parts[0])
        domain_id = int(parts[1])
    except ValueError as exc:
        raise argparse.ArgumentTypeError("--verifier ids must be integers") from exc
    return {"verifier_id": verifier_id, "domain_id": domain_id, "accepted": 1}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Emit a proof-mining-compatible claim from a verified solver round")
    parser.add_argument("--round", required=True, help="Verified round JSON path")
    parser.add_argument("--output", required=True, help="Output JSON path")
    parser.add_argument("--round-id", required=True, help="Deterministic round identifier")
    parser.add_argument("--reward-pool-before", type=int, required=True)
    parser.add_argument("--base-reward", type=int, required=True)
    parser.add_argument("--epoch", type=int, required=True)
    parser.add_argument("--proposal-slot", type=int, required=True)
    parser.add_argument("--prover-id", type=int, required=True)
    parser.add_argument("--chain-id", default="", help="Optional explicit proposal binding field")
    parser.add_argument("--prev-state-hash", default="", help="Optional explicit proposal binding field")
    parser.add_argument("--batch-hash", default="", help="Optional explicit proposal binding field")
    parser.add_argument("--dex-hash-after", default="", help="Optional explicit proposal binding field")
    parser.add_argument("--proof-ok", type=int, default=1)
    parser.add_argument("--binding-ok", type=int, default=1)
    parser.add_argument("--policy-ok", type=int, default=1)
    parser.add_argument("--nonce-ok", type=int, default=1)
    parser.add_argument("--unclaimed-ok", type=int, default=1)
    parser.add_argument(
        "--verifier",
        action="append",
        default=[],
        type=_parse_verifier_arg,
        help="Accepted verifier evidence as verifier_id:domain_id. Repeat for quorum.",
    )
    parser.add_argument(
        "--min-verifier-quorum",
        type=int,
        default=DEFAULT_MIN_VERIFIER_QUORUM,
    )
    parser.add_argument(
        "--min-verifier-domain-diversity",
        type=int,
        default=DEFAULT_MIN_VERIFIER_DOMAIN_DIVERSITY,
    )
    parser.add_argument(
        "--allow-gate-fail",
        action="store_true",
        help="Allow emission even when the Tau or verifier-evidence proof-mining gate would reject the claim.",
    )
    args = parser.parse_args(argv)

    claim = build_proof_mining_claim(
        round_obj=_load_json(Path(args.round)),
        round_id=str(args.round_id),
        reward_pool_before=int(args.reward_pool_before),
        base_reward=int(args.base_reward),
        epoch=int(args.epoch),
        proposal_slot=int(args.proposal_slot),
        prover_id=int(args.prover_id),
        proof_ok=int(args.proof_ok),
        binding_ok=int(args.binding_ok),
        policy_ok=int(args.policy_ok),
        nonce_ok=int(args.nonce_ok),
        unclaimed_ok=int(args.unclaimed_ok),
        chain_id=str(args.chain_id),
        prev_state_hash=str(args.prev_state_hash),
        batch_hash=str(args.batch_hash),
        dex_hash_after=str(args.dex_hash_after),
        allow_rejected=bool(args.allow_gate_fail),
        verifier_evidence=list(args.verifier),
        min_verifier_quorum=int(args.min_verifier_quorum),
        min_verifier_domain_diversity=int(args.min_verifier_domain_diversity),
    )
    Path(args.output).write_text(json.dumps(claim, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
