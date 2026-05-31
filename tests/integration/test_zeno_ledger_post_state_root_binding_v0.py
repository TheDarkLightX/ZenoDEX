"""ZenoLedger v0: a block header's post_state_root must bind to the re-executed body.

`validate_header_body_roots_v0` binds a header to its body's tx/ingress/evidence/body
roots and app_hash, but NOT to the resulting state — a header could carry ANY
post_state_root (even one inconsistent with applying the body) and pass. That is a
consensus disaster class: a block committing a wrong post-state, or an accepted body
that yields an un-committable (un-rootable) state stalling a producer.

`validate_block_state_transition_v0` closes it: it re-executes the body against the
pre-state and binds the claimed post_state_root to the recomputed committed root,
fail-closed (mismatch -> reject; un-rootable post-state -> reject, never crash).
"""

from __future__ import annotations

import pytest

from src.core.dex import DexState
from src.integration.dex_engine import DexEngineConfig
from src.integration.zeno_ledger_v0 import (
    build_header_v0,
    canonical_body_root_v0,
    compute_app_hash_v0,
    compute_evidence_root_v0,
    compute_ingress_root_v0,
    compute_tx_root_v0,
    dex_state_root_v0,
    validate_block_state_transition_v0,
)
from src.state.balances import BalanceTable
from src.state.lp import LPTable

# Reuse the canonical block-construction fixtures from the base v0 test module.
from tests.integration.test_zeno_ledger_v0 import _body, _root

ZERO_ROOT = "0x" + "00" * 32

_ASSET = "0x" + "22" * 32
_PK = "0x" + "11" * 48


def _canonical_pre_state() -> DexState:
    bal = BalanceTable()
    bal.set(_PK, _ASSET, 1_000)
    return DexState(balances=bal, pools={}, lp_balances=LPTable())


def _header_for(*, body: dict, post_state_root: str, pre_state_root: str) -> dict:
    """Build a structurally-valid header committing to `body` with the given roots
    (app_hash computed over post_state_root so validate_header_body_roots_v0 passes)."""
    evidence_root = compute_evidence_root_v0(body["evidence"])
    app_hash = compute_app_hash_v0(
        {
            "chain_id": body["chain_id"],
            "height": body["height"],
            "post_state_root": post_state_root,
            "evidence_root": evidence_root,
            "config_digest": _root("config"),
            "module_versions_digest": _root("modules"),
        }
    )
    return build_header_v0(
        chain_id=str(body["chain_id"]),
        height=int(body["height"]),
        time_ms=1_778_730_000_000,
        prev_header_hash=ZERO_ROOT,
        sequencer_set_hash=_root("sequencer-set"),
        ingress_root=compute_ingress_root_v0(body["ingress"]),
        tx_root=compute_tx_root_v0(body["transactions"]),
        pre_state_root=pre_state_root,
        post_state_root=post_state_root,
        app_hash=app_hash,
        evidence_root=evidence_root,
        body_root=canonical_body_root_v0(body),
        data_availability_root=_root("da"),
        proof_journal_hash=ZERO_ROOT,
        config_digest=_root("config"),
        module_versions_digest=_root("modules"),
        signature_set_root=ZERO_ROOT,
    )


def test_accepts_post_state_root_matching_reexecuted_body():
    pre = _canonical_pre_state()
    body = _body(txs=[])  # empty block: post-state == pre-state
    correct_root = dex_state_root_v0(pre)
    header = _header_for(body=body, post_state_root=correct_root, pre_state_root=correct_root)
    # Must not raise.
    validate_block_state_transition_v0(pre_state=pre, header=header, body=body, config=DexEngineConfig())


def test_rejects_post_state_root_not_matching_reexecuted_body():
    pre = _canonical_pre_state()
    body = _body(txs=[])
    # A header that is fully structurally valid (app_hash consistent with its claimed
    # post_state_root) but whose post_state_root is NOT the re-executed body's root.
    # validate_header_body_roots_v0 alone would accept this; the binding must reject it.
    wrong_root = _root("wrong-post-state")
    header = _header_for(body=body, post_state_root=wrong_root, pre_state_root=dex_state_root_v0(pre))
    with pytest.raises(ValueError, match="post_state_root does not match"):
        validate_block_state_transition_v0(pre_state=pre, header=header, body=body, config=DexEngineConfig())


def test_fails_closed_on_unrootable_post_state():
    # pre-state carries a non-canonical balance key (e.g. accepted via a permissive
    # path): compute_state_root cannot encode it. The binding must REJECT, not crash.
    bal = BalanceTable()
    bal.set("not_hex_recipient", _ASSET, 100)
    pre = DexState(balances=bal, pools={}, lp_balances=LPTable())
    body = _body(txs=[])
    header = _header_for(body=body, post_state_root=_root("any"), pre_state_root=_root("any"))
    with pytest.raises(ValueError, match="not computable"):
        validate_block_state_transition_v0(pre_state=pre, header=header, body=body, config=DexEngineConfig())
