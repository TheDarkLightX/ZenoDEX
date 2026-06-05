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

from dataclasses import replace

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


@pytest.mark.parametrize("field_name", ["vault", "oracle", "perps"])
def test_dex_state_root_v0_rejects_non_spot_lanes(field_name: str):
    # REVIEW [C -> A-]: D-CANON-002 was a root-collision review failure: the
    # spot ledger root ignored support-lane fields while accepting a full
    # DexState. The adapter now rejects any non-None vault/oracle/perps lane
    # before computing a root, forcing callers onto a dedicated lane root or a
    # future full-app commitment.
    state = replace(_canonical_pre_state(), **{field_name: object()})
    with pytest.raises(ValueError, match=field_name):
        dex_state_root_v0(state)


@pytest.mark.parametrize("field_name", ["vault", "oracle", "perps"])
def test_block_transition_rejects_pre_state_with_uncommitted_non_spot_lane(field_name: str):
    # REVIEW [B -> A]: the first regression test covered only perps, but the
    # consensus adapter's D-CANON-002 contract is the full excluded-lane set:
    # vault/oracle/perps must all be rejected before root binding. Parametrizing
    # the transition path keeps future edits from weakening one sibling lane.
    clean_pre = _canonical_pre_state()
    uncommitted_pre = replace(clean_pre, **{field_name: object()})
    body = _body(txs=[])
    spot_root = dex_state_root_v0(clean_pre)
    header = _header_for(body=body, post_state_root=spot_root, pre_state_root=spot_root)

    with pytest.raises(ValueError, match=f"pre_state_root not computable.*{field_name}"):
        validate_block_state_transition_v0(
            pre_state=uncommitted_pre,
            header=header,
            body=body,
            config=DexEngineConfig(),
        )


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


def test_fails_closed_on_unrootable_state():
    # pre-state carries a non-canonical balance key (e.g. accepted via a permissive
    # path): compute_state_root cannot encode it. The binding must REJECT, not crash.
    # NOTE: with an empty body (pre == post) this exercises the PRE-state root guard,
    # which fails before re-execution. The POST-state guard at validate_block_state_
    # transition_v0 is the symmetric `try: dex_state_root_v0(working_state) except ->
    # ValueError("not computable")`; covering it directly needs a body whose accepted
    # tx mutates state to a non-canonical key (executable-tx fixture) — tracked as a
    # follow-up. The C-1 accept guard prevents that under require_intent_signatures.
    bal = BalanceTable()
    bal.set("not_hex_recipient", _ASSET, 100)
    pre = DexState(balances=bal, pools={}, lp_balances=LPTable())
    body = _body(txs=[])
    header = _header_for(body=body, post_state_root=_root("any"), pre_state_root=_root("any"))
    with pytest.raises(ValueError, match="not computable"):
        validate_block_state_transition_v0(pre_state=pre, header=header, body=body, config=DexEngineConfig())


def test_rejects_pre_state_root_not_matching_supplied_pre_state():
    # Header claims a pre_state_root that is NOT the supplied pre-state's root: the
    # transition must be anchored at the pre end too, so this is rejected.
    pre = _canonical_pre_state()
    body = _body(txs=[])
    correct = dex_state_root_v0(pre)
    header = _header_for(body=body, post_state_root=correct, pre_state_root=_root("wrong-pre-state"))
    with pytest.raises(ValueError, match="pre_state_root does not match supplied pre_state"):
        validate_block_state_transition_v0(pre_state=pre, header=header, body=body, config=DexEngineConfig())


# ---- (b) chain state continuity: child.pre_state_root == parent.post_state_root ----

from src.integration.zeno_ledger_v0 import validate_header_chain_state_continuity_v0  # noqa: E402


def test_chain_state_continuity_accepts_continuous_chain():
    body = _body(txs=[])
    r0, r1, r2 = _root("s0"), _root("s1"), _root("s2")
    h1 = _header_for(body=body, post_state_root=r1, pre_state_root=r0)
    h2 = _header_for(body=body, post_state_root=r2, pre_state_root=r1)  # h2.pre == h1.post
    validate_header_chain_state_continuity_v0([h1, h2])  # must not raise


def test_chain_state_continuity_rejects_state_discontinuity():
    body = _body(txs=[])
    r0, r1, r2 = _root("s0"), _root("s1"), _root("s2")
    h1 = _header_for(body=body, post_state_root=r1, pre_state_root=r0)
    # h2 is hash-linkable but claims a pre_state_root that is NOT h1's post_state_root.
    h2_disc = _header_for(body=body, post_state_root=r2, pre_state_root=_root("forged-pre"))
    with pytest.raises(ValueError, match="does not match parent post_state_root"):
        validate_header_chain_state_continuity_v0([h1, h2_disc])
