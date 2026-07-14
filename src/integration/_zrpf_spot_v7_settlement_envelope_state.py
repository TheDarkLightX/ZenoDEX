"""Deterministic restricted state replay and ledger binding for Spot V7."""

from __future__ import annotations

from dataclasses import replace
from typing import Any

from src.core.dex import DexState
from src.integration._zrpf_spot_v7_atomic_settlement_capability import (
    _SpotV7SettlementCandidateInputV1,
)
from src.integration._zrpf_spot_v7_journal_projection import (
    _DecodedSpotV7SemanticJournalProjectionV1,
)
from src.integration._zrpf_spot_v7_settlement_envelope_codec import _hex, _sha256
from src.integration._zrpf_spot_v7_settlement_envelope_contract import (
    SpotV7SettlementEnvelopeReplayErrorV1,
)
from src.integration._zrpf_spot_v7_zeno_ledger_replay_observation import (
    _parse_body_proof_receipt_projection,
)
from src.integration.dex_snapshot import state_from_snapshot
from src.integration.zeno_ledger_replay import load_replay_snapshot_v0
from src.integration.zeno_ledger_spot_state_domain_bridge_v1 import (
    SpotStateDomainBridgeErrorV1,
    _derive_authenticated_spot_ledger_state_domain_bridge_v1,
)
from src.integration.zeno_ledger_v0 import (
    ZERO_ROOT_V0,
    dex_state_root_v0,
    validate_header_body_roots_v0,
    validate_header_chain_linkage_v0,
    validate_header_chain_state_continuity_v0,
)
from src.integration.zrpf_spot_v7_atomic_settlement_types import (
    SpotV7CellKindV1,
    SpotV7CellTransitionV1,
)


def _apply_exact_candidate(
    candidate: _SpotV7SettlementCandidateInputV1,
    semantic: _DecodedSpotV7SemanticJournalProjectionV1,
    pre_snapshot: dict[str, Any],
) -> DexState:
    try:
        pre_state, canonical_snapshot = load_replay_snapshot_v0(pre_snapshot)
    except (KeyError, TypeError, ValueError) as exc:
        raise SpotV7SettlementEnvelopeReplayErrorV1("pre_snapshot") from exc
    if dex_state_root_v0(pre_state) != candidate.pre_state_root:
        raise SpotV7SettlementEnvelopeReplayErrorV1("pre_state_root")
    working = state_from_snapshot(canonical_snapshot)
    sender = _hex(semantic.sender_pubkey)
    account_subjects = {
        row.pre.subject_id
        for row in candidate.cell_transitions
        if row.pre.kind is SpotV7CellKindV1.ACCOUNT_BALANCE
    }
    if account_subjects != {sender}:
        raise SpotV7SettlementEnvelopeReplayErrorV1("sender_transition")
    _apply_cell_transitions(working, candidate.cell_transitions)
    expected_pre_nonces = (
        {} if semantic.ingress_nonce == 1 else {sender: semantic.ingress_nonce - 1}
    )
    if working.nonces.get_all() != expected_pre_nonces:
        raise SpotV7SettlementEnvelopeReplayErrorV1("nonce_transition")
    working.nonces.set_last(sender, semantic.ingress_nonce)
    _require_state_domain_bridge(candidate, semantic, pre_state, working)
    if dex_state_root_v0(working) != candidate.post_state_root:
        raise SpotV7SettlementEnvelopeReplayErrorV1("post_state_root")
    return working


def _require_state_domain_bridge(
    candidate: _SpotV7SettlementCandidateInputV1,
    semantic: _DecodedSpotV7SemanticJournalProjectionV1,
    pre_state: DexState,
    post_state: DexState,
) -> None:
    sender = _hex(semantic.sender_pubkey)
    try:
        _derive_authenticated_spot_ledger_state_domain_bridge_v1(
            pre_state=pre_state,
            post_state=post_state,
            transactions=({"tx_sender_pubkey": sender, "nonce": semantic.ingress_nonce},),
            source_pre_app_hash=_hex(semantic.source_pre_app_hash),
            source_post_app_hash=_hex(semantic.source_post_app_hash),
            source_pre_nonce_root=_hex(semantic.source_pre_nonce_root),
            source_post_nonce_root=_hex(semantic.source_post_nonce_root),
            ledger_pre_state_root=candidate.pre_state_root,
            ledger_post_state_root=candidate.post_state_root,
        )
    except SpotStateDomainBridgeErrorV1 as exc:
        raise SpotV7SettlementEnvelopeReplayErrorV1("state_domain_bridge") from exc


def _apply_cell_transitions(
    state: DexState,
    transitions: tuple[SpotV7CellTransitionV1, ...],
) -> None:
    for transition in transitions:
        opening = transition.pre
        if opening.kind is SpotV7CellKindV1.ACCOUNT_BALANCE:
            if state.balances.get(opening.subject_id, opening.asset_id) != opening.atoms:
                raise SpotV7SettlementEnvelopeReplayErrorV1("cell_opening")
            state.balances.set(opening.subject_id, opening.asset_id, transition.post.atoms)
            continue
        pool = state.pools.get(opening.subject_id)
        if pool is None:
            raise SpotV7SettlementEnvelopeReplayErrorV1("cell_opening")
        if opening.asset_id == pool.asset0:
            actual = pool.reserve0
            updated = replace(pool, reserve0=transition.post.atoms)
        elif opening.asset_id == pool.asset1:
            actual = pool.reserve1
            updated = replace(pool, reserve1=transition.post.atoms)
        else:
            raise SpotV7SettlementEnvelopeReplayErrorV1("cell_opening")
        if actual != opening.atoms:
            raise SpotV7SettlementEnvelopeReplayErrorV1("cell_opening")
        state.pools[opening.subject_id] = updated


def _require_ledger_bindings(
    *,
    candidate: _SpotV7SettlementCandidateInputV1,
    header: dict[str, Any],
    body: dict[str, Any],
    config_digest: str,
    config_chain_id: str,
    parent_header: dict[str, Any] | None,
) -> None:
    try:
        validate_header_body_roots_v0(header, body)
        if parent_header is None:
            if header["height"] not in (0, 1) or header["prev_header_hash"] != ZERO_ROOT_V0:
                raise SpotV7SettlementEnvelopeReplayErrorV1("parent_anchor")
        else:
            validate_header_chain_linkage_v0([parent_header, header])
            validate_header_chain_state_continuity_v0([parent_header, header])
    except SpotV7SettlementEnvelopeReplayErrorV1:
        raise
    except (KeyError, TypeError, ValueError) as exc:
        raise SpotV7SettlementEnvelopeReplayErrorV1("header_body_binding") from exc
    if body.get("transactions") != []:
        raise SpotV7SettlementEnvelopeReplayErrorV1("transactions_not_empty")
    if body["evidence"]["rejection_receipts"] != []:
        raise SpotV7SettlementEnvelopeReplayErrorV1("rejection_receipts")
    try:
        committed_journal = _parse_body_proof_receipt_projection(body["evidence"]["proof_receipts"])
    except (KeyError, TypeError, ValueError) as exc:
        raise SpotV7SettlementEnvelopeReplayErrorV1("proof_receipt_projection") from exc
    expected_journal = _sha256(candidate.exact_v7_journal_bytes)
    checks = (
        (header["chain_id"] == config_chain_id, "config_chain_id"),
        (header["config_digest"] == config_digest, "config_digest"),
        (header["height"] == candidate.epoch_id, "epoch"),
        (header["pre_state_root"] == candidate.pre_state_root, "pre_state_root"),
        (header["post_state_root"] == candidate.post_state_root, "post_state_root"),
        (header["data_availability_root"] == candidate.data_root, "data_root"),
        (header["proof_journal_hash"] == expected_journal, "proof_journal_hash"),
        (committed_journal == expected_journal, "proof_receipt_projection"),
    )
    for accepted, code in checks:
        if not accepted:
            raise SpotV7SettlementEnvelopeReplayErrorV1(code)
