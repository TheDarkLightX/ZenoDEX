from __future__ import annotations

import importlib.util

import pytest

if importlib.util.find_spec("hypothesis") is None:  # pragma: no cover
    pytest.skip("hypothesis not installed", allow_module_level=True)

import hypothesis.strategies as st
from hypothesis import given, settings

from src.integration.zeno_ledger_anti_equivocation_v0 import (
    build_checkpoint_equivocation_slashing_evidence_v0,
    validate_checkpoint_non_equivocation_v0,
)
from src.integration.zeno_ledger_bonded_slashing_v0 import (
    BPS_SCALE_V0,
    apply_bonded_slashing_v0,
    build_bond_registry_v0,
    build_slashing_policy_v0,
    validate_bonded_slashing_receipt_v0,
)
from src.integration.zeno_ledger_dynamic_peers_v0 import (
    build_dynamic_peer_admission_v0,
    build_dynamic_peer_candidate_v0,
    canonical_peer_urls_v0,
    validate_dynamic_peer_admission_v0,
)
from src.integration.zeno_ledger_v0 import build_checkpoint_v0, build_header_v0, hash_v0


ZERO_ROOT = "0x" + "00" * 32


def _root(label: str) -> str:
    return hash_v0("symbolic_safety_test_root", {"label": label})


def _header(*, height: int, body_label: str) -> dict[str, object]:
    return build_header_v0(
        chain_id="zeno-ledger-symbolic-safety-testnet-0",
        height=height,
        time_ms=1_778_730_000_000 + height,
        prev_header_hash=ZERO_ROOT,
        sequencer_set_hash=_root("sequencer-set"),
        ingress_root=_root(f"ingress-{body_label}"),
        tx_root=_root(f"tx-{body_label}"),
        pre_state_root=_root(f"pre-{body_label}"),
        post_state_root=_root(f"post-{body_label}"),
        app_hash=_root(f"app-{body_label}"),
        evidence_root=_root(f"evidence-{body_label}"),
        body_root=_root(f"body-{body_label}"),
        data_availability_root=_root(f"da-{body_label}"),
        proof_journal_hash=_root(f"proof-{body_label}"),
        config_digest=_root("config"),
        module_versions_digest=_root("modules"),
        signature_set_root=ZERO_ROOT,
    )


def _checkpoint_evidence(*, height: int = 7) -> dict[str, object]:
    checkpoint_a = build_checkpoint_v0(_header(height=height, body_label="a"))
    checkpoint_b = build_checkpoint_v0(_header(height=height, body_label="b"))
    return build_checkpoint_equivocation_slashing_evidence_v0(checkpoint_a, checkpoint_b)


def _registry_for(
    evidence: dict[str, object],
    *,
    bonded_amount: int,
    slashed_amount: int,
) -> dict[str, object]:
    return build_bond_registry_v0(
        chain_id=str(evidence["chain_id"]),
        asset_id="ZENO",
        entries=[
            {
                "subject_id": evidence["subject_id"],
                "subject_kind": "validator_set",
                "bonded_amount": bonded_amount,
                "slashed_amount": slashed_amount,
                "slashable_until_height": 100,
                "status": "active",
                "processed_evidence_hashes": [],
            }
        ],
    )


@settings(max_examples=160, deadline=None)
@given(data=st.data())
def test_symbolic_bonded_slashing_never_exceeds_available_bond(data: st.DataObject) -> None:
    bonded = data.draw(st.integers(min_value=1, max_value=20_000), label="bonded")
    already_slashed = data.draw(st.integers(min_value=0, max_value=bonded - 1), label="already_slashed")
    available = bonded - already_slashed
    max_slash = data.draw(st.integers(min_value=1, max_value=available), label="max_slash")
    min_slash = data.draw(st.integers(min_value=1, max_value=max_slash), label="min_slash")
    slash_fraction_bps = data.draw(st.integers(min_value=0, max_value=BPS_SCALE_V0), label="slash_fraction_bps")
    burn_fraction_bps = data.draw(st.integers(min_value=0, max_value=BPS_SCALE_V0), label="burn_fraction_bps")

    evidence = _checkpoint_evidence()
    registry = _registry_for(
        evidence,
        bonded_amount=bonded,
        slashed_amount=already_slashed,
    )
    policy = build_slashing_policy_v0(
        chain_id=str(evidence["chain_id"]),
        policy_id="symbolic-slashing-policy-v0",
        evidence_kind=str(evidence["evidence_kind"]),
        slash_fraction_bps=slash_fraction_bps,
        min_slash_amount=min_slash,
        max_slash_amount=max_slash,
        burn_fraction_bps=burn_fraction_bps,
    )

    transition = apply_bonded_slashing_v0(evidence=evidence, bond_registry=registry, policy=policy)
    receipt = transition["receipt"]
    updated_entry = transition["bond_registry"]["entries"][0]
    expected_slash = min(max((bonded * slash_fraction_bps) // BPS_SCALE_V0, min_slash), max_slash)

    assert 1 <= receipt["slash_amount"] <= available
    assert receipt["slash_amount"] == expected_slash
    assert receipt["burn_amount"] + receipt["treasury_amount"] == receipt["slash_amount"]
    assert receipt["remaining_bond"] == bonded - already_slashed - receipt["slash_amount"]
    assert updated_entry["slashed_amount"] == already_slashed + receipt["slash_amount"]
    assert updated_entry["processed_evidence_hashes"] == [evidence["evidence_hash"]]
    validate_bonded_slashing_receipt_v0(
        receipt=receipt,
        updated_bond_registry=transition["bond_registry"],
        evidence=evidence,
        bond_registry_before=registry,
        policy=policy,
    )


@settings(max_examples=160, deadline=None)
@given(
    height=st.integers(min_value=0, max_value=500),
    body_a=st.text(
        alphabet=st.characters(whitelist_categories=("Ll", "Lu", "Nd")),
        min_size=1,
        max_size=12,
    ),
    body_b=st.text(
        alphabet=st.characters(whitelist_categories=("Ll", "Lu", "Nd")),
        min_size=1,
        max_size=12,
    ),
)
def test_symbolic_checkpoint_conflicts_are_rejected(height: int, body_a: str, body_b: str) -> None:
    if body_a == body_b:
        body_b = f"{body_b}x"
    checkpoint_a = build_checkpoint_v0(_header(height=height, body_label=body_a))
    checkpoint_b = build_checkpoint_v0(_header(height=height, body_label=body_b))

    with pytest.raises(ValueError, match="checkpoint equivocation"):
        validate_checkpoint_non_equivocation_v0([checkpoint_a, checkpoint_b])
    validate_checkpoint_non_equivocation_v0([checkpoint_a, dict(checkpoint_a)])


def _peer_url(port: int) -> str:
    return f"http://127.0.0.1:{port}"


def _peer_check(*, network_id: str, chain_id: str, urls: list[str]) -> dict[str, object]:
    return {
        "schema": "zenodex.zeno_ledger.node_peer_check_report.v0",
        "ok": True,
        "status": "accepted",
        "node_id": "node-a",
        "network_id": network_id,
        "chain_id": chain_id,
        "feature_suite_hash": _root("feature-suite"),
        "local_tip": {"height": 5, "header_hash": _root("tip")},
        "peer_count": len(urls),
        "peers": [{"peer_url": url, "ok": True, "status": "accepted"} for url in urls],
    }


@settings(max_examples=160, deadline=None)
@given(data=st.data())
def test_symbolic_dynamic_peer_admission_preserves_cap_and_binding(data: st.DataObject) -> None:
    network_id = "zeno-ledger-symbolic-peer-testnet-0"
    chain_id = "zeno-ledger-symbolic-peer-testnet-0"
    current_ports = data.draw(
        st.lists(st.integers(min_value=8_800, max_value=8_820), max_size=4),
        label="current_ports",
    )
    candidate_ports = data.draw(
        st.lists(st.integers(min_value=8_810, max_value=8_840), min_size=1, max_size=5),
        label="candidate_ports",
    )
    current = canonical_peer_urls_v0([_peer_url(port) for port in current_ports], name="current")
    candidate_urls = canonical_peer_urls_v0([_peer_url(port) for port in candidate_ports], name="candidate")
    final_urls = canonical_peer_urls_v0([*current, *candidate_urls], name="final")
    cap = data.draw(st.integers(min_value=len(final_urls), max_value=len(final_urls) + 3), label="cap")

    candidate = build_dynamic_peer_candidate_v0(
        network_id=network_id,
        chain_id=chain_id,
        source_node_id="node-a",
        source_peer_url=_peer_url(8_799),
        candidate_peer_urls=candidate_urls,
        observed_at_height=5,
    )
    peer_check = _peer_check(network_id=network_id, chain_id=chain_id, urls=candidate_urls)
    admission = build_dynamic_peer_admission_v0(
        current_peer_urls=current,
        candidate=candidate,
        peer_check_report=peer_check,
        max_peer_count=cap,
    )

    assert admission["final_peer_count"] <= cap
    assert admission["final_peer_urls"] == final_urls
    assert admission["admitted_peer_urls"] == [url for url in candidate_urls if url not in set(current)]
    validate_dynamic_peer_admission_v0(
        admission=admission,
        current_peer_urls=current,
        candidate=candidate,
        peer_check_report=peer_check,
        max_peer_count=cap,
    )


def test_symbolic_dynamic_peer_admission_teeth_rejects_mismatched_peer_check() -> None:
    network_id = "zeno-ledger-symbolic-peer-testnet-0"
    chain_id = "zeno-ledger-symbolic-peer-testnet-0"
    candidate = build_dynamic_peer_candidate_v0(
        network_id=network_id,
        chain_id=chain_id,
        source_node_id="node-a",
        source_peer_url=_peer_url(8_799),
        candidate_peer_urls=[_peer_url(8_801)],
        observed_at_height=5,
    )
    peer_check = _peer_check(network_id=network_id, chain_id=chain_id, urls=[_peer_url(8_802)])

    with pytest.raises(ValueError, match="peer-check URLs do not match"):
        build_dynamic_peer_admission_v0(
            current_peer_urls=[],
            candidate=candidate,
            peer_check_report=peer_check,
            max_peer_count=4,
        )
