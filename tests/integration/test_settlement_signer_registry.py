from __future__ import annotations

import importlib.util

import pytest

from src.integration.settlement_price_provenance import (
    SettlementSpotPriceEntry,
    build_settlement_spot_price_packet,
)
from src.integration.settlement_signer_registry import (
    ChainAnchoredSettlementSignerRegistrySnapshotLoader,
    InMemorySettlementSignerRegistryAnchorLoader,
    InMemorySettlementSignerRegistrySnapshotLoader,
    JsonRpcSettlementSignerRegistryAnchorLoader,
    SettlementSignerRegistrySnapshot,
    TauNetSettlementSignerRegistrySnapshotLoader,
    check_settlement_attestation_policy_registry_binding,
    coerce_settlement_signer_registry_anchor,
    coerce_settlement_signer_registry_contract_interface,
    coerce_settlement_signer_registry_snapshot,
    load_attestation_policy_and_registry_snapshot,
    resolve_attestation_policy_and_registry_snapshot,
)
from src.integration.tau_net_client import TauNetAppStateView, TauNetStateProofView
from tests.integration._attestation_policy_helper import (
    build_policy_bound_attestation,
    make_attestation_policy,
    make_attestation_registry_anchor,
    make_attestation_registry_contract_interface,
    make_attestation_registry_snapshot,
)

pytestmark = pytest.mark.skipif(importlib.util.find_spec("py_ecc") is None, reason="py_ecc is not available")


def _attestation():
    packet = build_settlement_spot_price_packet(
        entries=(
            SettlementSpotPriceEntry(
                asset="0x" + "01" * 32,
                price=100,
                observed_epoch=95,
                age_epochs=5,
                source_id="oracle:a",
            ),
            SettlementSpotPriceEntry(
                asset="0x" + "02" * 32,
                price=120,
                observed_epoch=97,
                age_epochs=3,
                source_id="oracle:b",
            ),
        ),
        now_epoch=100,
        max_staleness_epochs=10,
    )
    attestation, _policy = build_policy_bound_attestation(packet=packet, signer_privkey=7)
    return attestation


def test_settlement_signer_registry_snapshot_round_trips_and_resolves_policy() -> None:
    attestation = _attestation()
    snapshot = make_attestation_registry_snapshot(attestation)

    rebuilt = SettlementSignerRegistrySnapshot.from_dict(snapshot.to_dict())
    coerced = coerce_settlement_signer_registry_snapshot(snapshot.to_dict())
    resolved_policy, resolved_snapshot = resolve_attestation_policy_and_registry_snapshot(
        attestation_policy=None,
        attestation_registry_snapshot=snapshot.to_dict(),
    )

    assert rebuilt == snapshot
    assert coerced == snapshot
    assert resolved_snapshot == snapshot
    assert resolved_policy == snapshot.policy
    assert rebuilt.snapshot_hash_hex() == snapshot.snapshot_hash_hex()


def test_settlement_signer_registry_binding_rejects_policy_drift() -> None:
    attestation = _attestation()
    policy = make_attestation_policy(attestation)
    snapshot = make_attestation_registry_snapshot(attestation, policy_epoch=2)

    result = check_settlement_attestation_policy_registry_binding(
        policy=policy,
        registry_snapshot=snapshot,
    )

    assert result.ok is False
    assert result.error_code == "attestation_registry_binding_policy_epoch_mismatch"
    assert result.error is not None
    assert result.error.startswith("attestation policy_epoch does not match registry snapshot policy")
    assert result.details is not None
    assert result.details["policy_epoch"] == 1
    assert result.details["snapshot_policy_epoch"] == 2


def test_settlement_signer_registry_loader_returns_bound_snapshot() -> None:
    attestation = _attestation()
    policy = make_attestation_policy(attestation)
    snapshot = make_attestation_registry_snapshot(attestation)
    loader = InMemorySettlementSignerRegistrySnapshotLoader(
        {
            (
                int(policy.chain_id),
                policy.registry_contract,
                policy.policy_id,
                int(policy.policy_epoch),
            ): snapshot
        }
    )

    resolved_policy, resolved_snapshot = load_attestation_policy_and_registry_snapshot(
        attestation_policy=policy,
        attestation_registry_snapshot=None,
        attestation_registry_snapshot_loader=loader,
        consumer_now_epoch=103,
    )

    assert resolved_policy == policy
    assert resolved_snapshot == snapshot


def test_settlement_signer_registry_anchor_round_trips() -> None:
    attestation = _attestation()
    anchor = make_attestation_registry_anchor(attestation)

    rebuilt = coerce_settlement_signer_registry_anchor(anchor.to_dict())

    assert rebuilt == anchor


def test_settlement_signer_registry_contract_interface_round_trips() -> None:
    attestation = _attestation()
    interface = make_attestation_registry_contract_interface(attestation)

    rebuilt = coerce_settlement_signer_registry_contract_interface(interface.to_dict())

    assert rebuilt == interface


def test_chain_anchored_snapshot_loader_rebinds_snapshot_to_anchor_block() -> None:
    attestation = _attestation()
    policy = make_attestation_policy(attestation)
    source_snapshot = make_attestation_registry_snapshot(
        attestation,
        snapshot_block_number=7,
        snapshot_block_hash="0x" + "90" * 32,
    )
    anchor = make_attestation_registry_anchor(
        attestation,
        anchor_block_number=55,
        anchor_block_hash="0x" + "ab" * 32,
    )
    anchored_loader = ChainAnchoredSettlementSignerRegistrySnapshotLoader(
        anchor_loader=InMemorySettlementSignerRegistryAnchorLoader(
            {(int(policy.chain_id), policy.registry_contract, policy.policy_id, int(policy.policy_epoch)): anchor}
        ),
        snapshot_loader=InMemorySettlementSignerRegistrySnapshotLoader(
            {(int(policy.chain_id), policy.registry_contract, policy.policy_id, int(policy.policy_epoch)): source_snapshot}
        ),
    )

    resolved_policy, resolved_snapshot = load_attestation_policy_and_registry_snapshot(
        attestation_policy=policy,
        attestation_registry_snapshot=None,
        attestation_registry_snapshot_loader=anchored_loader,
        consumer_now_epoch=103,
    )

    assert resolved_policy == policy
    assert resolved_snapshot is not None
    assert resolved_snapshot.snapshot_block_number == 55
    assert resolved_snapshot.snapshot_block_hash == "0x" + "ab" * 32
    assert resolved_snapshot.registry_root == anchor.registry_root
    assert resolved_snapshot.policy == source_snapshot.policy


def test_chain_anchored_snapshot_loader_rejects_anchor_drift() -> None:
    attestation = _attestation()
    policy = make_attestation_policy(attestation)
    snapshot = make_attestation_registry_snapshot(attestation)
    drifting_anchor = make_attestation_registry_anchor(attestation, anchor_block_number=99)
    drifting_anchor = coerce_settlement_signer_registry_anchor(
        {
            **drifting_anchor.to_dict(),
            "policy_hash": "0x" + "ff" * 32,
        }
    )
    anchored_loader = ChainAnchoredSettlementSignerRegistrySnapshotLoader(
        anchor_loader=InMemorySettlementSignerRegistryAnchorLoader(
            {(int(policy.chain_id), policy.registry_contract, policy.policy_id, int(policy.policy_epoch)): drifting_anchor}
        ),
        snapshot_loader=InMemorySettlementSignerRegistrySnapshotLoader(
            {(int(policy.chain_id), policy.registry_contract, policy.policy_id, int(policy.policy_epoch)): snapshot}
        ),
    )

    with pytest.raises(ValueError, match="attestation registry anchor policy_hash does not match request hint"):
        load_attestation_policy_and_registry_snapshot(
            attestation_policy=policy,
            attestation_registry_snapshot=None,
            attestation_registry_snapshot_loader=anchored_loader,
            consumer_now_epoch=103,
        )


def test_json_rpc_settlement_signer_registry_anchor_loader_accepts_typed_anchor() -> None:
    attestation = _attestation()
    policy = make_attestation_policy(attestation)
    interface = make_attestation_registry_contract_interface(attestation)
    request_seen: dict[str, object] = {}

    def _transport(endpoint_url: str, headers: dict[str, str], payload: dict[str, object], timeout_s: float) -> dict[str, object]:
        request_seen["endpoint_url"] = endpoint_url
        request_seen["headers"] = headers
        request_seen["payload"] = payload
        request_seen["timeout_s"] = timeout_s
        return {
            "jsonrpc": "2.0",
            "id": payload["id"],
            "result": make_attestation_registry_anchor(attestation).to_dict(),
        }

    loader = JsonRpcSettlementSignerRegistryAnchorLoader(
        "https://rpc.example.invalid",
        interface=interface,
        transport=_transport,
    )

    resolved_policy, resolved_snapshot = load_attestation_policy_and_registry_snapshot(
        attestation_policy=policy,
        attestation_registry_snapshot=None,
        attestation_registry_snapshot_loader=ChainAnchoredSettlementSignerRegistrySnapshotLoader(
            anchor_loader=loader,
            snapshot_loader=InMemorySettlementSignerRegistrySnapshotLoader(
                {
                    (int(policy.chain_id), policy.registry_contract, policy.policy_id, int(policy.policy_epoch)): (
                        make_attestation_registry_snapshot(attestation)
                    )
                }
            ),
        ),
        consumer_now_epoch=103,
    )

    assert resolved_policy == policy
    assert resolved_snapshot is not None
    assert request_seen["endpoint_url"] == "https://rpc.example.invalid"
    assert request_seen["timeout_s"] == 5.0
    assert isinstance(request_seen["headers"], dict)
    assert request_seen["payload"] == {
        "jsonrpc": "2.0",
        "id": "settlement-signer-registry-anchor",
        "method": "zenodex_getSettlementSignerRegistryAnchor",
        "params": {
            "chain_id": 1,
            "registry_contract": policy.registry_contract,
            "policy_id": policy.policy_id,
            "policy_epoch": 1,
            "registry_root_hint": policy.registry_root,
            "policy_hash_hint": policy.policy_hash_hex(),
            "consumer_now_epoch": 103,
        },
    }


def test_json_rpc_settlement_signer_registry_anchor_loader_rejects_rpc_error() -> None:
    attestation = _attestation()
    policy = make_attestation_policy(attestation)
    interface = make_attestation_registry_contract_interface(attestation)

    def _transport(_endpoint_url: str, _headers: dict[str, str], payload: dict[str, object], _timeout_s: float) -> dict[str, object]:
        return {
            "jsonrpc": "2.0",
            "id": payload["id"],
            "error": {"code": -32001, "message": "anchor unavailable", "data": {"retryable": False}},
        }

    loader = JsonRpcSettlementSignerRegistryAnchorLoader(
        "https://rpc.example.invalid",
        interface=interface,
        transport=_transport,
    )

    with pytest.raises(ValueError, match="attestation registry json-rpc returned an error"):
        load_attestation_policy_and_registry_snapshot(
            attestation_policy=policy,
            attestation_registry_snapshot=None,
            attestation_registry_snapshot_loader=ChainAnchoredSettlementSignerRegistrySnapshotLoader(
                anchor_loader=loader,
                snapshot_loader=InMemorySettlementSignerRegistrySnapshotLoader(
                    {(int(policy.chain_id), policy.registry_contract, policy.policy_id, int(policy.policy_epoch)): make_attestation_registry_snapshot(attestation)}
                ),
            ),
            consumer_now_epoch=103,
        )


def test_json_rpc_settlement_signer_registry_anchor_loader_rejects_interface_drift() -> None:
    attestation = _attestation()
    policy = make_attestation_policy(attestation)
    drifting_interface = make_attestation_registry_contract_interface(attestation, chain_id=2)

    loader = JsonRpcSettlementSignerRegistryAnchorLoader(
        "https://rpc.example.invalid",
        interface=drifting_interface,
        transport=lambda *_args: {"jsonrpc": "2.0", "id": "settlement-signer-registry-anchor", "result": None},
    )

    with pytest.raises(ValueError, match="attestation registry interface chain_id does not match request"):
        load_attestation_policy_and_registry_snapshot(
            attestation_policy=policy,
            attestation_registry_snapshot=None,
            attestation_registry_snapshot_loader=ChainAnchoredSettlementSignerRegistrySnapshotLoader(
                anchor_loader=loader,
                snapshot_loader=InMemorySettlementSignerRegistrySnapshotLoader(
                    {(int(policy.chain_id), policy.registry_contract, policy.policy_id, int(policy.policy_epoch)): make_attestation_registry_snapshot(attestation)}
                ),
            ),
            consumer_now_epoch=103,
        )


class _FakeTauClient:
    def __init__(
        self,
        *,
        app_state_view: TauNetAppStateView | list[TauNetAppStateView],
        state_proof_view: TauNetStateProofView | list[TauNetStateProofView],
    ) -> None:
        self._app_state_views = app_state_view if isinstance(app_state_view, list) else [app_state_view]
        self._state_proof_views = state_proof_view if isinstance(state_proof_view, list) else [state_proof_view]
        self._app_state_index = 0
        self._state_proof_index = 0

    def getappstate_view(self) -> TauNetAppStateView:
        idx = min(self._app_state_index, len(self._app_state_views) - 1)
        self._app_state_index += 1
        return self._app_state_views[idx]

    def getstateproof_view(self) -> TauNetStateProofView:
        idx = min(self._state_proof_index, len(self._state_proof_views) - 1)
        self._state_proof_index += 1
        return self._state_proof_views[idx]


def test_tau_net_settlement_signer_registry_loader_reads_bridge_from_app_state() -> None:
    attestation = _attestation()
    policy = make_attestation_policy(attestation)
    anchor = make_attestation_registry_anchor(attestation)
    source_snapshot = make_attestation_registry_snapshot(
        attestation,
        snapshot_block_number=7,
        snapshot_block_hash="0x" + "90" * 32,
    )
    tau_loader = TauNetSettlementSignerRegistrySnapshotLoader(
        _FakeTauClient(
            app_state_view=TauNetAppStateView(
                app_hash="ab" * 32,
                app_state={
                    "schema": "zenodex/tau_app_state/v1",
                    "settlement_signer_registry_tau_bridge": {
                        "schema": "zenodex/settlement-signer-registry-tau-bridge/v1",
                        "anchor": anchor.to_dict(),
                        "snapshot": source_snapshot.to_dict(),
                    },
                },
            ),
            state_proof_view=TauNetStateProofView(
                state_hash="cd" * 32,
                present=True,
                proof_type="risc0.tauswap_transition.v1",
                proof_bytes=123,
                proof_sha256="ef" * 32,
            ),
        )
    )

    resolved_policy, resolved_snapshot = load_attestation_policy_and_registry_snapshot(
        attestation_policy=policy,
        attestation_registry_snapshot=None,
        attestation_registry_snapshot_loader=tau_loader,
        consumer_now_epoch=103,
    )

    assert resolved_policy == policy
    assert resolved_snapshot is not None
    assert resolved_snapshot.snapshot_block_number == anchor.anchor_block_number
    assert resolved_snapshot.snapshot_block_hash == anchor.anchor_block_hash
    assert resolved_snapshot.policy == source_snapshot.policy


def test_tau_net_settlement_signer_registry_loader_rejects_missing_state_proof() -> None:
    attestation = _attestation()
    policy = make_attestation_policy(attestation)
    anchor = make_attestation_registry_anchor(attestation)
    snapshot = make_attestation_registry_snapshot(attestation)
    tau_loader = TauNetSettlementSignerRegistrySnapshotLoader(
        _FakeTauClient(
            app_state_view=TauNetAppStateView(
                app_hash="ab" * 32,
                app_state={
                    "settlement_signer_registry_tau_bridge": {
                        "schema": "zenodex/settlement-signer-registry-tau-bridge/v1",
                        "anchor": anchor.to_dict(),
                        "snapshot": snapshot.to_dict(),
                    }
                },
            ),
            state_proof_view=TauNetStateProofView(state_hash="cd" * 32, present=False),
        )
    )

    with pytest.raises(ValueError, match="Tau state proof missing for settlement signer registry bridge"):
        load_attestation_policy_and_registry_snapshot(
            attestation_policy=policy,
            attestation_registry_snapshot=None,
            attestation_registry_snapshot_loader=tau_loader,
            consumer_now_epoch=103,
        )


def test_tau_net_settlement_signer_registry_loader_rejects_missing_bridge_payload() -> None:
    attestation = _attestation()
    policy = make_attestation_policy(attestation)
    tau_loader = TauNetSettlementSignerRegistrySnapshotLoader(
        _FakeTauClient(
            app_state_view=TauNetAppStateView(
                app_hash="ab" * 32,
                app_state={"schema": "zenodex/tau_app_state/v1"},
            ),
            state_proof_view=TauNetStateProofView(state_hash="cd" * 32, present=True),
        )
    )

    with pytest.raises(ValueError, match="Tau app_state is missing settlement signer registry bridge payload"):
        load_attestation_policy_and_registry_snapshot(
            attestation_policy=policy,
            attestation_registry_snapshot=None,
            attestation_registry_snapshot_loader=tau_loader,
            consumer_now_epoch=103,
        )


def test_tau_net_settlement_signer_registry_loader_retries_until_state_proof_view_stabilizes() -> None:
    attestation = _attestation()
    policy = make_attestation_policy(attestation)
    anchor = make_attestation_registry_anchor(attestation)
    snapshot = make_attestation_registry_snapshot(attestation)
    app_state_view = TauNetAppStateView(
        app_hash="ab" * 32,
        app_state={
            "settlement_signer_registry_tau_bridge": {
                "schema": "zenodex/settlement-signer-registry-tau-bridge/v1",
                "anchor": anchor.to_dict(),
                "snapshot": snapshot.to_dict(),
            }
        },
    )
    tau_loader = TauNetSettlementSignerRegistrySnapshotLoader(
        _FakeTauClient(
            app_state_view=[app_state_view, app_state_view],
            state_proof_view=[
                TauNetStateProofView(state_hash="cd" * 32, present=True, proof_type="proof-a"),
                TauNetStateProofView(state_hash="ef" * 32, present=True, proof_type="proof-b"),
                TauNetStateProofView(state_hash="aa" * 32, present=True, proof_type="proof-c"),
                TauNetStateProofView(state_hash="aa" * 32, present=True, proof_type="proof-c"),
            ],
        ),
        stable_read_attempts=2,
    )

    resolved_policy, resolved_snapshot = load_attestation_policy_and_registry_snapshot(
        attestation_policy=policy,
        attestation_registry_snapshot=None,
        attestation_registry_snapshot_loader=tau_loader,
        consumer_now_epoch=103,
    )

    assert resolved_policy == policy
    assert resolved_snapshot is not None
    assert resolved_snapshot.snapshot_block_hash == anchor.anchor_block_hash


def test_tau_net_settlement_signer_registry_loader_rejects_unstable_state_proof_view() -> None:
    attestation = _attestation()
    policy = make_attestation_policy(attestation)
    anchor = make_attestation_registry_anchor(attestation)
    snapshot = make_attestation_registry_snapshot(attestation)
    app_state_view = TauNetAppStateView(
        app_hash="ab" * 32,
        app_state={
            "settlement_signer_registry_tau_bridge": {
                "schema": "zenodex/settlement-signer-registry-tau-bridge/v1",
                "anchor": anchor.to_dict(),
                "snapshot": snapshot.to_dict(),
            }
        },
    )
    tau_loader = TauNetSettlementSignerRegistrySnapshotLoader(
        _FakeTauClient(
            app_state_view=[app_state_view, app_state_view],
            state_proof_view=[
                TauNetStateProofView(state_hash="cd" * 32, present=True, proof_type="proof-a"),
                TauNetStateProofView(state_hash="ef" * 32, present=True, proof_type="proof-b"),
                TauNetStateProofView(state_hash="11" * 32, present=True, proof_type="proof-c"),
                TauNetStateProofView(state_hash="22" * 32, present=True, proof_type="proof-d"),
            ],
        ),
        stable_read_attempts=2,
    )

    with pytest.raises(ValueError, match="Tau state proof view changed during settlement signer registry bridge load"):
        load_attestation_policy_and_registry_snapshot(
            attestation_policy=policy,
            attestation_registry_snapshot=None,
            attestation_registry_snapshot_loader=tau_loader,
            consumer_now_epoch=103,
        )
