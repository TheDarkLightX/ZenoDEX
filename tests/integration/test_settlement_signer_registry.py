from __future__ import annotations

import hashlib
import importlib.util

import pytest

import src.integration.tau_net_client as tau_net_client
import src.integration.settlement_signer_registry as registry_mod
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
from src.integration.tau_net_client import (
    TauNetAppStateView,
    TauNetStateProofView,
    TauNetTauStateView,
)
from src.state.canonical import canonical_json_bytes
from tests.integration._attestation_policy_helper import (
    build_policy_bound_attestation,
    make_attestation_policy,
    make_attestation_registry_anchor,
    make_attestation_registry_contract_interface,
    make_attestation_registry_snapshot,
)

pytestmark = pytest.mark.skipif(importlib.util.find_spec("py_ecc") is None, reason="py_ecc is not available")


def _require_blake3() -> None:
    if importlib.util.find_spec("blake3") is None:
        pytest.skip("blake3 not installed (install blake3 to run Tau state commitment validation tests)")


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


def test_json_rpc_transport_rejects_oversized_response(monkeypatch) -> None:
    class _HugeResponse:
        def __enter__(self):
            return self

        def __exit__(self, _exc_type, _exc, _traceback):
            return False

        def read(self, size: int = -1) -> bytes:
            assert size == registry_mod._JSON_RPC_MAX_RESPONSE_BYTES + 1
            return b"x" * (registry_mod._JSON_RPC_MAX_RESPONSE_BYTES + 1)

    monkeypatch.setattr(registry_mod.urllib_request, "urlopen", lambda *_args, **_kwargs: _HugeResponse())

    with pytest.raises(ValueError, match="json-rpc response exceeds size limit"):
        registry_mod._json_rpc_post_json(
            endpoint_url="https://rpc.example.invalid",
            headers={},
            payload={"jsonrpc": "2.0", "id": "test", "method": "test", "params": {}},
            timeout_s=1.0,
        )


class _FakeTauClient:
    def __init__(
        self,
        *,
        app_state_view: TauNetAppStateView | list[TauNetAppStateView],
        state_proof_view: TauNetStateProofView | list[TauNetStateProofView],
        tau_state_view: TauNetTauStateView | list[TauNetTauStateView] | None = None,
    ) -> None:
        self._app_state_views = app_state_view if isinstance(app_state_view, list) else [app_state_view]
        self._state_proof_views = state_proof_view if isinstance(state_proof_view, list) else [state_proof_view]
        if tau_state_view is None:
            self._tau_state_views: list[TauNetTauStateView] = []
        else:
            self._tau_state_views = tau_state_view if isinstance(tau_state_view, list) else [tau_state_view]
        self._app_state_index = 0
        self._state_proof_index = 0
        self._tau_state_index = 0

    def getappstate_view(self) -> TauNetAppStateView:
        idx = min(self._app_state_index, len(self._app_state_views) - 1)
        self._app_state_index += 1
        return self._app_state_views[idx]

    def getstateproof_view(self) -> TauNetStateProofView:
        idx = min(self._state_proof_index, len(self._state_proof_views) - 1)
        self._state_proof_index += 1
        return self._state_proof_views[idx]

    def gettaustate_view(self, _state_hash: str) -> TauNetTauStateView:
        if not self._tau_state_views:
            raise AssertionError("unexpected gettaustate_view call")
        idx = min(self._tau_state_index, len(self._tau_state_views) - 1)
        self._tau_state_index += 1
        return self._tau_state_views[idx]


def _tau_bridge_app_state_view(bridge_payload: dict[str, object], *, app_hash: str | None = None) -> TauNetAppStateView:
    app_state = {
        "schema": "zenodex/tau_app_state/v1",
        "settlement_signer_registry_tau_bridge": bridge_payload,
    }
    return TauNetAppStateView(
        app_hash=hashlib.sha256(canonical_json_bytes(app_state)).hexdigest() if app_hash is None else app_hash,
        app_state=app_state,
    )


def _tau_state_proof_view(
    *,
    state_hash: str,
    present: bool,
    proof_type: str | None = None,
    proof_bytes: int | None = None,
    proof_sha256: str | None = None,
    error: str | None = None,
) -> TauNetStateProofView:
    return TauNetStateProofView(
        state_hash=state_hash,
        present=present,
        proof_type=proof_type,
        proof_bytes=proof_bytes,
        proof_sha256=proof_sha256,
        error=error,
    )


def _tau_tau_state_view(
    *,
    state_hash: str | None = None,
    app_hash: str,
    rules: str = "rule_text",
    accounts_hash: str | None = None,
) -> TauNetTauStateView:
    normalized_accounts_hash = ("12" * 32) if accounts_hash is None else accounts_hash
    normalized_state_hash = (
        tau_net_client.compute_tau_state_commitment_hash_hex(
            rules=rules,
            accounts_hash=normalized_accounts_hash,
            app_hash=app_hash,
        )
        if state_hash is None
        else state_hash
    )
    return TauNetTauStateView(
        state_hash=normalized_state_hash,
        rules=rules,
        accounts_hash=normalized_accounts_hash,
        app_hash=app_hash,
    )


def test_tau_net_settlement_signer_registry_loader_reads_bridge_from_app_state() -> None:
    attestation = _attestation()
    policy = make_attestation_policy(attestation)
    anchor = make_attestation_registry_anchor(attestation)
    source_snapshot = make_attestation_registry_snapshot(
        attestation,
        snapshot_block_number=7,
        snapshot_block_hash="0x" + "90" * 32,
    )
    app_state_view = _tau_bridge_app_state_view(
        {
            "schema": "zenodex/settlement-signer-registry-tau-bridge/v1",
            "anchor": anchor.to_dict(),
            "snapshot": source_snapshot.to_dict(),
        }
    )
    tau_loader = TauNetSettlementSignerRegistrySnapshotLoader(
        _FakeTauClient(
            app_state_view=app_state_view,
            state_proof_view=_tau_state_proof_view(
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


def test_tau_net_settlement_signer_registry_loader_binds_app_hash_to_tau_state_when_enabled() -> None:
    _require_blake3()
    attestation = _attestation()
    policy = make_attestation_policy(attestation)
    anchor = make_attestation_registry_anchor(attestation)
    source_snapshot = make_attestation_registry_snapshot(attestation)
    app_state_view = _tau_bridge_app_state_view(
        {
            "schema": "zenodex/settlement-signer-registry-tau-bridge/v1",
            "anchor": anchor.to_dict(),
            "snapshot": source_snapshot.to_dict(),
        }
    )
    tau_state_view = _tau_tau_state_view(app_hash=app_state_view.app_hash)
    tau_loader = TauNetSettlementSignerRegistrySnapshotLoader(
        _FakeTauClient(
            app_state_view=app_state_view,
            state_proof_view=_tau_state_proof_view(
                state_hash=tau_state_view.state_hash,
                present=True,
                proof_type="risc0.tauswap_transition.v1",
                proof_bytes=123,
                proof_sha256="ef" * 32,
            ),
            tau_state_view=tau_state_view,
        ),
        require_tau_state_app_hash_binding=True,
    )

    resolved_policy, resolved_snapshot = load_attestation_policy_and_registry_snapshot(
        attestation_policy=policy,
        attestation_registry_snapshot=None,
        attestation_registry_snapshot_loader=tau_loader,
        consumer_now_epoch=103,
    )

    assert resolved_policy == policy
    assert resolved_snapshot is not None
    assert resolved_snapshot.policy == source_snapshot.policy


def test_tau_net_settlement_signer_registry_loader_rejects_tau_state_app_hash_drift() -> None:
    _require_blake3()
    attestation = _attestation()
    policy = make_attestation_policy(attestation)
    anchor = make_attestation_registry_anchor(attestation)
    snapshot = make_attestation_registry_snapshot(attestation)
    app_state_view = _tau_bridge_app_state_view(
        {
            "schema": "zenodex/settlement-signer-registry-tau-bridge/v1",
            "anchor": anchor.to_dict(),
            "snapshot": snapshot.to_dict(),
        }
    )
    tau_state_view = _tau_tau_state_view(app_hash="34" * 32)
    tau_loader = TauNetSettlementSignerRegistrySnapshotLoader(
        _FakeTauClient(
            app_state_view=app_state_view,
            state_proof_view=_tau_state_proof_view(
                state_hash=tau_state_view.state_hash,
                present=True,
                proof_type="risc0.tauswap_transition.v1",
                proof_bytes=123,
                proof_sha256="ef" * 32,
            ),
            tau_state_view=tau_state_view,
        ),
        require_tau_state_app_hash_binding=True,
    )

    with pytest.raises(
        ValueError,
        match="Tau state snapshot app_hash does not match committed app_state hash for settlement signer registry bridge",
    ):
        load_attestation_policy_and_registry_snapshot(
            attestation_policy=policy,
            attestation_registry_snapshot=None,
            attestation_registry_snapshot_loader=tau_loader,
            consumer_now_epoch=103,
        )


def test_tau_net_settlement_signer_registry_loader_rejects_tau_state_hash_drift() -> None:
    _require_blake3()
    attestation = _attestation()
    policy = make_attestation_policy(attestation)
    anchor = make_attestation_registry_anchor(attestation)
    snapshot = make_attestation_registry_snapshot(attestation)
    app_state_view = _tau_bridge_app_state_view(
        {
            "schema": "zenodex/settlement-signer-registry-tau-bridge/v1",
            "anchor": anchor.to_dict(),
            "snapshot": snapshot.to_dict(),
        }
    )
    tau_loader = TauNetSettlementSignerRegistrySnapshotLoader(
        _FakeTauClient(
            app_state_view=app_state_view,
            state_proof_view=_tau_state_proof_view(
                state_hash="ef" * 32,
                present=True,
                proof_type="risc0.tauswap_transition.v1",
                proof_bytes=123,
                proof_sha256="ef" * 32,
            ),
            tau_state_view=_tau_tau_state_view(
                state_hash="cd" * 32,
                app_hash=app_state_view.app_hash,
            ),
        ),
        require_tau_state_app_hash_binding=True,
    )

    with pytest.raises(
        ValueError,
        match="Tau state snapshot does not hash to committed state_hash for settlement signer registry bridge",
    ):
        load_attestation_policy_and_registry_snapshot(
            attestation_policy=policy,
            attestation_registry_snapshot=None,
            attestation_registry_snapshot_loader=tau_loader,
            consumer_now_epoch=103,
        )


def test_tau_net_settlement_signer_registry_loader_rejects_unstable_tau_state_view() -> None:
    attestation = _attestation()
    policy = make_attestation_policy(attestation)
    anchor = make_attestation_registry_anchor(attestation)
    snapshot = make_attestation_registry_snapshot(attestation)
    app_state_view = _tau_bridge_app_state_view(
        {
            "schema": "zenodex/settlement-signer-registry-tau-bridge/v1",
            "anchor": anchor.to_dict(),
            "snapshot": snapshot.to_dict(),
        }
    )
    tau_loader = TauNetSettlementSignerRegistrySnapshotLoader(
        _FakeTauClient(
            app_state_view=[app_state_view, app_state_view],
            state_proof_view=[
                _tau_state_proof_view(state_hash="cd" * 32, present=True, proof_type="proof-a"),
                _tau_state_proof_view(state_hash="cd" * 32, present=True, proof_type="proof-a"),
            ],
            tau_state_view=[
                _tau_tau_state_view(state_hash="cd" * 32, app_hash=app_state_view.app_hash, rules="rule-a"),
                _tau_tau_state_view(state_hash="cd" * 32, app_hash=app_state_view.app_hash, rules="rule-b"),
            ],
        ),
        require_tau_state_app_hash_binding=True,
        stable_read_attempts=1,
    )

    with pytest.raises(ValueError, match="Tau bridge views changed during settlement signer registry bridge load"):
        load_attestation_policy_and_registry_snapshot(
            attestation_policy=policy,
            attestation_registry_snapshot=None,
            attestation_registry_snapshot_loader=tau_loader,
            consumer_now_epoch=103,
        )


def test_tau_net_settlement_signer_registry_loader_rejects_missing_state_proof() -> None:
    attestation = _attestation()
    policy = make_attestation_policy(attestation)
    anchor = make_attestation_registry_anchor(attestation)
    snapshot = make_attestation_registry_snapshot(attestation)
    app_state_view = _tau_bridge_app_state_view(
        {
            "schema": "zenodex/settlement-signer-registry-tau-bridge/v1",
            "anchor": anchor.to_dict(),
            "snapshot": snapshot.to_dict(),
        }
    )
    tau_loader = TauNetSettlementSignerRegistrySnapshotLoader(
        _FakeTauClient(
            app_state_view=app_state_view,
            state_proof_view=_tau_state_proof_view(state_hash="cd" * 32, present=False),
        )
    )

    with pytest.raises(ValueError, match="Tau state proof missing for settlement signer registry bridge"):
        load_attestation_policy_and_registry_snapshot(
            attestation_policy=policy,
            attestation_registry_snapshot=None,
            attestation_registry_snapshot_loader=tau_loader,
            consumer_now_epoch=103,
        )


def test_tau_net_settlement_signer_registry_loader_rejects_missing_state_proof_view_after_stable_read(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    attestation = _attestation()
    policy = make_attestation_policy(attestation)
    anchor = make_attestation_registry_anchor(attestation)
    snapshot = make_attestation_registry_snapshot(attestation)
    app_state_view = _tau_bridge_app_state_view(
        {
            "schema": "zenodex/settlement-signer-registry-tau-bridge/v1",
            "anchor": anchor.to_dict(),
            "snapshot": snapshot.to_dict(),
        }
    )
    tau_loader = TauNetSettlementSignerRegistrySnapshotLoader(
        _FakeTauClient(
            app_state_view=app_state_view,
            state_proof_view=_tau_state_proof_view(state_hash="cd" * 32, present=True),
        )
    )

    monkeypatch.setattr(
        tau_loader,
        "_load_stable_tau_bridge_views",
        lambda _request: (app_state_view, None, None),
    )

    with pytest.raises(ValueError, match="Tau state proof view missing for settlement signer registry bridge"):
        load_attestation_policy_and_registry_snapshot(
            attestation_policy=policy,
            attestation_registry_snapshot=None,
            attestation_registry_snapshot_loader=tau_loader,
            consumer_now_epoch=103,
        )


def test_tau_net_settlement_signer_registry_loader_rejects_missing_tau_state_view_after_stable_read(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _require_blake3()
    attestation = _attestation()
    policy = make_attestation_policy(attestation)
    anchor = make_attestation_registry_anchor(attestation)
    snapshot = make_attestation_registry_snapshot(attestation)
    app_state_view = _tau_bridge_app_state_view(
        {
            "schema": "zenodex/settlement-signer-registry-tau-bridge/v1",
            "anchor": anchor.to_dict(),
            "snapshot": snapshot.to_dict(),
        }
    )
    state_proof_view = _tau_state_proof_view(state_hash="cd" * 32, present=True)
    tau_loader = TauNetSettlementSignerRegistrySnapshotLoader(
        _FakeTauClient(
            app_state_view=app_state_view,
            state_proof_view=state_proof_view,
            tau_state_view=_tau_tau_state_view(state_hash="cd" * 32, app_hash=app_state_view.app_hash),
        ),
        require_tau_state_app_hash_binding=True,
    )

    monkeypatch.setattr(
        tau_loader,
        "_load_stable_tau_bridge_views",
        lambda _request: (app_state_view, state_proof_view, None),
    )

    with pytest.raises(ValueError, match="Tau state snapshot view missing for settlement signer registry bridge"):
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
                app_hash=hashlib.sha256(canonical_json_bytes({"schema": "zenodex/tau_app_state/v1"})).hexdigest(),
                app_state={"schema": "zenodex/tau_app_state/v1"},
            ),
            state_proof_view=_tau_state_proof_view(
                state_hash="cd" * 32,
                present=True,
            ),
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
    app_state_view = _tau_bridge_app_state_view(
        {
            "schema": "zenodex/settlement-signer-registry-tau-bridge/v1",
            "anchor": anchor.to_dict(),
            "snapshot": snapshot.to_dict(),
        }
    )
    tau_loader = TauNetSettlementSignerRegistrySnapshotLoader(
        _FakeTauClient(
            app_state_view=[app_state_view, app_state_view],
            state_proof_view=[
                _tau_state_proof_view(state_hash="cd" * 32, present=True, proof_type="proof-a"),
                _tau_state_proof_view(state_hash="ef" * 32, present=True, proof_type="proof-b"),
                _tau_state_proof_view(state_hash="aa" * 32, present=True, proof_type="proof-c"),
                _tau_state_proof_view(state_hash="aa" * 32, present=True, proof_type="proof-c"),
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
    app_state_view = _tau_bridge_app_state_view(
        {
            "schema": "zenodex/settlement-signer-registry-tau-bridge/v1",
            "anchor": anchor.to_dict(),
            "snapshot": snapshot.to_dict(),
        }
    )
    tau_loader = TauNetSettlementSignerRegistrySnapshotLoader(
        _FakeTauClient(
            app_state_view=[app_state_view, app_state_view],
            state_proof_view=[
                _tau_state_proof_view(state_hash="cd" * 32, present=True, proof_type="proof-a"),
                _tau_state_proof_view(state_hash="ef" * 32, present=True, proof_type="proof-b"),
                _tau_state_proof_view(state_hash="11" * 32, present=True, proof_type="proof-c"),
                _tau_state_proof_view(state_hash="22" * 32, present=True, proof_type="proof-d"),
            ],
        ),
        stable_read_attempts=2,
    )

    with pytest.raises(ValueError, match="Tau bridge views changed during settlement signer registry bridge load"):
        load_attestation_policy_and_registry_snapshot(
            attestation_policy=policy,
            attestation_registry_snapshot=None,
            attestation_registry_snapshot_loader=tau_loader,
            consumer_now_epoch=103,
        )


def test_tau_net_settlement_signer_registry_loader_rejects_app_state_hash_drift() -> None:
    attestation = _attestation()
    policy = make_attestation_policy(attestation)
    anchor = make_attestation_registry_anchor(attestation)
    snapshot = make_attestation_registry_snapshot(attestation)
    tau_loader = TauNetSettlementSignerRegistrySnapshotLoader(
        _FakeTauClient(
            app_state_view=_tau_bridge_app_state_view(
                {
                    "schema": "zenodex/settlement-signer-registry-tau-bridge/v1",
                    "anchor": anchor.to_dict(),
                    "snapshot": snapshot.to_dict(),
                },
                app_hash="ab" * 32,
            ),
            state_proof_view=_tau_state_proof_view(
                state_hash="cd" * 32,
                present=True,
                proof_type="risc0.tauswap_transition.v1",
                proof_bytes=123,
                proof_sha256="ef" * 32,
            ),
        )
    )

    with pytest.raises(
        ValueError,
        match="Tau app_state does not hash to the committed app_hash for settlement signer registry bridge",
    ):
        load_attestation_policy_and_registry_snapshot(
            attestation_policy=policy,
            attestation_registry_snapshot=None,
            attestation_registry_snapshot_loader=tau_loader,
            consumer_now_epoch=103,
        )


def test_tau_net_settlement_signer_registry_loader_rejects_unstable_app_state_view() -> None:
    attestation = _attestation()
    policy = make_attestation_policy(attestation)
    anchor = make_attestation_registry_anchor(attestation)
    snapshot = make_attestation_registry_snapshot(attestation)
    app_state_view_before = _tau_bridge_app_state_view(
        {
            "schema": "zenodex/settlement-signer-registry-tau-bridge/v1",
            "anchor": anchor.to_dict(),
            "snapshot": snapshot.to_dict(),
        }
    )
    app_state_view_after = _tau_bridge_app_state_view(
        {
            "schema": "zenodex/settlement-signer-registry-tau-bridge/v1",
            "anchor": anchor.to_dict(),
            "snapshot": snapshot.to_dict(),
            "extra_note": "drift",
        }
    )
    tau_loader = TauNetSettlementSignerRegistrySnapshotLoader(
        _FakeTauClient(
            app_state_view=[app_state_view_before, app_state_view_after],
            state_proof_view=_tau_state_proof_view(
                state_hash="cd" * 32,
                present=True,
                proof_type="risc0.tauswap_transition.v1",
                proof_bytes=123,
                proof_sha256="ef" * 32,
            ),
        )
        ,
        stable_read_attempts=1,
    )

    with pytest.raises(
        ValueError,
        match="Tau bridge views changed during settlement signer registry bridge load",
    ):
        load_attestation_policy_and_registry_snapshot(
            attestation_policy=policy,
            attestation_registry_snapshot=None,
            attestation_registry_snapshot_loader=tau_loader,
            consumer_now_epoch=103,
        )
