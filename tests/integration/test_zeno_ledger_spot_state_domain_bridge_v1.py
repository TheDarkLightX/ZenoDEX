"""Exact restricted bridge from authenticated Spot roots to ledger state v5."""

from __future__ import annotations

import json
from copy import deepcopy
from pathlib import Path
from typing import Any

import pytest

from src.integration.dex_snapshot import state_from_snapshot
from src.integration.zeno_ledger_spot_state_domain_bridge_v1 import (
    RESTRICTED_SPOT_STATE_DOMAIN_COMPATIBILITY_PROFILE_ID_V1,
    RESTRICTED_SPOT_STATE_ROOT_SCHEME_ID_V5,
    SpotStateDomainBridgeErrorV1,
    _derive_authenticated_spot_ledger_state_domain_bridge_v1,
)

_ROOT = Path(__file__).resolve().parents[2]
_FIXTURE = _ROOT / "tests/fixtures/zrpf_spot_state_root_v5_bridge_v1.json"


def _vector() -> dict[str, Any]:
    return json.loads(_FIXTURE.read_text(encoding="utf-8"))


def _runtime_states() -> tuple[Any, Any, dict[str, Any]]:
    vector = _vector()
    sender = vector["sender_pubkey"]
    ingress_nonce = vector["ingress_nonce"]
    pre_state = state_from_snapshot(vector["pre_state"])
    post_state = state_from_snapshot(vector["post_state"])
    pre_state.nonces.set_last(sender, ingress_nonce - 1)
    post_state.nonces.set_last(sender, ingress_nonce)
    return pre_state, post_state, vector


def _derive(**overrides: Any) -> object:
    pre_state, post_state, vector = _runtime_states()
    expected = vector["expected"]
    values: dict[str, Any] = {
        "pre_state": pre_state,
        "post_state": post_state,
        "transactions": [
            {
                "tx_sender_pubkey": vector["sender_pubkey"],
                "nonce": vector["ingress_nonce"],
                "operations": {},
            }
        ],
        "source_pre_app_hash": expected["source_pre_app_hash"],
        "source_post_app_hash": expected["source_post_app_hash"],
        "source_pre_nonce_root": expected["source_pre_nonce_root"],
        "source_post_nonce_root": expected["source_post_nonce_root"],
        "ledger_pre_state_root": expected["pre_state_root_v5"],
        "ledger_post_state_root": expected["post_state_root_v5"],
    }
    values.update(overrides)
    return _derive_authenticated_spot_ledger_state_domain_bridge_v1(**values)


def test_exact_fixture_mints_private_bridge_with_cross_language_profile_ids() -> None:
    bridge = _derive()
    expected = _vector()["expected"]

    assert (
        object.__getattribute__(bridge, "_compatibility_profile_id")
        == RESTRICTED_SPOT_STATE_DOMAIN_COMPATIBILITY_PROFILE_ID_V1
        == expected["compatibility_profile_id"]
    )
    assert (
        object.__getattribute__(bridge, "_state_root_scheme_id")
        == RESTRICTED_SPOT_STATE_ROOT_SCHEME_ID_V5
        == expected["state_root_scheme_id"]
    )
    assert object.__getattribute__(bridge, "_source_and_ledger_roots_verified") is True


@pytest.mark.parametrize(
    "field",
    [
        "source_pre_app_hash",
        "source_post_app_hash",
        "source_pre_nonce_root",
        "source_post_nonce_root",
        "ledger_pre_state_root",
        "ledger_post_state_root",
    ],
)
def test_each_source_or_ledger_root_substitution_rejects(field: str) -> None:
    with pytest.raises(SpotStateDomainBridgeErrorV1, match=field):
        _derive(**{field: "0x" + "ff" * 32})


@pytest.mark.parametrize("state_name", ["pre_state", "post_state"])
def test_hidden_lp_duration_metadata_rejects(state_name: str) -> None:
    pre_state, post_state, vector = _runtime_states()
    state = pre_state if state_name == "pre_state" else post_state
    sender = vector["sender_pubkey"]
    pool_id = vector["pre_state"]["pools"][0]["pool_id"]
    state.lp_balances.set_last_mint_timestamp(sender, pool_id, 7)

    with pytest.raises(SpotStateDomainBridgeErrorV1, match="lp_duration_risk"):
        _derive(**{state_name: state})


def test_extra_runtime_nonce_rejects() -> None:
    pre_state, _post_state, _vector_obj = _runtime_states()
    pre_state.nonces.set_last("0x" + "bb" * 48, 1)

    with pytest.raises(SpotStateDomainBridgeErrorV1, match="runtime pre nonce"):
        _derive(pre_state=pre_state)


def test_nonce_one_requires_omitted_runtime_pre_nonce() -> None:
    vector = _vector()
    empty_snapshot = {
        "version": 1,
        "balances": [],
        "pools": [],
        "lp_balances": [],
        "fee_accumulator": {"dust": 0},
        "vault": None,
        "oracle": None,
    }
    pre_state = state_from_snapshot(empty_snapshot)
    post_state = state_from_snapshot(empty_snapshot)
    post_state.nonces.set_last(vector["sender_pubkey"], 1)
    mapping = vector["nonce_one_mapping"]

    bridge = _derive_authenticated_spot_ledger_state_domain_bridge_v1(
        pre_state=pre_state,
        post_state=post_state,
        transactions=[
            {
                "tx_sender_pubkey": vector["sender_pubkey"],
                "nonce": 1,
                "operations": {},
            }
        ],
        source_pre_app_hash=mapping["source_app_hash"],
        source_post_app_hash=mapping["source_app_hash"],
        source_pre_nonce_root=mapping["source_pre_nonce_root"],
        source_post_nonce_root=mapping["source_post_nonce_root"],
        ledger_pre_state_root=mapping["pre_state_root_v5"],
        ledger_post_state_root=mapping["post_state_root_v5"],
    )

    assert object.__getattribute__(bridge, "_ingress_nonce") == 1

    pre_state.nonces.set_last(vector["sender_pubkey"], 0)
    with pytest.raises(SpotStateDomainBridgeErrorV1, match="runtime pre nonce"):
        _derive_authenticated_spot_ledger_state_domain_bridge_v1(
            pre_state=pre_state,
            post_state=post_state,
            transactions=[
                {
                    "tx_sender_pubkey": vector["sender_pubkey"],
                    "nonce": 1,
                    "operations": {},
                }
            ],
            source_pre_app_hash=mapping["source_app_hash"],
            source_post_app_hash=mapping["source_app_hash"],
            source_pre_nonce_root=mapping["source_pre_nonce_root"],
            source_post_nonce_root=mapping["source_post_nonce_root"],
            ledger_pre_state_root=mapping["pre_state_root_v5"],
            ledger_post_state_root=mapping["post_state_root_v5"],
        )


def test_multiple_transactions_reject_the_singleton_profile() -> None:
    transaction = {
        "tx_sender_pubkey": _vector()["sender_pubkey"],
        "nonce": _vector()["ingress_nonce"],
        "operations": {},
    }
    with pytest.raises(SpotStateDomainBridgeErrorV1, match="exactly one transaction"):
        _derive(transactions=[transaction, deepcopy(transaction)])


def test_bridge_capability_is_immutable_and_unserializable() -> None:
    bridge = _derive()

    with pytest.raises(AttributeError):
        bridge._ingress_nonce = 8  # type: ignore[attr-defined]
    with pytest.raises(TypeError):
        deepcopy(bridge)


def test_caller_mapping_never_has_private_bridge_type() -> None:
    assert type({"source_and_ledger_roots_verified": True}) is not type(_derive())


def test_private_bridge_derivation_has_one_production_consumer() -> None:
    repository = Path(__file__).resolve().parents[2]
    symbol = "_derive_authenticated_spot_ledger_state_domain_bridge_v1"
    users = {
        path.relative_to(repository).as_posix()
        for path in (repository / "src").rglob("*.py")
        if symbol in path.read_text(encoding="utf-8")
    }

    assert users == {
        "src/integration/zeno_ledger_spot_state_domain_bridge_v1.py",
        "src/integration/zeno_ledger_strict_spot_authority_v1.py",
    }
