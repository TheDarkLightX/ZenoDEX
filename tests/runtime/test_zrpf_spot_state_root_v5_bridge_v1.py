"""Independent Python parity and ambiguity checks for the restricted bridge."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any, Mapping

from src.state.pools import compute_pool_id
from src.state.state_root import _compute_state_root_python
from tools.runtime import state_root_lib

_ROOT = Path(__file__).resolve().parents[2]
_FIXTURE = _ROOT / "tests/fixtures/zrpf_spot_state_root_v5_bridge_v1.json"


def _load() -> dict[str, Any]:
    return json.loads(_FIXTURE.read_text(encoding="utf-8"))


def _legacy_app_hash(snapshot: Mapping[str, Any]) -> str:
    payload = json.dumps(
        snapshot,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
    ).encode("utf-8")
    return "0x" + hashlib.sha256(payload).hexdigest()


def _profile_id(rules: list[str]) -> str:
    hasher = hashlib.sha256()
    for rule in rules:
        hasher.update(rule.encode("utf-8"))
        hasher.update(b"\0")
    return "0x" + hasher.hexdigest()


def _python_state_root(state: dict[str, Any]) -> str:
    balances, pools, lp, nonces, fee_accumulator = state_root_lib.build_tables(state)
    return _compute_state_root_python(
        balances=balances,
        pools=pools,
        lp_balances=lp,
        nonces=nonces,
        fee_accumulator=fee_accumulator,
    )


def _v5_projection(
    snapshot: Mapping[str, Any],
    *,
    sender: str,
    last_nonce: int,
    lp_duration_risk: list[dict[str, Any]] | None = None,
) -> dict[str, Any]:
    pools = [
        {
            **pool,
            "status": "active",
            "curve_tag": "CPMM",
            "curve_params": "",
        }
        for pool in snapshot["pools"]
    ]
    return {
        "balances": snapshot["balances"],
        "pools": pools,
        "lp_balances": snapshot["lp_balances"],
        "lp_duration_risk": [] if lp_duration_risk is None else lp_duration_risk,
        "nonces": []
        if last_nonce == 0
        else [{"pubkey": sender, "last_nonce": last_nonce}],
        "fee_accumulator": snapshot["fee_accumulator"],
    }


def test_shared_vector_matches_python_state_root_v5() -> None:
    vector = _load()
    sender = vector["sender_pubkey"]
    nonce = vector["ingress_nonce"]
    expected = vector["expected"]

    pre = _v5_projection(vector["pre_state"], sender=sender, last_nonce=nonce - 1)
    post = _v5_projection(vector["post_state"], sender=sender, last_nonce=nonce)
    assert _python_state_root(pre) == expected["pre_state_root_v5"]
    assert _python_state_root(post) == expected["post_state_root_v5"]
    assert _legacy_app_hash(vector["pre_state"]) == expected["source_pre_app_hash"]
    assert _legacy_app_hash(vector["post_state"]) == expected["source_post_app_hash"]


def test_complete_profile_rule_list_recomputes_the_committed_profile_id() -> None:
    vector = _load()
    assert _profile_id(vector["compatibility_profile_rules"]) == vector["expected"][
        "compatibility_profile_id"
    ]


def test_shared_vector_matches_direct_rust_state_root_v5_mirror() -> None:
    vector = _load()
    sender = vector["sender_pubkey"]
    nonce = vector["ingress_nonce"]
    states = [
        _v5_projection(vector["pre_state"], sender=sender, last_nonce=nonce - 1),
        _v5_projection(vector["post_state"], sender=sender, last_nonce=nonce),
    ]
    rust_bin = state_root_lib.locate_or_build_cli()
    results = state_root_lib.run_rust(
        rust_bin,
        [state_root_lib.to_rust_json(state) for state in states],
    )
    assert [result["state_root"] for result in results] == [
        vector["expected"]["pre_state_root_v5"],
        vector["expected"]["post_state_root_v5"],
    ]


def test_nonce_one_omits_runtime_zero_then_commits_last_one() -> None:
    vector = _load()
    sender = vector["sender_pubkey"]
    empty = {
        "version": 1,
        "balances": [],
        "pools": [],
        "lp_balances": [],
        "fee_accumulator": {"dust": 0},
        "vault": None,
        "oracle": None,
    }
    mapping = vector["nonce_one_mapping"]
    assert (
        _python_state_root(_v5_projection(empty, sender=sender, last_nonce=0))
        == mapping["pre_state_root_v5"]
    )
    assert (
        _python_state_root(_v5_projection(empty, sender=sender, last_nonce=1))
        == mapping["post_state_root_v5"]
    )


def test_u32_max_nonce_and_nonzero_fee_match_python_authority() -> None:
    vector = _load()
    sender = vector["sender_pubkey"]
    empty = {
        "version": 1,
        "balances": [],
        "pools": [],
        "lp_balances": [],
        "fee_accumulator": {"dust": 0},
        "vault": None,
        "oracle": None,
    }
    maximum = vector["nonce_u32_max_mapping"]
    assert (
        _python_state_root(
            _v5_projection(
                empty,
                sender=sender,
                last_nonce=maximum["ingress_nonce"] - 1,
            )
        )
        == maximum["pre_state_root_v5"]
    )
    assert (
        _python_state_root(
            _v5_projection(empty, sender=sender, last_nonce=maximum["ingress_nonce"])
        )
        == maximum["post_state_root_v5"]
    )

    fee = vector["nonzero_fee_mapping"]
    pre = {**vector["pre_state"], "fee_accumulator": {"dust": fee["dust"]}}
    post = {**vector["post_state"], "fee_accumulator": {"dust": fee["dust"]}}
    assert (
        _python_state_root(
            _v5_projection(pre, sender=sender, last_nonce=vector["ingress_nonce"] - 1)
        )
        == fee["pre_state_root_v5"]
    )
    assert (
        _python_state_root(
            _v5_projection(post, sender=sender, last_nonce=vector["ingress_nonce"])
        )
        == fee["post_state_root_v5"]
    )
    assert _legacy_app_hash(pre) == fee["source_pre_app_hash"]
    assert _legacy_app_hash(post) == fee["source_post_app_hash"]


def test_lp_duration_metadata_is_a_real_legacy_commitment_ambiguity() -> None:
    vector = _load()
    sender = vector["sender_pubkey"]
    legacy = {**vector["pre_state"], "balances": []}
    ambiguity = vector["lp_duration_ambiguity"]
    assert _legacy_app_hash(legacy) == ambiguity["legacy_app_hash"]

    empty = _v5_projection(legacy, sender=sender, last_nonce=0)
    with_duration = _v5_projection(
        legacy,
        sender=sender,
        last_nonce=0,
        lp_duration_risk=[
            {
                "pubkey": sender,
                "pool_id": legacy["pools"][0]["pool_id"],
                "last_mint_timestamp": 7,
                "last_remove_timestamp": None,
                "churn_tier": 0,
                "last_churn_update_timestamp": None,
            }
        ],
    )
    empty_root = _python_state_root(empty)
    duration_root = _python_state_root(with_duration)
    assert empty_root == ambiguity["empty_duration_state_root_v5"]
    assert duration_root == ambiguity["last_mint_timestamp_7_state_root_v5"]
    assert empty_root != duration_root


def test_legacy_pool_identity_selects_only_cpmm_with_empty_parameters() -> None:
    vector = _load()
    pool = vector["pre_state"]["pools"][0]
    assert pool["pool_id"] == compute_pool_id(
        pool["asset0"],
        pool["asset1"],
        pool["fee_bps"],
        curve_tag="CPMM",
        curve_params="",
    )
    assert pool["pool_id"] != compute_pool_id(
        pool["asset0"],
        pool["asset1"],
        pool["fee_bps"],
        curve_tag="CPMM",
        curve_params="{}",
    )
