"""Production proposer step: accept path, every refusal path, reject-is-no-op.

The proposer turns one observation into at most one admitted continuation
segment. These tests pin the module contract against the real trajectory
runner, session store file, and live admission guard — no mocks on the
authority path. Every refusal must leave the store head byte-identical.
"""

from __future__ import annotations

import json
from collections.abc import Mapping as MappingABC
from pathlib import Path
from typing import Any, Iterator, Mapping

import pytest

from src.integration.autonomous_governance_live_proposer import (
    AUTONOMOUS_GOVERNANCE_LIVE_PROPOSER_RECEIPT_SCHEMA_V1,
    load_autonomous_governance_pinned_policy_v1,
    current_autonomous_governance_live_surface_v1,
    propose_autonomous_governance_live_update_v1,
)
from src.integration.autonomous_governance_q_policy import policy_content_hash_v1
from src.integration.autonomous_governance_session_store_file import (
    current_session_store_file_head_v1,
    initialize_autonomous_governance_session_store_file_v1,
)

from tests.integration.test_autonomous_governance_session_store import (
    _genesis_pin,
    _genesis_receipt,
    _policy,
)


def _observation(**overrides: int) -> dict[str, int]:
    base = {
        "observed_price_bps": 10_400,
        "target_price_bps": 10_000,
        "volatility_bps": 100,
        "divergence_bps": 10,
        "freshness_lag_epochs": 0,
        "liquidity_depth_bps": 5_000,
    }
    return {**base, **overrides}


@pytest.fixture()
def store_and_policy(tmp_path: Path) -> tuple[Path, dict[str, Any]]:
    policy = _policy()
    store_path = tmp_path / "governance" / "session_store.json"
    genesis = _genesis_receipt(policy)
    init = initialize_autonomous_governance_session_store_file_v1(
        path=store_path,
        genesis_pin=_genesis_pin(policy, genesis),
        genesis_receipt=genesis,
        policy=policy,
    )
    assert init["ok"] is True, init["errors"]
    return store_path, policy


def _head_hash(store_path: Path) -> str:
    head = current_session_store_file_head_v1(path=store_path)
    assert head["ok"] is True, head["errors"]
    return str(head["store_hash"])


def _propose(
    store_path: Path,
    policy: Mapping[str, Any],
    *,
    observation: object = None,
    current_epoch: object = 103,
    proposal_epoch: object = 79,
    expected_policy_hash: object = None,
) -> dict[str, Any]:
    return propose_autonomous_governance_live_update_v1(
        store_path=store_path,
        policy=policy,
        expected_policy_hash=(
            str(policy["policy_hash"]) if expected_policy_hash is None else expected_policy_hash
        ),
        observation=_observation() if observation is None else observation,
        current_epoch=current_epoch,
        proposal_epoch=proposal_epoch,
    )


# ---------------------------------------------------------------------------
# Pinned policy loading.
# ---------------------------------------------------------------------------


def test_pinned_policy_load_accepts_exact_artifact(tmp_path: Path) -> None:
    policy = _policy()
    path = tmp_path / "policy.json"
    path.write_text(json.dumps(policy), encoding="utf-8")
    load = load_autonomous_governance_pinned_policy_v1(
        path=path, expected_policy_hash=str(policy["policy_hash"])
    )
    assert load["ok"] is True, load["errors"]
    assert load["policy_hash"] == policy["policy_hash"]
    assert load["policy"]["policy_id"] == policy["policy_id"]


def test_pinned_policy_load_refuses_content_tamper(tmp_path: Path) -> None:
    policy = _policy()
    path = tmp_path / "policy.json"
    path.write_text(json.dumps({**policy, "version": 2}), encoding="utf-8")
    load = load_autonomous_governance_pinned_policy_v1(
        path=path, expected_policy_hash=str(policy["policy_hash"])
    )
    assert load["ok"] is False
    assert "pinned_policy_content_hash_mismatch" in load["errors"]
    assert load["policy"] == {}


def test_pinned_policy_load_refuses_embedded_hash_drift(tmp_path: Path) -> None:
    """Content hash matches but the embedded policy_hash field was edited.

    policy_content_hash_v1 excludes the embedded field, so this isolates the
    hash-pin consistency check: both views must agree before evaluation.
    """

    policy = _policy()
    forged = {**policy, "policy_hash": "0x" + "ab" * 32}
    assert policy_content_hash_v1(forged) == policy["policy_hash"]
    path = tmp_path / "policy.json"
    path.write_text(json.dumps(forged), encoding="utf-8")
    load = load_autonomous_governance_pinned_policy_v1(
        path=path, expected_policy_hash=str(policy["policy_hash"])
    )
    assert load["ok"] is False
    assert "pinned_policy_embedded_hash_mismatch" in load["errors"]


def test_pinned_policy_load_refuses_missing_file_and_bad_inputs(tmp_path: Path) -> None:
    missing = load_autonomous_governance_pinned_policy_v1(
        path=tmp_path / "absent.json", expected_policy_hash="0x" + "11" * 32
    )
    assert missing["ok"] is False
    assert "pinned_policy_file_missing" in missing["errors"]

    class _HashStr(str):
        pass

    policy = _policy()
    path = tmp_path / "policy.json"
    path.write_text(json.dumps(policy), encoding="utf-8")
    subclassed = load_autonomous_governance_pinned_policy_v1(
        path=path, expected_policy_hash=_HashStr(policy["policy_hash"])
    )
    assert subclassed["ok"] is False
    assert "pinned_policy_expected_hash_required" in subclassed["errors"]

    not_object = tmp_path / "list.json"
    not_object.write_text("[1, 2, 3]", encoding="utf-8")
    rejected = load_autonomous_governance_pinned_policy_v1(
        path=not_object, expected_policy_hash=str(policy["policy_hash"])
    )
    assert rejected["ok"] is False
    assert "pinned_policy_file_json_must_be_object" in rejected["errors"]


# ---------------------------------------------------------------------------
# Accept path.
# ---------------------------------------------------------------------------


def test_propose_admits_policy_selected_move_and_advances_store(
    store_and_policy: tuple[Path, dict[str, Any]]
) -> None:
    store_path, policy = store_and_policy
    before = _head_hash(store_path)
    committed = current_session_store_file_head_v1(path=store_path)["surface_state"]

    receipt = _propose(store_path, policy)

    assert receipt["schema"] == AUTONOMOUS_GOVERNANCE_LIVE_PROPOSER_RECEIPT_SCHEMA_V1
    assert receipt["ok"] is True and receipt["admitted"] is True
    assert receipt["no_op"] is False and receipt["errors"] == ()
    assert receipt["step_admitted"] is True
    assert receipt["step_action_id"] == "raise_fee_10"
    # The 400 bps deviation bin selects raise_fee_10; the exact gates admit a
    # single +10 step from the committed fee.
    assert receipt["applied_state"]["fee_bps"] == committed["fee_bps"] + 10
    assert receipt["committed_surface_state"] == dict(committed)
    assert receipt["store_hash_before"] == before
    assert receipt["store_hash_after"] != before
    # The store head is the applied state: one writer, one head.
    head = current_session_store_file_head_v1(path=store_path)
    assert head["surface_state"] == receipt["applied_state"]
    assert head["store_hash"] == receipt["store_hash_after"]
    assert receipt["trajectory_hash"]
    assert receipt["live_update_hash"]
    assert receipt["proposer_receipt_hash"]


def test_propose_chains_segments_across_calls(
    store_and_policy: tuple[Path, dict[str, Any]]
) -> None:
    store_path, policy = store_and_policy
    first = _propose(store_path, policy, current_epoch=103, proposal_epoch=79)
    assert first["admitted"] is True
    second = _propose(store_path, policy, current_epoch=104, proposal_epoch=80)
    assert second["admitted"] is True, second["errors"]
    assert second["store_hash_before"] == first["store_hash_after"]
    assert second["applied_state"]["fee_bps"] == first["applied_state"]["fee_bps"] + 10


# ---------------------------------------------------------------------------
# No-op path: refused steps must not grow the store.
# ---------------------------------------------------------------------------


def test_propose_stale_oracle_is_no_op_and_store_unchanged(
    store_and_policy: tuple[Path, dict[str, Any]]
) -> None:
    store_path, policy = store_and_policy
    before = _head_hash(store_path)
    receipt = _propose(
        store_path, policy, observation=_observation(freshness_lag_epochs=9)
    )
    assert receipt["ok"] is True and receipt["admitted"] is False
    assert receipt["no_op"] is True
    assert receipt["step_admitted"] is False
    assert "freshness_lag_epochs_exceeds_max_freshness_lag_epochs" in receipt["step_errors"]
    assert receipt["applied_state"] == receipt["committed_surface_state"]
    assert _head_hash(store_path) == before


# ---------------------------------------------------------------------------
# Refusal paths: every reject is a no-op on the store.
# ---------------------------------------------------------------------------


def test_propose_refuses_bool_and_subclassed_epochs(
    store_and_policy: tuple[Path, dict[str, Any]]
) -> None:
    store_path, policy = store_and_policy
    before = _head_hash(store_path)

    class _EvilInt(int):
        def __sub__(self, other: object) -> int:
            return 0

    for bad_current, bad_proposal, expected_error in (
        (True, 79, "proposer_current_epoch_must_be_nonnegative_plain_int"),
        (103, False, "proposer_proposal_epoch_must_be_nonnegative_plain_int"),
        (_EvilInt(103), 79, "proposer_current_epoch_must_be_nonnegative_plain_int"),
        (-1, 79, "proposer_current_epoch_must_be_nonnegative_plain_int"),
        ("103", 79, "proposer_current_epoch_must_be_nonnegative_plain_int"),
    ):
        receipt = _propose(
            store_path, policy, current_epoch=bad_current, proposal_epoch=bad_proposal
        )
        assert receipt["ok"] is False and receipt["admitted"] is False
        assert expected_error in receipt["errors"]
    assert _head_hash(store_path) == before


def test_propose_refuses_non_mapping_and_hostile_observations(
    store_and_policy: tuple[Path, dict[str, Any]]
) -> None:
    store_path, policy = store_and_policy
    before = _head_hash(store_path)

    not_mapping = _propose(store_path, policy, observation=[("a", 1)])
    assert not_mapping["ok"] is False
    assert "proposer_observation_must_be_mapping" in not_mapping["errors"]

    class _Key:
        pass

    for hostile in (
        {_Key(): 1},  # non-str key
        _observation() | {"extra": object()},  # unencodable value
        _observation() | {"volatility_bps": True},  # bool is not a plain int
        _observation() | {"volatility_bps": "100"},  # str is not a plain int
    ):
        receipt = _propose(store_path, policy, observation=hostile)
        assert receipt["ok"] is False and receipt["admitted"] is False
        assert "proposer_observation_must_be_plain_int_map" in receipt["errors"]

    class _RaisingMapping(MappingABC):
        def __getitem__(self, key: str) -> int:
            raise RuntimeError("hostile getitem")

        def __iter__(self) -> Iterator[str]:
            raise RuntimeError("hostile iter")

        def __len__(self) -> int:
            return 1

    raising = _propose(store_path, policy, observation=_RaisingMapping())
    assert raising["ok"] is False and raising["admitted"] is False
    assert "proposer_observation_must_be_plain_int_map" in raising["errors"]

    assert _head_hash(store_path) == before


def test_propose_refuses_policy_not_matching_store_head(
    store_and_policy: tuple[Path, dict[str, Any]]
) -> None:
    store_path, _ = store_and_policy
    before = _head_hash(store_path)
    other = _policy("a_different_policy")
    receipt = _propose(store_path, other)
    assert receipt["ok"] is False and receipt["admitted"] is False
    assert "proposer_head_policy_hash_mismatch" in receipt["errors"]
    assert _head_hash(store_path) == before


def test_propose_refuses_missing_store(tmp_path: Path) -> None:
    policy = _policy()
    receipt = propose_autonomous_governance_live_update_v1(
        store_path=tmp_path / "absent.json",
        policy=policy,
        expected_policy_hash=str(policy["policy_hash"]),
        observation=_observation(),
        current_epoch=103,
        proposal_epoch=79,
    )
    assert receipt["ok"] is False and receipt["admitted"] is False
    assert any("session_store_file_missing" in error for error in receipt["errors"])
    assert receipt["applied_state"] == {}


def test_propose_stale_head_snapshot_refuses_via_cas(
    store_and_policy: tuple[Path, dict[str, Any]], monkeypatch: pytest.MonkeyPatch
) -> None:
    """A proposer holding a stale head must lose the store CAS, not fork it."""

    import src.integration.autonomous_governance_live_proposer as proposer_module

    store_path, policy = store_and_policy
    stale_head = current_session_store_file_head_v1(path=store_path)

    advanced = _propose(store_path, policy, current_epoch=103, proposal_epoch=79)
    assert advanced["admitted"] is True
    after_advance = _head_hash(store_path)

    monkeypatch.setattr(
        proposer_module,
        "current_session_store_file_head_v1",
        lambda *, path: stale_head,
    )
    stale = _propose(store_path, policy, current_epoch=104, proposal_epoch=80)
    assert stale["ok"] is False and stale["admitted"] is False
    assert "proposer_admission_live_expected_store_hash_mismatch" in stale["errors"]
    assert "proposer_admission_live_committed_surface_state_mismatch" in stale["errors"]
    assert _head_hash(store_path) == after_advance


# ---------------------------------------------------------------------------
# Read-only surface report.
# ---------------------------------------------------------------------------


def test_current_live_surface_reports_committed_head(
    store_and_policy: tuple[Path, dict[str, Any]]
) -> None:
    store_path, policy = store_and_policy
    report = current_autonomous_governance_live_surface_v1(store_path=store_path)
    assert report["ok"] is True
    assert report["policy_hash"] == policy["policy_hash"]
    # Genesis runs 3 admitted raise_fee_10 steps from fee 30: 30 -> 60.
    assert report["surface_state"]["fee_bps"] == 60
    assert report["segment_count"] == 1
    assert report["store_hash"] == _head_hash(store_path)
    assert report["report_hash"]


def test_current_live_surface_refuses_missing_store(tmp_path: Path) -> None:
    report = current_autonomous_governance_live_surface_v1(
        store_path=tmp_path / "absent.json"
    )
    assert report["ok"] is False
    assert report["surface_state"] == {}
    assert report["errors"]
