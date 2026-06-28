"""Live autonomous-governance admission wrapper tests."""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from typing import Any

from src.integration.autonomous_governance_live_apply import (
    admit_autonomous_governance_live_session_file_update_v1,
    autonomous_governance_live_session_file_context_hash_v1,
)
from src.integration.autonomous_governance_session_store_file import (
    current_session_store_file_head_v1,
    initialize_autonomous_governance_session_store_file_v1,
)
from tests.integration.test_autonomous_governance_session_store import (
    _authority_bundle,
    _continue,
    _genesis_receipt,
    _policy,
)


def _init_file(path: Path) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    policy = _policy()
    genesis = _genesis_receipt(policy)
    authority = _authority_bundle(policy, genesis)
    init = initialize_autonomous_governance_session_store_file_v1(
        path=path,
        genesis_pin=authority.pop("genesis_pin"),
        genesis_receipt=genesis,
        policy=policy,
        **authority,
    )
    assert init["ok"] is True, init["errors"]
    return policy, genesis, init


def _context_hash(
    *,
    path: Path,
    committed_surface_state: dict[str, Any],
    receipt: dict[str, Any],
    expected_policy_hash: str,
) -> str:
    head = current_session_store_file_head_v1(path=path)
    assert head["ok"] is True, head["errors"]
    return autonomous_governance_live_session_file_context_hash_v1(
        store_hash=str(head["store_hash"]),
        head_pin_hash=str(head["head_pin"]["pin_hash"]),
        committed_surface_state=committed_surface_state,
        trajectory_hash=str(receipt["trajectory_hash"]),
        expected_policy_hash=expected_policy_hash,
    )


def test_live_session_file_update_admits_verified_continuation(
    tmp_path: Path,
) -> None:
    path = tmp_path / "live-store.json"
    policy, genesis, init = _init_file(path)
    receipt = _continue(policy, genesis, 103)
    committed = dict(genesis["final_state"])
    context_hash = _context_hash(
        path=path,
        committed_surface_state=committed,
        receipt=receipt,
        expected_policy_hash=str(policy["policy_hash"]),
    )

    result = admit_autonomous_governance_live_session_file_update_v1(
        store_path=path,
        policy=policy,
        trajectory_receipt=receipt,
        committed_surface_state=committed,
        expected_policy_hash=str(policy["policy_hash"]),
        expected_store_hash=init["store_hash"],
        expected_live_context_hash=context_hash,
    )
    assert result["admitted"] is True, result["errors"]
    assert result["applied_state"] == receipt["final_state"]
    assert result["store_hash_before"] == init["store_hash"]
    assert result["store_hash_after"] != init["store_hash"]

    head = current_session_store_file_head_v1(path=path)
    assert head["ok"] is True, head["errors"]
    assert head["surface_state"] == receipt["final_state"]


def test_live_session_file_update_refuses_bad_context_before_store_write(
    tmp_path: Path,
) -> None:
    path = tmp_path / "live-store.json"
    policy, genesis, init = _init_file(path)
    receipt = _continue(policy, genesis, 103)

    result = admit_autonomous_governance_live_session_file_update_v1(
        store_path=path,
        policy=policy,
        trajectory_receipt=receipt,
        committed_surface_state=dict(genesis["final_state"]),
        expected_policy_hash=str(policy["policy_hash"]),
        expected_store_hash=init["store_hash"],
        expected_live_context_hash="0x" + "00" * 32,
    )
    assert result["admitted"] is False
    assert "live_context_hash_mismatch" in result["errors"]
    assert current_session_store_file_head_v1(path=path)["store_hash"] == init["store_hash"]


def test_live_session_file_update_refuses_committed_state_not_store_head(
    tmp_path: Path,
) -> None:
    path = tmp_path / "live-store.json"
    policy, genesis, init = _init_file(path)
    receipt = _continue(policy, genesis, 103)
    forged_committed = {**dict(genesis["final_state"]), "fee_bps": 999}
    context_hash = _context_hash(
        path=path,
        committed_surface_state=forged_committed,
        receipt=receipt,
        expected_policy_hash=str(policy["policy_hash"]),
    )

    result = admit_autonomous_governance_live_session_file_update_v1(
        store_path=path,
        policy=policy,
        trajectory_receipt=receipt,
        committed_surface_state=forged_committed,
        expected_policy_hash=str(policy["policy_hash"]),
        expected_store_hash=init["store_hash"],
        expected_live_context_hash=context_hash,
    )
    assert result["admitted"] is False
    assert "live_committed_surface_state_mismatch" in result["errors"]
    assert current_session_store_file_head_v1(path=path)["store_hash"] == init["store_hash"]


def test_live_session_file_update_refuses_forged_receipt(
    tmp_path: Path,
) -> None:
    path = tmp_path / "live-store.json"
    policy, genesis, init = _init_file(path)
    receipt = _continue(policy, genesis, 103)
    forged = dict(receipt)
    forged["final_state"] = {**dict(receipt["final_state"]), "fee_bps": 999}
    context_hash = _context_hash(
        path=path,
        committed_surface_state=dict(genesis["final_state"]),
        receipt=forged,
        expected_policy_hash=str(policy["policy_hash"]),
    )

    result = admit_autonomous_governance_live_session_file_update_v1(
        store_path=path,
        policy=policy,
        trajectory_receipt=forged,
        committed_surface_state=dict(genesis["final_state"]),
        expected_policy_hash=str(policy["policy_hash"]),
        expected_store_hash=init["store_hash"],
        expected_live_context_hash=context_hash,
    )
    assert result["admitted"] is False
    assert "live_trajectory_admission_refused" in result["errors"]
    assert current_session_store_file_head_v1(path=path)["store_hash"] == init["store_hash"]


def test_live_session_file_update_refuses_stale_expected_store_hash(
    tmp_path: Path,
) -> None:
    path = tmp_path / "live-store.json"
    policy, genesis, init = _init_file(path)
    receipt = _continue(policy, genesis, 103)
    committed = dict(genesis["final_state"])
    context_hash = _context_hash(
        path=path,
        committed_surface_state=committed,
        receipt=receipt,
        expected_policy_hash=str(policy["policy_hash"]),
    )

    result = admit_autonomous_governance_live_session_file_update_v1(
        store_path=path,
        policy=policy,
        trajectory_receipt=receipt,
        committed_surface_state=committed,
        expected_policy_hash=str(policy["policy_hash"]),
        expected_store_hash="0x" + "11" * 32,
        expected_live_context_hash=context_hash,
    )
    assert result["admitted"] is False
    assert "live_expected_store_hash_mismatch" in result["errors"]
    assert current_session_store_file_head_v1(path=path)["store_hash"] == init["store_hash"]


def test_cli_live_session_file_update_lifecycle(tmp_path: Path) -> None:
    path = tmp_path / "live-store.json"
    policy, genesis, init = _init_file(path)
    receipt = _continue(policy, genesis, 103)

    context_bundle = tmp_path / "live-context.json"
    context_bundle.write_text(
        json.dumps(
            {
                "path": str(path),
                "trajectory_receipt": receipt,
                "expected_policy_hash": policy["policy_hash"],
                "committed_surface_state": genesis["final_state"],
            },
            sort_keys=True,
        ),
        encoding="utf-8",
    )
    context = subprocess.run(
        [
            sys.executable,
            "tools/autonomous_governance_q_policy.py",
            "live-session-file-context",
            str(context_bundle),
        ],
        check=False,
        capture_output=True,
        text=True,
    )
    assert context.returncode == 0, context.stderr
    context_result = json.loads(context.stdout)
    assert context_result["ok"] is True, context_result["errors"]

    admit_bundle = tmp_path / "live-admit.json"
    admit_bundle.write_text(
        json.dumps(
            {
                "path": str(path),
                "policy": policy,
                "trajectory_receipt": receipt,
                "committed_surface_state": genesis["final_state"],
                "expected_policy_hash": policy["policy_hash"],
                "expected_store_hash": init["store_hash"],
                "expected_live_context_hash": context_result["live_context_hash"],
            },
            sort_keys=True,
        ),
        encoding="utf-8",
    )
    admitted = subprocess.run(
        [
            sys.executable,
            "tools/autonomous_governance_q_policy.py",
            "admit-live-session-file-update",
            str(admit_bundle),
        ],
        check=False,
        capture_output=True,
        text=True,
    )
    assert admitted.returncode == 0, admitted.stderr
    result = json.loads(admitted.stdout)
    assert result["admitted"] is True, result["errors"]
    assert result["applied_state"] == receipt["final_state"]
