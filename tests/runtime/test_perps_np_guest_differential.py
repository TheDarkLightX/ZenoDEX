"""P0-3 perps-NP guest <-> Python authority differential regressions."""

from __future__ import annotations

import json
import subprocess
from pathlib import Path

import pytest

from src.core.perp_np_clearinghouse import deposit as authority_deposit
from src.core.perp_np_clearinghouse import init_market as authority_init_market
from tests.runtime import perps_np_differential_corpus as corpus
from tools.runtime import perps_np_guest_differential as diff


@pytest.fixture(scope="module")
def risc0_cli() -> Path:
    return diff._ensure_cli()


def test_perps_np_guest_differential_corpus_observational_equivalence(risc0_cli: Path) -> None:
    # REVIEW [B -> A-]: the first corpus was present but not test-promoted, and
    # its script-only path failed every accept case. Keep the corpus in pytest so
    # future WIP cannot be described as evidence until guest and authority agree.
    failures = []
    for case in [*corpus.CORPUS, *corpus.REJECT_CORPUS]:
        result = diff.run_case(case, binp=risc0_cli)
        if not result["ok"]:
            failures.append(f"{case['name']}: {result.get('reason')}")
    assert failures == []


def test_guest_execute_result_is_labelled_non_proof(risc0_cli: Path) -> None:
    result = diff.run_guest([corpus.init(), corpus.deposit(corpus.OWNER_A, 5_000 * corpus.E8, 1)], binp=risc0_cli)

    assert result["schema"] == "tau_state_transition_result"
    assert result["proof_mode"] == "host_execute_no_receipt"
    assert result["production_security_claim"] is False
    assert result["expected_post_app_hash_enforced"] is False
    assert "proof" not in result


def test_seeded_pre_snapshot_is_hash_bound_and_equivalent(risc0_cli: Path) -> None:
    pre_state = authority_init_market(corpus.E8, insurance_seed_e8=1_000 * corpus.E8)
    pre_state = authority_deposit(pre_state, corpus.OWNER_A, 5_000 * corpus.E8)
    pre_state = diff._with_account_nonce(pre_state, corpus.OWNER_A, 1)
    pre_snapshot = diff.state_to_snapshot(pre_state, market_id="ZENO-PERP")

    result = diff.run_case(
        {
            "name": "seeded_pre_snapshot_deposit_second_wallet",
            "pre_state": pre_state,
            "pre_snapshot": pre_snapshot,
            "actions": [corpus.deposit(corpus.OWNER_B, 3_000 * corpus.E8, 1)],
        },
        binp=risc0_cli,
    )

    assert result["ok"], result.get("reason")


def test_execute_schema_rejects_caller_post_hash_claim(risc0_cli: Path) -> None:
    request = {
        "schema": "tau_state_transition_execute",
        "schema_version": 1,
        "proof_type": diff.PERPS_NP_PROOF_TYPE,
        "state_hash": "11" * 32,
        "context": {"chain_id": "zenodex-perps-np-differential"},
        "actions": [corpus.init(), corpus.deposit(corpus.OWNER_A, 5_000 * corpus.E8, 1)],
        "expected_post_app_hash": "22" * 32,
    }

    proc = subprocess.run(
        [str(risc0_cli)],
        input=json.dumps(request),
        text=True,
        capture_output=True,
        check=False,
    )

    assert proc.returncode == 2
    assert "does not enforce expected_post_app_hash" in proc.stderr
