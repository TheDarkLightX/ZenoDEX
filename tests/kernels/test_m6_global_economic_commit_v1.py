from __future__ import annotations

import importlib.util
import subprocess
import sys
from pathlib import Path
from types import ModuleType
from typing import Any

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
MODEL = REPO_ROOT / "src/kernels/dex/m6_global_economic_commit_v1.yaml"


@pytest.fixture(scope="module")
def reference_model(tmp_path_factory: pytest.TempPathFactory) -> ModuleType:
    output = tmp_path_factory.mktemp("m6_global_economic_commit_v1")
    subprocess.run(
        [
            sys.executable,
            "-m",
            "ESSO",
            "export-python",
            str(MODEL),
            "--output",
            str(output),
        ],
        cwd=REPO_ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    generated = output / "m6_global_economic_commit_v1_ref.py"
    spec = importlib.util.spec_from_file_location("m6_global_economic_commit_v1_ref", generated)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def _step(module: ModuleType, state: Any, tag: str, **args: Any) -> Any:
    result = module.step(state, module.Command(tag=tag, args=args))
    assert result.ok, result.error
    assert result.state is not None
    return result


def test_protocol_mint_preserves_current_liability_cover(reference_model: ModuleType) -> None:
    state = reference_model.init_state()
    staged = _step(
        reference_model,
        state,
        "stage_protocol_mint",
        authenticated=True,
        context_current=True,
        expected_head=0,
        nonce=1,
        principal_units=1,
        fee_units=1,
    )
    committed = _step(reference_model, staged.state, "commit_candidate")

    assert committed.state.free_debt_units == 2
    assert committed.state.external_supply_units == 1
    assert committed.state.protocol_fee_liability_units == 1
    assert committed.state.committed_outbox_count == 1
    assert committed.state.last_nonce == 1
    assert reference_model.check_invariants(committed.state) == (True, None)


def test_generic_zusd_mint_is_a_durable_noop(reference_model: ModuleType) -> None:
    state = reference_model.init_state()

    rejected = _step(
        reference_model,
        state,
        "reject_generic_canonical_zusd_mint",
        amount_units=2,
    )

    assert rejected.effects["accepted"] is False
    assert rejected.effects["decision"] == "DEC_RejectedManagedAssetAuthority"
    assert rejected.state == state


def test_stale_staged_candidate_cannot_commit(reference_model: ModuleType) -> None:
    state = reference_model.init_state()
    staged = _step(
        reference_model,
        state,
        "stage_protocol_mint",
        authenticated=True,
        context_current=True,
        expected_head=0,
        nonce=1,
        principal_units=1,
        fee_units=0,
    )
    advanced = _step(
        reference_model,
        staged.state,
        "advance_head_with_independent_safe_commit",
    )
    attempted_commit = reference_model.step(
        advanced.state,
        reference_model.Command(tag="commit_candidate", args={}),
    )
    assert attempted_commit.ok is False
    assert attempted_commit.error == "guard failed for commit_candidate"

    rejected = _step(reference_model, advanced.state, "reject_stale_candidate")
    assert rejected.effects["accepted"] is False
    assert rejected.state == advanced.state


def test_crash_before_commit_exposes_no_durable_economic_change(
    reference_model: ModuleType,
) -> None:
    state = reference_model.init_state()
    staged = _step(
        reference_model,
        state,
        "stage_protocol_mint",
        authenticated=True,
        context_current=True,
        expected_head=0,
        nonce=1,
        principal_units=2,
        fee_units=1,
    )

    crashed = _step(reference_model, staged.state, "crash_before_commit")

    assert crashed.effects["accepted"] is False
    assert crashed.state == state


def test_delivery_never_overtakes_committed_outbox_and_redelivery_is_idempotent(
    reference_model: ModuleType,
) -> None:
    state = reference_model.init_state()
    impossible = reference_model.step(
        state,
        reference_model.Command(tag="deliver_next_effect", args={}),
    )
    assert impossible.ok is False

    independent = _step(
        reference_model,
        state,
        "advance_head_with_independent_safe_commit",
    )
    assert independent.state.committed_outbox_count == 0
    no_phantom_effect = reference_model.step(
        independent.state,
        reference_model.Command(tag="deliver_next_effect", args={}),
    )
    assert no_phantom_effect.ok is False

    staged = _step(
        reference_model,
        state,
        "stage_protocol_mint",
        authenticated=True,
        context_current=True,
        expected_head=0,
        nonce=1,
        principal_units=1,
        fee_units=0,
    )
    committed = _step(reference_model, staged.state, "commit_candidate")
    delivered = _step(reference_model, committed.state, "deliver_next_effect")
    redelivered = _step(reference_model, delivered.state, "redeliver_last_effect")

    assert delivered.state.delivered_effect_count == 1
    assert delivered.state.committed_outbox_count == 1
    assert redelivered.state == delivered.state
    assert redelivered.effects["decision"] == "DEC_AlreadyDelivered"
