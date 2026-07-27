from __future__ import annotations

from dataclasses import replace
from typing import cast

import pytest

from src.state.canonical import canonical_json_bytes, sha256_hex
from tools import build_fcis_m5_p4b1_mounted_lp_refinement as target


def _rehash(artifact: dict[str, object]) -> bytes:
    payload = {key: value for key, value in artifact.items() if key != "artifact_sha256"}
    artifact["artifact_sha256"] = sha256_hex(canonical_json_bytes(payload))
    return canonical_json_bytes(artifact)


def test_p4b1_all_mounted_lp_rows_refine_without_authorizing_mount() -> None:
    artifact = target._build_artifact()

    assert artifact["row_count"] == 24
    assert artifact["refine_count"] == 24
    assert artifact["mismatch_count"] == 0
    assert artifact["verdict"] == "READY_FOR_P4B2"
    assert artifact["mount_authorized"] is False
    assert artifact["timestamps"] == list(target.P4B1_TIMESTAMPS_V1)
    assert artifact["logical_state_fields"] == list(target._LOGICAL_STATE_FIELDS_V1)
    rows = cast(list[dict[str, object]], artifact["rows"])
    assert all(row["parity"] == "REFINES" for row in rows)
    assert all(row["same_input_binding"] is True for row in rows)
    assert all(row["settlement_equal"] is True for row in rows)
    assert all(row["mounted_state_root"] == row["exact_state_root"] for row in rows)
    assert all(row["mounted_field_hashes"] == row["exact_field_hashes"] for row in rows)


@pytest.mark.parametrize(
    "fixture_id",
    (
        "add_liquidity_boundary_valid",
        "add_liquidity_smallest_accepted",
        "create_pool_smallest_accepted",
    ),
)
def test_p4b1_closes_each_original_lp_mismatch_at_consensus_time(fixture_id: str) -> None:
    mounted = target._selected_fixtures()[fixture_id]
    exact = target._selected_fixtures()[fixture_id]

    row = target._build_row(mounted, exact, 700)

    assert row["parity"] == "REFINES"
    assert row["mounted_state_root"] == row["exact_state_root"]
    assert row["mounted_field_hashes"] == row["exact_field_hashes"]


def test_p4b1_kills_omitted_mounted_timestamp_transition(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(
        target,
        "apply_lp_mint_timestamps_after_settlement",
        lambda **_kwargs: None,
    )

    artifact = target._build_artifact()

    assert artifact["verdict"] == "BLOCKED"
    assert cast(int, artifact["mismatch_count"]) > 0
    rows = cast(list[dict[str, object]], artifact["rows"])
    assert any(
        row["fixture_id"] in target.P4B1_FIXTURE_IDS_V1[:3] and row["parity"] == "MISMATCH"
        for row in rows
    )


def test_p4b1_kills_cross_side_command_substitution(monkeypatch: pytest.MonkeyPatch) -> None:
    original = target._selected_fixtures
    call_count = 0

    def substituted() -> dict[str, target._FixtureInput]:
        nonlocal call_count
        call_count += 1
        fixtures = original()
        if call_count == 2:
            fixture = fixtures["add_liquidity_smallest_accepted"]
            intent = replace(fixture.intents[0], deadline=fixture.intents[0].deadline + 1)
            fixtures[fixture.fixture_id] = replace(fixture, intents=[intent])
        return fixtures

    monkeypatch.setattr(target, "_selected_fixtures", substituted)

    artifact = target._build_artifact()

    assert artifact["verdict"] == "BLOCKED"
    rows = cast(list[dict[str, object]], artifact["rows"])
    affected = [row for row in rows if row["fixture_id"] == "add_liquidity_smallest_accepted"]
    assert affected
    assert all(row["same_input_binding"] is False for row in affected)
    assert all(row["parity"] == "MISMATCH" for row in affected)


def test_p4b1_checker_kills_rehashed_semantic_fabrication() -> None:
    artifact = target._build_artifact()
    rows = cast(list[dict[str, object]], artifact["rows"])
    rows[0]["mounted_state_root"] = "0x" + "00" * 32

    ok, reason = target.check_artifact_bytes_v1(_rehash(artifact))

    assert ok is False
    assert reason == "artifact_semantic_or_source_drift"


def test_p4b1_checker_kills_rehashed_row_deletion() -> None:
    artifact = target._build_artifact()
    rows = cast(list[dict[str, object]], artifact["rows"])
    artifact["rows"] = rows[:-1]
    artifact["row_count"] = len(rows) - 1
    artifact["refine_count"] = len(rows) - 1

    ok, reason = target.check_artifact_bytes_v1(_rehash(artifact))

    assert ok is False
    assert reason == "artifact_semantic_or_source_drift"


def test_p4b1_source_ledger_binds_mounted_and_exact_transition_files() -> None:
    artifact = target._build_artifact()
    source_hashes = cast(dict[str, str], artifact["source_hashes"])

    assert "src/integration/dex_engine.py" in source_hashes
    assert "src/integration/lp_position_age_gate.py" in source_hashes
    assert "src/core/fcis_step_evaluator.py" in source_hashes
    assert "src/state/lp_duration_transitions.py" in source_hashes
    assert all(value.startswith("0x") and len(value) == 66 for value in source_hashes.values())
