"""Independent finite obligations for the real migration experiment."""

from __future__ import annotations

import json
from itertools import product
from pathlib import Path

import pytest

from src.tau_workbench.catalog import build_catalog
from src.tau_workbench.compiler import check_pipeline
from src.tau_workbench.native import replay_bundles
from src.tau_workbench.programs import analyze
from tools import benchmark_tau_signal_migration as bench


def test_pre_edit_baseline_retains_every_field_hash_and_exact_error() -> None:
    observed = bench.baseline_parity()
    assert observed["metadata_rows"] == 128
    assert observed["accepted"] == 14
    assert observed["rejected"] == 114
    assert observed["reserved_bytes_rejected"] == 128


def test_baseline_tampering_cannot_be_reported_as_success(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    packet = json.loads((bench.ROOT / bench.BASELINE).read_text())
    packet["rows"][0]["outcome"]["error"] = "a different rejection"
    target = tmp_path / bench.BASELINE
    target.parent.mkdir(parents=True)
    target.write_text(json.dumps(packet))
    monkeypatch.setattr(bench, "ROOT", tmp_path)
    with pytest.raises(ValueError, match="^baseline_digest_mismatch$"):
        bench.baseline_parity()


def test_forged_historical_source_hash_cannot_be_reported_as_pre_edit_parity(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    packet = json.loads((bench.ROOT / bench.BASELINE).read_text())
    packet["sources"]["src/integration/autotrader_signals.py"] = "0" * 64
    target = tmp_path / bench.BASELINE
    target.parent.mkdir(parents=True)
    target.write_text(json.dumps(packet))
    monkeypatch.setattr(bench, "ROOT", tmp_path)
    with pytest.raises(ValueError, match="^baseline_digest_mismatch$"):
        bench.baseline_parity()


def test_historical_replay_cannot_be_replaced_by_a_claimed_pass(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    baseline = tmp_path / bench.BASELINE
    baseline.parent.mkdir(parents=True)
    baseline.write_bytes((bench.ROOT / bench.BASELINE).read_bytes())
    (tmp_path / bench.LEGACY_REPLAY).write_text('{"status":"PASS"}')
    monkeypatch.setattr(bench, "ROOT", tmp_path)
    with pytest.raises(ValueError, match="^legacy_replay_digest_mismatch$"):
        bench.baseline_parity()


def test_complete_candidate_relation_agrees_with_isolated_native_execution() -> None:
    task = bench.signal_task()
    central, raw = bench.cached_baselines(task)
    bundles = tuple(product(range(5), repeat=2))
    replay = replay_bundles(task, bundles)
    assert central["cached_artifact_checks"] == 25
    assert central["quotient_class_checks"] == 16
    assert central["accepted_artifact_bundles"] == 6
    assert central["accepted_class_bundles"] == 3
    assert tuple(value is None for value in replay.outcomes) == raw
    assert replay.component_inputs_checked == 2560


def test_equivalent_source_revisions_preserve_every_byte_but_format_changes_need_coordination() -> None:
    task = bench.signal_task()
    for stage in task.stages:
        assert stage.programs[0].sha256 != stage.programs[1].sha256
        assert analyze(stage.programs[0], 8).outputs == analyze(stage.programs[1], 8).outputs
    check_pipeline(task, tuple(stage.programs[1] for stage in task.stages))
    for programs in ((task.stages[0].programs[2], task.stages[1].programs[0]),
                     (task.stages[0].programs[0], task.stages[1].programs[2])):
        with pytest.raises(ValueError, match="^pipeline_behavior_mismatch$"):
            check_pipeline(task, programs)


def test_reserved_mask_mutant_is_killed_at_first_reserved_input() -> None:
    task = bench.signal_task()
    replay = replay_bundles(task, ((4, 2),))
    failure = replay.outcomes[0]
    assert failure is not None
    assert (failure.input, failure.expected, failure.observed) == (128, 255, 0)


def test_distinct_untagged_formats_have_no_safe_one_owner_rollout_edge() -> None:
    catalog = build_catalog(bench.signal_task())
    assert catalog.legal == frozenset({(0, 0), (1, 1), (2, 2)})
    result = bench.rolling_obstruction(catalog.legal)
    assert result["safe_rolling_path_between_distinct_formats"] is False


def test_wire_savings_include_the_versioned_json_object() -> None:
    result = bench.transport_benchmark(1, 1)
    assert result["observations_per_batch"] == 14
    assert all(b < a for a, b in zip(result["v1_bytes"], result["v2_bytes"], strict=True))
    assert result["saved_bytes"] == result["v1_total_bytes"] - result["v2_total_bytes"]
    # No assertion about speed: Python timings are measurements, not contracts.


@pytest.mark.parametrize("repetitions,trials", [(0, 5), (10001, 5), (100, 0), (100, 16)])
def test_invalid_benchmark_budget_has_no_output(
    tmp_path: Path, repetitions: int, trials: int,
) -> None:
    target = tmp_path / "fresh"
    result = bench.main(["--tau", str(tmp_path / "missing"), "--out", str(target),
                         "--repetitions", str(repetitions), "--trials", str(trials)])
    assert result == 1
    assert not target.exists()


def test_existing_evidence_is_never_overwritten(tmp_path: Path) -> None:
    sentinel = tmp_path / "report.json"
    sentinel.write_text("earlier evidence")
    assert bench.main(["--tau", str(tmp_path / "missing"), "--out", str(tmp_path)]) == 1
    assert sentinel.read_text() == "earlier evidence"
