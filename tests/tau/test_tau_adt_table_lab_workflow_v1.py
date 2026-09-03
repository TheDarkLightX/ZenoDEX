from __future__ import annotations

import re
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[2]
WORKFLOW = ROOT / ".github" / "workflows" / "tau-adt-table-lab.yml"

TAU_COMMIT = "1c1e58aea7ddec04e48ce11cb0e6ed0cbe2a0d43"
DEMOS_COMMIT = "b149ca30f0143e3a4c31f0ce4fc4b5b75ff77c54"
BASELINES = (
    "adt_tables_basic.tau",
    "adt_tables_advanced.tau",
    "adt_tables_beyond_sql.tau",
)


def _require_workflow_contract(text: str) -> None:
    assert f"TAU_COMMIT={TAU_COMMIT}" in text
    assert 'git checkout "$TAU_COMMIT"' in text
    assert 'test "$(git rev-parse HEAD)" = "$TAU_COMMIT"' in text

    assert f"DEMOS_COMMIT={DEMOS_COMMIT}" in text
    assert 'git checkout "$DEMOS_COMMIT"' in text
    assert 'test "$(git rev-parse HEAD)" = "$DEMOS_COMMIT"' in text

    for baseline in BASELINES:
        assert f"/tmp/tau-lang-demos/{baseline}" in text

    for output in ("basic.out", "advanced.out", "beyond_sql.out"):
        assert f"! grep -Fq '(Error)' experiments/tau_adt_tables/results/upstream/{output}" in text

    jobs_match = re.search(r"-DTAU_BUILD_JOBS=(\d+)", text)
    assert jobs_match is not None
    jobs = int(jobs_match.group(1))
    assert 1 <= jobs <= 2

    timeouts = {
        name: int(seconds)
        for seconds, name in re.findall(
            r"timeout\s+(\d+)s\s+\"\$TAU\"\s+-q\s+-X\s+<\s+"
            r"/tmp/tau-lang-demos/(adt_tables_[a-z_]+\.tau)",
            text,
        )
    }
    assert set(timeouts) == set(BASELINES)
    assert 60 <= timeouts["adt_tables_basic.tau"] <= 120
    assert 60 <= timeouts["adt_tables_advanced.tau"] <= 120
    assert 120 <= timeouts["adt_tables_beyond_sql.tau"] <= 180

    assert "run: python3 experiments/tau_adt_tables/scripts/run_contracts.py" in text
    assert "if: always()" in text
    assert "experiments/tau_adt_tables/results/" in text
    assert "experiments/tau_adt_tables/tau-version.txt" in text


def test_tau_table_lab_workflow_is_exact_source_bound_and_fail_closed() -> None:
    _require_workflow_contract(WORKFLOW.read_text(encoding="utf-8"))


@pytest.mark.parametrize(
    ("old", "new"),
    (
        (f"TAU_COMMIT={TAU_COMMIT}", "TAU_COMMIT=main"),
        (
            'test "$(git rev-parse HEAD)" = "$TAU_COMMIT"',
            'echo "$(git rev-parse HEAD)"',
        ),
        (f"DEMOS_COMMIT={DEMOS_COMMIT}", "DEMOS_COMMIT=main"),
        ("adt_tables_beyond_sql.tau", "adt_tables_advanced.tau"),
        (
            "! grep -Fq '(Error)' experiments/tau_adt_tables/results/upstream/beyond_sql.out",
            "true # ignore beyond-SQL diagnostics",
        ),
        ("-DTAU_BUILD_JOBS=2", "-DTAU_BUILD_JOBS=8"),
        (
            'timeout 180s "$TAU" -q -X < /tmp/tau-lang-demos/adt_tables_beyond_sql.tau',
            'timeout 30s "$TAU" -q -X < /tmp/tau-lang-demos/adt_tables_beyond_sql.tau',
        ),
    ),
)
def test_tau_table_lab_workflow_contract_kills_unsafe_mutations(
    old: str,
    new: str,
) -> None:
    text = WORKFLOW.read_text(encoding="utf-8")
    assert old in text
    mutated = text.replace(old, new, 1)
    with pytest.raises(AssertionError):
        _require_workflow_contract(mutated)


@pytest.mark.parametrize("jobs", (0, 3))
def test_tau_table_lab_build_parallelism_boundary_rejects_outside_safe_range(
    jobs: int,
) -> None:
    text = WORKFLOW.read_text(encoding="utf-8")
    mutated = text.replace("-DTAU_BUILD_JOBS=2", f"-DTAU_BUILD_JOBS={jobs}", 1)
    with pytest.raises(AssertionError):
        _require_workflow_contract(mutated)
