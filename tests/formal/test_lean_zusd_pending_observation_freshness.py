from __future__ import annotations

import ast
import re
import shutil
import subprocess
from pathlib import Path

from src.core.zusd import E8, ZUSDCommand, ZUSDState, step

CLAIMS = (
    "admitted_bool_eq_true_iff",
    "commit_admission_implies_pending_not_future",
    "commit_admission_implies_pending_age_bounded",
    "fresh_pending_admits_commit_after_finalized_staleness",
    "liquidation_admission_implies_pending_matches_finalized",
    "liquidation_admission_implies_finalized_not_future",
    "liquidation_admission_implies_finalized_age_bounded",
    "commit_records_pending_observation_epoch",
    "successful_commit_restores_finalized_freshness",
    "commit_does_not_restamp_later_commit_epoch",
)
FORBIDDEN_PROOF_TOKENS = ("sorry", "admit", "axiom", "unsafe", "native_decide")
BOUND = 5


def _paths() -> tuple[str, Path, Path]:
    lake = shutil.which("lake")
    if lake is None:
        raise AssertionError("formal claim gate requires the lake executable")
    root = Path(__file__).resolve().parents[2]
    lean_dir = root / "lean-mathlib"
    proof = lean_dir / "Proofs" / "ZUSDPendingObservationFreshness.lean"
    return lake, lean_dir, proof


def _formal_rows(
    tmp_path: Path,
) -> list[tuple[int, int, int, int, bool, bool, bool, int]]:
    lake, lean_dir, _proof = _paths()
    compile_result = subprocess.run(
        [lake, "build", "Proofs.ZUSDPendingObservationFreshness"],
        cwd=lean_dir,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=240,
        check=False,
    )
    assert compile_result.returncode == 0, compile_result.stdout + compile_result.stderr
    probe = tmp_path / "ZUSDPendingObservationFreshnessVector.lean"
    probe.write_text(
        "import Proofs.ZUSDPendingObservationFreshness\n"
        "#eval ZenoDEX.ZUSDPendingObservationFreshness."
        f"boundedAdmissionCSV {BOUND}\n",
        encoding="utf-8",
    )
    result = subprocess.run(
        [lake, "env", "lean", str(probe)],
        cwd=lean_dir,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=240,
        check=False,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    output_lines = [line.strip() for line in result.stdout.splitlines() if line.strip()]
    assert output_lines
    encoded_rows = ast.literal_eval(output_lines[-1]).split(",")
    rows: list[tuple[int, int, int, int, bool, bool, bool, int]] = []
    for encoded_row in encoded_rows:
        pending, finalized, now, maximum, matches, commit, liquidate, recorded = (
            int(value) for value in encoded_row.split(":")
        )
        rows.append(
            (
                pending,
                finalized,
                now,
                maximum,
                bool(matches),
                bool(commit),
                bool(liquidate),
                recorded,
            )
        )
    return rows


def _commit_runtime(
    *,
    pending_epoch: int,
    finalized_epoch: int,
    now_epoch: int,
    max_staleness_epochs: int,
    pending_matches_finalized: bool,
) -> tuple[bool, int | None]:
    try:
        state = ZUSDState(
            now_epoch=now_epoch,
            oracle_seen=True,
            oracle_last_update_epoch=finalized_epoch,
            oracle_pending_report_epoch=pending_epoch,
            price_e8=100 * E8,
            price_pending_e8=(100 if pending_matches_finalized else 90) * E8,
            max_oracle_staleness_epochs=max_staleness_epochs,
        )
    except ValueError:
        return False, None

    result = step(
        state,
        ZUSDCommand(tag="oracle_commit", args={"auth_ok": True}),
    )
    if not result.ok:
        assert result.state is None
        return False, None
    assert result.state is not None
    return True, result.state.oracle_last_update_epoch


def _liquidation_runtime(
    *,
    pending_epoch: int,
    finalized_epoch: int,
    now_epoch: int,
    max_staleness_epochs: int,
    pending_matches_finalized: bool,
) -> bool:
    try:
        state = ZUSDState(
            now_epoch=now_epoch,
            oracle_seen=True,
            oracle_last_update_epoch=finalized_epoch,
            oracle_pending_report_epoch=pending_epoch,
            price_e8=50 * E8,
            price_pending_e8=(50 if pending_matches_finalized else 40) * E8,
            max_oracle_staleness_epochs=max_staleness_epochs,
            collateral_e8=E8,
            debt_e8=100 * E8,
            sp_debt_e8=100 * E8,
        )
    except ValueError:
        return False

    result = step(state, ZUSDCommand(tag="liquidate", args={}))
    if not result.ok:
        assert result.state is None
    return result.ok


def test_zusd_pending_observation_freshness_theorems_compile() -> None:
    lake, lean_dir, proof = _paths()
    result = subprocess.run(
        [lake, "env", "lean", str(proof)],
        cwd=lean_dir,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=240,
        check=False,
    )
    assert result.returncode == 0, result.stdout + result.stderr


def test_zusd_pending_observation_claim_surface_is_explicit_and_clean() -> None:
    _, _, proof = _paths()
    source = proof.read_text(encoding="utf-8")
    lowered = source.lower()
    for token in FORBIDDEN_PROOF_TOKENS:
        assert re.search(rf"\b{re.escape(token)}\b", lowered) is None
    for claim in CLAIMS:
        assert re.search(rf"\btheorem\s+{re.escape(claim)}\b", source) is not None


def test_lean_freshness_matrix_matches_python_runtime_boundary(
    tmp_path: Path,
) -> None:
    rows = _formal_rows(tmp_path)

    assert len(rows) == (BOUND**4) * 2
    for (
        pending,
        finalized,
        now,
        maximum,
        matches,
        commit_ok,
        liquidate_ok,
        recorded,
    ) in rows:
        runtime_commit_ok, runtime_recorded = _commit_runtime(
            pending_epoch=pending,
            finalized_epoch=finalized,
            now_epoch=now,
            max_staleness_epochs=maximum,
            pending_matches_finalized=matches,
        )
        runtime_liquidate_ok = _liquidation_runtime(
            pending_epoch=pending,
            finalized_epoch=finalized,
            now_epoch=now,
            max_staleness_epochs=maximum,
            pending_matches_finalized=matches,
        )

        assert runtime_commit_ok is commit_ok
        assert runtime_liquidate_ok is liquidate_ok
        if commit_ok:
            assert runtime_recorded == recorded == pending
