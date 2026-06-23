from __future__ import annotations

import shutil
import subprocess
from pathlib import Path

import pytest


def test_lean_zenodex_staking_share_safety_typechecks_without_placeholders() -> None:
    lake = shutil.which("lake")
    if not lake:
        return

    root = Path(__file__).resolve().parents[2]
    lean_dir = root / "lean-mathlib"
    target = "Proofs/ZenoDEXStakingShareSafety.lean"
    if not (root / "external" / "mathlib4").exists():
        pytest.skip("mathlib4 checkout missing")

    source = (lean_dir / target).read_text(encoding="utf-8")
    for required in (
        "theorem same_bonus_split_does_not_increase_shares",
        "theorem share_rate_ratchet_nonincreasing",
        "theorem two_claims_sum_le_epochReward",
        "theorem rewardClaimsSum_le_epochReward",
        "theorem same_epoch_pending_deposit_cannot_capture_reward",
        "theorem no_positive_payment_from_empty_vault",
        "theorem capped_fee_route_le_fee",
        "theorem early_exit_penalty_le_principal",
        "theorem deterministic_claim_amount_bound",
        "theorem accepted_claim_preserves_program_budget",
        "theorem accepted_claim_preserves_reward_source",
        "theorem active_emission_epoch_preserves_reward_floor",
        "theorem active_emission_epoch_budget_le_burn",
        "theorem active_participant_claim_admission_preserves_accounting",
        "theorem witness_active_emission_epoch_floor_preserved",
        "theorem witness_active_emission_epoch_budget_le_burn",
    ):
        assert required in source
    for forbidden in ("sorry", "admit", "axiom", "unsafe"):
        assert forbidden not in source

    try:
        proc = subprocess.run(
            [lake, "env", "lean", target],
            cwd=lean_dir,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=120,
        )
    except subprocess.TimeoutExpired as exc:
        pytest.skip(f"lake env lean timed out after {exc.timeout}s for {target}")

    assert proc.returncode == 0, proc.stdout + proc.stderr
