from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
CLI_PATH = REPO_ROOT / "tools" / "autotrader_q_learning_sandbox.py"


def test_autotrader_q_learning_sandbox_cli_emits_advisory_summary(tmp_path: Path) -> None:
    out_path = tmp_path / "q_summary.json"
    completed = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            "--episodes",
            "24",
            "--seed",
            "19",
            "--pretty",
            "--summary-out",
            str(out_path),
        ],
        check=False,
        capture_output=True,
        text=True,
    )

    assert completed.returncode == 0, completed.stderr
    payload = json.loads(completed.stdout)
    persisted = json.loads(out_path.read_text(encoding="utf-8"))

    assert payload == persisted
    assert payload["schema"] == "zenodex/autotrader-tabular-q-sandbox/v1"
    assert payload["advisory_only"] is True
    assert payload["state_count"] == 324
    assert payload["training_config"]["episodes"] == 24
    assert payload["training_config"]["reward_profile"] == "balanced"
    assert payload["coarse_krr_match_ratio"] >= 0.0
    assert payload["probe_states"][0]["name"] == "favorable_submit"
    assert "q_table" not in payload


def test_autotrader_q_learning_sandbox_cli_can_include_q_table() -> None:
    completed = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            "--episodes",
            "8",
            "--seed",
            "5",
            "--include-q-table",
        ],
        check=False,
        capture_output=True,
        text=True,
    )

    assert completed.returncode == 0, completed.stderr
    payload = json.loads(completed.stdout)

    assert isinstance(payload.get("q_table"), dict)
    assert payload["q_table"]["0|0|2|0|0|0"]["submit"] > payload["q_table"]["0|0|2|0|0|0"]["skip"]


def test_autotrader_q_learning_sandbox_cli_accepts_reward_profile() -> None:
    completed = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            "--episodes",
            "24",
            "--seed",
            "7",
            "--reward-profile",
            "capital_preservation",
        ],
        check=False,
        capture_output=True,
        text=True,
    )

    assert completed.returncode == 0, completed.stderr
    payload = json.loads(completed.stdout)

    assert payload["training_config"]["reward_profile"] == "capital_preservation"


def test_autotrader_q_learning_sandbox_cli_can_compare_reward_profiles() -> None:
    completed = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            "--episodes",
            "24",
            "--seed",
            "7",
            "--compare-reward-profiles",
        ],
        check=False,
        capture_output=True,
        text=True,
    )

    assert completed.returncode == 0, completed.stderr
    payload = json.loads(completed.stdout)

    assert payload["schema"] == "zenodex/autotrader-tabular-q-profile-compare/v1"
    assert payload["baseline_profile"] == "balanced"
    assert payload["profile_summaries"]["throughput_bias"]["policy_action_counts"]["submit"] > payload[
        "profile_summaries"
    ]["capital_preservation"]["policy_action_counts"]["submit"]
    assert payload["pairwise_deltas"]["throughput_bias"]["submit_delta"] > 0
    flip_map = {entry["name"]: entry for entry in payload["probe_flip_states"]}
    assert flip_map["wait_for_spacing"]["profile_actions"]["throughput_bias"] == "submit"
    summary = payload["policy_flip_summary"]
    assert summary["state_count"] == 324
    assert summary["unstable_state_count"] > 0
    assert summary["top_unstable_states"][0]["flip_count"] >= 1
    coarse_krr_alignment = payload["coarse_krr_alignment"]
    assert coarse_krr_alignment["best_aligned_profile"] == "balanced"
    assert coarse_krr_alignment["worst_aligned_profile"] == "capital_preservation"
    assert coarse_krr_alignment["match_ratio_deltas_vs_baseline"]["throughput_bias"] < 0
