from __future__ import annotations

import copy
import json
import subprocess
import sys
from pathlib import Path

from tools.check_zeno_oracle_reporter_soak_gate import (
    check_reporter_soak_gate,
    observation_content_hash,
    policy_content_hash,
    sample_observation_bundle,
    sample_policy,
)
from tools.zenodex_oracle_source_diversity import source_set_content_hash

ROOT = Path(__file__).resolve().parents[1]


def _sample_inputs() -> tuple[dict[str, object], dict[str, object]]:
    policy = sample_policy()
    observations = sample_observation_bundle(policy)
    return policy, observations


def _refresh_observation_id(observation: dict[str, object]) -> None:
    observation["observation_id"] = observation_content_hash(observation)


def test_reporter_soak_gate_accepts_sample_observations() -> None:
    policy, observations = _sample_inputs()

    result = check_reporter_soak_gate(policy, observations)

    assert result["schema"] == "zenodex.oracle.reporter_soak_gate_check.v1"
    assert result["status"] == "accepted"
    assert result["observation_bundle_status"] == "accepted"
    assert result["reporter_count"] == 5
    assert result["distinct_operator_count"] == 5
    assert result["error_count"] == 0
    assert "does_not_claim_public_soak_completed" in result["not_claimed"]


def test_reporter_soak_gate_rejects_missing_observation_bundle() -> None:
    policy, _observations = _sample_inputs()

    result = check_reporter_soak_gate(policy, None)

    assert result["status"] == "rejected"
    assert result["observation_bundle_status"] == "missing"
    assert "observation_bundle_required" in result["errors"]


def test_reporter_soak_gate_rejects_operator_cartel() -> None:
    policy, observations = _sample_inputs()
    mutated = copy.deepcopy(observations)
    raw_observations = mutated["reporter_observations"]
    assert isinstance(raw_observations, list)
    for observation in raw_observations:
        assert isinstance(observation, dict)
        observation["operator_id"] = "operator.cartel"
        _refresh_observation_id(observation)

    result = check_reporter_soak_gate(policy, mutated)

    assert result["status"] == "rejected"
    assert "distinct_operator_count_below_policy" in result["errors"]
    assert "operator_share_exceeds_policy:operator.cartel" in result["errors"]


def test_reporter_soak_gate_rejects_low_success_rate() -> None:
    policy, observations = _sample_inputs()
    mutated = copy.deepcopy(observations)
    raw_observations = mutated["reporter_observations"]
    assert isinstance(raw_observations, list)
    first = raw_observations[0]
    assert isinstance(first, dict)
    first["successful_report_count"] = 1
    first["rejected_report_count"] = 99
    _refresh_observation_id(first)

    result = check_reporter_soak_gate(policy, mutated)

    assert result["status"] == "rejected"
    assert "reporter_success_rate_below_policy:reporter.prod.1" in result["errors"]


def test_reporter_soak_gate_rejects_active_epochs_after_observed_epoch() -> None:
    policy, observations = _sample_inputs()
    mutated = copy.deepcopy(observations)
    raw_observations = mutated["reporter_observations"]
    assert isinstance(raw_observations, list)
    first = raw_observations[0]
    assert isinstance(first, dict)
    first["active_epochs"] = int(mutated["observed_epoch"]) + 1
    _refresh_observation_id(first)

    result = check_reporter_soak_gate(policy, mutated)

    assert result["status"] == "rejected"
    assert "reporter_active_epochs_exceeds_observed_epoch:reporter.prod.1" in result["errors"]


def test_reporter_soak_gate_rejects_malformed_signed_report_root() -> None:
    policy, observations = _sample_inputs()
    mutated = copy.deepcopy(observations)
    raw_observations = mutated["reporter_observations"]
    assert isinstance(raw_observations, list)
    first = raw_observations[0]
    assert isinstance(first, dict)
    first["signed_report_root"] = "sha256:not-a-digest"
    _refresh_observation_id(first)

    result = check_reporter_soak_gate(policy, mutated)

    assert result["status"] == "rejected"
    assert "observation_0_signed_report_root_must_be_sha256" in result["errors"]


def test_reporter_soak_gate_rejects_source_diversity_drift() -> None:
    policy, observations = _sample_inputs()
    source_diversity = policy["source_diversity"]
    assert isinstance(source_diversity, dict)
    sources = source_diversity["sources"]
    assert isinstance(sources, list)
    for source in sources:
        assert isinstance(source, dict)
        source["operator_id"] = "operator.cartel"
    source_diversity["source_set_id"] = source_set_content_hash(source_diversity)
    policy["policy_id"] = policy_content_hash(policy)

    result = check_reporter_soak_gate(policy, observations)

    assert result["status"] == "rejected"
    assert "source_diversity_rejected" in result["errors"]
    assert "source_diversity:not_enough_distinct_operators" in result["errors"]


def test_reporter_soak_gate_cli_sample_and_require_live(tmp_path: Path) -> None:
    accepted = subprocess.run(
        [
            sys.executable,
            "tools/check_zeno_oracle_reporter_soak_gate.py",
            "--format",
            "text",
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert accepted.returncode == 0, accepted.stdout + accepted.stderr
    assert "status = accepted" in accepted.stdout
    assert "observation_bundle_status = accepted" in accepted.stdout

    sample_policy_proc = subprocess.run(
        [sys.executable, "tools/check_zeno_oracle_reporter_soak_gate.py", "--sample-policy"],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    policy_path = tmp_path / "reporter-soak-policy.json"
    policy_path.write_text(sample_policy_proc.stdout, encoding="utf-8")

    sample_observations_proc = subprocess.run(
        [
            sys.executable,
            "tools/check_zeno_oracle_reporter_soak_gate.py",
            "--policy",
            str(policy_path),
            "--sample-observations",
        ],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    observations_path = tmp_path / "reporter-soak-observations.json"
    observations_path.write_text(sample_observations_proc.stdout, encoding="utf-8")

    missing_observations = subprocess.run(
        [
            sys.executable,
            "tools/check_zeno_oracle_reporter_soak_gate.py",
            "--policy",
            str(policy_path),
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert missing_observations.returncode == 1
    missing_receipt = json.loads(missing_observations.stdout)
    assert "observation_bundle_required" in missing_receipt["errors"]

    accepted_custom = subprocess.run(
        [
            sys.executable,
            "tools/check_zeno_oracle_reporter_soak_gate.py",
            "--policy",
            str(policy_path),
            "--observations",
            str(observations_path),
            "--format",
            "text",
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert accepted_custom.returncode == 0, accepted_custom.stdout + accepted_custom.stderr

    require_live = subprocess.run(
        [
            sys.executable,
            "tools/check_zeno_oracle_reporter_soak_gate.py",
            "--require-live",
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert require_live.returncode == 1
    receipt = json.loads(require_live.stdout)
    assert receipt["observation_bundle_status"] == "rejected"
    assert "public_soak_not_completed" in receipt["errors"]
