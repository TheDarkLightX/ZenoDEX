from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
CLI = [sys.executable, "tools/zenodex_oracle_cli.py"]


def test_oracle_cli_doctor_and_list() -> None:
    doctor = subprocess.run(
        [*CLI, "doctor"],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert doctor.returncode == 0, doctor.stderr
    doctor_receipt = json.loads(doctor.stdout)
    assert doctor_receipt["ok"] is True
    assert doctor_receipt["surface_count"] >= 15
    assert doctor_receipt["chaos_surface_count"] >= 15
    assert doctor_receipt["missing_scripts"] == []

    listed = subprocess.run(
        [*CLI, "list"],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert listed.returncode == 0, listed.stderr
    listing = json.loads(listed.stdout)
    assert "feed" in listing["surfaces"]
    assert "signed-report" in listing["surfaces"]
    assert listing["aliases"]["feed-registry"] == "feed"


def test_oracle_cli_creates_and_verifies_feed_registry(tmp_path: Path) -> None:
    registry_path = tmp_path / "feed-registry.json"
    sample = subprocess.run(
        [*CLI, "sample", "feed", "--output", str(registry_path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert sample.returncode == 0, sample.stderr
    assert sample.stdout == ""
    assert registry_path.is_file()

    verify = subprocess.run(
        [*CLI, "verify", "feed", str(registry_path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert verify.returncode == 0, verify.stderr
    result = json.loads(verify.stdout)
    assert result["status"] == "accepted"
    assert result["feed_count"] == 1


def test_oracle_cli_creates_and_verifies_signed_report(tmp_path: Path) -> None:
    submission_path = tmp_path / "signed-report.json"
    sample = subprocess.run(
        [*CLI, "sample", "signed-report", "--output", str(submission_path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert sample.returncode == 0, sample.stderr
    assert sample.stdout == ""
    assert submission_path.is_file()

    verify = subprocess.run(
        [*CLI, "verify", "signed-report", str(submission_path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert verify.returncode == 0, verify.stderr
    result = json.loads(verify.stdout)
    assert result["status"] == "accepted"
    assert result["report_count"] == 2


def test_oracle_cli_runs_feed_registry_chaos() -> None:
    proc = subprocess.run(
        [*CLI, "chaos", "feed"],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stderr
    receipt = json.loads(proc.stdout)
    assert receipt["schema"] == "zenodex.oracle.feed_registry_chaos_replay.v1"
    assert receipt["ok"] is True
    assert receipt["case_count"] == 26
    assert receipt["failed_case_count"] == 0


def test_oracle_cli_registers_feed_registry_to_local_store(tmp_path: Path) -> None:
    registry_path = tmp_path / "feed-registry.json"
    store_path = tmp_path / "oracle-store"
    receipt_path = tmp_path / "feed-registration-receipt.json"
    sample = subprocess.run(
        [*CLI, "sample", "feed", "--output", str(registry_path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert sample.returncode == 0, sample.stderr

    register = subprocess.run(
        [
            *CLI,
            "register-feed",
            str(registry_path),
            "--store",
            str(store_path),
            "--receipt-output",
            str(receipt_path),
        ],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert register.returncode == 0, register.stderr
    assert register.stdout == ""
    receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
    assert receipt["schema"] == "zenodex.oracle.cli_feed_registration_receipt.v1"
    assert receipt["status"] == "accepted"
    stored = Path(receipt["stored_path"])
    assert stored.is_file()
    assert stored.parent == store_path / "feeds"


def test_oracle_cli_submits_signed_report_to_local_store(tmp_path: Path) -> None:
    submission_path = tmp_path / "signed-report.json"
    store_path = tmp_path / "oracle-store"
    sample = subprocess.run(
        [*CLI, "sample", "signed-report", "--output", str(submission_path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert sample.returncode == 0, sample.stderr

    submit = subprocess.run(
        [*CLI, "submit-report", str(submission_path), "--store", str(store_path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert submit.returncode == 0, submit.stderr
    receipt = json.loads(submit.stdout)
    assert receipt["schema"] == "zenodex.oracle.cli_report_submission_receipt.v1"
    assert receipt["status"] == "accepted"
    assert receipt["report_count"] == 2
    stored = Path(receipt["stored_path"])
    assert stored.is_file()
    assert stored.parent == store_path / "signed_reports"


def test_oracle_cli_rejects_unknown_surface() -> None:
    proc = subprocess.run(
        [*CLI, "sample", "unknown-surface"],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode != 0
    assert "unknown Oracle surface" in proc.stderr
