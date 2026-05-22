from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
CLI = [sys.executable, "tools/zenodex_oracle_cli.py"]
WRAPPER = [str(REPO / "bin" / "zenodex-oracle")]


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


def test_oracle_cli_packaged_wrapper_runs_doctor() -> None:
    doctor = subprocess.run(
        [*WRAPPER, "doctor"],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert doctor.returncode == 0, doctor.stderr
    receipt = json.loads(doctor.stdout)
    assert receipt["ok"] is True
    assert receipt["surface_count"] >= 15


def test_oracle_rc_package_exposes_bin_entrypoint() -> None:
    version = "zeno-oracle-pytest-rc"
    proc = subprocess.run(
        ["bash", "scripts/package_zeno_oracle_rc.sh", version],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stderr

    stage = REPO / "dist" / version
    manifest_path = stage / "ZEN_ORACLE_RC_MANIFEST.json"
    wrapper_path = stage / "bin" / "zenodex-oracle"
    assert wrapper_path.is_file()
    assert wrapper_path.stat().st_mode & 0o111
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    assert manifest["entrypoint"] == "bin/zenodex-oracle"
    assert manifest["python_entrypoint"] == "tools/zenodex_oracle_cli.py"
    assert manifest["product_name"] == "Zeno Oracle"
    assert manifest["branding"]["icon_256"] == "assets/branding/zeno-oracle/zeno_oracle_icon_256.png"
    assert manifest["whitepaper"] == "docs/papers/zeno-oracle-whitepaper/main.pdf"
    assert manifest["whitepaper_author"] == "Dana Edwards"
    assert manifest["devnet_alpha_gate"] == "scripts/check_zeno_oracle_devnet_alpha.sh"
    assert any(item["path"] == "bin/zenodex-oracle" for item in manifest["files"])
    assert any(item["path"] == "tools/check_disaster_obligation_certificate.py" for item in manifest["files"])
    assert any(item["path"] == "tools/zeno_oracle_o3_receipt_flow_replay.py" for item in manifest["files"])
    assert any(
        item["path"] == "tools/zeno_oracle_disaster_obligation_certificate_manifest.json"
        for item in manifest["files"]
    )
    assert any(item["path"] == "tools/zenodex_oracle_reporter_economics_replay.py" for item in manifest["files"])
    assert any(item["path"] == "tools/zenodex_oracle_devnet_service.py" for item in manifest["files"])
    assert any(item["path"] == "assets/branding/zeno-oracle/zeno_oracle_icon_256.png" for item in manifest["files"])
    assert any(item["path"] == "docs/papers/zeno-oracle-whitepaper/main.pdf" for item in manifest["files"])
    assert any(item["path"] == "docs/ZENO_DISASTER_STATE_MINIMIZATION_GOAL.md" for item in manifest["files"])
    assert (REPO / "dist" / f"{version}.receipt.json").is_file()
    assert (REPO / "dist" / f"{version}.sig").is_file()


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


def test_oracle_cli_dry_run_exercises_local_mvp_flow(tmp_path: Path) -> None:
    workdir = tmp_path / "dry-run"
    proc = subprocess.run(
        [*CLI, "dry-run", "--workdir", str(workdir)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stderr
    receipt = json.loads(proc.stdout)
    assert receipt["schema"] == "zenodex.oracle.cli_dry_run_receipt.v1"
    assert receipt["status"] == "accepted"
    assert receipt["step_count"] == receipt["accepted_step_count"]
    step_names = {step["name"] for step in receipt["steps"]}
    assert "register_feed_to_local_store" in step_names
    assert "submit_report_to_local_store" in step_names
    assert "verify_adapter_bundle" in step_names
    assert (workdir / "store" / "feeds").is_dir()
    assert (workdir / "store" / "signed_reports").is_dir()


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
