from __future__ import annotations

import re
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
LOCK = ROOT / "config" / "tau_lang_adt_research.lock"
TABLE_SPEC = (
    ROOT
    / "src"
    / "tau_specs"
    / "recommended"
    / "asset_registry_transfer_table_contract_v1.tau"
)
TAU_DIR_REL = "external/tau-lang-adt-logical-abi-v1"
TAU_DIR = ROOT / TAU_DIR_REL
TAU_BIN = TAU_DIR / "build-Release" / "tau"
_ANSI_RE = re.compile(r"\x1b\[[0-9;]*m")
_VERDICT_RE = re.compile(r"%\d+:\s*(T|F)\b")
_COMMIT_RE = re.compile(r"[0-9a-f]{40}")


def _lock_commit() -> str:
    rows: dict[str, str] = {}
    for raw in LOCK.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        key, sep, value = line.partition("=")
        assert sep and key and key not in rows
        rows[key] = value
    commit = rows["commit"]
    assert _COMMIT_RE.fullmatch(commit)
    return commit


def _git_head(path: Path) -> str | None:
    if not (path / ".git").exists():
        return None
    proc = subprocess.run(
        ["git", "-C", str(path), "rev-parse", "HEAD"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=15,
    )
    return proc.stdout.strip() if proc.returncode == 0 else None


def _ensure_pinned_tau() -> tuple[Path, str]:
    commit = _lock_commit()
    if TAU_BIN.is_file() and _git_head(TAU_DIR) == commit:
        return TAU_BIN, commit
    proc = subprocess.run(
        [
            "bash",
            "tools/build_tau_adt_research_pin_v1.sh",
            commit,
            TAU_DIR_REL,
            "build-Release",
        ],
        cwd=ROOT,
        text=True,
        timeout=2400,
    )
    assert proc.returncode == 0, "pinned Tau build failed; see streamed output"
    assert TAU_BIN.is_file()
    assert _git_head(TAU_DIR) == commit
    return TAU_BIN, commit


def _expected_results(text: str) -> list[str]:
    for line in text.splitlines():
        if line.startswith("# EXPECTED-RESULTS:"):
            values = line.split(":", 1)[1].strip().split()
            assert values and all(value in {"T", "F"} for value in values)
            return values
    raise AssertionError("missing EXPECTED-RESULTS header")


def test_tau_asset_registry_transfer_table_source_contract() -> None:
    text = TABLE_SPEC.read_text(encoding="utf-8")
    assert "type AssetTableInputADT1" in text
    assert "type AssetTableOutputADT1" in text
    assert "(tb | row)" in text
    assert "iat[t].asset_probe & oat[t-1].assets" in text
    assert "iat[t].transfer_row & oat[t].fk" in text
    assert "EXPECTED-RESULTS: T T T F T T T T T T" in text
    assert len(_expected_results(text)) == 10


def test_tau_asset_registry_transfer_table_pinned_replay(capsys) -> None:
    with capsys.disabled():
        tau_bin, commit = _ensure_pinned_tau()
        print(
            f"tau-table-logical-abi-v1: pinned Tau ready at {commit}",
            flush=True,
        )

    text = TABLE_SPEC.read_text(encoding="utf-8")
    proc = subprocess.run(
        [str(tau_bin), "-q"],
        cwd=ROOT,
        input=text,
        capture_output=True,
        text=True,
        timeout=180,
    )
    transcript = proc.stdout + proc.stderr
    clean_stdout = _ANSI_RE.sub("", proc.stdout)
    verdicts = _VERDICT_RE.findall(clean_stdout)

    assert proc.returncode == 0, transcript
    assert "(Error)" not in transcript, transcript
    assert verdicts == _expected_results(text), transcript
    # Five structured inputs plus the explicit t=0 initial state must execute.
    assert "oat[0] :=" in clean_stdout, transcript
    assert "oat[5] :=" in clean_stdout, transcript
