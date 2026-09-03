from __future__ import annotations

import re
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
LOCK = ROOT / "config" / "tau_lang_adt_research.lock"
MUTATION_SPEC = (
    ROOT
    / "src"
    / "tau_specs"
    / "recommended"
    / "proof_carrying_constitutional_mutation_v1.tau"
)
COORDINATION_SPEC = (
    ROOT
    / "src"
    / "tau_specs"
    / "recommended"
    / "mutation_coordination_classifier_v1.tau"
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


def _replay(tau_bin: Path, spec: Path, final_wire: str) -> None:
    text = spec.read_text(encoding="utf-8")
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
    assert proc.returncode == 0, transcript
    assert "(Error)" not in transcript, transcript
    assert _VERDICT_RE.findall(clean_stdout) == _expected_results(text), transcript
    assert final_wire in clean_stdout, transcript


def test_tau_proof_carrying_mutation_source_contract() -> None:
    mutation = MUTATION_SPEC.read_text(encoding="utf-8")
    coordination = COORDINATION_SPEC.read_text(encoding="utf-8")
    assert "gmi[t].proposal & gmo[t-1].law'" in mutation
    assert "gmo[t-1].law & gmi[t].proposal" in mutation
    assert "all x:tau" in mutation
    assert "EXPECTED-RESULTS: T F T F T F T T F T" in mutation
    assert len(_expected_results(mutation)) == 10
    assert "(mco[t-1].state & mci[t].keep) | mci[t].add" in coordination
    assert "ex tb:tau ex a:tau ex b:tau" in coordination
    assert "EXPECTED-RESULTS: T T F T F T T T" in coordination
    assert len(_expected_results(coordination)) == 8


def test_tau_proof_carrying_mutation_pinned_replay(capsys) -> None:
    with capsys.disabled():
        tau_bin, commit = _ensure_pinned_tau()
        print(
            f"tau-proof-carrying-mutation-v1: pinned Tau ready at {commit}",
            flush=True,
        )
    _replay(tau_bin, MUTATION_SPEC, "gmo[3] :=")
    _replay(tau_bin, COORDINATION_SPEC, "mco[2] :=")
