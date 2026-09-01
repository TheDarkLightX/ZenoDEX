"""Source-bound Lean evidence for the bounded GlobalAccountingAllocationCertificateV1 model.

This gate binds the theorem surface of the bounded three-lane, two-domain,
two-claimant model to the exact Python checker, its Rust twin, and the shared
golden fixture. It grants no verifier, settlement, release, or production
authority; the model proves nothing about finite-width arithmetic, canonical
bytes, roots, or the running implementation.
"""

from __future__ import annotations

import hashlib
import json
import re
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
LEAN_DIR = ROOT / "lean-mathlib"
PROOF = LEAN_DIR / "Proofs" / "GlobalAccountingAllocationCertificateV1.lean"
SCANNER = ROOT / "tools" / "scan_lean_proof_placeholders_v1.py"
PYTHON_CHECKER = ROOT / "src" / "core" / "global_accounting_allocation_certificate_v1.py"
RUST_TWIN = ROOT / "zk" / "global_settlement_abi_v1" / "src" / "global_accounting_allocation_certificate.rs"
FIXTURE = ROOT / "tests" / "data" / "global_accounting_allocation_certificate_v1_golden.json"

NAMESPACE = "Proofs.GlobalAccountingAllocationCertificateV1"
PINNED_SOURCES = {
    PROOF: "fd07786d38fbb235f4219dad2f10d6400050f29ef0e64af6c23c28e9abd198db",
    PYTHON_CHECKER: "4302b6463fbb566b996e6e4a220a142185d67265535b70adb0d3c48b6b2b36c7",
    RUST_TWIN: "4ceae85fe7f274de0750b7c9092adc51ecfcaa46e85869eb67c7286ac2e3d80e",
    FIXTURE: "51986e67a6ee656f6465c2693e9d67e93da0bd3e1cd851e9e7a7470086a8cb3d",
}

THEOREMS = (
    "certificate_implies_normativePartition",
    "certificate_implies_sameDomainBacked",
    "certificate_implies_terminalCovered",
    "certificate_noReserve_noExternal_implies_exactCustody",
    "noReceiptBacked_forces_allDisabled",
    "noReceiptBacked_implies_zeroTables",
    "emptyFragment_checks",
    "registeredEmpty_nonvacuous",
    "hotFragment_checks",
    "mixed_nonvacuous",
    "unassignedAtom_fails_partition",
    "reserve_cannot_cover_claimant",
    "enabledWithoutProducer_fails_gate",
    "terminalOverEntitlement_fails_bound",
    "unassigned_satisfies_all_but_partition",
    "lanePartition_premise_is_necessary",
)

ALLOWED_STANDARD_AXIOMS = frozenset({"propext", "Quot.sound", "Classical.choice"})

# Reject codes of the running checker that the model's predicates stand for.
MIRRORED_REJECT_CODES = (
    "BLOCKED_LANE_PRODUCER_MISSING",
    "DISABLED_LANE_NOT_EMPTY",
    "SOURCE_ATOM_NOT_ASSIGNED_EXACTLY_ONCE",
    "ENTITLEMENT_ROWS_DRIFT",
    "RESERVE_ROWS_DRIFT",
    "EXTERNAL_OBLIGATION_BINDING_DRIFT",
    "TERMINAL_BINDING_DRIFT",
    "LANE_AGGREGATE_DRIFT",
)


def _require_lake() -> str:
    lake = shutil.which("lake")
    assert lake is not None, "bounded certificate formal gate requires lake"
    return lake


def _lean(*args: str, timeout: int = 600) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [_require_lake(), *args],
        cwd=LEAN_DIR,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=timeout,
        check=False,
    )


def _theorem_names(source: str) -> tuple[str, ...]:
    return tuple(re.findall(r"^theorem\s+([A-Za-z0-9_.]+)", source, re.MULTILINE))


def _axiom_dependencies(output: str) -> set[str]:
    dependencies: set[str] = set()
    for body in re.findall(r"depends on axioms:\s*\[([^\]]*)\]", output, re.DOTALL):
        dependencies.update(item.strip() for item in body.split(",") if item.strip())
    return dependencies


@pytest.fixture(scope="module")
def compiled_proof() -> None:
    result = _lean("env", "lean", "-DwarningAsError=true", str(PROOF))
    assert result.returncode == 0, result.stdout + result.stderr


def test_exact_sources_are_pinned() -> None:
    for path, expected_sha256 in PINNED_SOURCES.items():
        assert hashlib.sha256(path.read_bytes()).hexdigest() == expected_sha256, path


def test_explicit_theorem_surface_is_compiler_checked(compiled_proof: None) -> None:
    assert _theorem_names(PROOF.read_text(encoding="utf-8")) == THEOREMS


def test_repository_placeholder_scanner_accepts_the_proof() -> None:
    result = subprocess.run(
        [sys.executable, str(SCANNER), str(PROOF), "--json"],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=120,
        check=False,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    payload = json.loads(result.stdout)
    assert payload["blocked"] is False
    assert payload["match_count"] == 0
    assert payload["axiom_check"] is True


def test_theorem_surface_uses_only_standard_axioms(
    compiled_proof: None,
    tmp_path: Path,
) -> None:
    qualified = tuple(f"{NAMESPACE}.{name}" for name in THEOREMS)
    probe = tmp_path / "GlobalAccountingAllocationCertificateV1Axioms.lean"
    probe.write_text(
        PROOF.read_text(encoding="utf-8")
        + "\n"
        + "\n".join(f"#print axioms {name}" for name in qualified)
        + "\n",
        encoding="utf-8",
    )
    result = _lean("env", "lean", str(probe))
    assert result.returncode == 0, result.stdout + result.stderr
    for name in qualified:
        assert f"'{name}'" in result.stdout, name
    assert _axiom_dependencies(result.stdout) <= ALLOWED_STANDARD_AXIOMS
    assert "sorryAx" not in result.stdout


def test_model_predicates_name_the_checker_reject_codes() -> None:
    lean = PROOF.read_text(encoding="utf-8")
    python = PYTHON_CHECKER.read_text(encoding="utf-8")
    rust = RUST_TWIN.read_text(encoding="utf-8")
    fixture = json.loads(FIXTURE.read_text(encoding="utf-8"))
    for code in MIRRORED_REJECT_CODES:
        assert f"`{code}`" in lean, code
        assert f'{code} = "{code}"' in python, code
        assert code in rust, code
        assert code in fixture["reject_messages"], code
    for predicate in ("def ProducerGate", "def LanePartition", "def TerminalBound", "def RowsEqual", "def AggregateEqual", "def CertificateRelation"):
        assert predicate in lean, predicate
    assert "RECEIPT_BACKED" not in {entry["producer_kind"] for entry in fixture["producer_registry"].values()}


def test_claim_ceiling_excludes_runtime_and_authority_promotion() -> None:
    proof = " ".join(PROOF.read_text(encoding="utf-8").split())
    for phrase in (
        "Research-only",
        "canonical bytes, roots, and authority are outside this model",
        "replayed, not proved",
        "a reserve never stands in for a missing entitlement",
    ):
        assert phrase in proof, phrase
