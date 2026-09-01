"""Source-bound Lean evidence for the bounded V1 claimant/custody relation.

This gate binds the Lean theorem surface to the exact ESSO target model and to
the Python/Rust V1 sources that implement only the visible necessary checks.
It deliberately grants no verifier, settlement, release, or production
authority.
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
PROOF = LEAN_DIR / "Proofs" / "GlobalClaimantCustodyRelationV1.lean"
SCANNER = ROOT / "tools" / "scan_lean_proof_placeholders_v1.py"
ESSO_MODEL = (
    ROOT / "src" / "kernels" / "dex" / "global_claimant_custody_certificate_v1.yaml"
)
PYTHON_TYPES = ROOT / "src" / "core" / "global_settlement_types_v1.py"
PYTHON_REFINEMENT = (
    ROOT / "src" / "core" / "global_economic_state_effect_refinement_v1.py"
)
RUST_STATE = ROOT / "zk" / "global_settlement_abi_v1" / "src" / "state.rs"
RUST_REFINEMENT = (
    ROOT
    / "zk"
    / "global_settlement_abi_v1"
    / "src"
    / "global_economic_state_effect_refinement.rs"
)

NAMESPACE = "Proofs.GlobalClaimantCustodyRelationV1"
PINNED_SOURCES = {
    PROOF: "1fc04ed21c4615d483d037549ff151b3a5bd10bbdf263bcaa4ff992c4bf6b9d8",
    ESSO_MODEL: "492283e6791663550a424423571fc0cf1466cda604732dc2d3e6c027e6b2a60d",
    PYTHON_TYPES: "13871fb586d7e5c1106edd5c0a9fdcd6f817016925027a6bdfb5ca8f53f29f58",
    PYTHON_REFINEMENT: "2c80fe364241de0fa2c93c258767dd93ad65233fbb58de71af398b3b5c1c2d54",
    RUST_STATE: "44f6874589e72c7fefdcac8b6c220fb311c6dc0f1e53bb3b962e32a6d593b98c",
    RUST_REFINEMENT: "44352e36e147c59ca397e571237d48eebd91787066df26fb7a5b65b2a78b2672",
}

THEOREMS = (
    "exactAllocation_implies_necessaryRelation",
    "exactAllocation_noUnclassified_implies_certificateRelation",
    "controlledClaimReserveEquation_iff_exactCustody",
    "necessaryRelation_nonvacuous",
    "currentProfileCertificateRelation_nonvacuous",
    "deposit_preserves_necessaryRelation",
    "deposit_preserves_controlledClaimReserveEquation",
    "deposit_preserves_currentProfileCertificateRelation",
    "drain_preserves_necessaryRelation",
    "drain_preserves_controlledClaimReserveEquation",
    "drain_preserves_currentProfileCertificateRelation",
    "aggregateOnly_permits_crossDomainBacking",
    "aggregateClaimants_permit_claimantSwap",
    "reservesCanMaskMissingCustody",
    "reserveMasking_violates_controlledClaimReserveEquation",
    "terminalProjection_domainErasure_witness",
    "terminalProjection_domainErasure_notInjective",
    "terminalProjection_hasNoUniversalDomainRecovery",
)

ALLOWED_STANDARD_AXIOMS = frozenset({"propext", "Quot.sound", "Classical.choice"})


def _require_lake() -> str:
    lake = shutil.which("lake")
    assert lake is not None, "bounded claimant/custody formal gate requires lake"
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
    probe = tmp_path / "GlobalClaimantCustodyRelationV1Axioms.lean"
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


def test_lean_esso_and_runtime_sources_share_the_bounded_relation() -> None:
    lean = PROOF.read_text(encoding="utf-8")
    esso = ESSO_MODEL.read_text(encoding="utf-8")
    python = PYTHON_REFINEMENT.read_text(encoding="utf-8")
    rust = RUST_REFINEMENT.read_text(encoding="utf-8")

    assert "def SameDomainLiabilitiesBacked" in lean
    assert "def OpenTerminalClaimsCovered" in lean
    assert "def ControlledClaimReserveEquation" in lean
    assert "controlledClaimReserveEquation_iff_exactCustody" in lean
    assert "terminalProjection_hasNoUniversalDomainRecovery" in lean
    assert "inv_exact_claimant_domain_liabilities" in esso
    assert "inv_open_terminals_fit_exact_allocations" in esso
    assert "inv_current_profile_has_no_unclassified_custody" in esso
    assert "inv_controlled_claim_reserve_equation" in esso
    assert "inv_accept_requires_exact_bound_evidence" in esso
    for runtime in (python, rust):
        assert "liabilities exceed same-domain custody backing" in runtime
        assert "open terminal obligations exceed claimant liabilities" in runtime
        assert "root-bound" in runtime


def test_claim_ceiling_excludes_runtime_and_authority_promotion() -> None:
    proof = " ".join(PROOF.read_text(encoding="utf-8").split())
    for phrase in (
        "does not model canonical bytes",
        "runtime refinement",
        "verifier admission",
        "settlement authority",
        "production safety",
    ):
        assert phrase in proof
