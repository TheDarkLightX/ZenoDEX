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
    PROOF: "687a18bb663fbbbf0b565da137ecee8defb790126e1249303ba2773fb694d005",
    ESSO_MODEL: "d7b547e32790828c149fb0e3bdd6b32e11a235bbb67b6cf02eaaff4db2681252",
    PYTHON_TYPES: "8d37ed72fcf15cf7849179d4ff358f4fbbdc33905348f7ab790b2fe090e8044d",
    PYTHON_REFINEMENT: "abf60faacdcd45def5163e618494a2202c9c1ab7e11bde1f44b7b29cd0057697",
    RUST_STATE: "44f6874589e72c7fefdcac8b6c220fb311c6dc0f1e53bb3b962e32a6d593b98c",
    RUST_REFINEMENT: "e91f27cd2f38db434b1d8c77ef72a34508ec4ab744dff3843261fe263139316f",
}

THEOREMS = (
    "necessaryRelation_independent_of_reserves",
    "exactCurrentProfileCustody_independent_of_reserves",
    "exactAllocation_implies_necessaryRelation",
    "exactAllocation_noUnclassified_implies_exactCurrentProfileRelation",
    "necessaryRelation_nonvacuous",
    "exactCurrentProfileRelation_nonvacuous",
    "overCollateralised_isBacked_notExact",
    "noUnclassified_premise_is_necessary",
    "deposit_preserves_reserves",
    "deposit_preserves_necessaryRelation",
    "deposit_preserves_exactCurrentProfileCustody",
    "deposit_preserves_exactCurrentProfileRelation",
    "drain_preserves_reserves",
    "drain_preserves_necessaryRelation",
    "drain_preserves_exactCurrentProfileCustody",
    "drain_preserves_exactCurrentProfileRelation",
    "sameDomainBacked_implies_aggregateBacked",
    "aggregateOnly_permits_crossDomainBacking",
    "openTerminalCovered_implies_aggregateCovered",
    "aggregateClaimants_permit_claimantSwap",
    "sameDomainBacked_implies_reserveInclusiveBacking",
    "reserveInclusiveBacking_permits_missingExactCustody",
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
    assert "def ExactCurrentProfileCustody" in lean
    assert "def ExactCurrentProfileRelation" in lean
    assert "exactAllocation_noUnclassified_implies_exactCurrentProfileRelation" in lean
    assert "reserveInclusiveBacking_permits_missingExactCustody" in lean
    assert "necessaryRelation_independent_of_reserves" in lean
    assert "terminalProjection_hasNoUniversalDomainRecovery" in lean
    assert "inv_exact_custody_partition_d0" in esso
    assert "inv_exact_custody_partition_d1" in esso
    assert "inv_exact_claimant_domain_liabilities" in esso
    assert "inv_open_terminals_fit_exact_allocations" in esso
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
