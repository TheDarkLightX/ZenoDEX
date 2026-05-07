from __future__ import annotations

import re
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
TARGET = ROOT / "lean-mathlib" / "Proofs" / "ZenoProofMarket.lean"


TRUST_ESCAPE_RE = re.compile(
    r"^\s*(sorry|admit)\b|^\s*axiom\b|^\s*unsafe\b|\bsorryAx\b",
    re.MULTILINE,
)

AXIOM_AUDIT = """
import Proofs.ZenoProofMarket
#print axioms Proofs.ZenoProofMarket.settlement_certificate_assumptions_nonvacuous
#print axioms Proofs.ZenoProofMarket.accepted_settlement_contract_nonvacuous
#print axioms Proofs.ZenoProofMarket.primary_market_without_secondary_exchange_nonvacuous
#print axioms Proofs.ZenoProofMarket.full_exchange_nonvacuous
#print axioms Proofs.ZenoProofMarket.zk_pre_disclosure_assumptions_nonvacuous
#print axioms Proofs.ZenoProofMarket.zk_payment_release_assumptions_nonvacuous
#print axioms Proofs.ZenoProofMarket.zk_pre_disclosure_acceptance_locks_without_reveal
#print axioms Proofs.ZenoProofMarket.zk_payment_release_requires_reveal_and_conserves_payment
"""


def test_lean_zenoproof_market_builds() -> None:
    subprocess.run(
        ["lake", "env", "lean", "Proofs/ZenoProofMarket.lean"],
        cwd=ROOT / "lean-mathlib",
        check=True,
    )


def test_lean_zenoproof_market_has_no_trust_escapes() -> None:
    text = TARGET.read_text(encoding="utf-8")
    assert TRUST_ESCAPE_RE.search(text) is None


def test_lean_zenoproof_market_nonvacuity_axiom_audit() -> None:
    subprocess.run(
        ["lake", "build", "Proofs.ZenoProofMarket"],
        cwd=ROOT / "lean-mathlib",
        check=True,
    )
    proc = subprocess.run(
        ["lake", "env", "lean", "--stdin"],
        cwd=ROOT / "lean-mathlib",
        input=AXIOM_AUDIT,
        text=True,
        capture_output=True,
        check=True,
    )
    output = proc.stdout + proc.stderr

    assert "sorryAx" not in output
    assert "primary_market_without_secondary_exchange_nonvacuous' does not depend on any axioms" in output
    assert "full_exchange_nonvacuous' does not depend on any axioms" in output
    assert "settlement_certificate_assumptions_nonvacuous' depends on axioms: [propext," in output
    assert "accepted_settlement_contract_nonvacuous' depends on axioms: [propext," in output
    assert "zk_pre_disclosure_assumptions_nonvacuous' depends on axioms: [propext," in output
    assert "zk_payment_release_assumptions_nonvacuous' depends on axioms: [propext," in output
    assert "zk_pre_disclosure_acceptance_locks_without_reveal' does not depend on any axioms" in output
    assert "zk_payment_release_requires_reveal_and_conserves_payment' depends on axioms: [propext," in output
