#!/usr/bin/env python3
"""Cross-language and verifier readiness matrix for FCIS M5-P4A.

Produces a machine-readable JSON matrix mapping every FCIS authority surface
to its cross-language (Python/Rust) status, verifier readiness, and proof
infrastructure status.

M5-P4A-XLANG-001: every trusted core authority surface is enumerated.
M5-P4A-XLANG-002: Rust authority status is derived from source.
M5-P4A-XLANG-003: verifier and proof infrastructure status is enumerated.
"""

from __future__ import annotations

import hashlib
import sys
from pathlib import Path
from typing import Any

from src.runtime.authority import (
    PUBLIC_TESTNET_REQUIRED_RUST_AUTHORITY_SURFACES,
    TRUSTED_CORE_AUTHORITY_SURFACES,
)
from src.state.canonical import canonical_json_bytes

_REPO_ROOT = Path(__file__).resolve().parents[1]
_REPORT_PATH = _REPO_ROOT / "docs" / "research" / "FCIS_M5_P4A_CROSS_LANGUAGE_MATRIX_V1.json"
_SCHEMA = "zenodex/fcis-m5-p4a-cross-language-matrix/v1"


def _check_rust_surface(surface: str) -> dict[str, Any]:
    """Check if a Rust implementation exists for the given surface."""
    rust_paths = [
        _REPO_ROOT / "rust" / "src" / f"{surface}.rs",
        _REPO_ROOT / "rust" / f"{surface}.rs",
        _REPO_ROOT / "src" / "runtime" / f"rust_{surface}.py",
    ]
    rust_exists = any(p.exists() for p in rust_paths)
    return {
        "surface": surface,
        "rust_implementation_exists": rust_exists,
        "rust_paths_checked": [str(p.relative_to(_REPO_ROOT)) for p in rust_paths],
    }


def _check_proof_infrastructure() -> dict[str, Any]:
    """Check proof/verifier infrastructure status."""
    proof_paths = {
        "proof_verifier": _REPO_ROOT / "src" / "integration" / "proof_verifier.py",
        "proof_mining_context": _REPO_ROOT / "src" / "integration" / "proof_mining_context.py",
        "settlement_strong_certificate": _REPO_ROOT / "src" / "integration" / "settlement_strong_certificate.py",
        "settlement_end_to_end_certificate": _REPO_ROOT / "src" / "integration" / "settlement_end_to_end_certificate_packet.py",
        "risc0_journal": _REPO_ROOT / "src" / "integration" / "risc0_journal.py",
        "lean_proofs": _REPO_ROOT / "proofs",
        "rust_workspace": _REPO_ROOT / "rust" / "Cargo.toml",
    }
    return {
        name: path.exists()
        for name, path in proof_paths.items()
    }


def _check_verifier_readiness() -> dict[str, Any]:
    """Check verifier readiness for FCIS mount."""
    authority_checker = _REPO_ROOT / "tools" / "check_fcis_authority_snapshot_contract.py"
    fcis_step_evaluator = _REPO_ROOT / "src" / "core" / "fcis_step_evaluator.py"
    fcis_spot_shadow = _REPO_ROOT / "src" / "integration" / "fcis_spot_shadow.py"
    settlement_strong_validator = _REPO_ROOT / "src" / "core" / "settlement_strong_validator.py"
    support_root = _REPO_ROOT / "src" / "state" / "support_root.py"
    return {
        "authority_snapshot_checker": authority_checker.exists(),
        "fcis_step_evaluator": fcis_step_evaluator.exists(),
        "fcis_spot_shadow": fcis_spot_shadow.exists(),
        "settlement_strong_validator": settlement_strong_validator.exists(),
        "support_root_v5": support_root.exists(),
    }


def _build_surface_matrix() -> list[dict[str, Any]]:
    """Build the cross-language surface matrix."""
    surfaces = sorted(TRUSTED_CORE_AUTHORITY_SURFACES)
    matrix: list[dict[str, Any]] = []
    for surface in surfaces:
        rust_status = _check_rust_surface(surface)
        required_for_testnet = surface in PUBLIC_TESTNET_REQUIRED_RUST_AUTHORITY_SURFACES
        matrix.append({
            "surface": surface,
            "trusted_core": True,
            "required_for_public_testnet": required_for_testnet,
            "rust_implementation_exists": rust_status["rust_implementation_exists"],
            "python_authority_default": True,
            "mount_readiness": "READY" if rust_status["rust_implementation_exists"] else "PENDING_RUST",
        })
    return matrix


def _build_fcis_specific_matrix() -> list[dict[str, Any]]:
    """Build FCIS-specific cross-language readiness entries."""
    fcis_surfaces = [
        {
            "surface": "fcis_step_evaluator",
            "component": "src/core/fcis_step_evaluator.py",
            "python_implemented": True,
            "rust_implemented": False,
            "verifier_gate": "authority_snapshot_checker",
            "mount_readiness": "PENDING_AUTHORITY_CONTRACT",
        },
        {
            "surface": "fcis_spot_shadow",
            "component": "src/integration/fcis_spot_shadow.py",
            "python_implemented": True,
            "rust_implemented": False,
            "verifier_gate": "differential_replay",
            "mount_readiness": "PENDING_PARITY_CLOSURE",
        },
        {
            "surface": "fcis_settlement_strong_validator",
            "component": "src/core/settlement_strong_validator.py",
            "python_implemented": True,
            "rust_implemented": False,
            "verifier_gate": "authority_snapshot_checker",
            "mount_readiness": "PENDING_AUTHORITY_CONTRACT",
        },
        {
            "surface": "fcis_support_root_v5",
            "component": "src/core/fcis_support_profile_v5.py",
            "python_implemented": True,
            "rust_implemented": False,
            "verifier_gate": "golden_vector",
            "mount_readiness": "PENDING_RUST",
        },
        {
            "surface": "fcis_legacy_state_snapshots",
            "component": "src/state/legacy_state_snapshots.py",
            "python_implemented": True,
            "rust_implemented": False,
            "verifier_gate": "authority_snapshot_checker",
            "mount_readiness": "PENDING_DELETION",
        },
        {
            "surface": "fcis_route_settlement",
            "component": "src/core/route_settlement.py",
            "python_implemented": True,
            "rust_implemented": False,
            "verifier_gate": "authority_snapshot_checker",
            "mount_readiness": "PENDING_AUTHORITY_CONTRACT",
        },
    ]
    return fcis_surfaces


def _build_matrix() -> dict[str, Any]:
    surface_matrix = _build_surface_matrix()
    fcis_matrix = _build_fcis_specific_matrix()
    proof_infra = _check_proof_infrastructure()
    verifier_readiness = _check_verifier_readiness()
    matrix: dict[str, Any] = {
        "schema": _SCHEMA,
        "trusted_core_surfaces": sorted(TRUSTED_CORE_AUTHORITY_SURFACES),
        "public_testnet_required_surfaces": sorted(PUBLIC_TESTNET_REQUIRED_RUST_AUTHORITY_SURFACES),
        "surface_matrix": surface_matrix,
        "fcis_specific_matrix": fcis_matrix,
        "proof_infrastructure": proof_infra,
        "verifier_readiness": verifier_readiness,
        "overall_readiness": "NOT_READY",
    }
    ready_count = sum(1 for s in surface_matrix if s["mount_readiness"] == "READY")
    total = len(surface_matrix)
    fcis_ready = sum(1 for s in fcis_matrix if s["mount_readiness"] == "READY")
    fcis_total = len(fcis_matrix)
    matrix["surface_readiness_summary"] = {
        "trusted_core_ready": ready_count,
        "trusted_core_total": total,
        "fcis_ready": fcis_ready,
        "fcis_total": fcis_total,
    }
    matrix_bytes = canonical_json_bytes(matrix)
    matrix["matrix_sha256"] = "0x" + hashlib.sha256(matrix_bytes).hexdigest()
    return matrix


def _write_matrix(matrix: dict[str, Any]) -> None:
    _REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    _REPORT_PATH.write_bytes(canonical_json_bytes(matrix))


def main() -> int:
    check_mode = "--check" in sys.argv
    matrix = _build_matrix()
    if check_mode:
        if not _REPORT_PATH.exists():
            print("ERROR: cross-language matrix does not exist", file=sys.stderr)
            return 1
        existing = _REPORT_PATH.read_bytes()
        new_bytes = canonical_json_bytes(matrix)
        if existing != new_bytes:
            print("ERROR: cross-language matrix changed", file=sys.stderr)
            return 1
        print(f"OK: cross-language matrix matches (sha256={matrix['matrix_sha256']})")
        return 0
    _write_matrix(matrix)
    summary = matrix["surface_readiness_summary"]
    print(
        f"OK: wrote {_REPORT_PATH} "
        f"(trusted_core={summary['trusted_core_ready']}/{summary['trusted_core_total']}, "
        f"fcis={summary['fcis_ready']}/{summary['fcis_total']})"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
