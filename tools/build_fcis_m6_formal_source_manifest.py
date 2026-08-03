#!/usr/bin/env python3
"""Build or verify the closed FCIS M6 bounded-assurance source manifest."""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path

SOURCE_PATHS = (
    ".github/workflows/fcis-m6-bounded-formal-assurance.yml",
    "docs/research/FCIS_M6_FORMAL_RUNTIME_REFINEMENT_MATRIX_V1.json",
    "docs/research/FCIS_M6_FORMAL_SUITE_BOUNDED_RESULT_V1.json",
    "docs/research/FCIS_M6_FORMAL_SUITE_REPORT_V1.md",
    "docs/research/FCIS_M6_FORMAL_TO_RUNTIME_ASSURANCE_V1.md",
    "docs/research/FCIS_M6_PR509_REPAIR_V2_REPORT_20260802.md",
    "features/fcis_m6_formal_runtime_refinement.feature",
    "formal/esso/fcis_m6_atomic_publication_v1.yaml",
    "formal/esso/fcis_m6_formal_suite_v1.json",
    "formal/esso/fcis_m6_history_fixed_point_v1.yaml",
    "formal/esso/fcis_m6_managed_asset_issuance_v1.yaml",
    "formal/esso/fcis_m6_migration_writer_v1.yaml",
    "formal/esso/fcis_m6_no_bypass_v1.yaml",
    "formal/esso/fcis_m6_nonce_retry_classifier_v1.yaml",
    "formal/esso/fcis_m6_oracle_risk_gate_v1.yaml",
    "formal/esso/fcis_m6_outbox_delivery_v1.yaml",
    "formal/esso/fcis_m6_promotion_subject_v1.yaml",
    "formal/esso/fcis_m6_proof_context_v1.yaml",
    "formal/esso/fcis_m6_reopen_reauthorization_v1.yaml",
    "formal/esso/fcis_m6_value_flow_kernel_v1.yaml",
    "formal/esso/fcis_m6_zenoledger_tau_continuity_v1.yaml",
    "tests/test_fcis_m6_formal_assurance_packet.py",
    "tools/build_fcis_m6_formal_source_manifest.py",
    "tools/check_fcis_m6_formal_runtime_matrix.py",
    "tools/check_fcis_m6_formal_specs.py",
    "tools/run_fcis_m6_formal_assurance_gate.sh",
)


def render(root: Path) -> bytes:
    if SOURCE_PATHS != tuple(sorted(set(SOURCE_PATHS))):
        raise RuntimeError("source allowlist must be unique and sorted")
    lines: list[str] = []
    for relative in SOURCE_PATHS:
        path = root / relative
        if not path.is_file():
            raise RuntimeError(f"missing source file: {relative}")
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        lines.append(f"{digest}  {relative}")
    return ("\n".join(lines) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    output_group = parser.add_mutually_exclusive_group()
    output_group.add_argument("--output", type=Path)
    output_group.add_argument("--check", action="store_true")
    args = parser.parse_args()

    expected_path = args.root / "docs/research/FCIS_M6_FORMAL_SUITE_SOURCE_MANIFEST.sha256"
    rendered = render(args.root)
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_bytes(rendered)
        print(f"FCIS_M6_FORMAL_SOURCE_MANIFEST_WRITTEN entries={len(SOURCE_PATHS)}")
        return 0
    if not expected_path.is_file() or expected_path.read_bytes() != rendered:
        print("FCIS_M6_FORMAL_SOURCE_MANIFEST_DRIFT")
        return 1
    print(f"FCIS_M6_FORMAL_SOURCE_MANIFEST_MATCH entries={len(SOURCE_PATHS)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
