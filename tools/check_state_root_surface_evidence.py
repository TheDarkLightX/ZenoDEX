#!/usr/bin/env python3
"""Build/check the state-root surface evidence receipt.

This is the Phase 4 committed-receipt gate for the `state_root` CBC row. Build
mode runs the replayable proof slice that is cheap enough locally (Python
preimage injectivity + Rust Kani guard contracts) and records source hashes.
Check mode re-hashes the same tracked sources and validates the result envelope
without needing Kani.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_SPEC = ROOT / "src" / "kernels" / "dex" / "state_root_v5_scope_contract.json"
DEFAULT_RECEIPT = ROOT / "docs" / "assurance" / "state_root_surface_evidence_receipt.json"

SPEC_SCHEMA = "zenodex.state_root.formal_spec.v1"
RECEIPT_SCHEMA = "zenodex.state_root.surface_evidence_receipt.v1"
CHECK_SCHEMA = "zenodex.state_root.surface_evidence_receipt_check.v1"

EXPECTED_VERSION = 5
EXPECTED_SECTIONS = ["BAL", "POL", "LPB", "LPA", "NNC", "FEE"]
EXPECTED_EXCLUDED_LANES = ["vault", "oracle", "perps"]

EXPECTED_SOURCE_FILES = [
    "src/kernels/dex/state_root_v5_scope_contract.json",
    "tools/check_state_root_surface_evidence.py",
    "tests/test_check_state_root_surface_evidence.py",
    "src/state/state_root.py",
    "src/integration/zeno_ledger_v0.py",
    "src/runtime/authority.py",
    "src/runtime/rust_invoker.py",
    "rust-runtime/crates/zenodex-runtime-core/src/state_root.rs",
    "tools/runtime/state_root_lib.py",
    "tools/runtime/state_root_injectivity.py",
    "tests/state/test_state_root_determinism.py",
    "tests/runtime/test_state_root_vectors.py",
    "tests/runtime/test_state_root_live_path.py",
    "tests/runtime/test_state_root_injectivity_proof.py",
    "tests/runtime/test_state_root_section_framing_grid.py",
    "tests/runtime/test_state_root_curve_config_grid.py",
    "tests/runtime/test_state_root_lp_duration_exhaustive_grid.py",
    "tests/integration/test_zeno_ledger_post_state_root_binding_v0.py",
    "tests/integration/test_proof_verifier_perps_scope_guard_regression.py",
    "config/deploy/production-strict.yaml",
    "config/deploy/public-testnet.yaml",
    ".github/workflows/runtime-shadow.yml",
]

KANI_HARNESSES = [
    "state_root::kani_contracts::pool_fee_bps_guard_is_exact",
    "state_root::kani_contracts::nonce_guard_is_exact",
    "state_root::kani_contracts::duration_metadata_presence_is_exact",
    "state_root::kani_contracts::pool_asset_order_guard_matches_fixed_width_byte_order",
    "state_root::kani_contracts::pool_asset_order_guard_rejects_equal_assets",
    "state_root::kani_contracts::pool_status_codes_are_in_domain_and_distinct",
    "state_root::kani_contracts::state_root_guard_covers_are_reachable",
]

KANI_EXPECTED_TOTALS: dict[str, dict[str, int]] = {
    "state_root::kani_contracts::pool_fee_bps_guard_is_exact": {
        "checks_total": 118,
        "cover_properties_total": 0,
    },
    "state_root::kani_contracts::nonce_guard_is_exact": {
        "checks_total": 118,
        "cover_properties_total": 0,
    },
    "state_root::kani_contracts::duration_metadata_presence_is_exact": {
        "checks_total": 1,
        "cover_properties_total": 0,
    },
    "state_root::kani_contracts::pool_asset_order_guard_matches_fixed_width_byte_order": {
        "checks_total": 42,
        "cover_properties_total": 0,
    },
    "state_root::kani_contracts::pool_asset_order_guard_rejects_equal_assets": {
        "checks_total": 42,
        "cover_properties_total": 0,
    },
    "state_root::kani_contracts::pool_status_codes_are_in_domain_and_distinct": {
        "checks_total": 7,
        "cover_properties_total": 0,
    },
    "state_root::kani_contracts::state_root_guard_covers_are_reachable": {
        "checks_total": 44,
        "cover_properties_total": 3,
    },
}

REQUIRED_TEST_COMMANDS = [
    {
        "id": "state_root_python_semantics",
        "command": [
            "python3",
            "-m",
            "pytest",
            "-q",
            "tests/state/test_state_root_determinism.py",
            "tests/runtime/test_state_root_injectivity_proof.py",
            "tests/runtime/test_state_root_section_framing_grid.py",
            "tests/runtime/test_state_root_lp_duration_exhaustive_grid.py",
        ],
    },
    {
        "id": "state_root_python_rust_differential",
        "command": [
            "python3",
            "-m",
            "pytest",
            "-q",
            "tests/runtime/test_state_root_vectors.py",
            "tests/runtime/test_state_root_curve_config_grid.py",
            "tests/runtime/test_state_root_live_path.py",
        ],
    },
    {
        "id": "state_root_runtime_binding",
        "command": [
            "python3",
            "-m",
            "pytest",
            "-q",
            "tests/integration/test_zeno_ledger_post_state_root_binding_v0.py",
            "tests/integration/test_proof_verifier_perps_scope_guard_regression.py",
        ],
    },
]


class EvidenceError(ValueError):
    pass


def _canonical_json_bytes(obj: Any) -> bytes:
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")


def _sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _load_json_object(path: Path, *, name: str) -> dict[str, Any]:
    try:
        obj = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise EvidenceError(f"{name} missing: {path}") from exc
    except Exception as exc:
        raise EvidenceError(f"{name} is not valid JSON: {path}: {exc}") from exc
    if not isinstance(obj, dict):
        raise EvidenceError(f"{name} must be a JSON object: {path}")
    return obj


def _source_hashes() -> list[dict[str, str]]:
    out: list[dict[str, str]] = []
    for rel in EXPECTED_SOURCE_FILES:
        path = ROOT / rel
        if not path.is_file():
            raise EvidenceError(f"source file missing: {rel}")
        out.append({"path": rel, "sha256": _sha256_file(path)})
    return out


def _receipt_hash_body(receipt: Mapping[str, Any]) -> dict[str, Any]:
    return {k: v for k, v in receipt.items() if k != "receipt_sha256"}


def _validate_spec_against_source(spec: Mapping[str, Any]) -> list[str]:
    errors: list[str] = []
    if spec.get("schema") != SPEC_SCHEMA:
        errors.append(f"spec.schema must be {SPEC_SCHEMA!r}")
    if spec.get("surface_id") != "state_root":
        errors.append("spec.surface_id must be 'state_root'")
    if spec.get("state_root_version") != EXPECTED_VERSION:
        errors.append(f"spec.state_root_version must be {EXPECTED_VERSION}")
    formula = spec.get("root_formula")
    if not isinstance(formula, Mapping):
        errors.append("spec.root_formula must be an object")
    else:
        domain = formula.get("domain")
        if not isinstance(domain, Mapping) or domain.get("tag") != "state_root" or domain.get("version") != EXPECTED_VERSION:
            errors.append("spec.root_formula.domain must be state_root/v5")
        if formula.get("hash") != "sha256":
            errors.append("spec.root_formula.hash must be sha256")
        if list(formula.get("section_order") or []) != EXPECTED_SECTIONS:
            errors.append("spec.root_formula.section_order does not match v5 source pin")
    widths = spec.get("identifier_widths")
    if widths != {"pubkey_bytes": 48, "asset_bytes": 32, "pool_id_bytes": 32}:
        errors.append("spec.identifier_widths must match fixed-width state-root identifiers")
    included = spec.get("included_sections")
    if not isinstance(included, Mapping) or sorted(included) != sorted(EXPECTED_SECTIONS):
        errors.append("spec.included_sections must cover exactly the v5 sections")
    excluded = spec.get("excluded_lanes")
    if not isinstance(excluded, list):
        errors.append("spec.excluded_lanes must be a list")
    else:
        fields = [item.get("field") for item in excluded if isinstance(item, Mapping)]
        if fields != EXPECTED_EXCLUDED_LANES:
            errors.append(f"spec.excluded_lanes fields {fields!r} != {EXPECTED_EXCLUDED_LANES!r}")
        for item in excluded:
            if not isinstance(item, Mapping):
                errors.append("spec.excluded_lanes entries must be objects")
                continue
            if item.get("required_value") != "None":
                errors.append(f"excluded lane {item.get('field')!r} must require None")
            if item.get("enforced_by") != "src.integration.zeno_ledger_v0.validate_dex_state_root_v0_spot_scope":
                errors.append(f"excluded lane {item.get('field')!r} has wrong enforcement ref")

    # Cross-check the spec against the imported Python implementation constants.
    sys.path.insert(0, str(ROOT))
    from src.state import state_root as state_root_mod  # noqa: PLC0415

    if state_root_mod.STATE_ROOT_VERSION != EXPECTED_VERSION:
        errors.append("src.state.state_root.STATE_ROOT_VERSION drifted")
    labels = [label.decode("ascii") for label in state_root_mod.STATE_ROOT_SECTION_LABELS]
    if labels != EXPECTED_SECTIONS:
        errors.append(f"src.state.state_root.STATE_ROOT_SECTION_LABELS {labels!r} != spec")
    return errors


def _run_injectivity_proof() -> dict[str, Any]:
    sys.path.insert(0, str(ROOT))
    from tools.runtime.state_root_injectivity import run_injectivity_proof  # noqa: PLC0415

    report = run_injectivity_proof()
    if not isinstance(report, dict) or report.get("ok") is not True:
        raise EvidenceError(f"state-root injectivity proof failed: {report!r}")
    names = {item.get("obligation"): item for item in report.get("obligations", []) if isinstance(item, Mapping)}
    expected = {
        "framing_injectivity_unconditional",
        "uvarint_injectivity",
        "bounded_no_collision_incl_FEE",
    }
    if set(names) != expected or any(item.get("ok") is not True for item in names.values()):
        raise EvidenceError(f"state-root injectivity obligations malformed: {report!r}")
    return report


def _kani_command() -> list[str]:
    command = [
        "cargo",
        "kani",
        "-p",
        "zenodex-runtime-core",
        "--lib",
    ]
    for harness in KANI_HARNESSES:
        command.extend(["--harness", harness])
    command.extend(["--exact", "--output-format", "terse", "--harness-timeout", "10m", "-Z", "unstable-options"])
    return command


def _parse_kani_output(stdout: str) -> list[dict[str, Any]]:
    harnesses: dict[str, dict[str, Any]] = {}
    for raw in stdout.split("Checking harness ")[1:]:
        name = raw.split("...", 1)[0].strip()
        checks = re.search(r"\*\* (\d+) of (\d+) failed", raw)
        status = re.search(r"VERIFICATION:-\s+(\w+)", raw)
        cover = re.search(r"\*\* (\d+) of (\d+) cover properties satisfied", raw)
        if checks is None or status is None:
            raise EvidenceError(f"could not parse Kani result for {name!r}")
        harnesses[name] = {
            "name": name,
            "verdict": "VERIFIED" if status.group(1) == "SUCCESSFUL" else status.group(1),
            "checks_failed": int(checks.group(1)),
            "checks_total": int(checks.group(2)),
            "cover_properties_satisfied": int(cover.group(1)) if cover else 0,
            "cover_properties_total": int(cover.group(2)) if cover else 0,
        }
    if set(harnesses) != set(KANI_HARNESSES):
        raise EvidenceError(
            f"Kani harness mismatch: parsed={sorted(harnesses)} expected={sorted(KANI_HARNESSES)}"
        )
    return [harnesses[name] for name in KANI_HARNESSES]


def _validate_kani_result(result: Any) -> list[str]:
    errors: list[str] = []
    if not isinstance(result, Mapping):
        return ["proof_artifact.kani must be an object"]
    if result.get("verdict") != "VERIFIED":
        errors.append("Kani proof verdict must be VERIFIED")
    if result.get("cargo_kani_version") != "cargo-kani 0.60.0":
        errors.append("Kani proof must use source-pinned cargo-kani 0.60.0")
    if result.get("command") != _kani_command():
        errors.append("Kani proof command drifted")
    harnesses = result.get("harnesses")
    if not isinstance(harnesses, list) or [h.get("name") for h in harnesses if isinstance(h, Mapping)] != KANI_HARNESSES:
        return errors + ["Kani proof harness list/order drifted"]
    for item in harnesses:
        if not isinstance(item, Mapping):
            errors.append("Kani harness row must be an object")
            continue
        name = item.get("name")
        exp = KANI_EXPECTED_TOTALS.get(str(name))
        if exp is None:
            errors.append(f"unexpected Kani harness {name!r}")
            continue
        if item.get("verdict") != "VERIFIED" or item.get("checks_failed") != 0:
            errors.append(f"{name}: Kani harness did not verify cleanly")
        if item.get("checks_total") != exp["checks_total"]:
            errors.append(f"{name}: checks_total drifted")
        if item.get("cover_properties_total") != exp["cover_properties_total"]:
            errors.append(f"{name}: cover total drifted")
        if exp["cover_properties_total"] and item.get("cover_properties_satisfied") != exp["cover_properties_total"]:
            errors.append(f"{name}: cover properties not all satisfied")
    return errors


def _run_kani() -> dict[str, Any]:
    version_proc = subprocess.run(
        ["cargo", "kani", "--version"],
        cwd=str(ROOT / "rust-runtime"),
        capture_output=True,
        text=True,
        timeout=30,
    )
    if version_proc.returncode != 0:
        raise EvidenceError(f"cargo kani --version failed: {version_proc.stderr[-400:]}")
    command = _kani_command()
    proc = subprocess.run(
        command,
        cwd=str(ROOT / "rust-runtime"),
        capture_output=True,
        text=True,
        timeout=1800,
    )
    if proc.returncode != 0:
        raise EvidenceError(
            f"cargo kani failed with returncode={proc.returncode}: "
            f"stdout={proc.stdout[-1200:]} stderr={proc.stderr[-1200:]}"
        )
    result = {
        "verdict": "VERIFIED",
        "cargo_kani_version": version_proc.stdout.strip(),
        "command": command,
        "harnesses": _parse_kani_output(proc.stdout),
    }
    errors = _validate_kani_result(result)
    if errors:
        raise EvidenceError("; ".join(errors))
    return result


def _runtime_shadow_paths_are_gated() -> list[str]:
    workflow = (ROOT / ".github" / "workflows" / "runtime-shadow.yml").read_text(encoding="utf-8")
    required_snippets = [
        "src/state/state_root.py",
        "rust-runtime/**",
        "tools/runtime/**",
        "tests/runtime/**",
        "tests/runtime/test_state_root_vectors.py",
    ]
    return [snippet for snippet in required_snippets if snippet not in workflow]


def _profile_result() -> dict[str, Any]:
    try:
        import yaml  # type: ignore[import-untyped]
    except Exception as exc:  # pragma: no cover - dependency is in dev requirements
        raise EvidenceError(f"PyYAML unavailable for deployment profile check: {exc}") from exc

    prod = yaml.safe_load((ROOT / "config" / "deploy" / "production-strict.yaml").read_text(encoding="utf-8"))
    testnet = yaml.safe_load((ROOT / "config" / "deploy" / "public-testnet.yaml").read_text(encoding="utf-8"))
    prod_policy = prod["runtime_authority_policy"]
    testnet_policy = testnet["runtime_authority_policy"]
    if prod_policy["default"] != "python_authority" or prod_policy["per_surface"] != {}:
        raise EvidenceError("production-strict authority policy for state_root is not all-Python")
    if testnet_policy["per_surface"].get("state_root") != "rust_authority_with_python_shadow":
        raise EvidenceError("public-testnet state_root must run Rust authority with Python shadow")
    if "state_root" not in set(testnet_policy.get("promoted_surfaces") or []):
        raise EvidenceError("public-testnet state_root must be in promoted_surfaces")
    return {
        "verdict": "CHECKED",
        "production_strict": "python_authority",
        "public_testnet": "rust_authority_with_python_shadow",
    }


def build_receipt(*, spec_path: Path = DEFAULT_SPEC) -> dict[str, Any]:
    spec = _load_json_object(spec_path, name="state-root formal spec")
    spec_errors = _validate_spec_against_source(spec)
    if spec_errors:
        raise EvidenceError("; ".join(spec_errors))
    missing_workflow = _runtime_shadow_paths_are_gated()
    if missing_workflow:
        raise EvidenceError(f"runtime-shadow workflow missing state-root gates: {missing_workflow}")
    receipt = {
        "schema": RECEIPT_SCHEMA,
        "surface_id": "state_root",
        "state_root_version": EXPECTED_VERSION,
        "evidence_columns": {
            "running_impl": {
                "verdict": "CHECKED",
                "refs": ["src/state/state_root.py", "src/integration/zeno_ledger_v0.py::dex_state_root_v0"],
            },
            "formal_spec": {
                "verdict": "CROSS_CHECKED",
                "ref": "src/kernels/dex/state_root_v5_scope_contract.json",
                "spec_sha256": _sha256_file(spec_path),
            },
            "proof_artifact": {
                "verdict": "VERIFIED",
                "preimage_injectivity": _run_injectivity_proof(),
                "kani": _run_kani(),
            },
            "differential_tests": {
                "verdict": "PR_GATED",
                "command_ids": ["state_root_python_rust_differential"],
            },
            "runtime_invariants": {
                "verdict": "ENFORCED_AND_TESTED",
                "command_ids": ["state_root_runtime_binding"],
            },
            "authority_mode": _profile_result(),
        },
        "required_test_commands": REQUIRED_TEST_COMMANDS,
        "source_files": _source_hashes(),
        "private_toolchain_source_included": False,
    }
    receipt["receipt_sha256"] = _sha256_bytes(_canonical_json_bytes(_receipt_hash_body(receipt)))
    return receipt


def verify_receipt(receipt: Mapping[str, Any], *, spec_path: Path = DEFAULT_SPEC) -> list[str]:
    errors: list[str] = []
    if receipt.get("schema") != RECEIPT_SCHEMA:
        errors.append(f"receipt.schema must be {RECEIPT_SCHEMA!r}")
    if receipt.get("surface_id") != "state_root":
        errors.append("receipt.surface_id must be 'state_root'")
    expected_hash = _sha256_bytes(_canonical_json_bytes(_receipt_hash_body(receipt)))
    if receipt.get("receipt_sha256") != expected_hash:
        errors.append("receipt_sha256 mismatch")

    spec = _load_json_object(spec_path, name="state-root formal spec")
    errors.extend(_validate_spec_against_source(spec))

    source_rows = receipt.get("source_files")
    if not isinstance(source_rows, list):
        errors.append("receipt.source_files must be a list")
    else:
        paths = [row.get("path") for row in source_rows if isinstance(row, Mapping)]
        if paths != EXPECTED_SOURCE_FILES:
            errors.append("receipt.source_files path list/order drifted")
        current = {row["path"]: row["sha256"] for row in _source_hashes()}
        for row in source_rows:
            if not isinstance(row, Mapping):
                errors.append("receipt.source_files entries must be objects")
                continue
            path = row.get("path")
            if not isinstance(path, str):
                errors.append("receipt source path must be a string")
                continue
            if row.get("sha256") != current.get(path):
                errors.append(f"source hash drift: {path}")

    columns = receipt.get("evidence_columns")
    if not isinstance(columns, Mapping):
        errors.append("receipt.evidence_columns must be an object")
        return errors
    expected_columns = {
        "running_impl",
        "formal_spec",
        "proof_artifact",
        "differential_tests",
        "runtime_invariants",
        "authority_mode",
    }
    if set(columns) != expected_columns:
        errors.append("receipt.evidence_columns must cover exactly the six evidence columns")
        return errors
    if columns["running_impl"].get("verdict") != "CHECKED":
        errors.append("running_impl verdict must be CHECKED")
    formal = columns["formal_spec"]
    if formal.get("verdict") != "CROSS_CHECKED" or formal.get("spec_sha256") != _sha256_file(spec_path):
        errors.append("formal_spec receipt does not match live spec")
    proof = columns["proof_artifact"]
    if proof.get("verdict") != "VERIFIED":
        errors.append("proof_artifact verdict must be VERIFIED")
    try:
        live_injectivity = _run_injectivity_proof()
        if proof.get("preimage_injectivity") != live_injectivity:
            errors.append("preimage injectivity proof result drifted")
    except EvidenceError as exc:
        errors.append(str(exc))
    errors.extend(_validate_kani_result(proof.get("kani")))
    if columns["differential_tests"].get("verdict") != "PR_GATED":
        errors.append("differential_tests verdict must be PR_GATED")
    if columns["runtime_invariants"].get("verdict") != "ENFORCED_AND_TESTED":
        errors.append("runtime_invariants verdict must be ENFORCED_AND_TESTED")
    try:
        if columns["authority_mode"] != _profile_result():
            errors.append("authority_mode profile result drifted")
    except EvidenceError as exc:
        errors.append(str(exc))
    if receipt.get("required_test_commands") != REQUIRED_TEST_COMMANDS:
        errors.append("required_test_commands drifted")
    if receipt.get("private_toolchain_source_included") is not False:
        errors.append("receipt must not include private toolchain source")
    missing_workflow = _runtime_shadow_paths_are_gated()
    if missing_workflow:
        errors.append(f"runtime-shadow workflow missing state-root gates: {missing_workflow}")
    return errors


def check_receipt_file(
    *,
    receipt_path: Path = DEFAULT_RECEIPT,
    spec_path: Path = DEFAULT_SPEC,
) -> dict[str, Any]:
    errors: list[str] = []
    try:
        receipt = _load_json_object(receipt_path, name="state-root surface evidence receipt")
        errors.extend(verify_receipt(receipt, spec_path=spec_path))
    except EvidenceError as exc:
        errors.append(str(exc))
    return {
        "schema": CHECK_SCHEMA,
        "ok": not errors,
        "receipt": str(receipt_path),
        "spec": str(spec_path),
        "errors": errors,
    }


def _cmd_build(args: argparse.Namespace) -> int:
    receipt = build_receipt(spec_path=Path(args.spec))
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    if args.pretty:
        print(json.dumps({"ok": True, "receipt": str(out)}, indent=2, sort_keys=True))
    else:
        print(json.dumps({"ok": True, "receipt": str(out)}, sort_keys=True))
    return 0


def _cmd_check(args: argparse.Namespace) -> int:
    report = check_receipt_file(receipt_path=Path(args.receipt), spec_path=Path(args.spec))
    print(json.dumps(report, indent=2 if args.pretty else None, sort_keys=True))
    return 0 if report["ok"] else 1


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="State-root surface evidence receipt gate")
    sub = parser.add_subparsers(dest="cmd", required=True)
    p_build = sub.add_parser("build")
    p_build.add_argument("--spec", default=str(DEFAULT_SPEC))
    p_build.add_argument("--out", default=str(DEFAULT_RECEIPT))
    p_build.add_argument("--pretty", action="store_true")
    p_build.set_defaults(func=_cmd_build)
    p_check = sub.add_parser("check")
    p_check.add_argument("--spec", default=str(DEFAULT_SPEC))
    p_check.add_argument("--receipt", default=str(DEFAULT_RECEIPT))
    p_check.add_argument("--pretty", action="store_true")
    p_check.set_defaults(func=_cmd_check)
    args = parser.parse_args(argv)
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
