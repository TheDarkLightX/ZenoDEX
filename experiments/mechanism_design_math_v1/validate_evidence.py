#!/usr/bin/env python3
"""
Schema validator for mechanism_design_math_v1 evidence files.

Adapted from experiments/research_program_v2/validate_evidence.py with one
program-specific rule change: formal-verification hypotheses use the
three-segment prefix H-MD-FV- (not H-FV-) and must carry an existing
proof_file.

Validates all results.json files against the canonical schema:
{
  "wave": <int>,
  "domain": "<string>",
  "timestamp": "<ISO 8601>",
  "hypotheses": [
    {
      "id": "<H-MD-XX-NNN>",
      "description": "<string>",
      "verdict": "SUPPORTED|FALSIFIED|PARTIALLY_FALSIFIED|INCONCLUSIVE|NOT_APPLICABLE",
      "tests_passed": <int>,
      "tests_failed": <int>,
      "confidence": <float 0-1>,
      "key_finding": "<string>",
      "reproduction": "<pytest command>",
      "proof_file": "<path>"        # required iff id starts with H-MD-FV-
      "obligation": "<O-XX-NN>"     # optional charter back-pointer
    }
  ],
  "total_tests": <int>,
  "total_passed": <int>,
  "total_failed": <int>
}

Exit 0 if all files valid, 1 otherwise (warnings also exit 1).
"""

import json
import os
import re
import sys
from pathlib import Path

VALID_VERDICTS = {
    "SUPPORTED",
    "FALSIFIED",
    "PARTIALLY_FALSIFIED",
    "INCONCLUSIVE",
    "NOT_APPLICABLE",
}

ISO_8601_PATTERN = re.compile(
    r"^\d{4}-\d{2}-\d{2}(T\d{2}:\d{2}:\d{2}(Z|[+-]\d{2}:\d{2})?)?$"
)

HYPOTHESIS_ID_PATTERN = re.compile(r"^H-[A-Z]{2}(-[A-Z]+)*-\d{2,3}.*$")

# Program-specific: formal-verification lane prefix requiring proof_file.
FV_PREFIX = "H-MD-FV-"


def find_evidence_files(base_dir: str) -> list[str]:
    """Find all results.json files in wave directories."""
    base = Path(base_dir)
    files = []
    for pattern in [
        "wave*_*/evidence/results.json",
        "wave*_formal/results.json",
    ]:
        files.extend(str(p) for p in base.glob(pattern))
    return sorted(set(files))


def validate_hypothesis(hyp: dict, file_path: str, idx: int) -> list[str]:
    """Validate a single hypothesis entry. Returns list of errors."""
    errors = []
    prefix = f"  hypotheses[{idx}]"
    hid = None

    # id
    if "id" not in hyp:
        errors.append(f"{prefix}: missing 'id'")
    elif not isinstance(hyp["id"], str):
        errors.append(f"{prefix}: 'id' must be string, got {type(hyp['id']).__name__}")
    elif not HYPOTHESIS_ID_PATTERN.match(hyp["id"]):
        errors.append(
            f"{prefix}: 'id' must match H-XX-NNN pattern, got '{hyp['id']}'"
        )
    else:
        hid = hyp["id"]

    # proof_file is required for formal-verification hypotheses
    if isinstance(hid, str) and hid.startswith(FV_PREFIX):
        if "proof_file" not in hyp:
            errors.append(f"{prefix}: {FV_PREFIX} hypothesis missing 'proof_file'")
        elif not isinstance(hyp["proof_file"], str):
            errors.append(
                f"{prefix}: 'proof_file' must be string, got {type(hyp['proof_file']).__name__}"
            )
        elif not hyp["proof_file"].strip():
            errors.append(
                f"{prefix}: 'proof_file' must be non-empty for {FV_PREFIX} hypotheses"
            )
        elif not os.path.exists(hyp["proof_file"]):
            errors.append(
                f"{prefix}: proof_file does not exist: '{hyp['proof_file']}'"
            )

    # description
    if "description" not in hyp:
        errors.append(f"{prefix}: missing 'description'")
    elif not isinstance(hyp["description"], str):
        errors.append(
            f"{prefix}: 'description' must be string, got {type(hyp['description']).__name__}"
        )

    # verdict
    if "verdict" not in hyp:
        errors.append(f"{prefix}: missing 'verdict'")
    elif hyp["verdict"] not in VALID_VERDICTS:
        errors.append(
            f"{prefix}: invalid verdict '{hyp['verdict']}', must be one of {VALID_VERDICTS}"
        )

    # tests_passed
    if "tests_passed" not in hyp:
        errors.append(f"{prefix}: missing 'tests_passed'")
    elif not isinstance(hyp["tests_passed"], int):
        errors.append(
            f"{prefix}: 'tests_passed' must be int, got {type(hyp['tests_passed']).__name__}"
        )
    elif hyp["tests_passed"] < 0:
        errors.append(f"{prefix}: 'tests_passed' must be >= 0")

    # tests_failed
    if "tests_failed" not in hyp:
        errors.append(f"{prefix}: missing 'tests_failed'")
    elif not isinstance(hyp["tests_failed"], int):
        errors.append(
            f"{prefix}: 'tests_failed' must be int, got {type(hyp['tests_failed']).__name__}"
        )
    elif hyp["tests_failed"] < 0:
        errors.append(f"{prefix}: 'tests_failed' must be >= 0")

    # confidence
    if "confidence" not in hyp:
        errors.append(f"{prefix}: missing 'confidence'")
    elif not isinstance(hyp["confidence"], (int, float)):
        errors.append(
            f"{prefix}: 'confidence' must be float, got {type(hyp['confidence']).__name__}"
        )
    elif not (0.0 <= hyp["confidence"] <= 1.0):
        errors.append(
            f"{prefix}: 'confidence' must be in [0, 1], got {hyp['confidence']}"
        )

    # key_finding
    if "key_finding" not in hyp:
        errors.append(f"{prefix}: missing 'key_finding'")
    elif not isinstance(hyp["key_finding"], str):
        errors.append(
            f"{prefix}: 'key_finding' must be string, got {type(hyp['key_finding']).__name__}"
        )

    # reproduction
    if "reproduction" not in hyp:
        errors.append(f"{prefix}: missing 'reproduction'")
    elif not isinstance(hyp["reproduction"], str):
        errors.append(
            f"{prefix}: 'reproduction' must be string, got {type(hyp['reproduction']).__name__}"
        )

    # obligation (optional charter back-pointer)
    if "obligation" in hyp:
        if not isinstance(hyp["obligation"], str) or not re.match(
            r"^O-[A-Z]{2}-\d{2}$", hyp["obligation"]
        ):
            errors.append(
                f"{prefix}: 'obligation' must match O-XX-NN, got '{hyp['obligation']}'"
            )

    return errors


def validate_file(file_path: str) -> tuple[list[str], list[str]]:
    """Validate a single results.json file. Returns (errors, warnings)."""
    errors = []
    warnings = []
    rel = os.path.relpath(file_path)

    try:
        with open(file_path, "r") as f:
            data = json.load(f)
    except json.JSONDecodeError as e:
        return [f"{rel}: invalid JSON: {e}"], []
    except FileNotFoundError:
        return [f"{rel}: file not found"], []

    if not isinstance(data, dict):
        return [f"{rel}: root must be a JSON object"], []

    # wave
    if "wave" not in data:
        errors.append(f"{rel}: missing 'wave'")
    elif not isinstance(data["wave"], int):
        errors.append(
            f"{rel}: 'wave' must be int, got {type(data['wave']).__name__}: {data['wave']}"
        )

    # domain
    if "domain" not in data:
        errors.append(f"{rel}: missing 'domain'")
    elif not isinstance(data["domain"], str):
        errors.append(
            f"{rel}: 'domain' must be string, got {type(data['domain']).__name__}"
        )

    # timestamp
    if "timestamp" not in data:
        errors.append(f"{rel}: missing 'timestamp'")
    elif not isinstance(data["timestamp"], str):
        errors.append(
            f"{rel}: 'timestamp' must be string, got {type(data['timestamp']).__name__}"
        )
    elif not ISO_8601_PATTERN.match(data["timestamp"]):
        errors.append(
            f"{rel}: 'timestamp' must be ISO 8601, got '{data['timestamp']}'"
        )

    # hypotheses
    if "hypotheses" not in data:
        errors.append(f"{rel}: missing 'hypotheses'")
    elif not isinstance(data["hypotheses"], list):
        errors.append(
            f"{rel}: 'hypotheses' must be array, got {type(data['hypotheses']).__name__}"
        )
    else:
        if len(data["hypotheses"]) == 0:
            errors.append(f"{rel}: 'hypotheses' array is empty")
        for i, hyp in enumerate(data["hypotheses"]):
            if not isinstance(hyp, dict):
                errors.append(f"{rel}: hypotheses[{i}] must be object")
            else:
                errors.extend(validate_hypothesis(hyp, file_path, i))

    # total_tests
    if "total_tests" not in data:
        errors.append(f"{rel}: missing 'total_tests'")
    elif not isinstance(data["total_tests"], int):
        errors.append(
            f"{rel}: 'total_tests' must be int, got {type(data['total_tests']).__name__}"
        )

    # total_passed
    if "total_passed" not in data:
        errors.append(f"{rel}: missing 'total_passed'")
    elif not isinstance(data["total_passed"], int):
        errors.append(
            f"{rel}: 'total_passed' must be int, got {type(data['total_passed']).__name__}"
        )

    # total_failed
    if "total_failed" not in data:
        errors.append(f"{rel}: missing 'total_failed'")
    elif not isinstance(data["total_failed"], int):
        errors.append(
            f"{rel}: 'total_failed' must be int, got {type(data['total_failed']).__name__}"
        )

    # Cross-check: total_tests == total_passed + total_failed
    if (
        isinstance(data.get("total_tests"), int)
        and isinstance(data.get("total_passed"), int)
        and isinstance(data.get("total_failed"), int)
    ):
        if data["total_tests"] != data["total_passed"] + data["total_failed"]:
            errors.append(
                f"{rel}: total_tests ({data['total_tests']}) != "
                f"total_passed ({data['total_passed']}) + total_failed ({data['total_failed']})"
            )

    # Cross-check: per-hypothesis sums should not exceed totals
    if (
        isinstance(data.get("total_tests"), int)
        and isinstance(data.get("hypotheses"), list)
    ):
        hyps = data["hypotheses"]
        hyp_sum = sum(
            h.get("tests_passed", 0) + h.get("tests_failed", 0)
            for h in hyps
            if isinstance(h, dict)
        )
        if hyp_sum > data["total_tests"]:
            warnings.append(
                f"{rel}: per-hypothesis test sum ({hyp_sum}) exceeds "
                f"total_tests ({data['total_tests']})"
            )

    # Error: non-NA hypotheses with zero tests
    if isinstance(data.get("hypotheses"), list):
        zero_test_ids = []
        for h in data["hypotheses"]:
            if not isinstance(h, dict):
                continue
            v = h.get("verdict", "")
            if v == "NOT_APPLICABLE":
                continue
            tp = h.get("tests_passed", 0)
            tf = h.get("tests_failed", 0)
            if tp == 0 and tf == 0:
                zero_test_ids.append(h.get("id", "?"))
        if zero_test_ids:
            errors.append(
                f"{rel}: {len(zero_test_ids)} non-NA hypotheses have zero tests: "
                + ", ".join(zero_test_ids[:10])
                + ("..." if len(zero_test_ids) > 10 else "")
            )

    # Error: SUPPORTED hypotheses with tests_failed > 0
    if isinstance(data.get("hypotheses"), list):
        bad_supported = []
        for h in data["hypotheses"]:
            if not isinstance(h, dict):
                continue
            if h.get("verdict") == "SUPPORTED" and h.get("tests_failed", 0) > 0:
                bad_supported.append(h.get("id", "?"))
        if bad_supported:
            errors.append(
                f"{rel}: {len(bad_supported)} SUPPORTED hypotheses have tests_failed > 0: "
                + ", ".join(bad_supported[:10])
                + ("..." if len(bad_supported) > 10 else "")
            )

    return errors, warnings


def check_global_id_uniqueness(files: list[str]) -> tuple[list[str], list[str]]:
    """Check hypothesis ID uniqueness. In-file dups are errors, cross-wave are warnings."""
    errors = []
    warnings = []
    global_ids: dict[str, list[str]] = {}
    for file_path in files:
        try:
            with open(file_path) as f:
                data = json.load(f)
        except Exception:
            continue
        rel = os.path.relpath(file_path)
        file_ids: dict[str, int] = {}
        for h in data.get("hypotheses", []):
            hid = h.get("id", "")
            file_ids[hid] = file_ids.get(hid, 0) + 1
            if hid in global_ids:
                global_ids[hid].append(rel)
            else:
                global_ids[hid] = [rel]
        for hid, count in file_ids.items():
            if count > 1:
                errors.append(
                    f"In-file duplicate ID '{hid}' ({count}x) in {rel}"
                )
    # Cross-file duplicates are informational warnings (legitimate re-tests
    # must use the -wN suffix convention instead).
    for hid, sources in sorted(global_ids.items()):
        unique_files = list(dict.fromkeys(sources))
        if len(unique_files) > 1:
            warnings.append(
                f"Cross-wave duplicate ID '{hid}' in: {', '.join(unique_files)}"
            )
    return errors, warnings


def main():
    base_dir = os.path.join(
        os.path.dirname(os.path.abspath(__file__))
    )
    files = find_evidence_files(base_dir)

    if not files:
        print("ERROR: No evidence files found", file=sys.stderr)
        sys.exit(1)

    total_errors = 0
    total_warnings = 0
    total_files = 0

    for file_path in files:
        total_files += 1
        errors, file_warnings = validate_file(file_path)
        rel = os.path.relpath(file_path)
        if errors:
            print(f"FAIL: {rel}", file=sys.stderr)
            for e in errors:
                print(f"  {e}", file=sys.stderr)
            total_errors += len(errors)
        else:
            print(f"  OK: {rel}")
        if file_warnings:
            for w in file_warnings:
                print(f"  WARN: {w}")
            total_warnings += len(file_warnings)

    global_errors, global_warnings = check_global_id_uniqueness(files)
    if global_errors or global_warnings:
        print("\nGLOBAL CHECKS:")
        for e in global_errors:
            print(f"  ERROR: {e}", file=sys.stderr)
        for w in global_warnings:
            print(f"  INFO: {w}")
        total_errors += len(global_errors)
        total_warnings += len(global_warnings)

    print(f"\nValidated {total_files} files, {total_errors} errors, {total_warnings} warnings")
    if total_errors > 0:
        print("VALIDATION FAILED", file=sys.stderr)
        sys.exit(1)
    elif total_warnings > 0:
        print("VALIDATION PASSED WITH WARNINGS", file=sys.stderr)
        sys.exit(1)
    else:
        print("ALL VALID")
        sys.exit(0)


if __name__ == "__main__":
    main()
