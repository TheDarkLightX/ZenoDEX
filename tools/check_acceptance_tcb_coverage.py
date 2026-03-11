#!/usr/bin/env python3
"""
Check branch coverage floors for the spot DEX acceptance TCB.

This is intentionally narrower than the repo-wide quality gate. It enforces
explicit coverage floors on the code that decides whether untrusted inputs are
accepted into the money-moving core.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

OVERALL_BRANCH_THRESHOLD = 79.0

BRANCH_THRESHOLDS = {
    "src/core/intent_normal_form.py": 78.0,
    "src/core/quote_receipts.py": 95.0,
    "src/core/settlement_strong_validator.py": 78.0,
    "src/integration/dex_engine.py": 73.0,
    "src/integration/operations.py": 76.0,
    "src/integration/proof_verifier.py": 82.0,
    "src/integration/validation.py": 76.0,
    "src/state/canonical.py": 82.0,
    "src/state/nonces.py": 80.0,
    "src/state/state_root.py": 77.0,
    "src/state/support_root.py": 80.0,
}


def _branch_pct(summary: dict[str, object]) -> float:
    branches = int(summary.get("num_branches", 0) or 0)
    covered = int(summary.get("covered_branches", 0) or 0)
    if branches <= 0:
        return 100.0
    return (100.0 * covered) / float(branches)


def main(argv: list[str]) -> int:
    if len(argv) != 2:
        print("usage: check_acceptance_tcb_coverage.py <coverage-json>", file=sys.stderr)
        return 2

    report_path = Path(argv[1])
    if not report_path.is_file():
        print(f"error: coverage report not found: {report_path}", file=sys.stderr)
        return 2

    data = json.loads(report_path.read_text(encoding="utf-8"))
    files = data.get("files")
    if not isinstance(files, dict):
        print("error: coverage report missing files section", file=sys.stderr)
        return 2

    missing = [path for path in BRANCH_THRESHOLDS if path not in files]
    if missing:
        print("error: acceptance coverage report missing expected modules:", file=sys.stderr)
        for path in missing:
            print(f"  - {path}", file=sys.stderr)
        return 1

    total_branches = 0
    total_covered = 0
    failures: list[str] = []

    print("== acceptance-tcb: branch coverage floors ==")
    for path, threshold in BRANCH_THRESHOLDS.items():
        info = files[path]
        if not isinstance(info, dict):
            failures.append(f"{path}: malformed coverage entry")
            continue
        summary = info.get("summary")
        if not isinstance(summary, dict):
            failures.append(f"{path}: missing summary")
            continue
        branches = int(summary.get("num_branches", 0) or 0)
        covered = int(summary.get("covered_branches", 0) or 0)
        pct = _branch_pct(summary)
        total_branches += branches
        total_covered += covered
        status = "ok" if pct >= threshold else "fail"
        print(f"{status:>4}  {pct:5.1f}%  floor {threshold:4.1f}%  {path}")
        if pct < threshold:
            failures.append(f"{path}: branch coverage {pct:.1f}% < floor {threshold:.1f}%")

    overall_pct = 100.0 if total_branches <= 0 else (100.0 * total_covered) / float(total_branches)
    print(f"total {overall_pct:5.1f}%  floor {OVERALL_BRANCH_THRESHOLD:4.1f}%  acceptance TCB overall")
    if overall_pct < OVERALL_BRANCH_THRESHOLD:
        failures.append(
            f"acceptance TCB overall branch coverage {overall_pct:.1f}% < floor {OVERALL_BRANCH_THRESHOLD:.1f}%"
        )

    if failures:
        print("error: acceptance-tcb coverage gate failed", file=sys.stderr)
        for failure in failures:
            print(f"  - {failure}", file=sys.stderr)
        return 1

    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
