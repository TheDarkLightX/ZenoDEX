#!/usr/bin/env python3
from __future__ import annotations

import json
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "src/core/split_routing.py"
TEST_CMD = [
    sys.executable,
    "-m",
    "pytest",
    "-q",
    "tests/core/test_split_routing.py",
    "tests/tools/test_zenodex_metamuse_workflow.py",
]


@dataclass(frozen=True)
class TextMutant:
    mutant_id: str
    description: str
    needle: str
    replacement: str


MUTANTS: tuple[TextMutant, ...] = (
    TextMutant(
        mutant_id="flip_output_tie_break",
        description="Prefer larger split a on equal output instead of smaller a.",
        needle="    return bool(cand[0] > best[0] or (cand[0] == best[0] and cand[1] < best[1]))\n",
        replacement="    return bool(cand[0] > best[0] or (cand[0] == best[0] and cand[1] > best[1]))\n",
    ),
    TextMutant(
        mutant_id="disable_left_canonicalization",
        description="Stop canonical leftward walk immediately.",
        needle="    while best_a > int(lo_both):\n",
        replacement="    while False and best_a > int(lo_both):\n",
    ),
    TextMutant(
        mutant_id="adaptive_v7_uses_baseline",
        description="Route adaptive_v7 easy manifold back to baseline_canon16.",
        needle="        if prof == \"adaptive_v7\":\n            return 64, \"dgstr_v1\"\n",
        replacement="        if prof == \"adaptive_v7\":\n            return 64, \"baseline_canon16\"\n",
    ),
    TextMutant(
        mutant_id="dgstr_reverse_probe_order",
        description="Reverse dgstr probe preference so weaker side can win interval shrink decisions.",
        needle="        if v2 is None or (v1 is not None and int(v1) > int(v2)):\n            cur_hi = int(m2)\n        elif v1 is None or int(v2) > int(v1):\n            cur_lo = int(m1)\n",
        replacement="        if v2 is None or (v1 is not None and int(v1) > int(v2)):\n            cur_lo = int(m1)\n        elif v1 is None or int(v2) > int(v1):\n            cur_hi = int(m2)\n",
    ),
    TextMutant(
        mutant_id="limit_dgstr_rescue_to_top1",
        description="Only scan the single strongest rescue center instead of the top six.",
        needle="    rescue_centers = [int(a) for _v, a in ranked[:6]]\n",
        replacement="    rescue_centers = [int(a) for _v, a in ranked[:1]]\n",
    ),
)


def _write_json(path: Path, obj: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _run_tests() -> tuple[int, str, str, float]:
    t0 = time.time()
    proc = subprocess.run(TEST_CMD, cwd=str(ROOT), text=True, capture_output=True)
    return int(proc.returncode), str(proc.stdout), str(proc.stderr), float(time.time() - t0)


def main() -> int:
    original = TARGET.read_text(encoding="utf-8")
    rows: list[dict[str, Any]] = []
    try:
        for mutant in MUTANTS:
            if mutant.needle not in original:
                rows.append(
                    {
                        "mutant_id": mutant.mutant_id,
                        "description": mutant.description,
                        "status": "inconclusive",
                        "reason": "needle_not_found",
                    }
                )
                continue
            mutated = original.replace(mutant.needle, mutant.replacement, 1)
            TARGET.write_text(mutated, encoding="utf-8")
            rc, stdout, stderr, duration_s = _run_tests()
            rows.append(
                {
                    "mutant_id": mutant.mutant_id,
                    "description": mutant.description,
                    "status": "killed" if rc != 0 else "survived",
                    "duration_s": duration_s,
                    "rc": rc,
                    "stdout_tail": stdout[-2000:],
                    "stderr_tail": stderr[-2000:],
                }
            )
            TARGET.write_text(original, encoding="utf-8")
    finally:
        TARGET.write_text(original, encoding="utf-8")

    killed = sum(1 for row in rows if row.get("status") == "killed")
    survived = sum(1 for row in rows if row.get("status") == "survived")
    inconclusive = sum(1 for row in rows if row.get("status") == "inconclusive")
    out = {
        "schema": "zenodex/split-routing-mutation-harness/v1",
        "target": str(TARGET.relative_to(ROOT)),
        "test_command": TEST_CMD,
        "totals": {
            "killed": killed,
            "survived": survived,
            "inconclusive": inconclusive,
            "mutation_score": 0.0 if killed + survived == 0 else float(killed) / float(killed + survived),
        },
        "rows": rows,
    }
    out_path = ROOT / "generated" / "split_routing_mutation_harness.json"
    _write_json(out_path, out)
    print(json.dumps({"ok": True, "out": str(out_path), "totals": out["totals"]}, sort_keys=True))
    return 0 if survived == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
