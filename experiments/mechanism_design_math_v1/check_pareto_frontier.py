#!/usr/bin/env python3
"""Validate pareto_frontier.json against actual evidence files.

Recomputes key metrics from evidence JSONs and checks them against the
static pareto_frontier.json artifact (a Wave-5 deliverable). Exits 0 if
consistent, 1 if drifted.

Before Wave 5 the artifact does not exist: the default mode prints a SKIP
note and exits 0 so intermediate gate runs stay green. Pass --require to
make a missing artifact a hard failure (Wave-5 / final-review mode).
"""

import json
import sys
from collections import Counter
from pathlib import Path


def main():
    require = "--require" in sys.argv[1:]
    base = Path(__file__).parent
    pareto_path = base / "pareto_frontier.json"

    if not pareto_path.exists():
        if require:
            print("ERROR: pareto_frontier.json not found", file=sys.stderr)
            sys.exit(1)
        print("SKIP: pareto_frontier.json not yet written (Wave-5 artifact); "
              "use --require to enforce")
        sys.exit(0)

    pareto = json.loads(pareto_path.read_text())

    ev_files = sorted(
        set(list(base.glob("wave*_*/evidence/results.json"))
            + list(base.glob("wave*_formal/results.json")))
    )

    all_ids = []
    verdicts = Counter()
    total_obs = 0
    total_failures = 0

    for fp in ev_files:
        data = json.loads(fp.read_text())
        for h in data.get("hypotheses", []):
            all_ids.append(h["id"])
            verdicts[h["verdict"]] += 1
        total_obs += data.get("total_tests", 0)
        total_failures += data.get("total_failed", 0)

    # Program-local Lean files (experimental + any promoted files the
    # frontier explicitly lists are counted there, not re-globbed).
    lean_exp = list((base / "math_notes" / "lean_experimental").glob("*.lean"))

    errors = []

    def check(name, expected, actual):
        if expected != actual:
            errors.append(f"  DRIFT: {name}: pareto={expected}, actual={actual}")

    check("total_hypothesis_entries", pareto["total_hypothesis_entries"], len(all_ids))
    check("evidence_test_observations", pareto["evidence_test_observations"], total_obs)
    check("evidence_test_failures", pareto["evidence_test_failures"], total_failures)
    check("lean_experimental_files", pareto["lean_experimental_files"], len(lean_exp))
    check("total_wave_directories", pareto["total_wave_directories"], len(ev_files))

    vb = pareto.get("verdict_breakdown", {})
    for v in ["supported", "falsified", "partially_falsified", "inconclusive",
              "not_applicable"]:
        check(f"verdict_{v}", vb.get(v, 0), verdicts.get(v.upper(), 0))

    if errors:
        print("pareto_frontier.json DRIFTED:")
        for e in errors:
            print(e)
        sys.exit(1)

    print(f"pareto_frontier.json consistent: {len(all_ids)} hypothesis entries, "
          f"{total_obs} test observations, {len(ev_files)} wave files")
    sys.exit(0)


if __name__ == "__main__":
    main()
