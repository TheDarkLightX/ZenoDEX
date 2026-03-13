from __future__ import annotations

from pathlib import Path

from src.integration.tau_spec_assurance import ROOT, run_assurance_registry


REGISTRY = ROOT / "tests" / "tau" / "spec_assurance_registry.json"


def test_tau_spec_assurance_registry() -> None:
    report = run_assurance_registry(tau_bin=None, registry_path=REGISTRY)
    failures: list[str] = []
    for result in report["results"]:
        if result["passed"]:
            continue
        failures.append(f"{result['id']}: assurance mismatch")
        for mismatch in result["oracle_mismatches"]:
            failures.append(
                f"  oracle mismatch {mismatch['output']} case={mismatch['case_index']} "
                f"expected={mismatch['expected']} got={mismatch['got']}"
            )
        for group in ("properties", "static_properties"):
            for prop in result[group]:
                if prop["passed"]:
                    continue
                failures.append(
                    f"  {prop['id']} expect={prop['expect']} checked={prop['checked_cases']} "
                    f"counterexamples={len(prop['counterexamples'])}"
                )

    assert not failures, "Tau assurance mismatches:\n" + "\n".join(failures)
