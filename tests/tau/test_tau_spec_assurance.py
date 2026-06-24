from __future__ import annotations

from pathlib import Path

import pytest

from src.integration.tau_spec_assurance import ROOT, run_assurance_registry, safe_eval


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


def test_tau_spec_safe_eval_allows_registry_expression_subset() -> None:
    context = {"i1": 1, "i2": 2, "i3": 3, "o1": 1, "spec_text": "set charvar off"}

    assert safe_eval("(o1 == 1 and i3 == ((i2 + 1) & 0xFFFFFFFF))", context) is True
    assert safe_eval('"set charvar off" in spec_text', context) is True
    assert safe_eval("1 if i1 == 1 else 0", context) == 1


def test_tau_spec_safe_eval_rejects_object_introspection() -> None:
    with pytest.raises(ValueError, match="unsupported expression|only permits direct function calls"):
        safe_eval("().__class__.__mro__", {})
