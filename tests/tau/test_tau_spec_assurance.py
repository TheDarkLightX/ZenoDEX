from __future__ import annotations

import pytest

from src.integration.tau_spec_assurance import ROOT, run_assurance_registry, safe_eval


REGISTRY = ROOT / "tests" / "tau" / "spec_assurance_registry.json"


def test_tau_spec_assurance_safe_eval_supports_registry_expression_subset() -> None:
    context = {"i1": 1, "i2": 2, "i3": 3, "outputs": {"o1": 1}}

    assert safe_eval("1 if (i3 > 0 and i2 >= i1) else 0", context) == 1
    assert safe_eval("i3 == ((i2 + 1) & 0xFFFFFFFF)", context) is True
    assert safe_eval("outputs['o1'] == 1", context) is True
    assert safe_eval("BV(32, i1) < BV(32, i2)", context) is True
    assert safe_eval("len(sorted([3, 1, 2])) == 3", context) is True


@pytest.mark.parametrize(
    "expr",
    [
        "__import__('os').system('echo unsafe')",
        "(1).__class__",
        "open('/tmp/x', 'w')",
        "lambda x: x",
    ],
)
def test_tau_spec_assurance_safe_eval_rejects_unsafe_syntax(expr: str) -> None:
    with pytest.raises((NameError, ValueError)):
        safe_eval(expr, {})


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
