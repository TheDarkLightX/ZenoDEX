"""Characterization corpus for ``_verify_fire_math_object_spec_file``.

This test follows the CHARACTERIZATION-CORPUS-FIRST technique:

1.  A single valid FIRE math-object-spec payload (``valid_base``) verifies OK.
    It is intentionally self-contained yet exercises every branch family of the
    verifier: multiple term fields, a source bound, a *real* imported interface
    (``burn_index_v1`` from the committed stdlib), a witness with a contract,
    multiple outputs, and an arithmetic (``mul``) expression.
2.  A corpus of single mutations drives every *reachable* reject code of the
    verifier exactly once, plus a handful of two-fault cases that pin the
    first-failure ORDERING (precedence), plus the upstream-``from_dict``
    boundary and the empty-outputs ``IndexError`` (a latent bug that is locked,
    not fixed).
3.  The recorded ``(seam, ok, err)`` / raise behaviour is committed to
    ``fixtures/fmos_file_v1_characterization.json``.  The refactored verifier
    must reproduce this fixture EXACTLY.

The corpus locks BOTH every reject code AND the short-circuit precedence between
the verifier's ordered sections.  Regenerate (records the behaviour of the
*current* verifier, never asserts -- run deliberately and review the diff) with
either::

    python3 tests/kernels/test_fmos_file_v1_characterization.py --regen
    REGEN_FMOS_CHARACTERIZATION=1 python3 -m pytest \
        tests/kernels/test_fmos_file_v1_characterization.py -k regen

The regen path lives entirely in this file (no conftest option) so the module is
self-contained.
"""

from __future__ import annotations

import copy
import dataclasses
import json
import os
from pathlib import Path
from typing import Any, Callable

import pytest

from src.fire.compiler.fmos_file_v1 import (
    FireExprFile,
    FireMathObjectSpecFile,
    verify_fire_math_object_spec_file,
)


FIXTURE_PATH = Path(__file__).resolve().parent / "fixtures" / "fmos_file_v1_characterization.json"


# ---------------------------------------------------------------------------
# Valid base spec (verifies OK) and the recording seam.
# ---------------------------------------------------------------------------


def valid_base() -> dict[str, Any]:
    """A self-contained spec that verifies OK.

    Imports the *real* committed stdlib leaf ``burn_index_v1`` so the verifier's
    recursive import branch (the dependency-digest check) is exercised
    deterministically.  The import name ``burn_final`` and the source-bound name
    ``src_final`` are distinct to avoid a ``duplicate_source_interface_name``.
    """

    return {
        "schema": "zenodex/fire-math-object-spec/v1",
        "object_id": "char_demo_v1",
        "object_name": "CharDemo",
        "cli_help": "Characterization demo object",
        "object_version": "v1",
        "object_family": "demo",
        "settlement_asset": "zUSD",
        "payoff_summary": "demo payoff",
        "ir_hash": "sha256:" + "0" * 64,
        "term_fields": [
            {"name": "n_notional", "description": "notional", "unit": "Amount[zUSD]", "minimum": 0, "maximum": 1000},
            {"name": "rate_idx", "description": "index", "unit": "Index", "minimum": 0, "maximum": 100},
        ],
        "source_bounds": [
            {
                "name": "src_final",
                "unit": "Index",
                "lower": {"kind": "const", "value": 0},
                "upper": {"kind": "term", "term": "rate_idx"},
            },
        ],
        "imports": [
            {
                "name": "burn_final",
                "interface_object_id": "burn_index_v1",
                "interface_output": "burn_final",
                "unit": "Index",
                "lower": {"kind": "const", "value": 0},
                "upper": {"kind": "term", "term": "rate_idx"},
            },
        ],
        "witnesses": [
            {
                "name": "SrcCertificate[zUSD]",
                "freshness": "1 epoch",
                "unit": "Index",
                "lower": {"kind": "const", "value": 0},
                "upper": {"kind": "term", "term": "rate_idx"},
                "contract": {"name": "src_contract", "role": "witness:SrcCertificate[zUSD]"},
            },
        ],
        "outputs": [
            {
                "name": "settlement_payoff",
                "description": "payoff",
                "unit": "Amount[zUSD]",
                "expression": {
                    "kind": "mul",
                    "left": {"kind": "source_bound", "name": "src_final"},
                    "right": {"kind": "exact_param", "name": "n_notional"},
                },
            },
            {
                "name": "secondary",
                "description": "second",
                "unit": "Amount[zUSD]",
                "expression": {"kind": "exact_param", "name": "n_notional"},
            },
        ],
        "expression": {
            "kind": "mul",
            "left": {"kind": "source_bound", "name": "src_final"},
            "right": {"kind": "exact_param", "name": "n_notional"},
        },
    }


def evaluate_payload(payload: dict[str, Any]) -> list[Any]:
    """Record behaviour at the verifier seam, building the spec via ``from_dict``.

    Mirrors the production ``load_fire_math_object_spec_file`` decomposition but
    keeps reject codes intact: ``from_dict`` rejects (e.g. inverted term bounds)
    surface as ``parse_raise`` rather than collapsing into ``load``'s
    ``ValueError`` wrapper, and the verifier's own ``(ok, err)`` / raises are
    captured separately.
    """

    try:
        spec_file = FireMathObjectSpecFile.from_dict(payload)
    except Exception as exc:  # noqa: BLE001 - intentionally catch+record
        return ["parse_raise", type(exc).__name__, str(exc)]
    return evaluate_spec_file(spec_file)


def evaluate_spec_file(spec_file: Any) -> list[Any]:
    """Run the verifier on an already-built spec object, recording raises."""

    try:
        ok, err = verify_fire_math_object_spec_file(spec_file)
    except Exception as exc:  # noqa: BLE001 - intentionally catch+record
        return ["verify_raise", type(exc).__name__, str(exc)]
    return ["verify", ok, err]


# ---------------------------------------------------------------------------
# Mutation builders.  Payload mutations operate on a deep copy of valid_base;
# spec mutations construct a FireMathObjectSpecFile directly (for branches that
# from_dict structurally shields).
# ---------------------------------------------------------------------------


def _mutate(fn: Callable[[dict[str, Any]], None]) -> dict[str, Any]:
    payload = copy.deepcopy(valid_base())
    fn(payload)
    return payload


def _base_spec() -> FireMathObjectSpecFile:
    return FireMathObjectSpecFile.from_dict(valid_base())


def _add_mismatch_expr() -> FireExprFile:
    # add of Index (source_bound src_final) + Amount[zUSD] (exact_param n_notional)
    return FireExprFile(
        kind="add",
        left=FireExprFile(kind="source_bound", name="src_final"),
        right=FireExprFile(kind="exact_param", name="n_notional"),
    )


def _empty_name_expr() -> FireExprFile:
    # constructable directly (from_dict rejects empty name, dataclass ctor allows it)
    return FireExprFile(kind="exact_param", name="")


@dataclasses.dataclass(frozen=True)
class Case:
    cid: str
    locks: str
    builder: Callable[[], Any]
    is_spec: bool = False  # True => builder returns a FireMathObjectSpecFile


def corpus() -> list[Case]:
    """The ordered characterization corpus.

    Ordering mirrors the verifier's section order (top guard -> dup checks ->
    term -> source -> import -> witness -> duplicate_output -> global expr ->
    per-output) so the file reads as a precedence map.
    """

    cases: list[Case] = []

    def payload(cid: str, locks: str, fn: Callable[[dict[str, Any]], None]) -> None:
        cases.append(Case(cid, locks, (lambda fn=fn: _mutate(fn))))

    def spec(cid: str, locks: str, fn: Callable[[], Any]) -> None:
        cases.append(Case(cid, locks, fn, is_spec=True))

    # --- valid baseline ---
    cases.append(Case("valid_baseline", "verifies OK", valid_base))

    # --- top-of-function guard (line 490) ---
    spec("not_a_spec_type", "TypeError when spec_file is not FireMathObjectSpecFile",
         lambda: {"not": "a spec"})

    # --- duplicate-name checks (lines 501-510) ---
    payload("dup_term_field", "duplicate_term_field",
            lambda p: p["term_fields"].append(dict(p["term_fields"][0])))
    payload("dup_source_bound", "duplicate_source_bound",
            lambda p: p["source_bounds"].append(dict(p["source_bounds"][0])))
    payload("dup_import", "duplicate_import",
            lambda p: p["imports"].append(dict(p["imports"][0])))
    payload("dup_source_interface_name", "duplicate_source_interface_name (source name == import name)",
            lambda p: p["source_bounds"][0].__setitem__("name", "burn_final"))
    payload("dup_witness", "duplicate_witness",
            lambda p: p["witnesses"].append(dict(p["witnesses"][0])))

    # --- term-field loop (lines 516-522) ---
    payload("term_field_unit_invalid", "term_field_unit_invalid",
            lambda p: p["term_fields"][1].__setitem__("unit", "Bogus["))
    # term_field_bounds_invalid (line 522) is unreachable via from_dict AND via
    # direct construction (FireTermFieldSpec.__post_init__ rejects inverted
    # bounds first). The observable behaviour is the upstream parse raise.
    payload("term_field_bounds_invalid_boundary", "BOUNDARY: inverted bounds rejected upstream in from_dict",
            lambda p: (p["term_fields"][0].__setitem__("minimum", 9),
                       p["term_fields"][0].__setitem__("maximum", 3)))

    # --- source-bound loop (lines 524-540) ---
    payload("source_bound_unit_invalid", "source_bound_unit_invalid",
            lambda p: p["source_bounds"][0].__setitem__("unit", "Bogus["))
    payload("unknown_term_ref_in_source_bound_lower", "unknown_term_ref_in_source_bound (lower)",
            lambda p: p["source_bounds"][0].__setitem__("lower", {"kind": "term", "term": "ghost"}))
    payload("unknown_term_ref_in_source_bound_upper", "unknown_term_ref_in_source_bound (upper)",
            lambda p: p["source_bounds"][0].__setitem__("upper", {"kind": "term", "term": "ghost"}))
    payload("source_bound_unit_mismatch", "source_bound_unit_mismatch (bound unit != term field unit)",
            lambda p: p["source_bounds"][0].__setitem__("unit", "Amount[zUSD]"))

    # --- import loop (lines 541-572): the dependency-digest check ---
    payload("import_unit_invalid", "import_unit_invalid",
            lambda p: p["imports"][0].__setitem__("unit", "Bogus["))
    payload("unknown_term_ref_in_import_lower", "unknown_term_ref_in_import (lower)",
            lambda p: p["imports"][0].__setitem__("lower", {"kind": "term", "term": "ghost"}))
    payload("unknown_term_ref_in_import_upper", "unknown_term_ref_in_import (upper)",
            lambda p: p["imports"][0].__setitem__("upper", {"kind": "term", "term": "ghost"}))
    payload("import_unit_mismatch", "import_unit_mismatch (import unit != term field unit)",
            lambda p: p["imports"][0].__setitem__("unit", "Amount[zUSD]"))
    payload("unknown_import_interface", "unknown_import_interface (dependency target absent)",
            lambda p: p["imports"][0].__setitem__("interface_object_id", "missing_index_v1"))
    payload("unknown_import_output", "unknown_import_output (forged/absent imported output)",
            lambda p: p["imports"][0].__setitem__("interface_output", "no_such_output"))
    payload("import_output_unit_mismatch", "import_output_unit_mismatch (tampered dependency unit digest)",
            lambda p: (p["imports"][0].__setitem__("unit", "Rate"),
                       p["imports"][0].__setitem__("lower", {"kind": "const", "value": 0}),
                       p["imports"][0].__setitem__("upper", {"kind": "const", "value": 5})))

    # --- witness loop (lines 573-589) ---
    payload("witness_unit_invalid", "witness_unit_invalid",
            lambda p: p["witnesses"][0].__setitem__("unit", "Bogus["))
    payload("unknown_term_ref_in_witness_lower", "unknown_term_ref_in_witness (lower)",
            lambda p: p["witnesses"][0].__setitem__("lower", {"kind": "term", "term": "ghost"}))
    payload("unknown_term_ref_in_witness_upper", "unknown_term_ref_in_witness (upper)",
            lambda p: p["witnesses"][0].__setitem__("upper", {"kind": "term", "term": "ghost"}))
    payload("witness_unit_mismatch", "witness_unit_mismatch",
            lambda p: p["witnesses"][0].__setitem__("unit", "Amount[zUSD]"))

    # --- duplicate_output (line 590 -- AFTER the witness loop, NOT batched with
    #     the other duplicate-name checks). This placement is load-bearing. ---
    payload("dup_output", "duplicate_output (checked AFTER witness loop)",
            lambda p: p["outputs"].append(dict(p["outputs"][0])))

    # --- global expression ref/unit checks (lines 593-617) ---
    spec("expression_invalid", "expression_invalid (empty-name ref in global expr)",
         lambda: dataclasses.replace(_base_spec(), expression=_empty_name_expr()))
    payload("unknown_exact_params", "unknown_exact_params (global expr references missing term)",
            lambda p: p.__setitem__("expression", {"kind": "exact_param", "name": "ghost"}))
    payload("unknown_source_bounds", "unknown_source_bounds (global expr references missing source)",
            lambda p: p.__setitem__("expression", {"kind": "source_bound", "name": "ghost"}))
    spec("expression_unit_invalid", "expression_unit_invalid (add of mismatched units)",
         lambda: dataclasses.replace(_base_spec(), expression=_add_mismatch_expr()))
    payload("expression_unit_mismatch", "expression_unit_mismatch (global expr unit != outputs[0].unit)",
            lambda p: p.__setitem__("expression", {"kind": "exact_param", "name": "rate_idx"}))

    # --- per-output loop (lines 619-645) ---
    payload("output_unit_invalid", "output_unit_invalid",
            lambda p: p["outputs"][1].__setitem__("unit", "Bogus["))
    spec("output_expression_invalid", "output_expression_invalid (empty-name ref in output expr)",
         lambda: _spec_with_output_expr(_empty_name_expr()))
    payload("unknown_output_exact_params", "unknown_output_exact_params",
            lambda p: p["outputs"][1].__setitem__("expression", {"kind": "exact_param", "name": "ghost"}))
    payload("unknown_output_source_bounds", "unknown_output_source_bounds",
            lambda p: p["outputs"][1].__setitem__("expression", {"kind": "source_bound", "name": "ghost"}))
    spec("output_expression_unit_invalid", "output_expression_unit_invalid (add of mismatched units)",
         lambda: _spec_with_output_expr(_add_mismatch_expr(), output_unit="Index"))
    payload("output_expression_unit_mismatch", "output_expression_unit_mismatch",
            lambda p: p["outputs"][1].__setitem__("expression", {"kind": "exact_param", "name": "rate_idx"}))

    # --- latent bug: empty outputs reaches outputs[0] (line 615) -> IndexError ---
    payload("empty_outputs_indexerror", "LATENT BUG: empty outputs -> IndexError at outputs[0] (locked, not fixed)",
            lambda p: p.__setitem__("outputs", []))

    # --- two-fault ORDERING cases (lock short-circuit precedence between sections) ---
    payload("order_dup_term_before_dup_source", "ORDER: duplicate_term_field wins over duplicate_source_bound",
            lambda p: (p["term_fields"].append(dict(p["term_fields"][0])),
                       p["source_bounds"].append(dict(p["source_bounds"][0]))))
    payload("order_source_before_import", "ORDER: source_bound_unit_mismatch wins over import_unit_invalid",
            lambda p: (p["source_bounds"][0].__setitem__("unit", "Amount[zUSD]"),
                       p["imports"][0].__setitem__("unit", "Bogus[")))
    payload("order_witness_before_dup_output", "ORDER: witness_unit_mismatch wins over duplicate_output",
            lambda p: (p["witnesses"][0].__setitem__("unit", "Amount[zUSD]"),
                       p["outputs"].append(dict(p["outputs"][0]))))
    payload("order_dup_output_before_global_expr", "ORDER: duplicate_output wins over unknown_exact_params",
            lambda p: (p["outputs"].append(dict(p["outputs"][0])),
                       p.__setitem__("expression", {"kind": "exact_param", "name": "ghost"})))

    # --- INTRA-ITEM interleave ORDERING: within source/import/witness loops the
    #     verifier checks BOTH lower+upper existence BEFORE either unit-mismatch.
    #     A lower-unit-mismatch + upper-unknown-term must report the UPPER unknown
    #     ref, not the lower mismatch. This pins the two-phase interleave that any
    #     deeper extraction must preserve. ---
    def _amt_term(p: dict[str, Any]) -> None:
        p["term_fields"].append({"name": "amt_term", "description": "a", "unit": "Amount[zUSD]", "minimum": 0, "maximum": 10})

    payload("order_source_unknown_upper_before_mismatch_lower",
            "ORDER(intra): source unknown_term_ref(upper) wins over unit_mismatch(lower)",
            lambda p: (_amt_term(p),
                       p["source_bounds"][0].__setitem__("lower", {"kind": "term", "term": "amt_term"}),
                       p["source_bounds"][0].__setitem__("upper", {"kind": "term", "term": "ghost"})))
    payload("order_import_unknown_upper_before_mismatch_lower",
            "ORDER(intra): import unknown_term_ref(upper) wins over unit_mismatch(lower)",
            lambda p: (_amt_term(p),
                       p["imports"][0].__setitem__("lower", {"kind": "term", "term": "amt_term"}),
                       p["imports"][0].__setitem__("upper", {"kind": "term", "term": "ghost"})))
    payload("order_witness_unknown_upper_before_mismatch_lower",
            "ORDER(intra): witness unknown_term_ref(upper) wins over unit_mismatch(lower)",
            lambda p: (_amt_term(p),
                       p["witnesses"][0].__setitem__("lower", {"kind": "term", "term": "amt_term"}),
                       p["witnesses"][0].__setitem__("upper", {"kind": "term", "term": "ghost"})))

    return cases


def _spec_with_output_expr(expr: FireExprFile, *, output_unit: str | None = None) -> FireMathObjectSpecFile:
    sf = _base_spec()
    out = sf.outputs[1]
    out = dataclasses.replace(out, expression=expr)
    if output_unit is not None:
        out = dataclasses.replace(out, unit=output_unit)
    return dataclasses.replace(sf, outputs=(sf.outputs[0], out))


def _run_case(case: Case) -> list[Any]:
    obj = case.builder()
    if case.is_spec:
        return evaluate_spec_file(obj)
    return evaluate_payload(obj)


# ---------------------------------------------------------------------------
# Fixture I/O + --regen.
# ---------------------------------------------------------------------------


def _regenerate_fixture() -> dict[str, Any]:
    record = {case.cid: _run_case(case) for case in corpus()}
    FIXTURE_PATH.parent.mkdir(parents=True, exist_ok=True)
    FIXTURE_PATH.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return record


def _load_fixture() -> dict[str, Any]:
    return json.loads(FIXTURE_PATH.read_text(encoding="utf-8"))


def test_regen_fixture_when_requested() -> None:
    """When ``REGEN_FMOS_CHARACTERIZATION=1`` is set, (re)write the fixture.

    This is the only test that writes the corpus; it never asserts the verifier,
    so a deliberate regeneration is required to change the locked behaviour.
    Without the env flag it is a no-op skip.
    """

    if os.environ.get("REGEN_FMOS_CHARACTERIZATION") != "1":
        pytest.skip("set REGEN_FMOS_CHARACTERIZATION=1 to regenerate the fixture")
    _regenerate_fixture()


def test_fixture_exists_and_is_complete() -> None:
    assert FIXTURE_PATH.exists(), (
        f"missing characterization fixture {FIXTURE_PATH}; "
        "regenerate with --regen-fmos-characterization"
    )
    fixture = _load_fixture()
    corpus_ids = {case.cid for case in corpus()}
    assert set(fixture) == corpus_ids, (
        "fixture corpus drifted; regenerate with --regen-fmos-characterization"
    )
    # Sanity: corpus is large enough to actually exercise the verifier.
    assert len(corpus_ids) >= 35


@pytest.mark.parametrize("case", corpus(), ids=lambda c: c.cid)
def test_characterization_reproduces_fixture(case: Case) -> None:
    """The (refactored) verifier must reproduce the committed corpus EXACTLY."""

    fixture = _load_fixture()
    expected = fixture[case.cid]
    actual = _run_case(case)
    assert actual == expected, (
        f"characterization drift for {case.cid!r} ({case.locks}): "
        f"expected {expected!r}, got {actual!r}"
    )


def test_valid_baseline_verifies_ok() -> None:
    assert _run_case(corpus()[0]) == ["verify", True, None]


# ---------------------------------------------------------------------------
# TEETH: independent mutation tests that MUST go RED if the verifier weakens.
# These do not consult the fixture; they assert the security-critical reject
# behaviour directly, so the fixture can never "lock in" an accepting verifier.
# ---------------------------------------------------------------------------


def test_teeth_forged_imported_output_is_rejected() -> None:
    """A spec that forges a non-existent imported output MUST be rejected.

    Catches mutation: dropping the ``unknown_import_output`` check (an attacker
    declaring a dependency output that the dependency does not actually export).
    """

    payload = _mutate(lambda p: p["imports"][0].__setitem__("interface_output", "forged_output"))
    spec_file = FireMathObjectSpecFile.from_dict(payload)
    ok, err = verify_fire_math_object_spec_file(spec_file)
    assert ok is False
    assert err == "unknown_import_output:burn_index_v1:forged_output"


def test_teeth_tampered_dependency_unit_digest_is_rejected() -> None:
    """A spec whose declared import unit disagrees with the dependency's real
    output unit MUST be rejected (tampered dependency digest).

    Catches mutation: dropping the ``import_output_unit_mismatch`` check, which
    would let a caller bind a dependency under a wrong unit.
    """

    payload = _mutate(
        lambda p: (
            p["imports"][0].__setitem__("unit", "Rate"),
            p["imports"][0].__setitem__("lower", {"kind": "const", "value": 0}),
            p["imports"][0].__setitem__("upper", {"kind": "const", "value": 5}),
        )
    )
    spec_file = FireMathObjectSpecFile.from_dict(payload)
    ok, err = verify_fire_math_object_spec_file(spec_file)
    assert ok is False
    assert err == "import_output_unit_mismatch:burn_final:burn_index_v1:burn_final"


def test_teeth_weak_spec_unknown_expression_ref_is_rejected() -> None:
    """A spec whose payoff expression references an undeclared term MUST be
    rejected (a weak/under-specified spec).

    Catches mutation: dropping the ``unknown_exact_params`` check.
    """

    payload = _mutate(lambda p: p.__setitem__("expression", {"kind": "exact_param", "name": "undeclared"}))
    spec_file = FireMathObjectSpecFile.from_dict(payload)
    ok, err = verify_fire_math_object_spec_file(spec_file)
    assert ok is False
    assert err == "unknown_exact_params:undeclared"


def test_teeth_unit_unsound_expression_is_rejected() -> None:
    """A spec whose payoff expression yields a unit different from the declared
    primary output unit MUST be rejected (unit-unsound spec).

    Catches mutation: dropping the ``expression_unit_mismatch`` check.
    """

    payload = _mutate(lambda p: p.__setitem__("expression", {"kind": "exact_param", "name": "rate_idx"}))
    spec_file = FireMathObjectSpecFile.from_dict(payload)
    ok, err = verify_fire_math_object_spec_file(spec_file)
    assert ok is False
    assert err == "expression_unit_mismatch:expected_Amount[zUSD]:got_Index"


def test_teeth_duplicate_output_precedence_is_preserved() -> None:
    """Two faults (witness unit mismatch + duplicate output) MUST report the
    witness error, because ``duplicate_output`` is checked AFTER the witness
    loop.  Pins the load-bearing section ordering.
    """

    payload = _mutate(
        lambda p: (
            p["witnesses"][0].__setitem__("unit", "Amount[zUSD]"),
            p["outputs"].append(dict(p["outputs"][0])),
        )
    )
    spec_file = FireMathObjectSpecFile.from_dict(payload)
    ok, err = verify_fire_math_object_spec_file(spec_file)
    assert ok is False
    assert err == "witness_unit_mismatch:SrcCertificate[zUSD]:rate_idx"


# ---------------------------------------------------------------------------
# Recursive dependency rejects (import_invalid / import_cycle).
#
# These two reject codes only fire INSIDE the recursive import verification, so
# they cannot be driven by a top-level corpus payload (the public entrypoint
# seeds ``visited=frozenset()`` and the cycle/child-failure is wrapped into the
# parent's ``import_invalid``). They are locked here via monkeypatch of the
# import loader -- no source/fixture files are touched.
# ---------------------------------------------------------------------------


def test_import_invalid_wraps_failing_dependency(monkeypatch: pytest.MonkeyPatch) -> None:
    """A spec importing a dependency that itself fails verification MUST be
    rejected with the wrapped child error (``import_invalid:<id>:<child_err>``).

    Locks the deepest dependency-digest failure path: the recursive
    ``_verify_fire_math_object_spec_file`` call inside ``_check_import_interface``.
    """

    child_payload = _mutate(
        lambda p: (
            p.__setitem__("object_id", "fake_child_v1"),
            p["term_fields"].append(dict(p["term_fields"][0])),  # duplicate term -> child rejects
        )
    )
    bad_child = FireMathObjectSpecFile.from_dict(child_payload)
    monkeypatch.setattr(
        "src.fire.compiler.fmos_file_v1._load_imported_spec_file",
        lambda _id: bad_child,
    )
    parent = FireMathObjectSpecFile.from_dict(valid_base())  # imports burn_index_v1
    ok, err = verify_fire_math_object_spec_file(parent)
    assert ok is False
    assert err == "import_invalid:burn_index_v1:duplicate_term_field"


def test_import_cycle_is_rejected_through_recursion(monkeypatch: pytest.MonkeyPatch) -> None:
    """An import whose dependency re-enters the current object id MUST be
    rejected via the recursion cycle guard, surfaced through the parent's
    ``import_invalid`` wrapper.

    Locks the ``import_cycle`` reject code (only reachable inside recursion).
    """

    cyclic_child = FireMathObjectSpecFile.from_dict(
        _mutate(lambda p: p.__setitem__("object_id", "char_demo_v1"))  # == parent id
    )
    monkeypatch.setattr(
        "src.fire.compiler.fmos_file_v1._load_imported_spec_file",
        lambda _id: cyclic_child,
    )
    parent = FireMathObjectSpecFile.from_dict(valid_base())
    ok, err = verify_fire_math_object_spec_file(parent)
    assert ok is False
    assert err == "import_invalid:burn_index_v1:import_cycle:char_demo_v1"


if __name__ == "__main__":  # pragma: no cover - manual regen entrypoint
    import sys

    if "--regen" in sys.argv:
        rec = _regenerate_fixture()
        print(f"wrote {len(rec)} corpus entries to {FIXTURE_PATH}")
    else:
        print("pass --regen to (re)write the characterization fixture")
