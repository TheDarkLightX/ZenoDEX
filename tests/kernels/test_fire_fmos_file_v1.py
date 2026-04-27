from __future__ import annotations

import json
from dataclasses import replace
from pathlib import Path

import pytest

from src.fire.pathing_v1 import fire_stdlib_objects_dir
from src.fire.compiler.fmos_file_v1 import (
    FIRE_FMOS_FILE_SCHEMA,
    build_certificate_env_from_spec_file,
    build_expression_from_spec_file,
    build_output_intervals_from_spec_file,
    build_source_intervals_from_spec_file,
    build_witnesses_from_spec_file,
    load_fire_math_object_spec_file,
    verify_fire_math_object_spec_file,
)
from src.fire.compiler.fmos_v1 import compile_fmos_artifact
from src.fire.compiler.object_compiler_v1 import compile_interval_expression_certificate
from src.fire.verifier.cert_v1 import FireInterval, verify_interval_certificate
from src.fire.runtime.burn_boost_call_v1 import BurnBoostCallTerms, SPEC as BURN_SPEC


REPO_ROOT = Path(__file__).resolve().parents[2]
SPEC_DIR = fire_stdlib_objects_dir()


def test_load_fire_math_object_spec_file_reads_burn_spec() -> None:
    spec_file = load_fire_math_object_spec_file(SPEC_DIR / "burn_boost_call_v1.json")

    assert spec_file.schema == FIRE_FMOS_FILE_SCHEMA
    assert spec_file.object_id == "burn_boost_call_v1"
    assert spec_file.object_name == "BurnBoostCall"
    assert [field.name for field in spec_file.term_fields] == [
        "n_notional",
        "strike_index",
        "cap_index",
        "source_upper",
    ]
    assert spec_file.term_fields[0].unit == "Amount[zUSD]"
    assert spec_file.term_fields[0].minimum == 0
    assert spec_file.term_fields[0].maximum == 1000
    assert spec_file.source_bounds == ()
    assert len(spec_file.imports) == 1
    assert spec_file.imports[0].name == "burn_final"
    assert spec_file.imports[0].interface_object_id == "burn_index_v1"
    assert spec_file.imports[0].interface_output == "burn_final"
    assert spec_file.outputs[0].name == "settlement_payoff"
    assert spec_file.outputs[0].unit == "Amount[zUSD]"


def test_build_expression_and_env_from_spec_file_compile_expected_interval() -> None:
    spec_file = load_fire_math_object_spec_file(SPEC_DIR / "burn_boost_call_v1.json")
    terms = BurnBoostCallTerms(n_notional=10, strike_index=4, cap_index=3, source_upper=9)

    expr = build_expression_from_spec_file(spec_file)
    env = build_certificate_env_from_spec_file(spec_file, terms)
    certificate = compile_interval_expression_certificate(expr, env)
    ok, err, interval = verify_interval_certificate(certificate, env)

    assert ok is True
    assert err is None
    assert interval == FireInterval(lower=0, upper=30)


def test_build_witnesses_from_spec_file_matches_external_spec() -> None:
    spec_file = load_fire_math_object_spec_file(SPEC_DIR / "burn_boost_call_v1.json")
    terms = BurnBoostCallTerms(n_notional=10, strike_index=4, cap_index=3, source_upper=9)

    witnesses = build_witnesses_from_spec_file(spec_file, terms)

    assert len(witnesses) == 1
    assert witnesses[0].name == "BurnCertificate[TDEX]"
    assert witnesses[0].freshness == "1 epoch"
    assert witnesses[0].lower == 0
    assert witnesses[0].upper == 9


def test_build_output_intervals_from_spec_file_matches_external_spec() -> None:
    spec_file = load_fire_math_object_spec_file(SPEC_DIR / "burn_boost_call_v1.json")
    terms = BurnBoostCallTerms(n_notional=10, strike_index=4, cap_index=3, source_upper=9)

    outputs = build_output_intervals_from_spec_file(spec_file, terms)

    assert outputs["settlement_payoff"] == FireInterval(lower=0, upper=30)


def test_build_source_intervals_from_spec_file_resolves_imported_interface_bounds() -> None:
    spec_file = load_fire_math_object_spec_file(SPEC_DIR / "burn_boost_call_v1.json")
    terms = BurnBoostCallTerms(n_notional=10, strike_index=4, cap_index=3, source_upper=9)

    source_intervals = build_source_intervals_from_spec_file(spec_file, terms)

    assert source_intervals == {"burn_final": FireInterval(lower=0, upper=9)}


def test_verify_fire_math_object_spec_file_rejects_unknown_expression_ref() -> None:
    spec_file = load_fire_math_object_spec_file(SPEC_DIR / "burn_boost_call_v1.json")
    bad_expr = spec_file.expression.__class__(kind="exact_param", name="missing_term")
    bad_spec_file = spec_file.__class__(
        schema=spec_file.schema,
        object_id=spec_file.object_id,
        object_name=spec_file.object_name,
        cli_help=spec_file.cli_help,
        object_version=spec_file.object_version,
        object_family=spec_file.object_family,
        settlement_asset=spec_file.settlement_asset,
        payoff_summary=spec_file.payoff_summary,
        ir_hash=spec_file.ir_hash,
        term_fields=spec_file.term_fields,
        source_bounds=spec_file.source_bounds,
        imports=spec_file.imports,
        witnesses=spec_file.witnesses,
        outputs=spec_file.outputs,
        expression=bad_expr,
    )

    assert verify_fire_math_object_spec_file(bad_spec_file) == (False, "unknown_exact_params:missing_term")


def test_verify_fire_math_object_spec_file_rejects_unit_invalid_expression() -> None:
    spec_file = load_fire_math_object_spec_file(SPEC_DIR / "burn_boost_call_v1.json")
    bad_term_fields = (
        replace(spec_file.term_fields[0], unit="Index"),
        *spec_file.term_fields[1:],
    )
    bad_spec_file = spec_file.__class__(
        schema=spec_file.schema,
        object_id=spec_file.object_id,
        object_name=spec_file.object_name,
        cli_help=spec_file.cli_help,
        object_version=spec_file.object_version,
        object_family=spec_file.object_family,
        settlement_asset=spec_file.settlement_asset,
        payoff_summary=spec_file.payoff_summary,
        ir_hash=spec_file.ir_hash,
        term_fields=bad_term_fields,
        source_bounds=spec_file.source_bounds,
        imports=spec_file.imports,
        witnesses=spec_file.witnesses,
        outputs=spec_file.outputs,
        expression=spec_file.expression,
    )

    assert verify_fire_math_object_spec_file(bad_spec_file) == (
        False,
        "expression_unit_mismatch:expected_Amount[zUSD]:got_Scalar",
    )


def test_compile_fmos_artifact_enforces_external_term_bounds_for_typed_terms() -> None:
    narrowed_spec = replace(
        BURN_SPEC,
        term_fields=(
            replace(BURN_SPEC.term_fields[0], maximum=5),
            *BURN_SPEC.term_fields[1:],
        ),
    )

    with pytest.raises(ValueError, match="n_notional outside FIRE FMOS bound \\[0, 5\\]"):
        compile_fmos_artifact(
            narrowed_spec,
            BurnBoostCallTerms(n_notional=10, strike_index=4, cap_index=3, source_upper=9),
        )


def test_compile_fmos_artifact_rejects_unit_invalid_spec_for_typed_terms() -> None:
    unit_broken_spec = replace(
        BURN_SPEC,
        term_fields=(
            replace(BURN_SPEC.term_fields[0], unit="Index"),
            *BURN_SPEC.term_fields[1:],
        ),
    )

    with pytest.raises(
        ValueError,
        match="FIRE expression unit mismatch for burn_boost_call_v1: expected Amount\\[zUSD\\], got Scalar",
    ):
        compile_fmos_artifact(
            unit_broken_spec,
            BurnBoostCallTerms(n_notional=10, strike_index=4, cap_index=3, source_upper=9),
        )


def test_load_fire_math_object_spec_file_rejects_inverted_term_bounds(tmp_path: Path) -> None:
    bad_spec = json.loads((SPEC_DIR / "burn_boost_call_v1.json").read_text(encoding="utf-8"))
    bad_path = tmp_path / "bad_bounds.json"
    bad_spec["term_fields"][0]["minimum"] = 9
    bad_spec["term_fields"][0]["maximum"] = 3
    bad_path.write_text(json.dumps(bad_spec, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    with pytest.raises(ValueError, match="term field n_notional has inverted bounds"):
        load_fire_math_object_spec_file(bad_path)


def test_load_fire_math_object_spec_file_rejects_missing_file(tmp_path: Path) -> None:
    with pytest.raises(FileNotFoundError):
        load_fire_math_object_spec_file(tmp_path / "missing.json")


def test_load_fire_math_object_spec_file_rejects_unknown_import_interface(tmp_path: Path) -> None:
    bad_spec = json.loads((SPEC_DIR / "burn_boost_call_v1.json").read_text(encoding="utf-8"))
    bad_path = tmp_path / "bad_import.json"
    bad_spec["imports"][0]["interface_object_id"] = "missing_index_v1"
    bad_path.write_text(json.dumps(bad_spec, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    with pytest.raises(ValueError, match="unknown_import_interface:missing_index_v1"):
        load_fire_math_object_spec_file(bad_path)
