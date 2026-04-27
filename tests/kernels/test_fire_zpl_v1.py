from __future__ import annotations

import json
from pathlib import Path

import pytest

from src.fire.compiler.object_compiler_v1 import FireBinaryExpr
from src.fire.compiler.zpl_v1 import (
    FireZplBinaryExpr,
    FireZplCapExpr,
    FireZplDiagnosticError,
    FireZplPositivePartExpr,
    compile_fire_zpl_file,
    compile_fire_zpl_to_fmos_payload,
    parse_zpl_expression_ast,
    zpl_expr_to_fire_expr,
)
from src.fire.pathing_v1 import fire_stdlib_objects_dir, fire_zpl_dir


REPO_ROOT = Path(__file__).resolve().parents[2]
ZPL_DIR = fire_zpl_dir()
SPEC_DIR = fire_stdlib_objects_dir()


def _strip_contract_metadata(payload: object) -> object:
    if isinstance(payload, dict):
        return {
            key: _strip_contract_metadata(value)
            for key, value in payload.items()
            if key != "contract"
        }
    if isinstance(payload, list):
        return [_strip_contract_metadata(item) for item in payload]
    return payload


@pytest.mark.parametrize(
    ("zpl_name", "json_name"),
    [
        ("burn_boost_call_v1.zpl", "burn_boost_call_v1.json"),
        ("fee_note_v1.zpl", "fee_note_v1.json"),
        ("lp_loss_cover_v1.zpl", "lp_loss_cover_v1.json"),
        ("burn_index_v1.zpl", "burn_index_v1.json"),
        ("fee_index_v1.zpl", "fee_index_v1.json"),
        ("reward_index_v1.zpl", "reward_index_v1.json"),
        ("hodl_value_v1.zpl", "hodl_value_v1.json"),
        ("lp_value_v1.zpl", "lp_value_v1.json"),
    ],
)
def test_compile_fire_zpl_file_matches_existing_fmos_specs(zpl_name: str, json_name: str) -> None:
    compiled = compile_fire_zpl_file(ZPL_DIR / zpl_name)
    expected = json.loads((SPEC_DIR / json_name).read_text(encoding="utf-8"))

    assert compiled == expected


def test_compile_fire_zpl_to_fmos_payload_rejects_unknown_expression_operator() -> None:
    bad_zpl = """
object bad_v1;
name Bad;
cli_help "Bad";
version v1;
family test;
settlement zUSD;
summary "bad";
ir_hash sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa;
term x "X" Index 0 10;
output y "Y" Index = unknown(exact_param(x));
expression = unknown(exact_param(x));
end
""".strip()

    with pytest.raises(ValueError, match="unsupported ZPL expression function: unknown"):
        compile_fire_zpl_to_fmos_payload(bad_zpl)


def test_parse_zpl_expression_ast_preserves_cap_and_positive_part_nodes() -> None:
    expr = parse_zpl_expression_ast(
        "cap(positive_part(sub(source_bound(burn_final), exact_param(strike_index))), exact_param(cap_index))"
    )

    assert isinstance(expr, FireZplCapExpr)
    assert isinstance(expr.inner, FireZplPositivePartExpr)
    assert isinstance(expr.inner.inner, FireZplBinaryExpr)
    assert expr.inner.inner.op == "sub"


def test_zpl_expr_to_fire_expr_lowers_special_nodes_to_typed_compiler_ast() -> None:
    expr = parse_zpl_expression_ast(
        "cap(positive_part(sub(source_bound(burn_final), exact_param(strike_index))), exact_param(cap_index))"
    )
    lowered = zpl_expr_to_fire_expr(expr)

    assert isinstance(lowered, FireBinaryExpr)
    assert lowered.op == "min"
    assert isinstance(lowered.left, FireBinaryExpr)
    assert lowered.left.op == "max"


def test_compile_fire_zpl_to_fmos_payload_reports_exact_param_span() -> None:
    bad_zpl = """
object bad_v1;
name Bad;
cli_help "Bad";
version v1;
family test;
settlement zUSD;
summary "bad";
ir_hash sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa;
term x "X" Index 0 10;
output y "Y" Index = exact_param(missing);
expression = exact_param(missing);
end
""".strip()

    with pytest.raises(FireZplDiagnosticError, match=r"line 10, col 22 .*unknown exact_param reference: missing"):
        compile_fire_zpl_to_fmos_payload(bad_zpl)


def test_compile_fire_zpl_to_fmos_payload_reports_import_validation_span() -> None:
    canonical_text = (ZPL_DIR / "burn_boost_call_v1.zpl").read_text(encoding="utf-8")
    bad_zpl = canonical_text.replace("burn_index_v1", "missing_index_v1", 1)

    with pytest.raises(FireZplDiagnosticError, match=r"line 14, col 1 .*unknown_import_interface:missing_index_v1"):
        compile_fire_zpl_to_fmos_payload(bad_zpl)


def test_compile_fire_zpl_to_fmos_payload_reports_expression_unit_mismatch_span() -> None:
    canonical_text = (ZPL_DIR / "burn_boost_call_v1.zpl").read_text(encoding="utf-8")
    bad_zpl = canonical_text.replace('output settlement_payoff "Certified settlement payoff bound" Amount[zUSD]', 'output settlement_payoff "Certified settlement payoff bound" Scalar', 1)

    with pytest.raises(FireZplDiagnosticError, match=r"line 16, col 1 .*expression_unit_mismatch:expected_Scalar:got_Amount\[zUSD\]"):
        compile_fire_zpl_to_fmos_payload(bad_zpl)


def test_compile_fire_zpl_to_fmos_payload_accepts_named_contract_reuse() -> None:
    canonical_text = (ZPL_DIR / "burn_boost_call_v1.zpl").read_text(encoding="utf-8")
    compiled = compile_fire_zpl_to_fmos_payload(canonical_text)
    expected = json.loads((SPEC_DIR / "burn_boost_call_v1.json").read_text(encoding="utf-8"))

    assert compiled == expected
    assert compiled["imports"][0]["contract"] == {
        "name": "burn_contract",
        "role": "import:burn_index_v1.burn_final",
    }
    assert compiled["witnesses"][0]["contract"] == {
        "name": "burn_contract",
        "role": "witness:BurnCertificate[TDEX]",
    }


def test_compile_fire_zpl_to_fmos_payload_accepts_named_contract_reuse_for_source() -> None:
    canonical_text = (ZPL_DIR / "lp_value_v1.zpl").read_text(encoding="utf-8")
    compiled = compile_fire_zpl_to_fmos_payload(canonical_text)
    expected = json.loads((SPEC_DIR / "lp_value_v1.json").read_text(encoding="utf-8"))

    assert compiled == expected
    assert compiled["source_bounds"][0]["contract"] == {
        "name": "lpv_contract",
        "role": "source:lpv_final",
    }


def test_compile_fire_zpl_to_fmos_payload_rejects_unknown_contract_reference() -> None:
    canonical_text = (ZPL_DIR / "burn_boost_call_v1.zpl").read_text(encoding="utf-8")
    bad_zpl = canonical_text.replace(
        'import burn_final burn_index_v1 burn_final contract:burn_contract;',
        'import burn_final burn_index_v1 burn_final contract:missing_contract;',
        1,
    )

    with pytest.raises(FireZplDiagnosticError, match=r"line 14, col 1 .*unknown contract reference: missing_contract"):
        compile_fire_zpl_to_fmos_payload(bad_zpl)


def test_compile_fire_zpl_to_fmos_payload_accepts_multiline_statement_grammar() -> None:
    canonical_text = (ZPL_DIR / "burn_boost_call_v1.zpl").read_text(encoding="utf-8")
    multiline_text = canonical_text.replace(
        'output settlement_payoff "Certified settlement payoff bound" Amount[zUSD] = mul(exact_param(n_notional), cap(positive_part(sub(source_bound(burn_final), exact_param(strike_index))), exact_param(cap_index)));',
        """output settlement_payoff "Certified settlement payoff bound" Amount[zUSD] =
mul(
  exact_param(n_notional),
  cap(
    positive_part(sub(source_bound(burn_final), exact_param(strike_index))),
    exact_param(cap_index)
  )
);""",
        1,
    ).replace(
        "expression = mul(exact_param(n_notional), cap(positive_part(sub(source_bound(burn_final), exact_param(strike_index))), exact_param(cap_index)));",
        """expression =
mul(
  exact_param(n_notional),
  cap(
    positive_part(sub(source_bound(burn_final), exact_param(strike_index))),
    exact_param(cap_index)
  )
);""",
        1,
    )

    compiled = compile_fire_zpl_to_fmos_payload(multiline_text)
    expected = json.loads((SPEC_DIR / "burn_boost_call_v1.json").read_text(encoding="utf-8"))

    assert compiled == expected


def test_compile_fire_zpl_to_fmos_payload_rejects_duplicate_scalar_statement() -> None:
    bad_zpl = """
object bad_v1;
name Bad;
name BadAgain;
cli_help "Bad";
version v1;
family test;
settlement zUSD;
summary "bad";
ir_hash sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa;
term x "X" Index 0 10;
output y "Y" Index = exact_param(x);
expression = exact_param(x);
end
""".strip()

    with pytest.raises(ValueError, match="duplicate ZPL statement: name"):
        compile_fire_zpl_to_fmos_payload(bad_zpl)


def test_compile_fire_zpl_to_fmos_payload_rejects_trailing_statement_after_end() -> None:
    bad_zpl = """
object bad_v1;
name Bad;
cli_help "Bad";
version v1;
family test;
settlement zUSD;
summary "bad";
ir_hash sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa;
term x "X" Index 0 10;
output y "Y" Index = exact_param(x);
expression = exact_param(x);
end
name Trailing;
""".strip()

    with pytest.raises(ValueError, match="unexpected ZPL statement after end: name Trailing"):
        compile_fire_zpl_to_fmos_payload(bad_zpl)
