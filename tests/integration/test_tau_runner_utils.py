from __future__ import annotations

import pytest

from src.integration.tau_runner import TauDefinition, inline_definitions, normalize_spec_text, parse_definitions


def test_normalize_spec_text_collapses_multiline_always_and_preserves_bv_hash() -> None:
    spec = """
# comment
set charvar 128

always
  a && b
  && ({ #x0000 } = { #x0000 }).

foo := { #x0001 }. # inline comment
""".lstrip()

    out = normalize_spec_text(spec)
    assert "set charvar" not in out
    assert "always a && b && ({ #x0000 } = { #x0000 })." in out
    assert "foo := { #x0001 }." in out
    assert "# inline comment" not in out


def test_normalize_spec_text_rejects_unterminated_always_block() -> None:
    spec = "always\n  a && b\n"
    with pytest.raises(ValueError, match="unterminated always block"):
        normalize_spec_text(spec)


def test_inline_definitions_detects_recursive_definitions() -> None:
    defs = {"f": TauDefinition(name="f", params=("x",), body="f(x)")}
    with pytest.raises(ValueError, match="max_depth"):
        inline_definitions("f(a)", defs, max_depth=3)


def test_parse_definitions_supports_multiline_bodies() -> None:
    spec = """
foo(a : bv[32], b : bv[32]) :=
  (a <= b) &&
  (b <= { #x00002710 }:bv[32]).
always (o1[t]:sbf = 1:sbf <-> foo(i1[t]:bv[32], i2[t]:bv[32])).
""".lstrip()

    normalized = normalize_spec_text(spec)
    defs = parse_definitions(normalized)
    assert "foo" in defs
    assert defs["foo"].params == ("a", "b")
    assert defs["foo"].body.startswith("(a <= b)")

    always_expr = normalized.splitlines()[-1].split("always", 1)[1].strip().removesuffix(".").strip()
    expanded = inline_definitions(always_expr, defs)
    assert "foo(" not in expanded
    assert "(a <= b)" not in expanded  # formals replaced
    assert "i1[t]:bv[32]" in expanded
    assert "i2[t]:bv[32]" in expanded
    assert "<=" in expanded
