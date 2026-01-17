from __future__ import annotations

import pytest

from src.integration.tau_runner import TauDefinition, inline_definitions, normalize_spec_text


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

