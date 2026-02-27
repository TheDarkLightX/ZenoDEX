#!/usr/bin/env python3
"""
Tests for LogicSpec transpiler.

Run with: python -m pytest tools/logicspec/tests/test_transpiler.py -v
Or standalone: python tools/logicspec/tests/test_transpiler.py
"""

import sys
from pathlib import Path

# Add parent to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent.parent))

from logicspec import transpile, parse, generate_tau
from logicspec.lexer import tokenize, TokenKind
from logicspec.ast import TypeKind, BinOp


class TestLexer:
    """Test the lexer (tokenizer)."""

    def test_unicode_operators(self):
        """Test that Unicode logic symbols are tokenized correctly."""
        tokens = tokenize("∧ ∨ ¬ → ↔ □ ◇ ∀ ∃ ≤ ≥ ≠")

        kinds = [t.kind for t in tokens if t.kind != TokenKind.EOF]
        assert TokenKind.AND in kinds
        assert TokenKind.OR in kinds
        assert TokenKind.NOT in kinds
        assert TokenKind.IMPLIES in kinds
        assert TokenKind.IFF in kinds
        assert TokenKind.ALWAYS in kinds
        assert TokenKind.FORALL in kinds
        assert TokenKind.EXISTS in kinds

    def test_ascii_operators(self):
        """Test that ASCII alternatives are tokenized correctly."""
        tokens = tokenize("and or not implies iff always forall exists <= >= !=")

        kinds = [t.kind for t in tokens if t.kind != TokenKind.EOF]
        assert TokenKind.AND in kinds
        assert TokenKind.OR in kinds
        assert TokenKind.NOT in kinds
        assert TokenKind.IMPLIES in kinds
        assert TokenKind.IFF in kinds
        assert TokenKind.ALWAYS in kinds
        assert TokenKind.FORALL in kinds
        assert TokenKind.EXISTS in kinds

    def test_time_index(self):
        """Test time index parsing."""
        tokens = tokenize("[t] [t-1] [t+2] [0]")

        time_tokens = [t for t in tokens if t.kind == TokenKind.TIME_INDEX]
        assert len(time_tokens) == 4
        assert time_tokens[0].value == "[t]"
        assert time_tokens[1].value == "[t-1]"


class TestParser:
    """Test the parser."""

    def test_simple_spec(self):
        """Test parsing a simple specification."""
        source = """
        spec Test {
          inputs {
            x: u32
          }
          outputs {
            valid: bool
          }
          invariant main {
            □ (valid ↔ x > 0)
          }
        }
        """
        spec = parse(source)

        assert spec.name == "Test"
        assert len(spec.inputs) == 1
        assert spec.inputs[0].name == "x"
        assert spec.inputs[0].type.kind == TypeKind.U32
        assert len(spec.outputs) == 1
        assert spec.outputs[0].name == "valid"
        assert len(spec.invariants) == 1

    def test_definition(self):
        """Test parsing function definitions."""
        source = """
        spec Test {
          inputs { x: u32 }
          outputs { y: bool }
          define positive(a: u32) := a > 0
          invariant main {
            □ (y ↔ positive(x))
          }
        }
        """
        spec = parse(source)

        assert len(spec.definitions) == 1
        assert spec.definitions[0].name == "positive"
        assert len(spec.definitions[0].params) == 1

    def test_complex_expression(self):
        """Test parsing complex nested expressions."""
        source = """
        spec Test {
          inputs { a: u32, b: u32, c: u32 }
          outputs { ok: bool }
          invariant main {
            □ (ok ↔ (a > 0 ∧ b > 0) → (a + b ≥ c))
          }
        }
        """
        spec = parse(source)
        assert spec.name == "Test"
        assert len(spec.invariants) == 1


class TestCodeGen:
    """Test code generation."""

    def test_simple_tau_output(self):
        """Test generating basic Tau output."""
        source = """
        spec Test {
          inputs { x: u32 }
          outputs { valid: bool }
          invariant main {
            □ (valid ↔ x > 0)
          }
        }
        """
        tau = transpile(source)

        assert "set charvar off" in tau
        assert "i1" in tau  # input mapping
        assert "o1" in tau  # output mapping
        assert "always" in tau
        assert "<->" in tau  # biconditional

    def test_definition_generation(self):
        """Test that definitions are generated correctly."""
        source = """
        spec Test {
          inputs { x: u32 }
          outputs { ok: bool }
          define is_positive(a: u32) := a > 0
          invariant main {
            □ (ok ↔ is_positive(x))
          }
        }
        """
        tau = transpile(source)

        assert "is_positive" in tau
        assert ":=" in tau

    def test_operator_translation(self):
        """Test that logic operators are translated correctly."""
        source = """
        spec Test {
          inputs { a: bool, b: bool, c: bool }
          outputs { ok: bool }
          invariant main {
            □ (ok ↔ (a ∧ b) ∨ (¬c → a))
          }
        }
        """
        tau = transpile(source)

        assert "&&" in tau  # ∧ -> &&
        assert "||" in tau  # ∨ -> ||
        assert "!" in tau   # ¬ -> !
        assert "->" in tau  # → -> ->


class TestEndToEnd:
    """End-to-end transpilation tests."""

    def test_rate_limiter(self):
        """Test transpiling the rate limiter example."""
        examples_dir = Path(__file__).parent.parent / "examples"
        rate_limiter = examples_dir / "rate_limiter_v1.lspec"

        if rate_limiter.exists():
            with open(rate_limiter) as f:
                source = f.read()

            tau = transpile(source)

            # Check key elements
            assert "set charvar off" in tau
            assert "limit" in tau.lower()
            assert "always" in tau

    def test_flash_loan_guard(self):
        """Test transpiling the flash loan guard example."""
        examples_dir = Path(__file__).parent.parent / "examples"
        flash_loan = examples_dir / "flash_loan_guard_v1.lspec"

        if flash_loan.exists():
            with open(flash_loan) as f:
                source = f.read()

            tau = transpile(source)

            # Check key elements
            assert "flash" in tau.lower()
            assert "!" in tau  # negation for safety check


def run_tests():
    """Run all tests without pytest."""
    import traceback

    test_classes = [TestLexer, TestParser, TestCodeGen, TestEndToEnd]
    passed = 0
    failed = 0

    for test_class in test_classes:
        instance = test_class()
        for method_name in dir(instance):
            if method_name.startswith('test_'):
                try:
                    getattr(instance, method_name)()
                    print(f"✓ {test_class.__name__}.{method_name}")
                    passed += 1
                except Exception as e:
                    print(f"✗ {test_class.__name__}.{method_name}")
                    print(f"  {e}")
                    traceback.print_exc()
                    failed += 1

    print()
    print(f"Passed: {passed}, Failed: {failed}")
    return failed == 0


if __name__ == "__main__":
    success = run_tests()
    sys.exit(0 if success else 1)
