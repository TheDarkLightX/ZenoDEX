"""
LogicSpec Transpiler - Main entry point.

This module provides the high-level transpile() function that converts
LogicSpec source code to Tau Language output.

LICENSING NOTE:
This transpiler generates Tau Language syntax as text output.
It does NOT include, distribute, or require any Tau Language source code,
binaries, grammar files, or other copyrighted materials.

To actually execute the generated .tau files, users must:
1. Obtain Tau Language from the official source (https://github.com/IDNI/tau-lang)
2. Build and install it according to their license terms
3. Run the generated .tau files with the Tau runtime

This transpiler is public domain / MIT licensed.
"""

from typing import Optional
from .parser import parse, ParseError
from .lexer import LexerError
from .codegen import generate_tau, CodeGenError


class TranspileError(Exception):
    """Error during transpilation."""
    pass


def transpile(source: str, *, validate: bool = True) -> str:
    """
    Transpile LogicSpec source code to Tau Language.

    Args:
        source: LogicSpec source code string.
        validate: Whether to perform additional validation (default True).

    Returns:
        Tau Language source code string.

    Raises:
        TranspileError: On any error during transpilation.

    Example:
        >>> source = '''
        ... spec Example {
        ...   inputs { x: u32 }
        ...   outputs { valid: bool }
        ...   invariant main {
        ...     □ (valid ↔ x > 0)
        ...   }
        ... }
        ... '''
        >>> tau_code = transpile(source)
        >>> print(tau_code)
    """
    try:
        # Parse LogicSpec to AST
        spec = parse(source)

        # Validate if requested
        if validate:
            _validate_spec(spec)

        # Generate Tau code
        tau_code = generate_tau(spec)

        return tau_code

    except (ParseError, LexerError) as e:
        raise TranspileError(f"Parse error: {e}") from e
    except CodeGenError as e:
        raise TranspileError(f"Code generation error: {e}") from e


def _validate_spec(spec) -> None:
    """Perform semantic validation on the spec."""
    # Check that all outputs are defined in invariants
    # (soft validation - just warnings for now)

    # Check for undefined function calls
    defined_funcs = {d.name for d in spec.definitions}

    def check_calls(expr):
        from .ast import Call, BinExpr, UnaryExpr, TemporalExpr, Paren, Quantifier

        if isinstance(expr, Call):
            if expr.name not in defined_funcs:
                # Could be a built-in or external - just note it
                pass
            for arg in expr.args:
                check_calls(arg)
        elif isinstance(expr, BinExpr):
            check_calls(expr.left)
            check_calls(expr.right)
        elif isinstance(expr, UnaryExpr):
            check_calls(expr.operand)
        elif isinstance(expr, TemporalExpr):
            check_calls(expr.operand)
        elif isinstance(expr, Paren):
            check_calls(expr.inner)
        elif isinstance(expr, Quantifier):
            check_calls(expr.body)

    for inv in spec.invariants:
        check_calls(inv.body)


def transpile_file(input_path: str, output_path: Optional[str] = None) -> str:
    """
    Transpile a LogicSpec file to Tau Language.

    Args:
        input_path: Path to .lspec file.
        output_path: Optional path for .tau output. If None, returns the code.

    Returns:
        Generated Tau code (also written to output_path if provided).
    """
    with open(input_path, 'r', encoding='utf-8') as f:
        source = f.read()

    tau_code = transpile(source)

    if output_path:
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(tau_code)

    return tau_code
