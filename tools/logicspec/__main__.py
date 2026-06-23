#!/usr/bin/env python3
"""
LogicSpec CLI - Command-line interface for the transpiler.

Usage:
    python -m logicspec compile input.lspec [-o output.tau] [--validate]
    python -m logicspec check input.lspec
    python -m logicspec status
    python -m logicspec version

LICENSING:
This tool generates Tau-style output. To validate and run the output,
you must obtain Tau Language separately from https://github.com/IDNI/tau-lang

VALIDATION:
To enable output validation, you need:
1. tau.tgf grammar file from tau-lang repo
2. Built tau binary

Set environment variables:
  TAU_TGF_PATH=/path/to/tau.tgf
  TAU_BINARY_PATH=/path/to/tau
"""

import argparse
import sys
from pathlib import Path

from . import __version__
from .transpiler import transpile, transpile_file, TranspileError
from .parser import parse, ParseError
from .lexer import LexerError
from .grammar_loader import GrammarLoader


def cmd_compile(args):
    """Compile LogicSpec to Tau-style output."""
    input_path = Path(args.input)

    if not input_path.exists():
        print(f"Error: File not found: {input_path}", file=sys.stderr)
        return 1

    # Determine output path
    if args.output:
        output_path = args.output
    else:
        output_path = input_path.with_suffix('.tau')

    try:
        tau_code = transpile_file(str(input_path), str(output_path))

        if args.stdout:
            print(tau_code)
        else:
            print(f"Compiled: {input_path} -> {output_path}")

        # Validate if requested
        if args.validate:
            loader = GrammarLoader()
            if not loader.available:
                print("Warning: Validation unavailable (tau binary not found)", file=sys.stderr)
                print("  Set TAU_BINARY_PATH or build tau-lang", file=sys.stderr)
                return 0

            valid, error = loader.validate(tau_code)
            if valid:
                print("Validation: PASSED")
            else:
                print(f"Validation: FAILED", file=sys.stderr)
                print(f"  {error}", file=sys.stderr)
                return 1

        return 0

    except TranspileError as e:
        print(f"Error: {e}", file=sys.stderr)
        return 1


def cmd_status(args):
    """Show grammar/validation status."""
    loader = GrammarLoader()
    print("LogicSpec Transpiler Status")
    print("=" * 40)
    print(loader.get_status())
    return 0


def cmd_check(args):
    """Check LogicSpec syntax without generating output."""
    input_path = Path(args.input)

    if not input_path.exists():
        print(f"Error: File not found: {input_path}", file=sys.stderr)
        return 1

    try:
        with open(input_path, 'r', encoding='utf-8') as f:
            source = f.read()

        spec = parse(source)

        print(f"✓ {input_path}")
        print(f"  Spec: {spec.name}")
        print(f"  Inputs: {len(spec.inputs)}")
        print(f"  Outputs: {len(spec.outputs)}")
        print(f"  Definitions: {len(spec.definitions)}")
        print(f"  Invariants: {len(spec.invariants)}")

        return 0

    except (ParseError, LexerError) as e:
        print(f"✗ {input_path}", file=sys.stderr)
        print(f"  {e}", file=sys.stderr)
        return 1


def cmd_version(args):
    """Print version information."""
    print(f"LogicSpec Transpiler v{__version__}")
    print()
    print("This tool generates Tau Language syntax as text output.")
    print("To execute .tau files, obtain Tau Language from:")
    print("  https://github.com/IDNI/tau-lang")
    return 0


def cmd_symbols(args):
    """Print supported logic symbols."""
    print("LogicSpec Symbol Reference")
    print("=" * 50)
    print()
    print("LOGICAL OPERATORS:")
    print("  ∧  and      Conjunction (both true)")
    print("  ∨  or       Disjunction (at least one true)")
    print("  ¬  not  !   Negation (inverts truth)")
    print("  →  implies  Implication (if...then)")
    print("  ↔  iff      Biconditional (if and only if)")
    print()
    print("TEMPORAL OPERATORS:")
    print("  □  always   At all times")
    print("  ◇  eventually  At some future time")
    print("  ○  next     At the next time step")
    print()
    print("QUANTIFIERS:")
    print("  ∀  forall   For all")
    print("  ∃  exists   There exists")
    print()
    print("COMPARISON:")
    print("  =           Equal")
    print("  ≠  !=       Not equal")
    print("  <           Less than")
    print("  ≤  <=       Less than or equal")
    print("  >           Greater than")
    print("  ≥  >=       Greater than or equal")
    print()
    print("ARITHMETIC:")
    print("  +           Addition")
    print("  -           Subtraction")
    print("  ·  *        Multiplication")
    print("  /           Division")
    print("  %           Modulo")
    print()
    print("TYPES:")
    print("  bool        Boolean (true/false)")
    print("  u16         16-bit unsigned integer")
    print("  u32         32-bit unsigned integer")
    print("  u64         64-bit unsigned integer")
    return 0


def main():
    parser = argparse.ArgumentParser(
        description="LogicSpec: Standard Logic to Tau Language Transpiler",
        epilog="For more info: https://github.com/IDNI/tau-lang (Tau Language)"
    )

    subparsers = parser.add_subparsers(dest='command', help='Commands')

    # compile command
    compile_parser = subparsers.add_parser(
        'compile',
        help='Compile LogicSpec to Tau Language'
    )
    compile_parser.add_argument('input', help='Input .lspec file')
    compile_parser.add_argument(
        '-o', '--output',
        help='Output .tau file (default: input with .tau extension)'
    )
    compile_parser.add_argument(
        '--stdout',
        action='store_true',
        help='Also print output to stdout'
    )
    compile_parser.set_defaults(func=cmd_compile)

    # check command
    check_parser = subparsers.add_parser(
        'check',
        help='Check LogicSpec syntax'
    )
    check_parser.add_argument('input', help='Input .lspec file')
    check_parser.set_defaults(func=cmd_check)

    # version command
    version_parser = subparsers.add_parser(
        'version',
        help='Print version information'
    )
    version_parser.set_defaults(func=cmd_version)

    # symbols command
    symbols_parser = subparsers.add_parser(
        'symbols',
        help='Print supported logic symbols'
    )
    symbols_parser.set_defaults(func=cmd_symbols)

    args = parser.parse_args()

    if args.command is None:
        parser.print_help()
        return 1

    return args.func(args)


if __name__ == '__main__':
    sys.exit(main())
