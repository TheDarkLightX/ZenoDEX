"""
LogicSpec: Standard Logic to Tau Language Transpiler

This module provides a transpiler from standard mathematical logic notation
to Tau Language specifications. It enables LLMs and mathematicians to write
formal specifications using familiar symbols (∧, ∨, →, □) which are then
compiled to valid Tau syntax.
"""

__version__ = "0.1.0"

from .parser import parse
from .codegen import generate_tau
from .transpiler import transpile

__all__ = ["parse", "generate_tau", "transpile", "__version__"]
