"""
LogicSpec Code Generator.

Generates Tau Language code from the LogicSpec AST.
"""

from typing import Dict, List, Optional, Set
from .ast import (
    Type, TypeKind, BinOp, UnaryOp, TemporalOp,
    Var, Literal, BinExpr, UnaryExpr, TemporalExpr, Call, Paren, Quantifier,
    Expr, Param, Definition, Invariant, Spec
)


class CodeGenError(Exception):
    """Code generation error."""
    pass


class TauCodeGen:
    """
    Generates Tau Language code from LogicSpec AST.

    Handles:
    - Type mapping (u32 -> bv[32], bool -> sbf)
    - Operator translation (∧ -> &&, → -> ->)
    - Input/output stream mapping (inputs -> i1, i2, ...; outputs -> o1, o2, ...)
    - Literal encoding (10000 -> { #x00002710 }:bv[32])
    - Time indexing (x[t] -> x[t]:bv[32])
    """

    def __init__(self, spec: Spec):
        self.spec = spec
        self.input_map: Dict[str, tuple[int, Type]] = {}   # name -> (index, type)
        self.output_map: Dict[str, tuple[int, Type]] = {}  # name -> (index, type)
        self.definitions: Dict[str, Definition] = {}
        self.used_defs: Set[str] = set()
        self.current_params: Dict[str, Type] = {}  # Current function's parameter types

        # Build mappings
        for i, param in enumerate(spec.inputs, start=1):
            self.input_map[param.name] = (i, param.type)

        for i, param in enumerate(spec.outputs, start=1):
            self.output_map[param.name] = (i, param.type)

        for defn in spec.definitions:
            self.definitions[defn.name] = defn

    def int_to_hex(self, value: int, bit_width: int) -> str:
        """Convert integer to Tau hex literal."""
        if bit_width == 16:
            fmt = "#x{:04X}"
        elif bit_width == 32:
            fmt = "#x{:08X}"
        elif bit_width == 64:
            fmt = "#x{:016X}"
        else:
            fmt = "#x{:X}"

        return "{{ {} }}".format(fmt.format(value & ((1 << bit_width) - 1)))

    def gen_literal(self, lit: Literal, context_type: Optional[Type] = None) -> str:
        """Generate a literal value."""
        if isinstance(lit.value, bool):
            return "1:sbf" if lit.value else "0:sbf"

        # Integer literal
        value = lit.value
        typ = lit.type_hint or context_type or Type(TypeKind.U32)
        bit_width = typ.bit_width()

        return f"{self.int_to_hex(value, bit_width)}:{typ.to_tau()}"

    def gen_var(self, var: Var, *, in_iff_lhs: bool = False) -> str:
        """
        Generate a variable reference.

        Args:
            var: The variable AST node.
            in_iff_lhs: If True, this var is on the LHS of a biconditional and
                        needs special handling for outputs (o1[t]:sbf = 1:sbf).
        """
        name = var.name
        time_idx = var.time_index or "t"

        # Check if it's an input
        if name in self.input_map:
            idx, typ = self.input_map[name]
            if typ.kind == TypeKind.BOOL:
                # Boolean inputs need = 1:sbf comparison
                return f"(i{idx}[{time_idx}]:sbf = 1:sbf)"
            return f"i{idx}[{time_idx}]:{typ.to_tau()}"

        # Check if it's an output
        if name in self.output_map:
            idx, typ = self.output_map[name]
            if typ.kind == TypeKind.BOOL:
                if in_iff_lhs:
                    # Output on LHS of <-> needs = 1:sbf
                    return f"o{idx}[{time_idx}]:sbf = 1:sbf"
                else:
                    return f"o{idx}[{time_idx}]:sbf"
            return f"o{idx}[{time_idx}]:{typ.to_tau()}"

        # Local variable or parameter (no type suffix in local context)
        return name

    def gen_call(self, call: Call) -> str:
        """Generate a function call."""
        self.used_defs.add(call.name)
        args = ", ".join(self.gen_expr(arg) for arg in call.args)
        return f"{call.name}({args})"

    def gen_binary(self, expr: BinExpr) -> str:
        """Generate a binary expression."""
        # Special handling for biconditional with output on LHS
        if expr.op == BinOp.IFF and isinstance(expr.left, Var):
            left = self.gen_var(expr.left, in_iff_lhs=True)
        else:
            left = self.gen_expr(expr.left)
        right = self.gen_expr(expr.right)
        op = expr.op.to_tau()
        return f"({left} {op} {right})"

    def gen_unary(self, expr: UnaryExpr) -> str:
        """Generate a unary expression."""
        operand = self.gen_expr(expr.operand)
        op = expr.op.to_tau()
        return f"{op}({operand})"

    def gen_temporal(self, expr: TemporalExpr) -> str:
        """Generate a temporal expression."""
        operand = self.gen_expr(expr.operand)
        if expr.op == TemporalOp.ALWAYS:
            return f"always\n  {operand}"
        elif expr.op == TemporalOp.EVENTUALLY:
            # Tau doesn't have direct 'eventually' - may need to handle specially
            return f"eventually {operand}"
        elif expr.op == TemporalOp.NEXT:
            return f"next {operand}"
        return operand

    def gen_paren(self, expr: Paren) -> str:
        """Generate a parenthesized expression."""
        inner = self.gen_expr(expr.inner)
        return f"({inner})"

    def gen_quantifier(self, expr: Quantifier) -> str:
        """Generate a quantified expression (expand to finite form if needed)."""
        # Tau handles quantifiers implicitly through the temporal logic
        # For now, just generate the body
        # TODO: proper quantifier expansion
        return self.gen_expr(expr.body)

    def gen_expr(self, expr: Expr) -> str:
        """Generate code for any expression."""
        if isinstance(expr, Var):
            return self.gen_var(expr)
        elif isinstance(expr, Literal):
            return self.gen_literal(expr)
        elif isinstance(expr, BinExpr):
            return self.gen_binary(expr)
        elif isinstance(expr, UnaryExpr):
            return self.gen_unary(expr)
        elif isinstance(expr, TemporalExpr):
            return self.gen_temporal(expr)
        elif isinstance(expr, Call):
            return self.gen_call(expr)
        elif isinstance(expr, Paren):
            return self.gen_paren(expr)
        elif isinstance(expr, Quantifier):
            return self.gen_quantifier(expr)
        else:
            raise CodeGenError(f"Unknown expression type: {type(expr)}")

    def gen_definition(self, defn: Definition) -> str:
        """Generate a function definition."""
        params = ", ".join(
            f"{p.name} : {p.type.to_tau()}" for p in defn.params
        )
        body = self.gen_expr(defn.body)
        return f"{defn.name}({params}) := {body}."

    def gen_stream_mapping_comment(self) -> str:
        """Generate the stream mapping comment block."""
        lines = ["# Stream mapping:"]

        for name, (idx, typ) in self.input_map.items():
            lines.append(f"# i{idx} = {name}")

        for name, (idx, typ) in self.output_map.items():
            lines.append(f"# o{idx} = {name}")

        return "\n".join(lines)

    def gen_header_comment(self) -> str:
        """Generate the header comment block."""
        lines = [f"# {self.spec.name} (generated from LogicSpec)"]

        if self.spec.mutability != "IMMUTABLE":
            lines.append(f"# MUTABILITY: {self.spec.mutability}")

        if self.spec.updatable_params:
            params = ", ".join(self.spec.updatable_params)
            lines.append(f"# UPDATABLE_PARAMS: {params}")

        # Add original comments
        for comment in self.spec.comments:
            lines.append(f"# {comment}")

        return "\n".join(lines)

    def gen_invariant(self, inv: Invariant) -> str:
        """Generate an invariant."""
        body = self.gen_expr(inv.body)
        comment = f"# @section: {inv.name}"
        return f"{comment}\n  {body}"

    def generate(self) -> str:
        """Generate complete Tau specification."""
        sections = []

        # Header
        sections.append(self.gen_header_comment())
        sections.append("")
        sections.append(self.gen_stream_mapping_comment())
        sections.append("")

        # Tau boilerplate
        sections.append("set charvar off")
        sections.append("")

        # First pass: collect ALL used definitions by traversing invariants and definitions
        # We need to find the transitive closure of dependencies
        def collect_all_deps(expr: Expr, visited: set) -> None:
            """Recursively collect all definition names used in an expression."""
            if isinstance(expr, Call):
                if expr.name not in visited and expr.name in self.definitions:
                    visited.add(expr.name)
                    # Also collect deps from the definition body
                    collect_all_deps(self.definitions[expr.name].body, visited)
                for arg in expr.args:
                    collect_all_deps(arg, visited)
            elif isinstance(expr, BinExpr):
                collect_all_deps(expr.left, visited)
                collect_all_deps(expr.right, visited)
            elif isinstance(expr, UnaryExpr):
                collect_all_deps(expr.operand, visited)
            elif isinstance(expr, TemporalExpr):
                collect_all_deps(expr.operand, visited)
            elif isinstance(expr, Paren):
                collect_all_deps(expr.inner, visited)
            elif isinstance(expr, Quantifier):
                collect_all_deps(expr.body, visited)

        all_used_defs: set = set()
        for inv in self.spec.invariants:
            collect_all_deps(inv.body, all_used_defs)

        # Generate definitions in dependency order using simple iteration
        # Since we have the full set, just generate each once
        generated_defs: set = set()
        def gen_def_recursive(name: str, in_progress: set):
            if name in generated_defs or name not in self.definitions:
                return
            if name in in_progress:
                # Circular dependency - just skip for now
                return
            in_progress.add(name)
            defn = self.definitions[name]

            # First generate dependencies from this definition's body
            local_deps: set = set()
            collect_all_deps(defn.body, local_deps)
            for dep in local_deps:
                if dep != name:
                    gen_def_recursive(dep, in_progress)

            # Then generate this definition
            sections.append(self.gen_definition(defn))
            generated_defs.add(name)
            in_progress.discard(name)

        for name in all_used_defs:
            gen_def_recursive(name, set())

        if generated_defs:
            sections.append("")

        # Generate invariants (wrapped in 'always')
        if self.spec.invariants:
            # Check if any invariant has temporal operator at top level
            has_temporal = any(
                isinstance(inv.body, TemporalExpr)
                for inv in self.spec.invariants
            )

            if has_temporal:
                # Temporal operator already present
                for inv in self.spec.invariants:
                    sections.append(self.gen_invariant(inv))
            else:
                # Wrap all invariants in 'always'
                inv_bodies = []
                for inv in self.spec.invariants:
                    comment = f"  # @section: {inv.name}"
                    body = self.gen_expr(inv.body)
                    inv_bodies.append(f"{comment}\n  {body}")

                sections.append("always")
                sections.append(" &&\n".join(inv_bodies) + ".")

        return "\n".join(sections) + "\n"

    def _collect_used_defs(self, expr: Expr) -> None:
        """Recursively collect used definition names."""
        if isinstance(expr, Call):
            self.used_defs.add(expr.name)
            for arg in expr.args:
                self._collect_used_defs(arg)
        elif isinstance(expr, BinExpr):
            self._collect_used_defs(expr.left)
            self._collect_used_defs(expr.right)
        elif isinstance(expr, UnaryExpr):
            self._collect_used_defs(expr.operand)
        elif isinstance(expr, TemporalExpr):
            self._collect_used_defs(expr.operand)
        elif isinstance(expr, Paren):
            self._collect_used_defs(expr.inner)
        elif isinstance(expr, Quantifier):
            self._collect_used_defs(expr.body)


def generate_tau(spec: Spec) -> str:
    """
    Generate Tau Language code from a LogicSpec AST.

    Args:
        spec: The parsed specification.

    Returns:
        Tau Language source code.
    """
    codegen = TauCodeGen(spec)
    return codegen.generate()
