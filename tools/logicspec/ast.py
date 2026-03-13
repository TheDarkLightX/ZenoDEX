"""
LogicSpec Abstract Syntax Tree definitions.

Defines the node types for the parsed LogicSpec language.
"""

from dataclasses import dataclass, field
from typing import List, Optional, Union
from enum import Enum, auto


class TypeKind(Enum):
    """Primitive type kinds in LogicSpec."""
    BOOL = auto()   # Boolean (maps to sbf)
    U16 = auto()    # 16-bit unsigned (maps to bv[16])
    U32 = auto()    # 32-bit unsigned (maps to bv[32])
    U64 = auto()    # 64-bit unsigned (maps to bv[64])


@dataclass
class Type:
    """A type annotation."""
    kind: TypeKind

    def to_tau(self) -> str:
        """Convert to Tau type syntax."""
        return {
            TypeKind.BOOL: "sbf",
            TypeKind.U16: "bv[16]",
            TypeKind.U32: "bv[32]",
            TypeKind.U64: "bv[64]",
        }[self.kind]

    def bit_width(self) -> int:
        """Return the bit width of the type."""
        return {
            TypeKind.BOOL: 1,
            TypeKind.U16: 16,
            TypeKind.U32: 32,
            TypeKind.U64: 64,
        }[self.kind]


class BinOp(Enum):
    """Binary operators."""
    # Logical
    AND = "∧"
    OR = "∨"
    IMPLIES = "→"
    IFF = "↔"
    # Comparison
    EQ = "="
    NEQ = "≠"
    LT = "<"
    LE = "≤"
    GT = ">"
    GE = "≥"
    # Arithmetic
    ADD = "+"
    SUB = "-"
    MUL = "·"
    DIV = "/"
    MOD = "%"
    # Bitwise
    BAND = "&"
    BOR = "|"

    def to_tau(self) -> str:
        """Convert to Tau operator syntax."""
        return {
            BinOp.AND: "&&",
            BinOp.OR: "||",
            BinOp.IMPLIES: "->",
            BinOp.IFF: "<->",
            BinOp.EQ: "=",
            BinOp.NEQ: "!=",
            BinOp.LT: "<",
            BinOp.LE: "<=",
            BinOp.GT: ">",
            BinOp.GE: ">=",
            BinOp.ADD: "+",
            BinOp.SUB: "-",
            BinOp.MUL: "*",
            BinOp.DIV: "/",
            BinOp.MOD: "%",
            BinOp.BAND: "&",
            BinOp.BOR: "|",
        }[self]


class UnaryOp(Enum):
    """Unary operators."""
    NOT = "¬"
    NEG = "-"

    def to_tau(self) -> str:
        """Convert to Tau operator syntax."""
        return {
            UnaryOp.NOT: "!",
            UnaryOp.NEG: "-",
        }[self]


class TemporalOp(Enum):
    """Temporal operators."""
    ALWAYS = "□"      # G (globally)
    EVENTUALLY = "◇"  # F (finally)
    NEXT = "○"        # X (next)

    def to_tau(self) -> str:
        """Convert to Tau temporal syntax."""
        return {
            TemporalOp.ALWAYS: "always",
            TemporalOp.EVENTUALLY: "eventually",
            TemporalOp.NEXT: "next",
        }[self]


# Expression types
@dataclass
class Var:
    """Variable reference."""
    name: str
    time_index: Optional[str] = None  # e.g., "t", "t-1"


@dataclass
class Literal:
    """Literal value (integer or boolean)."""
    value: Union[int, bool]
    type_hint: Optional[Type] = None


@dataclass
class BinExpr:
    """Binary expression."""
    op: BinOp
    left: "Expr"
    right: "Expr"


@dataclass
class UnaryExpr:
    """Unary expression."""
    op: UnaryOp
    operand: "Expr"


@dataclass
class TemporalExpr:
    """Temporal expression (□, ◇, ○)."""
    op: TemporalOp
    operand: "Expr"


@dataclass
class Call:
    """Function/predicate call."""
    name: str
    args: List["Expr"]


@dataclass
class Paren:
    """Parenthesized expression."""
    inner: "Expr"


@dataclass
class Quantifier:
    """Quantified expression (∀, ∃)."""
    kind: str  # "forall" or "exists"
    var: str
    var_type: Type
    body: "Expr"


# Type alias for any expression
Expr = Union[Var, Literal, BinExpr, UnaryExpr, TemporalExpr, Call, Paren, Quantifier]


# Top-level declarations
@dataclass
class Param:
    """Parameter declaration (input or output)."""
    name: str
    type: Type


@dataclass
class Definition:
    """Function/predicate definition."""
    name: str
    params: List[Param]
    body: Expr
    return_type: Optional[Type] = None


@dataclass
class Invariant:
    """Named invariant block."""
    name: str
    body: Expr
    comment: Optional[str] = None


@dataclass
class Spec:
    """Complete specification."""
    name: str
    inputs: List[Param]
    outputs: List[Param]
    definitions: List[Definition]
    invariants: List[Invariant]
    comments: List[str] = field(default_factory=list)
    mutability: str = "IMMUTABLE"  # or "UPDATABLE"
    updatable_params: List[str] = field(default_factory=list)
