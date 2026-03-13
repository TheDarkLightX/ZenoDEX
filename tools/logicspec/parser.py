"""
LogicSpec Parser.

Parses a stream of tokens into an Abstract Syntax Tree (AST).
Uses recursive descent with operator precedence climbing.
"""

from typing import List, Optional, Callable
from .lexer import Token, TokenKind, tokenize, filter_comments, LexerError
from .ast import (
    Type, TypeKind, BinOp, UnaryOp, TemporalOp,
    Var, Literal, BinExpr, UnaryExpr, TemporalExpr, Call, Paren, Quantifier,
    Expr, Param, Definition, Invariant, Spec
)


class ParseError(Exception):
    """Parser error with location info."""
    def __init__(self, message: str, token: Token):
        super().__init__(f"Line {token.line}, column {token.column}: {message}")
        self.token = token


class Parser:
    """
    Recursive descent parser for LogicSpec.

    Grammar (simplified):
        spec       := 'spec' IDENT '{' inputs outputs defines* invariants* '}'
        inputs     := 'inputs' '{' param* '}'
        outputs    := 'outputs' '{' param* '}'
        param      := IDENT ':' type
        type       := 'bool' | 'u16' | 'u32' | 'u64'
        define     := 'define' IDENT '(' params ')' ':=' expr
        invariant  := 'invariant' IDENT '{' expr '}'
        expr       := temporal_expr
        temporal   := ('□' | '◇' | '○') expr | iff_expr
        iff_expr   := impl_expr (('↔' | 'iff') impl_expr)*
        impl_expr  := or_expr (('→' | 'implies') or_expr)*
        or_expr    := and_expr (('∨' | 'or') and_expr)*
        and_expr   := cmp_expr (('∧' | 'and') cmp_expr)*
        cmp_expr   := add_expr (('=' | '≠' | '<' | '≤' | '>' | '≥') add_expr)*
        add_expr   := mul_expr (('+' | '-') mul_expr)*
        mul_expr   := unary_expr (('·' | '*' | '/' | '%') unary_expr)*
        unary_expr := ('¬' | 'not' | '-') unary_expr | primary
        primary    := IDENT time_index? | IDENT '(' args ')' | literal | '(' expr ')' | quantifier
        quantifier := ('∀' | '∃') IDENT ':' type '.' expr
    """

    def __init__(self, tokens: List[Token]):
        self.tokens = tokens
        self.pos = 0
        self.comments: List[str] = []

    def current(self) -> Token:
        """Get current token."""
        if self.pos < len(self.tokens):
            return self.tokens[self.pos]
        return self.tokens[-1]  # EOF

    def peek(self, offset: int = 0) -> Token:
        """Peek at token at offset from current."""
        idx = self.pos + offset
        if idx < len(self.tokens):
            return self.tokens[idx]
        return self.tokens[-1]

    def advance(self) -> Token:
        """Consume and return current token."""
        tok = self.current()
        self.pos += 1
        return tok

    def match(self, *kinds: TokenKind) -> bool:
        """Check if current token matches any of the given kinds."""
        return self.current().kind in kinds

    def expect(self, kind: TokenKind, message: str = None) -> Token:
        """Consume token of expected kind, or raise error."""
        tok = self.current()
        if tok.kind != kind:
            msg = message or f"Expected {kind.name}, got {tok.kind.name}"
            raise ParseError(msg, tok)
        return self.advance()

    def parse_type(self) -> Type:
        """Parse a type annotation."""
        tok = self.current()
        if tok.kind == TokenKind.BOOL:
            self.advance()
            return Type(TypeKind.BOOL)
        elif tok.kind == TokenKind.U16:
            self.advance()
            return Type(TypeKind.U16)
        elif tok.kind == TokenKind.U32:
            self.advance()
            return Type(TypeKind.U32)
        elif tok.kind == TokenKind.U64:
            self.advance()
            return Type(TypeKind.U64)
        else:
            raise ParseError(f"Expected type, got {tok.kind.name}", tok)

    def parse_param(self) -> Param:
        """Parse a parameter declaration: name : type"""
        name_tok = self.expect(TokenKind.IDENT, "Expected parameter name")
        self.expect(TokenKind.COLON, "Expected ':' after parameter name")
        typ = self.parse_type()
        return Param(name_tok.value, typ)

    def parse_params_block(self, block_kind: TokenKind) -> List[Param]:
        """Parse inputs { ... } or outputs { ... }"""
        self.expect(block_kind)
        self.expect(TokenKind.LBRACE)

        params = []
        while not self.match(TokenKind.RBRACE, TokenKind.EOF):
            params.append(self.parse_param())
            # Optional comma or newline between params
            if self.match(TokenKind.COMMA):
                self.advance()

        self.expect(TokenKind.RBRACE)
        return params

    def parse_definition(self) -> Definition:
        """Parse a function definition: define name(params) := expr"""
        self.expect(TokenKind.DEFINE)
        name_tok = self.expect(TokenKind.IDENT, "Expected function name")

        # Parse parameters
        self.expect(TokenKind.LPAREN)
        params = []
        if not self.match(TokenKind.RPAREN):
            params.append(self.parse_param())
            while self.match(TokenKind.COMMA):
                self.advance()
                params.append(self.parse_param())
        self.expect(TokenKind.RPAREN)

        # Optional return type
        return_type = None
        if self.match(TokenKind.COLON):
            self.advance()
            return_type = self.parse_type()

        self.expect(TokenKind.ASSIGN, "Expected ':=' in definition")
        body = self.parse_expr()

        return Definition(name_tok.value, params, body, return_type)

    def parse_invariant(self) -> Invariant:
        """Parse an invariant block: invariant name { expr }"""
        self.expect(TokenKind.INVARIANT)
        name_tok = self.expect(TokenKind.IDENT, "Expected invariant name")
        self.expect(TokenKind.LBRACE)
        body = self.parse_expr()
        self.expect(TokenKind.RBRACE)
        return Invariant(name_tok.value, body)

    def parse_expr(self) -> Expr:
        """Parse an expression (entry point)."""
        return self.parse_temporal()

    def parse_temporal(self) -> Expr:
        """Parse temporal operators (□, ◇, ○)."""
        if self.match(TokenKind.ALWAYS):
            self.advance()
            operand = self.parse_temporal()
            return TemporalExpr(TemporalOp.ALWAYS, operand)
        elif self.match(TokenKind.EVENTUALLY):
            self.advance()
            operand = self.parse_temporal()
            return TemporalExpr(TemporalOp.EVENTUALLY, operand)
        elif self.match(TokenKind.NEXT):
            self.advance()
            operand = self.parse_temporal()
            return TemporalExpr(TemporalOp.NEXT, operand)
        else:
            return self.parse_iff()

    def parse_iff(self) -> Expr:
        """Parse biconditional (↔, iff)."""
        left = self.parse_implies()
        while self.match(TokenKind.IFF):
            self.advance()
            right = self.parse_implies()
            left = BinExpr(BinOp.IFF, left, right)
        return left

    def parse_implies(self) -> Expr:
        """Parse implication (→, implies)."""
        left = self.parse_or()
        while self.match(TokenKind.IMPLIES):
            self.advance()
            right = self.parse_or()
            left = BinExpr(BinOp.IMPLIES, left, right)
        return left

    def parse_or(self) -> Expr:
        """Parse disjunction (∨, or)."""
        left = self.parse_and()
        while self.match(TokenKind.OR):
            self.advance()
            right = self.parse_and()
            left = BinExpr(BinOp.OR, left, right)
        return left

    def parse_and(self) -> Expr:
        """Parse conjunction (∧, and)."""
        left = self.parse_cmp()
        while self.match(TokenKind.AND):
            self.advance()
            right = self.parse_cmp()
            left = BinExpr(BinOp.AND, left, right)
        return left

    def parse_cmp(self) -> Expr:
        """Parse comparison operators."""
        left = self.parse_add()
        while self.match(TokenKind.EQ, TokenKind.NEQ, TokenKind.LT,
                         TokenKind.LE, TokenKind.GT, TokenKind.GE):
            tok = self.advance()
            op = {
                TokenKind.EQ: BinOp.EQ,
                TokenKind.NEQ: BinOp.NEQ,
                TokenKind.LT: BinOp.LT,
                TokenKind.LE: BinOp.LE,
                TokenKind.GT: BinOp.GT,
                TokenKind.GE: BinOp.GE,
            }[tok.kind]
            right = self.parse_add()
            left = BinExpr(op, left, right)
        return left

    def parse_add(self) -> Expr:
        """Parse addition and subtraction."""
        left = self.parse_mul()
        while self.match(TokenKind.PLUS, TokenKind.MINUS):
            tok = self.advance()
            op = BinOp.ADD if tok.kind == TokenKind.PLUS else BinOp.SUB
            right = self.parse_mul()
            left = BinExpr(op, left, right)
        return left

    def parse_mul(self) -> Expr:
        """Parse multiplication, division, modulo."""
        left = self.parse_unary()
        while self.match(TokenKind.STAR, TokenKind.SLASH, TokenKind.PERCENT):
            tok = self.advance()
            op = {
                TokenKind.STAR: BinOp.MUL,
                TokenKind.SLASH: BinOp.DIV,
                TokenKind.PERCENT: BinOp.MOD,
            }[tok.kind]
            right = self.parse_unary()
            left = BinExpr(op, left, right)
        return left

    def parse_unary(self) -> Expr:
        """Parse unary operators (¬, not, -)."""
        if self.match(TokenKind.NOT):
            self.advance()
            operand = self.parse_unary()
            return UnaryExpr(UnaryOp.NOT, operand)
        elif self.match(TokenKind.MINUS):
            self.advance()
            operand = self.parse_unary()
            return UnaryExpr(UnaryOp.NEG, operand)
        else:
            return self.parse_primary()

    def parse_primary(self) -> Expr:
        """Parse primary expressions."""
        tok = self.current()

        # Parenthesized expression
        if tok.kind == TokenKind.LPAREN:
            self.advance()
            inner = self.parse_expr()
            self.expect(TokenKind.RPAREN)
            return Paren(inner)

        # Quantifier
        if tok.kind in (TokenKind.FORALL, TokenKind.EXISTS):
            return self.parse_quantifier()

        # Boolean literals
        if tok.kind == TokenKind.TRUE:
            self.advance()
            return Literal(True, Type(TypeKind.BOOL))
        if tok.kind == TokenKind.FALSE:
            self.advance()
            return Literal(False, Type(TypeKind.BOOL))

        # Integer literals
        if tok.kind == TokenKind.INT:
            self.advance()
            return Literal(int(tok.value))
        if tok.kind == TokenKind.HEX:
            self.advance()
            return Literal(int(tok.value, 16))

        # Identifier (variable or function call)
        if tok.kind == TokenKind.IDENT:
            name = self.advance().value

            # Check for function call
            if self.match(TokenKind.LPAREN):
                self.advance()
                args = []
                if not self.match(TokenKind.RPAREN):
                    args.append(self.parse_expr())
                    while self.match(TokenKind.COMMA):
                        self.advance()
                        args.append(self.parse_expr())
                self.expect(TokenKind.RPAREN)
                return Call(name, args)

            # Check for time index
            time_index = None
            if self.match(TokenKind.TIME_INDEX):
                time_tok = self.advance()
                # Extract the index from [t], [t-1], [0], etc.
                time_index = time_tok.value.strip("[]").strip()

            return Var(name, time_index)

        raise ParseError(f"Unexpected token in expression: {tok.kind.name}", tok)

    def parse_quantifier(self) -> Quantifier:
        """Parse a quantified expression: ∀x: T. expr or ∃x: T. expr"""
        tok = self.advance()
        kind = "forall" if tok.kind == TokenKind.FORALL else "exists"

        var_tok = self.expect(TokenKind.IDENT, "Expected variable name in quantifier")
        self.expect(TokenKind.COLON, "Expected ':' after quantifier variable")
        var_type = self.parse_type()

        # Expect a separator (. or :)
        if self.match(TokenKind.COLON):
            self.advance()
        # Also accept implicit continuation

        body = self.parse_expr()
        return Quantifier(kind, var_tok.value, var_type, body)

    def parse_spec(self) -> Spec:
        """Parse a complete specification."""
        self.expect(TokenKind.SPEC, "Expected 'spec' keyword")
        name_tok = self.expect(TokenKind.IDENT, "Expected spec name")
        self.expect(TokenKind.LBRACE)

        # Parse sections in any order
        inputs = []
        outputs = []
        definitions = []
        invariants = []
        mutability = "IMMUTABLE"
        updatable_params = []

        while not self.match(TokenKind.RBRACE, TokenKind.EOF):
            if self.match(TokenKind.INPUTS):
                inputs = self.parse_params_block(TokenKind.INPUTS)
            elif self.match(TokenKind.OUTPUTS):
                outputs = self.parse_params_block(TokenKind.OUTPUTS)
            elif self.match(TokenKind.DEFINE):
                definitions.append(self.parse_definition())
            elif self.match(TokenKind.INVARIANT):
                invariants.append(self.parse_invariant())
            elif self.match(TokenKind.MUTABILITY):
                self.advance()
                self.expect(TokenKind.COLON)
                mut_tok = self.expect(TokenKind.IDENT)
                mutability = mut_tok.value
            elif self.match(TokenKind.UPDATABLE_PARAMS):
                self.advance()
                self.expect(TokenKind.COLON)
                self.expect(TokenKind.LBRACKET)
                while not self.match(TokenKind.RBRACKET):
                    p = self.expect(TokenKind.IDENT)
                    updatable_params.append(p.value)
                    if self.match(TokenKind.COMMA):
                        self.advance()
                self.expect(TokenKind.RBRACKET)
            else:
                raise ParseError(
                    f"Unexpected token in spec body: {self.current().kind.name}",
                    self.current()
                )

        self.expect(TokenKind.RBRACE)

        return Spec(
            name=name_tok.value,
            inputs=inputs,
            outputs=outputs,
            definitions=definitions,
            invariants=invariants,
            comments=self.comments,
            mutability=mutability,
            updatable_params=updatable_params,
        )


def parse(source: str) -> Spec:
    """
    Parse LogicSpec source code into an AST.

    Args:
        source: The source code string.

    Returns:
        Parsed Spec AST.

    Raises:
        ParseError: On syntax errors.
        LexerError: On invalid tokens.
    """
    tokens = tokenize(source)
    tokens, comments = filter_comments(tokens)

    parser = Parser(tokens)
    parser.comments = comments

    return parser.parse_spec()
