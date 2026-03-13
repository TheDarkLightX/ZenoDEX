"""
LogicSpec Lexer (Tokenizer).

Converts LogicSpec source text into a stream of tokens, handling both
Unicode logic symbols and ASCII alternatives.
"""

import re
from dataclasses import dataclass
from typing import Iterator, List, Optional
from enum import Enum, auto


class TokenKind(Enum):
    """Token types."""
    # Structural
    SPEC = auto()
    INPUTS = auto()
    OUTPUTS = auto()
    DEFINE = auto()
    INVARIANT = auto()
    LBRACE = auto()
    RBRACE = auto()
    LPAREN = auto()
    RPAREN = auto()
    LBRACKET = auto()
    RBRACKET = auto()
    COLON = auto()
    COMMA = auto()
    ASSIGN = auto()  # :=

    # Types
    BOOL = auto()
    U16 = auto()
    U32 = auto()
    U64 = auto()

    # Logical operators
    AND = auto()
    OR = auto()
    NOT = auto()
    IMPLIES = auto()
    IFF = auto()

    # Temporal operators
    ALWAYS = auto()
    EVENTUALLY = auto()
    NEXT = auto()

    # Quantifiers
    FORALL = auto()
    EXISTS = auto()

    # Comparison
    EQ = auto()
    NEQ = auto()
    LT = auto()
    LE = auto()
    GT = auto()
    GE = auto()

    # Arithmetic
    PLUS = auto()
    MINUS = auto()
    STAR = auto()
    SLASH = auto()
    PERCENT = auto()

    # Bitwise
    AMPERSAND = auto()
    PIPE = auto()

    # Literals
    INT = auto()
    HEX = auto()
    TRUE = auto()
    FALSE = auto()

    # Identifiers
    IDENT = auto()

    # Meta
    COMMENT = auto()
    MUTABILITY = auto()
    UPDATABLE_PARAMS = auto()

    # Special
    TIME_INDEX = auto()  # [t], [t-1], etc.
    EOF = auto()
    NEWLINE = auto()


@dataclass
class Token:
    """A lexical token."""
    kind: TokenKind
    value: str
    line: int
    column: int


# Token patterns (order matters - longer matches first)
PATTERNS = [
    # Comments (capture for documentation)
    (r'#[^\n]*', TokenKind.COMMENT),
    (r'//[^\n]*', TokenKind.COMMENT),

    # Multi-char operators and keywords (before single-char)
    (r':=', TokenKind.ASSIGN),
    (r'<->', TokenKind.IFF),
    (r'↔', TokenKind.IFF),
    (r'->', TokenKind.IMPLIES),
    (r'→', TokenKind.IMPLIES),
    (r'<=', TokenKind.LE),
    (r'≤', TokenKind.LE),
    (r'>=', TokenKind.GE),
    (r'≥', TokenKind.GE),
    (r'!=', TokenKind.NEQ),
    (r'≠', TokenKind.NEQ),
    (r'&&', TokenKind.AND),
    (r'\|\|', TokenKind.OR),

    # Unicode logic symbols
    (r'∧', TokenKind.AND),
    (r'∨', TokenKind.OR),
    (r'¬', TokenKind.NOT),
    (r'□', TokenKind.ALWAYS),
    (r'◇', TokenKind.EVENTUALLY),
    (r'○', TokenKind.NEXT),
    (r'∀', TokenKind.FORALL),
    (r'∃', TokenKind.EXISTS),
    (r'·', TokenKind.STAR),  # multiplication dot

    # Keywords (must come before IDENT)
    (r'\bspec\b', TokenKind.SPEC),
    (r'\binputs\b', TokenKind.INPUTS),
    (r'\boutputs\b', TokenKind.OUTPUTS),
    (r'\bdefine\b', TokenKind.DEFINE),
    (r'\binvariant\b', TokenKind.INVARIANT),
    (r'\bbool\b', TokenKind.BOOL),
    (r'\bu16\b', TokenKind.U16),
    (r'\bu32\b', TokenKind.U32),
    (r'\bu64\b', TokenKind.U64),
    (r'\band\b', TokenKind.AND),
    (r'\bor\b', TokenKind.OR),
    (r'\bnot\b', TokenKind.NOT),
    (r'\bimplies\b', TokenKind.IMPLIES),
    (r'\biff\b', TokenKind.IFF),
    (r'\balways\b', TokenKind.ALWAYS),
    (r'\beventually\b', TokenKind.EVENTUALLY),
    (r'\bnext\b', TokenKind.NEXT),
    (r'\bforall\b', TokenKind.FORALL),
    (r'\bexists\b', TokenKind.EXISTS),
    (r'\btrue\b', TokenKind.TRUE),
    (r'\bfalse\b', TokenKind.FALSE),
    (r'\bMUTABILITY\b', TokenKind.MUTABILITY),
    (r'\bUPDATABLE_PARAMS\b', TokenKind.UPDATABLE_PARAMS),

    # Time index (e.g., [t], [t-1], [t+1], [0])
    (r'\[\s*t\s*[+-]\s*\d+\s*\]', TokenKind.TIME_INDEX),
    (r'\[\s*t\s*\]', TokenKind.TIME_INDEX),
    (r'\[\s*\d+\s*\]', TokenKind.TIME_INDEX),

    # Literals
    (r'0x[0-9a-fA-F]+', TokenKind.HEX),
    (r'\d+', TokenKind.INT),

    # Single-char tokens
    (r'\{', TokenKind.LBRACE),
    (r'\}', TokenKind.RBRACE),
    (r'\(', TokenKind.LPAREN),
    (r'\)', TokenKind.RPAREN),
    (r'\[', TokenKind.LBRACKET),
    (r'\]', TokenKind.RBRACKET),
    (r':', TokenKind.COLON),
    (r',', TokenKind.COMMA),
    (r'=', TokenKind.EQ),
    (r'<', TokenKind.LT),
    (r'>', TokenKind.GT),
    (r'\+', TokenKind.PLUS),
    (r'-', TokenKind.MINUS),
    (r'\*', TokenKind.STAR),
    (r'/', TokenKind.SLASH),
    (r'%', TokenKind.PERCENT),
    (r'&', TokenKind.AMPERSAND),
    (r'\|', TokenKind.PIPE),
    (r'!', TokenKind.NOT),

    # Identifiers (last, as catch-all for names)
    (r'[a-zA-Z_][a-zA-Z0-9_]*', TokenKind.IDENT),

    # Whitespace (skip, but track newlines)
    (r'\n', TokenKind.NEWLINE),
    (r'[ \t\r]+', None),  # Skip whitespace
]

# Compile patterns
COMPILED_PATTERNS = [(re.compile(p), k) for p, k in PATTERNS]


class LexerError(Exception):
    """Lexer error with location info."""
    def __init__(self, message: str, line: int, column: int):
        super().__init__(f"Line {line}, column {column}: {message}")
        self.line = line
        self.column = column


def tokenize(source: str) -> List[Token]:
    """
    Tokenize LogicSpec source code.

    Args:
        source: The source code string.

    Returns:
        List of tokens.

    Raises:
        LexerError: On invalid input.
    """
    tokens = []
    pos = 0
    line = 1
    line_start = 0

    while pos < len(source):
        matched = False

        for pattern, kind in COMPILED_PATTERNS:
            match = pattern.match(source, pos)
            if match:
                value = match.group()
                column = pos - line_start + 1

                if kind == TokenKind.NEWLINE:
                    line += 1
                    line_start = match.end()
                elif kind is not None:
                    tokens.append(Token(kind, value, line, column))

                pos = match.end()
                matched = True
                break

        if not matched:
            column = pos - line_start + 1
            char = source[pos]
            raise LexerError(f"Unexpected character: {char!r}", line, column)

    # Add EOF token
    tokens.append(Token(TokenKind.EOF, "", line, pos - line_start + 1))

    return tokens


def filter_comments(tokens: List[Token]) -> tuple[List[Token], List[str]]:
    """
    Separate comments from other tokens.

    Returns:
        Tuple of (filtered_tokens, comments).
    """
    filtered = []
    comments = []

    for tok in tokens:
        if tok.kind == TokenKind.COMMENT:
            # Strip comment prefix
            text = tok.value.lstrip('#').lstrip('/').strip()
            if text:
                comments.append(text)
        else:
            filtered.append(tok)

    return filtered, comments
