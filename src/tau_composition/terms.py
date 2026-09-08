"""Immutable Boolean terms and a bounded parser for native Tau BA terms.

``parse_native_term`` accepts only a Boolean-algebra term right-hand side.  The
caller must extract it from any LGRS assignment before parsing.  It recognizes
the native LGRS forms needed by the composition research, including implicit
meet, postfix complement, braces as grouping, and an ``:sbf`` type suffix.
It deliberately does not parse Tau statements, streams, quantifiers, or other
Tau language surfaces.
"""

from __future__ import annotations

import json
import re
from collections.abc import Mapping
from dataclasses import dataclass
from hashlib import sha256
from typing import Final, Literal

TermKind = Literal["constant", "variable", "negate", "meet", "join", "xor"]

MAX_NATIVE_TERM_BYTES: Final[int] = 4_096
MAX_NATIVE_TERM_NODES: Final[int] = 256
MAX_NATIVE_TERM_DEPTH: Final[int] = 64
_MAX_NATIVE_SYMBOLS: Final[int] = 64

_SYMBOL_RE: Final[re.Pattern[str]] = re.compile(r"[A-Za-z][A-Za-z0-9_]{0,63}", re.ASCII)
_TYPED_SYMBOL_RE: Final[re.Pattern[str]] = re.compile(
    r"([A-Za-z][A-Za-z0-9_]{0,63}):sbf", re.ASCII
)
_BRACED_TYPED_SYMBOL_RE: Final[re.Pattern[str]] = re.compile(
    r"\{([A-Za-z][A-Za-z0-9_]{0,63})\}:sbf", re.ASCII
)
_TERM_KINDS: Final[frozenset[str]] = frozenset(
    {"constant", "variable", "negate", "meet", "join", "xor"}
)
_RESERVED_NATIVE_WORDS: Final[frozenset[str]] = frozenset(
    {
        "always",
        "assume",
        "assert",
        "bv",
        "coefficient",
        "console",
        "exists",
        "forall",
        "in",
        "out",
        "sbf",
        "set",
        "stream",
        "streams",
    }
)

_ERR_INVALID_NATIVE: Final[str] = "native term has invalid syntax"
_ERR_UNKNOWN_NATIVE_SYMBOL: Final[str] = "native term contains an unknown symbol"
_ERR_AMBIGUOUS_NATIVE_SYMBOL: Final[str] = "native term symbol segmentation is ambiguous"
_ERR_NATIVE_TOO_LARGE: Final[str] = "native term exceeds byte limit"
_ERR_NATIVE_TOO_DEEP: Final[str] = "native term exceeds depth limit"
_ERR_NATIVE_TOO_MANY_NODES: Final[str] = "native term exceeds node limit"


def _validate_symbol(value: object, *, message: str) -> str:
    if type(value) is not str or _SYMBOL_RE.fullmatch(value) is None:
        raise ValueError(message)
    return value


def _validate_native_atom(value: object, *, message: str) -> str:
    symbol = _validate_symbol(value, message=message)
    if symbol in _RESERVED_NATIVE_WORDS:
        raise ValueError(message)
    return symbol


def _is_valid_term_kind(value: object) -> bool:
    """Keep the runtime guard for callers that bypass static type checking."""

    return type(value) is str and value in _TERM_KINDS


@dataclass(frozen=True, slots=True)
class Term:
    """A validated immutable Boolean-expression node.

    ``value`` is a bool for constants and a supported external symbol for
    variables.  Composite nodes use ``operands``.  Public constructors below
    preserve the canonical node shape and perform only trivial constant
    folding; they do not perform Boolean solving or equivalence rewriting.
    """

    kind: TermKind
    value: bool | str | None = None
    operands: tuple["Term", ...] = ()

    def __post_init__(self) -> None:
        if not _is_valid_term_kind(self.kind):
            raise ValueError("invalid term kind")
        if type(self.operands) is not tuple or any(not isinstance(term, Term) for term in self.operands):
            raise ValueError("term operands must be a tuple of Term values")
        if self.kind == "constant":
            if type(self.value) is not bool or self.operands:
                raise ValueError("constant terms require one bool value")
            return
        if self.kind == "variable":
            if self.operands:
                raise ValueError("variable terms cannot have operands")
            _validate_symbol(self.value, message="invalid variable name")
            return
        if self.value is not None:
            raise ValueError("composite terms cannot have a value")
        expected_arity = 1 if self.kind == "negate" else 2
        if self.kind in {"meet", "join"}:
            if len(self.operands) < expected_arity:
                raise ValueError("meet and join terms require at least two operands")
            return
        if len(self.operands) != expected_arity:
            raise ValueError(f"{self.kind} terms require {expected_arity} operands")

    def evaluate(self, values: Mapping[str, bool]) -> bool:
        """Evaluate against exact bool values after validating every free variable."""

        if not isinstance(values, Mapping):
            raise ValueError("variable values must be a mapping")
        for name in self.variables():
            if name not in values:
                raise ValueError("missing variable value")
            if type(values[name]) is not bool:
                raise ValueError("variable value must be bool")
        return _evaluate(self, values)

    def variables(self) -> frozenset[str]:
        """Return the exact set of free external symbols."""

        if self.kind == "constant":
            return frozenset()
        if self.kind == "variable":
            if type(self.value) is not str:
                raise RuntimeError("validated variable term lost its symbol")
            return frozenset((self.value,))
        names: set[str] = set()
        for operand in self.operands:
            names.update(operand.variables())
        return frozenset(names)

    def substitute(self, mapping: Mapping[str, "Term"]) -> "Term":
        """Apply one simultaneous substitution without rewriting replacements."""

        replacements = _validate_substitutions(mapping)
        return _substitute(self, replacements)

    def to_tau(self, symbols: Mapping[str, str] | None = None) -> str:
        """Render an explicitly parenthesized Tau Boolean-algebra term.

        When supplied, ``symbols`` maps external term names to safe Tau atoms.
        A rendered atom may be bare (``v0``), typed (``v0:sbf``), or a typed
        coefficient (``{a}:sbf``).  ``parse_native_term`` uses the reverse
        direction: bare Tau atoms mapped to external names.
        """

        rendered_symbols = _resolve_rendered_symbols(self.variables(), symbols)
        return _render_tau(self, rendered_symbols)

    def canonical_data(self) -> dict[str, object]:
        """Return a JSON-safe tree whose JSON encoding is canonicalized below."""

        if self.kind == "constant":
            return {"kind": self.kind, "value": self.value}
        if self.kind == "variable":
            return {"kind": self.kind, "value": self.value}
        return {
            "kind": self.kind,
            "operands": [operand.canonical_data() for operand in self.operands],
        }

    def canonical_json(self) -> str:
        """Return a deterministic UTF-8-safe JSON serialization of this tree."""

        return json.dumps(
            self.canonical_data(), ensure_ascii=True, separators=(",", ":"), sort_keys=True
        )

    def sha256(self) -> str:
        """Return the SHA-256 digest of ``canonical_json()`` as lowercase hex."""

        return sha256(self.canonical_json().encode("utf-8")).hexdigest()


def constant(value: bool) -> Term:
    """Construct an exact Boolean constant without accepting integer lookalikes."""

    if type(value) is not bool:
        raise ValueError("constant value must be bool")
    return Term("constant", value=value)


def variable(name: str) -> Term:
    """Construct a variable with a bounded ASCII identifier."""

    _validate_symbol(name, message="invalid variable name")
    return Term("variable", value=name)


def negate(term: Term) -> Term:
    """Construct complement, folding a constant child only."""

    _require_term(term)
    if term.kind == "constant":
        return constant(term.value is False)
    return Term("negate", operands=(term,))


def meet(*terms: Term) -> Term:
    """Construct conjunction with identity and absorbing constant folding only."""

    _require_terms(terms)
    retained: list[Term] = []
    for term in terms:
        if term.kind == "constant":
            if term.value is False:
                return constant(False)
            continue
        retained.append(term)
    if not retained:
        return constant(True)
    if len(retained) == 1:
        return retained[0]
    return Term("meet", operands=tuple(retained))


def join(*terms: Term) -> Term:
    """Construct disjunction with identity and absorbing constant folding only."""

    _require_terms(terms)
    retained: list[Term] = []
    for term in terms:
        if term.kind == "constant":
            if term.value is True:
                return constant(True)
            continue
        retained.append(term)
    if not retained:
        return constant(False)
    if len(retained) == 1:
        return retained[0]
    return Term("join", operands=tuple(retained))


def xor(left: Term, right: Term) -> Term:
    """Construct exclusive-or, folding only a pair of constants."""

    _require_term(left)
    _require_term(right)
    if left.kind == "constant" and right.kind == "constant":
        return constant((left.value is True) != (right.value is True))
    return Term("xor", operands=(left, right))


def _require_term(term: object) -> None:
    if not isinstance(term, Term):
        raise ValueError("term operand must be a Term")


def _require_terms(terms: tuple[Term, ...]) -> None:
    for term in terms:
        _require_term(term)


def _evaluate(term: Term, values: Mapping[str, bool]) -> bool:
    if term.kind == "constant":
        return term.value is True
    if term.kind == "variable":
        if type(term.value) is not str:
            raise RuntimeError("validated variable term lost its symbol")
        return values[term.value]
    if term.kind == "negate":
        return not _evaluate(term.operands[0], values)
    if term.kind == "meet":
        return all(_evaluate(operand, values) for operand in term.operands)
    if term.kind == "join":
        return any(_evaluate(operand, values) for operand in term.operands)
    if term.kind == "xor":
        return _evaluate(term.operands[0], values) != _evaluate(term.operands[1], values)
    raise RuntimeError("validated term has an unknown kind")


def _validate_substitutions(mapping: Mapping[str, Term]) -> dict[str, Term]:
    if not isinstance(mapping, Mapping):
        raise ValueError("substitution must be a mapping")
    replacements: dict[str, Term] = {}
    for name, replacement in mapping.items():
        validated_name = _validate_symbol(name, message="invalid substitution name")
        _require_term(replacement)
        replacements[validated_name] = replacement
    return replacements


def _substitute(term: Term, replacements: Mapping[str, Term]) -> Term:
    if term.kind == "constant":
        return term
    if term.kind == "variable":
        if type(term.value) is not str:
            raise RuntimeError("validated variable term lost its symbol")
        return replacements.get(term.value, term)
    replaced = tuple(_substitute(operand, replacements) for operand in term.operands)
    if term.kind == "negate":
        return negate(replaced[0])
    if term.kind == "meet":
        return meet(*replaced)
    if term.kind == "join":
        return join(*replaced)
    if term.kind == "xor":
        return xor(replaced[0], replaced[1])
    raise RuntimeError("validated term has an unknown kind")


def _resolve_rendered_symbols(
    variables: frozenset[str], symbols: Mapping[str, str] | None
) -> dict[str, str]:
    if symbols is None:
        resolved = {name: name for name in variables}
    else:
        if not isinstance(symbols, Mapping):
            raise ValueError("Tau symbol map must be a mapping")
        resolved = {}
        for external, rendered in symbols.items():
            external_name = _validate_symbol(external, message="invalid Tau symbol map key")
            _validate_rendered_native_symbol(rendered)
            if external_name in variables:
                resolved[external_name] = rendered
        if set(resolved) != variables:
            raise ValueError("Tau symbol map is incomplete")
    rendered_atoms: set[str] = set()
    for rendered in resolved.values():
        atom = _validate_rendered_native_symbol(rendered)
        if atom in rendered_atoms:
            raise ValueError("Tau symbol map aliases native symbols")
        rendered_atoms.add(atom)
    return resolved


def _validate_rendered_native_symbol(value: object) -> str:
    if type(value) is not str:
        raise ValueError("invalid Tau symbol map value")
    bare = _SYMBOL_RE.fullmatch(value)
    typed = _TYPED_SYMBOL_RE.fullmatch(value)
    braced = _BRACED_TYPED_SYMBOL_RE.fullmatch(value)
    if bare is not None:
        return _validate_native_atom(value, message="invalid Tau symbol map value")
    if typed is not None:
        return _validate_native_atom(typed.group(1), message="invalid Tau symbol map value")
    if braced is not None:
        return _validate_native_atom(braced.group(1), message="invalid Tau symbol map value")
    raise ValueError("invalid Tau symbol map value")


def _render_tau(term: Term, symbols: Mapping[str, str]) -> str:
    if term.kind == "constant":
        return "1" if term.value is True else "0"
    if term.kind == "variable":
        if type(term.value) is not str:
            raise RuntimeError("validated variable term lost its symbol")
        return symbols[term.value]
    if term.kind == "negate":
        return f"({_render_tau(term.operands[0], symbols)})'"
    if term.kind == "meet":
        return f"({'&'.join(_render_tau(operand, symbols) for operand in term.operands)})"
    if term.kind == "join":
        return f"({'|'.join(_render_tau(operand, symbols) for operand in term.operands)})"
    if term.kind == "xor":
        return f"({_render_tau(term.operands[0], symbols)}^{_render_tau(term.operands[1], symbols)})"
    raise RuntimeError("validated term has an unknown kind")


@dataclass(frozen=True, slots=True)
class _Token:
    kind: str
    value: str | None = None


@dataclass(frozen=True, slots=True)
class _ParsedTerm:
    term: Term
    depth: int


_FACTOR_STARTS: Final[frozenset[str]] = frozenset({"VAR", "CONST", "LPAREN", "LBRACE"})


def parse_native_term(text: str, symbols: Mapping[str, str]) -> Term:
    """Parse one bounded native Tau Boolean-algebra term.

    ``symbols`` maps bare Tau atoms to external term names.  The segmentation
    of adjacent native atoms must be unique; the parser rejects an expression
    such as ``ab`` when both ``ab`` and ``a b`` are possible mappings.
    """

    native_symbols = _validate_native_symbols(symbols)
    tokens = _lex_native_term(text, native_symbols)
    return _NativeTermParser(tokens).parse()


def _validate_native_symbols(symbols: Mapping[str, str]) -> dict[str, str]:
    if not isinstance(symbols, Mapping):
        raise ValueError("native symbol map must be a mapping")
    normalized: dict[str, str] = {}
    external_names: set[str] = set()
    for native, external in symbols.items():
        if len(normalized) >= _MAX_NATIVE_SYMBOLS:
            raise ValueError("native symbol map exceeds symbol limit")
        native_name = _validate_native_atom(native, message="invalid native symbol map key")
        external_name = _validate_symbol(external, message="invalid native symbol map value")
        if native_name in normalized or external_name in external_names:
            raise ValueError("native symbol map must be one-to-one")
        normalized[native_name] = external_name
        external_names.add(external_name)
    return normalized


def _lex_native_term(text: str, native_symbols: Mapping[str, str]) -> tuple[_Token, ...]:
    if type(text) is not str:
        raise ValueError("native term must be text")
    if not text.isascii():
        raise ValueError(_ERR_INVALID_NATIVE)
    if len(text.encode("utf-8")) > MAX_NATIVE_TERM_BYTES:
        raise ValueError(_ERR_NATIVE_TOO_LARGE)
    tokens: list[_Token] = []
    position = 0
    while position < len(text):
        char = text[position]
        if char in " \t\r\n":
            position += 1
            continue
        if _is_symbol_start(char):
            end = position + 1
            while end < len(text) and _is_symbol_continue(text[end]):
                end += 1
            word = text[position:end]
            if word in _RESERVED_NATIVE_WORDS:
                raise ValueError(_ERR_INVALID_NATIVE)
            pieces = _segment_native_word(word, native_symbols)
            tokens.extend(_Token("VAR", native_symbols[piece]) for piece in pieces)
            position = end
            continue
        if char in {"0", "1"}:
            if position + 1 < len(text) and _is_symbol_continue(text[position + 1]):
                raise ValueError(_ERR_INVALID_NATIVE)
            tokens.append(_Token("CONST", char))
            position += 1
            continue
        if char == ":":
            suffix_end = position + 4
            if text.startswith(":sbf", position) and (
                suffix_end == len(text) or not _is_symbol_continue(text[suffix_end])
            ):
                tokens.append(_Token("SBF"))
                position = suffix_end
                continue
            raise ValueError(_ERR_INVALID_NATIVE)
        token_kind = {
            "&": "MEET",
            "|": "JOIN",
            "^": "XOR",
            "'": "NEGATE",
            "(": "LPAREN",
            ")": "RPAREN",
            "{": "LBRACE",
            "}": "RBRACE",
        }.get(char)
        if token_kind is None:
            raise ValueError(_ERR_INVALID_NATIVE)
        tokens.append(_Token(token_kind))
        position += 1
    tokens.append(_Token("END"))
    return tuple(tokens)


def _is_symbol_start(char: str) -> bool:
    return "A" <= char <= "Z" or "a" <= char <= "z"


def _is_symbol_continue(char: str) -> bool:
    return _is_symbol_start(char) or "0" <= char <= "9" or char == "_"


def _native_constant_value(value: object) -> bool:
    if value == "0":
        return False
    if value == "1":
        return True
    raise ValueError(_ERR_INVALID_NATIVE)


def _segment_native_word(word: str, native_symbols: Mapping[str, str]) -> tuple[str, ...]:
    candidates = tuple(sorted(native_symbols))
    counts = [0] * (len(word) + 1)
    first_piece: list[str | None] = [None] * len(word)
    counts[len(word)] = 1
    for start in range(len(word) - 1, -1, -1):
        for candidate in candidates:
            end = start + len(candidate)
            if not word.startswith(candidate, start) or counts[end] == 0:
                continue
            if counts[start] == 0:
                first_piece[start] = candidate
            counts[start] = min(2, counts[start] + counts[end])
            if counts[start] == 2:
                break
    if counts[0] == 0:
        raise ValueError(_ERR_UNKNOWN_NATIVE_SYMBOL)
    if counts[0] > 1:
        raise ValueError(_ERR_AMBIGUOUS_NATIVE_SYMBOL)
    pieces: list[str] = []
    position = 0
    while position < len(word):
        piece = first_piece[position]
        if piece is None:
            raise RuntimeError("unique native segmentation was incomplete")
        pieces.append(piece)
        position += len(piece)
    return tuple(pieces)


class _NativeTermParser:
    def __init__(self, tokens: tuple[_Token, ...]) -> None:
        self._tokens = tokens
        self._position = 0
        self._nodes = 0

    def parse(self) -> Term:
        parsed = self._parse_join(0)
        if self._peek().kind != "END":
            raise ValueError(_ERR_INVALID_NATIVE)
        return parsed.term

    def _parse_join(self, group_depth: int) -> _ParsedTerm:
        terms = [self._parse_xor(group_depth)]
        while self._peek().kind == "JOIN":
            self._advance()
            terms.append(self._parse_xor(group_depth))
        return self._combine_join(terms)

    def _parse_xor(self, group_depth: int) -> _ParsedTerm:
        parsed = self._parse_meet(group_depth)
        while self._peek().kind == "XOR":
            self._advance()
            parsed = self._combine_xor(parsed, self._parse_meet(group_depth))
        return parsed

    def _parse_meet(self, group_depth: int) -> _ParsedTerm:
        terms = [self._parse_factor(group_depth)]
        while True:
            token_kind = self._peek().kind
            if token_kind == "MEET":
                self._advance()
                terms.append(self._parse_factor(group_depth))
                continue
            if token_kind in _FACTOR_STARTS:
                terms.append(self._parse_factor(group_depth))
                continue
            break
        return self._combine_meet(terms)

    def _parse_factor(self, group_depth: int) -> _ParsedTerm:
        token = self._advance()
        if token.kind == "VAR":
            self._add_nodes(1)
            parsed = _ParsedTerm(variable(_validate_symbol(token.value, message=_ERR_INVALID_NATIVE)), 1)
        elif token.kind == "CONST":
            self._add_nodes(1)
            parsed = _ParsedTerm(constant(_native_constant_value(token.value)), 1)
        elif token.kind in {"LPAREN", "LBRACE"}:
            self._check_group_depth(group_depth + 1)
            closing_kind = "RPAREN" if token.kind == "LPAREN" else "RBRACE"
            parsed = self._parse_join(group_depth + 1)
            self._advance(closing_kind)
        else:
            raise ValueError(_ERR_INVALID_NATIVE)
        saw_type_suffix = False
        while True:
            token_kind = self._peek().kind
            if token_kind == "NEGATE":
                self._advance()
                self._add_nodes(1)
                parsed = _ParsedTerm(negate(parsed.term), parsed.depth + 1)
                self._check_term_depth(parsed.depth)
                continue
            if token_kind == "SBF":
                if saw_type_suffix:
                    raise ValueError(_ERR_INVALID_NATIVE)
                saw_type_suffix = True
                self._advance()
                continue
            return parsed

    def _combine_meet(self, terms: list[_ParsedTerm]) -> _ParsedTerm:
        if len(terms) == 1:
            return terms[0]
        operands, depth = self._combine_variadic_operands(terms)
        return _ParsedTerm(meet(*operands), depth)

    def _combine_join(self, terms: list[_ParsedTerm]) -> _ParsedTerm:
        if len(terms) == 1:
            return terms[0]
        operands, depth = self._combine_variadic_operands(terms)
        return _ParsedTerm(join(*operands), depth)

    def _combine_variadic_operands(self, terms: list[_ParsedTerm]) -> tuple[tuple[Term, ...], int]:
        self._add_nodes(len(terms) - 1)
        depth = 1 + max(term.depth for term in terms)
        self._check_term_depth(depth)
        operands = tuple(term.term for term in terms)
        return operands, depth

    def _combine_xor(self, left: _ParsedTerm, right: _ParsedTerm) -> _ParsedTerm:
        self._add_nodes(1)
        depth = 1 + max(left.depth, right.depth)
        self._check_term_depth(depth)
        return _ParsedTerm(xor(left.term, right.term), depth)

    def _peek(self) -> _Token:
        return self._tokens[self._position]

    def _advance(self, expected_kind: str | None = None) -> _Token:
        token = self._peek()
        if expected_kind is not None and token.kind != expected_kind:
            raise ValueError(_ERR_INVALID_NATIVE)
        self._position += 1
        return token

    def _add_nodes(self, count: int) -> None:
        self._nodes += count
        if self._nodes > MAX_NATIVE_TERM_NODES:
            raise ValueError(_ERR_NATIVE_TOO_MANY_NODES)

    @staticmethod
    def _check_group_depth(depth: int) -> None:
        if depth > MAX_NATIVE_TERM_DEPTH:
            raise ValueError(_ERR_NATIVE_TOO_DEEP)

    @staticmethod
    def _check_term_depth(depth: int) -> None:
        if depth > MAX_NATIVE_TERM_DEPTH:
            raise ValueError(_ERR_NATIVE_TOO_DEEP)
