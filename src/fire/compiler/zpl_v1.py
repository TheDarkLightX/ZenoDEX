from __future__ import annotations

import json
import re
import shlex
from dataclasses import dataclass
from pathlib import Path

from .fmos_file_v1 import (
    FIRE_FMOS_FILE_SCHEMA,
    FireMathObjectSpecFile,
    verify_fire_math_object_spec_file,
)
from .object_compiler_v1 import (
    FireExpr,
    add_expr,
    cap_expr,
    clamp_expr,
    const_expr,
    exact_param_expr,
    max_expr,
    min_expr,
    mul_expr,
    positive_part_expr,
    source_bound_expr,
    sub_expr,
)


@dataclass(frozen=True)
class FireZplSpan:
    start_line: int
    start_col: int
    end_line: int
    end_col: int

    def render(self) -> str:
        if self.start_line == self.end_line and self.start_col == self.end_col:
            return f"line {self.start_line}, col {self.start_col}"
        return f"line {self.start_line}, col {self.start_col} to line {self.end_line}, col {self.end_col}"


class FireZplDiagnosticError(ValueError):
    def __init__(self, message: str, *, span: FireZplSpan | None = None) -> None:
        super().__init__(message)
        self.message = message
        self.span = span

    def __str__(self) -> str:
        if self.span is None:
            return self.message
        return f"{self.span.render()}: {self.message}"


@dataclass(frozen=True)
class FireZplSourceStatement:
    text: str
    span: FireZplSpan


@dataclass(frozen=True)
class _ExprToken:
    text: str
    span: FireZplSpan


@dataclass(frozen=True)
class FireZplTerm:
    name: str
    description: str
    unit: str
    minimum: int
    maximum: int
    span: FireZplSpan | None = None

    def to_dict(self) -> dict[str, object]:
        return {
            "name": self.name,
            "description": self.description,
            "unit": self.unit,
            "minimum": self.minimum,
            "maximum": self.maximum,
        }


@dataclass(frozen=True)
class FireZplValueRef:
    kind: str
    value: int | None = None
    term: str | None = None

    def to_dict(self) -> dict[str, object]:
        payload: dict[str, object] = {"kind": self.kind}
        if self.value is not None:
            payload["value"] = self.value
        if self.term is not None:
            payload["term"] = self.term
        return payload


@dataclass(frozen=True)
class FireZplContract:
    name: str
    unit: str
    lower: FireZplValueRef
    upper: FireZplValueRef
    span: FireZplSpan | None = None


@dataclass(frozen=True)
class FireZplSource:
    name: str
    unit: str
    lower: FireZplValueRef
    upper: FireZplValueRef
    contract_ref: str | None = None
    span: FireZplSpan | None = None

    def to_dict(self) -> dict[str, object]:
        payload = {
            "name": self.name,
            "unit": self.unit,
            "lower": self.lower.to_dict(),
            "upper": self.upper.to_dict(),
        }
        if self.contract_ref is not None:
            payload["contract"] = {
                "name": self.contract_ref,
                "role": f"source:{self.name}",
            }
        return payload


@dataclass(frozen=True)
class FireZplImport:
    name: str
    interface_object_id: str
    interface_output: str
    unit: str
    lower: FireZplValueRef
    upper: FireZplValueRef
    contract_ref: str | None = None
    span: FireZplSpan | None = None

    def to_dict(self) -> dict[str, object]:
        payload = {
            "name": self.name,
            "interface_object_id": self.interface_object_id,
            "interface_output": self.interface_output,
            "unit": self.unit,
            "lower": self.lower.to_dict(),
            "upper": self.upper.to_dict(),
        }
        if self.contract_ref is not None:
            payload["contract"] = {
                "name": self.contract_ref,
                "role": f"import:{self.interface_object_id}.{self.interface_output}",
            }
        return payload


@dataclass(frozen=True)
class FireZplWitness:
    name: str
    freshness: str
    unit: str
    lower: FireZplValueRef
    upper: FireZplValueRef
    contract_ref: str | None = None
    span: FireZplSpan | None = None

    def to_dict(self) -> dict[str, object]:
        payload = {
            "name": self.name,
            "freshness": self.freshness,
            "unit": self.unit,
            "lower": self.lower.to_dict(),
            "upper": self.upper.to_dict(),
        }
        if self.contract_ref is not None:
            payload["contract"] = {
                "name": self.contract_ref,
                "role": f"witness:{self.name}",
            }
        return payload


@dataclass(frozen=True)
class FireZplOutput:
    name: str
    description: str
    unit: str
    expression: "FireZplExpr"
    span: FireZplSpan | None = None

    def to_dict(self) -> dict[str, object]:
        return {
            "name": self.name,
            "description": self.description,
            "unit": self.unit,
            "expression": _zpl_expr_to_dict(self.expression),
        }


@dataclass(frozen=True)
class FireZplConstExpr:
    value: int
    span: FireZplSpan


@dataclass(frozen=True)
class FireZplExactParamExpr:
    name: str
    span: FireZplSpan


@dataclass(frozen=True)
class FireZplSourceBoundExpr:
    name: str
    span: FireZplSpan


@dataclass(frozen=True)
class FireZplBinaryExpr:
    op: str
    left: "FireZplExpr"
    right: "FireZplExpr"
    span: FireZplSpan


@dataclass(frozen=True)
class FireZplPositivePartExpr:
    inner: "FireZplExpr"
    span: FireZplSpan


@dataclass(frozen=True)
class FireZplCapExpr:
    inner: "FireZplExpr"
    upper: "FireZplExpr"
    span: FireZplSpan


@dataclass(frozen=True)
class FireZplClampExpr:
    inner: "FireZplExpr"
    lower: "FireZplExpr"
    upper: "FireZplExpr"
    span: FireZplSpan


FireZplExpr = (
    FireZplConstExpr
    | FireZplExactParamExpr
    | FireZplSourceBoundExpr
    | FireZplBinaryExpr
    | FireZplPositivePartExpr
    | FireZplCapExpr
    | FireZplClampExpr
)
_ZPL_EXPR_TYPES = (
    FireZplConstExpr,
    FireZplExactParamExpr,
    FireZplSourceBoundExpr,
    FireZplBinaryExpr,
    FireZplPositivePartExpr,
    FireZplCapExpr,
    FireZplClampExpr,
)


@dataclass(frozen=True)
class FireZplProgram:
    object_id: str
    object_name: str
    cli_help: str
    object_version: str
    object_family: str
    settlement_asset: str
    payoff_summary: str
    ir_hash: str
    term_fields: tuple[FireZplTerm, ...]
    contracts: tuple[FireZplContract, ...]
    source_bounds: tuple[FireZplSource, ...]
    imports: tuple[FireZplImport, ...]
    witnesses: tuple[FireZplWitness, ...]
    outputs: tuple[FireZplOutput, ...]
    expression: FireZplExpr
    statement_spans: dict[str, FireZplSpan] | None = None

    def to_fmos_payload(self) -> dict[str, object]:
        payload = {
            "schema": FIRE_FMOS_FILE_SCHEMA,
            "object_id": self.object_id,
            "object_name": self.object_name,
            "cli_help": self.cli_help,
            "object_version": self.object_version,
            "object_family": self.object_family,
            "settlement_asset": self.settlement_asset,
            "payoff_summary": self.payoff_summary,
            "ir_hash": self.ir_hash,
            "term_fields": [item.to_dict() for item in self.term_fields],
            "source_bounds": [item.to_dict() for item in self.source_bounds],
            "witnesses": [item.to_dict() for item in self.witnesses],
            "outputs": [item.to_dict() for item in self.outputs],
            "expression": _zpl_expr_to_dict(self.expression),
        }
        if self.imports:
            payload["imports"] = [item.to_dict() for item in self.imports]
        return payload


@dataclass(frozen=True)
class FireZplObjectStmt:
    object_id: str


@dataclass(frozen=True)
class FireZplNameStmt:
    object_name: str


@dataclass(frozen=True)
class FireZplCliHelpStmt:
    cli_help: str


@dataclass(frozen=True)
class FireZplVersionStmt:
    object_version: str


@dataclass(frozen=True)
class FireZplFamilyStmt:
    object_family: str


@dataclass(frozen=True)
class FireZplSettlementStmt:
    settlement_asset: str


@dataclass(frozen=True)
class FireZplSummaryStmt:
    payoff_summary: str


@dataclass(frozen=True)
class FireZplIrHashStmt:
    ir_hash: str


@dataclass(frozen=True)
class FireZplTermStmt:
    term: FireZplTerm


@dataclass(frozen=True)
class FireZplContractStmt:
    contract: FireZplContract


@dataclass(frozen=True)
class FireZplSourceStmt:
    source: FireZplSource


@dataclass(frozen=True)
class FireZplImportStmt:
    imported: FireZplImport


@dataclass(frozen=True)
class FireZplWitnessStmt:
    witness: FireZplWitness


@dataclass(frozen=True)
class FireZplOutputStmt:
    output: FireZplOutput


@dataclass(frozen=True)
class FireZplExpressionStmt:
    expression: FireZplExpr


@dataclass(frozen=True)
class FireZplEndStmt:
    pass


FireZplStatement = (
    FireZplObjectStmt
    | FireZplNameStmt
    | FireZplCliHelpStmt
    | FireZplVersionStmt
    | FireZplFamilyStmt
    | FireZplSettlementStmt
    | FireZplSummaryStmt
    | FireZplIrHashStmt
    | FireZplTermStmt
    | FireZplContractStmt
    | FireZplSourceStmt
    | FireZplImportStmt
    | FireZplWitnessStmt
    | FireZplOutputStmt
    | FireZplExpressionStmt
    | FireZplEndStmt
)


class _ExprParser:
    def __init__(self, text: str, *, base_line: int = 1, base_col: int = 1) -> None:
        self.tokens = self._tokenize(text, base_line=base_line, base_col=base_col)
        self.index = 0

    def _tokenize(self, text: str, *, base_line: int, base_col: int) -> list[_ExprToken]:
        tokens: list[_ExprToken] = []
        pos = 0
        line = base_line
        col = base_col
        while pos < len(text):
            while pos < len(text) and text[pos].isspace():
                line, col = _advance_position(line, col, text[pos])
                pos += 1
            if pos >= len(text):
                break
            match = re.match(r"[A-Za-z_][A-Za-z0-9_]*|-?[0-9]+|[(),]", text[pos:])
            if match is None:
                raise FireZplDiagnosticError(
                    f"invalid ZPL expression syntax near: {text[pos:pos + 20]!r}",
                    span=FireZplSpan(line, col, line, col),
                )
            token = match.group(0)
            start_line = line
            start_col = col
            for char in token:
                line, col = _advance_position(line, col, char)
            tokens.append(
                _ExprToken(
                    text=token,
                    span=FireZplSpan(
                        start_line=start_line,
                        start_col=start_col,
                        end_line=line,
                        end_col=col,
                    ),
                )
            )
            pos += len(token)
        return tokens

    def _peek(self) -> _ExprToken | None:
        if self.index >= len(self.tokens):
            return None
        return self.tokens[self.index]

    def _take(self, expected: str | None = None) -> _ExprToken:
        token = self._peek()
        if token is None:
            raise FireZplDiagnosticError("unexpected end of ZPL expression")
        if expected is not None and token.text != expected:
            raise FireZplDiagnosticError(f"expected {expected!r}, got {token.text!r}", span=token.span)
        self.index += 1
        return token

    def parse(self) -> FireZplExpr:
        expr = self._parse_expr()
        if self._peek() is not None:
            raise FireZplDiagnosticError(
                f"unexpected trailing token in ZPL expression: {self._peek().text!r}",
                span=self._peek().span,
            )
        return expr

    def _parse_expr(self) -> FireZplExpr:
        token = self._take()
        if re.fullmatch(r"-?[0-9]+", token.text):
            return FireZplConstExpr(value=int(token.text), span=token.span)
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", token.text):
            raise FireZplDiagnosticError(f"invalid ZPL expression token: {token.text!r}", span=token.span)
        if self._peek() is None or self._peek().text != "(":
            raise FireZplDiagnosticError(
                f"bare identifiers are not allowed in ZPL expressions: {token.text}",
                span=token.span,
            )
        self._take("(")
        args: list[FireZplExpr | str | int] = []
        if self._peek() is None or self._peek().text != ")":
            while True:
                if token.text in {"exact_param", "source_bound"}:
                    name_token = self._take()
                    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", name_token.text):
                        raise FireZplDiagnosticError(
                            f"invalid identifier in {token.text}: {name_token.text!r}",
                            span=name_token.span,
                        )
                    args.append(name_token.text)
                elif token.text == "const":
                    value_token = self._take()
                    if not re.fullmatch(r"-?[0-9]+", value_token.text):
                        raise FireZplDiagnosticError(
                            f"const expects integer literal, got {value_token.text!r}",
                            span=value_token.span,
                        )
                    args.append(int(value_token.text))
                else:
                    args.append(self._parse_expr())
                if self._peek() is not None and self._peek().text == ",":
                    self._take(",")
                    continue
                break
        close_token = self._take(")")
        return _build_expr_call(
            token.text,
            args,
            span=_merge_spans(token.span, close_token.span),
        )


def _build_expr_call(name: str, args: list[FireZplExpr | str | int], *, span: FireZplSpan) -> FireZplExpr:
    if name == "const":
        if len(args) != 1 or not isinstance(args[0], int):
            raise FireZplDiagnosticError("const expects one integer argument", span=span)
        return FireZplConstExpr(value=args[0], span=span)
    if name == "exact_param":
        if len(args) != 1 or not isinstance(args[0], str):
            raise FireZplDiagnosticError("exact_param expects one identifier", span=span)
        return FireZplExactParamExpr(name=args[0], span=span)
    if name == "source_bound":
        if len(args) != 1 or not isinstance(args[0], str):
            raise FireZplDiagnosticError("source_bound expects one identifier", span=span)
        return FireZplSourceBoundExpr(name=args[0], span=span)
    if name in {"add", "sub", "mul", "min", "max"}:
        if len(args) != 2 or any(not isinstance(arg, _ZPL_EXPR_TYPES) for arg in args):
            raise FireZplDiagnosticError(f"{name} expects two expression arguments", span=span)
        return FireZplBinaryExpr(op=name, left=args[0], right=args[1], span=span)  # type: ignore[arg-type]
    if name == "positive_part":
        if len(args) != 1 or not isinstance(args[0], _ZPL_EXPR_TYPES):
            raise FireZplDiagnosticError("positive_part expects one expression argument", span=span)
        return FireZplPositivePartExpr(inner=args[0], span=span)  # type: ignore[arg-type]
    if name == "cap":
        if len(args) != 2 or any(not isinstance(arg, _ZPL_EXPR_TYPES) for arg in args):
            raise FireZplDiagnosticError("cap expects two expression arguments", span=span)
        return FireZplCapExpr(inner=args[0], upper=args[1], span=span)  # type: ignore[arg-type]
    if name == "clamp":
        if len(args) != 3 or any(not isinstance(arg, _ZPL_EXPR_TYPES) for arg in args):
            raise FireZplDiagnosticError("clamp expects three expression arguments", span=span)
        return FireZplClampExpr(inner=args[0], lower=args[1], upper=args[2], span=span)  # type: ignore[arg-type]
    raise FireZplDiagnosticError(f"unsupported ZPL expression function: {name}", span=span)


def _zpl_expr_to_dict(expr: FireZplExpr) -> dict[str, object]:
    if isinstance(expr, FireZplConstExpr):
        return {"kind": "const", "value": expr.value}
    if isinstance(expr, FireZplExactParamExpr):
        return {"kind": "exact_param", "name": expr.name}
    if isinstance(expr, FireZplSourceBoundExpr):
        return {"kind": "source_bound", "name": expr.name}
    if isinstance(expr, FireZplBinaryExpr):
        return {
            "kind": expr.op,
            "left": _zpl_expr_to_dict(expr.left),
            "right": _zpl_expr_to_dict(expr.right),
        }
    if isinstance(expr, FireZplPositivePartExpr):
        return {"kind": "positive_part", "inner": _zpl_expr_to_dict(expr.inner)}
    if isinstance(expr, FireZplCapExpr):
        return {
            "kind": "cap",
            "inner": _zpl_expr_to_dict(expr.inner),
            "upper": _zpl_expr_to_dict(expr.upper),
        }
    if isinstance(expr, FireZplClampExpr):
        return {
            "kind": "clamp",
            "inner": _zpl_expr_to_dict(expr.inner),
            "lower": _zpl_expr_to_dict(expr.lower),
            "upper": _zpl_expr_to_dict(expr.upper),
        }
    raise TypeError(f"unsupported ZPL expression type: {type(expr)!r}")


def zpl_expr_to_fire_expr(expr: FireZplExpr) -> FireExpr:
    if isinstance(expr, FireZplConstExpr):
        return const_expr(expr.value)
    if isinstance(expr, FireZplExactParamExpr):
        return exact_param_expr(expr.name)
    if isinstance(expr, FireZplSourceBoundExpr):
        return source_bound_expr(expr.name)
    if isinstance(expr, FireZplBinaryExpr):
        left = zpl_expr_to_fire_expr(expr.left)
        right = zpl_expr_to_fire_expr(expr.right)
        if expr.op == "add":
            return add_expr(left, right)
        if expr.op == "sub":
            return sub_expr(left, right)
        if expr.op == "mul":
            return mul_expr(left, right)
        if expr.op == "min":
            return min_expr(left, right)
        if expr.op == "max":
            return max_expr(left, right)
        raise ValueError(f"unsupported ZPL binary op: {expr.op}")
    if isinstance(expr, FireZplPositivePartExpr):
        return positive_part_expr(zpl_expr_to_fire_expr(expr.inner))
    if isinstance(expr, FireZplCapExpr):
        return cap_expr(zpl_expr_to_fire_expr(expr.inner), zpl_expr_to_fire_expr(expr.upper))
    if isinstance(expr, FireZplClampExpr):
        return clamp_expr(
            zpl_expr_to_fire_expr(expr.inner),
            zpl_expr_to_fire_expr(expr.lower),
            zpl_expr_to_fire_expr(expr.upper),
        )
    raise TypeError(f"unsupported ZPL expression type: {type(expr)!r}")


def parse_zpl_expression_ast(text: str) -> FireZplExpr:
    return _ExprParser(text).parse()


def parse_zpl_expression_ast_with_span(text: str, *, base_line: int, base_col: int) -> FireZplExpr:
    return _ExprParser(text, base_line=base_line, base_col=base_col).parse()


def parse_zpl_expression(text: str) -> dict[str, object]:
    return _zpl_expr_to_dict(parse_zpl_expression_ast(text))


def _parse_value_ref(token: str) -> FireZplValueRef:
    if token.startswith("const:"):
        return FireZplValueRef(kind="const", value=int(token[len("const:") :]))
    if token.startswith("term:"):
        term = token[len("term:") :]
        if not term:
            raise ValueError("term value ref requires term name")
        return FireZplValueRef(kind="term", term=term)
    raise ValueError(f"unsupported ZPL value ref: {token}")


def _resolve_contract_ref(
    token: str,
    *,
    contracts: dict[str, FireZplContract],
    span: FireZplSpan,
) -> FireZplContract:
    if not token.startswith("contract:"):
        raise FireZplDiagnosticError(f"unsupported contract ref syntax: {token}", span=span)
    contract_name = token[len("contract:") :]
    if not contract_name:
        raise FireZplDiagnosticError("contract ref requires non-empty name", span=span)
    if contract_name not in contracts:
        raise FireZplDiagnosticError(f"unknown contract reference: {contract_name}", span=span)
    return contracts[contract_name]


def _advance_position(line: int, col: int, char: str) -> tuple[int, int]:
    if char == "\n":
        return line + 1, 1
    return line, col + 1


def _advance_position_text(line: int, col: int, text: str) -> tuple[int, int]:
    for char in text:
        line, col = _advance_position(line, col, char)
    return line, col


def _merge_spans(start: FireZplSpan, end: FireZplSpan) -> FireZplSpan:
    return FireZplSpan(
        start_line=start.start_line,
        start_col=start.start_col,
        end_line=end.end_line,
        end_col=end.end_col,
    )


def _split_zpl_statements(text: str) -> list[FireZplSourceStatement]:
    statements: list[FireZplSourceStatement] = []
    buf: list[str] = []
    in_string = False
    escaped = False
    index = 0
    line = 1
    col = 1
    statement_start: tuple[int, int] | None = None
    while index < len(text):
        char = text[index]
        if in_string:
            if statement_start is None:
                statement_start = (line, col)
            buf.append(char)
            if char == '"' and not escaped:
                in_string = False
            if char == "\\" and not escaped:
                escaped = True
            else:
                escaped = False
            line, col = _advance_position(line, col, char)
            index += 1
            continue
        if char == "#":
            while index < len(text) and text[index] != "\n":
                line, col = _advance_position(line, col, text[index])
                index += 1
            continue
        if char == '"':
            in_string = True
            if statement_start is None:
                statement_start = (line, col)
            buf.append(char)
            line, col = _advance_position(line, col, char)
            index += 1
            continue
        if char == ";":
            statement = "".join(buf).strip()
            if statement and statement_start is not None:
                statements.append(
                    FireZplSourceStatement(
                        text=statement,
                        span=FireZplSpan(
                            start_line=statement_start[0],
                            start_col=statement_start[1],
                            end_line=line,
                            end_col=col,
                        ),
                    )
                )
            buf.clear()
            statement_start = None
            line, col = _advance_position(line, col, char)
            index += 1
            continue
        if char == "\n" and "".join(buf).strip() == "end":
            if statement_start is not None:
                statements.append(
                    FireZplSourceStatement(
                        text="end",
                        span=FireZplSpan(
                            start_line=statement_start[0],
                            start_col=statement_start[1],
                            end_line=line,
                            end_col=col,
                        ),
                    )
                )
            buf.clear()
            statement_start = None
            line, col = _advance_position(line, col, char)
            index += 1
            continue
        if statement_start is None and not char.isspace():
            statement_start = (line, col)
        buf.append(char)
        line, col = _advance_position(line, col, char)
        index += 1
    if in_string:
        raise FireZplDiagnosticError(
            "unterminated string literal in ZPL source",
            span=None
            if statement_start is None
            else FireZplSpan(
                start_line=statement_start[0],
                start_col=statement_start[1],
                end_line=line,
                end_col=col,
            ),
        )
    remainder = "".join(buf).strip()
    if remainder and statement_start is not None:
        statements.append(
            FireZplSourceStatement(
                text=remainder,
                span=FireZplSpan(
                    start_line=statement_start[0],
                    start_col=statement_start[1],
                    end_line=line,
                    end_col=col,
                ),
            )
        )
    return statements


def _expression_start_span(statement: FireZplSourceStatement) -> FireZplSpan:
    eq_index = statement.text.index("=") + 1
    expr_suffix = statement.text[eq_index:]
    lstrip_count = len(expr_suffix) - len(expr_suffix.lstrip())
    line, col = _advance_position_text(
        statement.span.start_line,
        statement.span.start_col,
        statement.text[: eq_index + lstrip_count],
    )
    return FireZplSpan(start_line=line, start_col=col, end_line=line, end_col=col)


def _parse_fire_zpl_statement(
    statement: FireZplSourceStatement,
    *,
    contracts: dict[str, FireZplContract],
) -> FireZplStatement:
    if statement.text == "end":
        return FireZplEndStmt()
    if statement.text.startswith("output "):
        if "=" not in statement.text:
            raise FireZplDiagnosticError(
                "output statement must be: output <name> <description> <unit> = <expr>",
                span=statement.span,
            )
        prefix, expr_text = statement.text.split("=", 1)
        parts = shlex.split(prefix)
        if len(parts) != 4:
            raise FireZplDiagnosticError(
                "output statement must be: output <name> <description> <unit> = <expr>",
                span=statement.span,
            )
        _, name, description, unit = parts
        expr_span = _expression_start_span(statement)
        return FireZplOutputStmt(
            output=FireZplOutput(
                name=name,
                description=description,
                unit=unit,
                expression=parse_zpl_expression_ast_with_span(
                    expr_text.strip(),
                    base_line=expr_span.start_line,
                    base_col=expr_span.start_col,
                ),
                span=statement.span,
            )
        )
    if statement.text.startswith("expression "):
        if "=" not in statement.text:
            raise FireZplDiagnosticError("expression statement must be: expression = <expr>", span=statement.span)
        _, expr_text = statement.text.split("=", 1)
        expr_span = _expression_start_span(statement)
        return FireZplExpressionStmt(
            expression=parse_zpl_expression_ast_with_span(
                expr_text.strip(),
                base_line=expr_span.start_line,
                base_col=expr_span.start_col,
            )
        )

    parts = shlex.split(statement.text)
    if not parts:
        raise FireZplDiagnosticError("empty ZPL statement", span=statement.span)
    keyword = parts[0]
    if keyword == "object" and len(parts) == 2:
        return FireZplObjectStmt(object_id=parts[1])
    if keyword == "name" and len(parts) == 2:
        return FireZplNameStmt(object_name=parts[1])
    if keyword == "cli_help" and len(parts) == 2:
        return FireZplCliHelpStmt(cli_help=parts[1])
    if keyword == "version" and len(parts) == 2:
        return FireZplVersionStmt(object_version=parts[1])
    if keyword == "family" and len(parts) == 2:
        return FireZplFamilyStmt(object_family=parts[1])
    if keyword == "settlement" and len(parts) == 2:
        return FireZplSettlementStmt(settlement_asset=parts[1])
    if keyword == "summary" and len(parts) == 2:
        return FireZplSummaryStmt(payoff_summary=parts[1])
    if keyword == "ir_hash" and len(parts) == 2:
        return FireZplIrHashStmt(ir_hash=parts[1])
    if keyword == "term" and len(parts) == 6:
        _, name, description, unit, minimum, maximum = parts
        return FireZplTermStmt(
            term=FireZplTerm(
                name=name,
                description=description,
                unit=unit,
                minimum=int(minimum),
                maximum=int(maximum),
                span=statement.span,
            )
        )
    if keyword == "contract" and len(parts) == 5:
        _, name, unit, lower, upper = parts
        return FireZplContractStmt(
            contract=FireZplContract(
                name=name,
                unit=unit,
                lower=_parse_value_ref(lower),
                upper=_parse_value_ref(upper),
                span=statement.span,
            )
        )
    if keyword == "source" and len(parts) == 5:
        _, name, unit, lower, upper = parts
        return FireZplSourceStmt(
            source=FireZplSource(
                name=name,
                unit=unit,
                lower=_parse_value_ref(lower),
                upper=_parse_value_ref(upper),
                contract_ref=None,
                span=statement.span,
            )
        )
    if keyword == "source" and len(parts) == 3:
        _, name, contract_ref = parts
        contract = _resolve_contract_ref(contract_ref, contracts=contracts, span=statement.span)
        return FireZplSourceStmt(
            source=FireZplSource(
                name=name,
                unit=contract.unit,
                lower=contract.lower,
                upper=contract.upper,
                contract_ref=contract.name,
                span=statement.span,
            )
        )
    if keyword == "import" and len(parts) == 7:
        _, name, interface_object_id, interface_output, unit, lower, upper = parts
        return FireZplImportStmt(
            imported=FireZplImport(
                name=name,
                interface_object_id=interface_object_id,
                interface_output=interface_output,
                unit=unit,
                lower=_parse_value_ref(lower),
                upper=_parse_value_ref(upper),
                contract_ref=None,
                span=statement.span,
            )
        )
    if keyword == "import" and len(parts) == 5:
        _, name, interface_object_id, interface_output, contract_ref = parts
        contract = _resolve_contract_ref(contract_ref, contracts=contracts, span=statement.span)
        return FireZplImportStmt(
            imported=FireZplImport(
                name=name,
                interface_object_id=interface_object_id,
                interface_output=interface_output,
                unit=contract.unit,
                lower=contract.lower,
                upper=contract.upper,
                contract_ref=contract.name,
                span=statement.span,
            )
        )
    if keyword == "witness" and len(parts) == 6:
        _, name, freshness, unit, lower, upper = parts
        return FireZplWitnessStmt(
            witness=FireZplWitness(
                name=name,
                freshness=freshness,
                unit=unit,
                lower=_parse_value_ref(lower),
                upper=_parse_value_ref(upper),
                contract_ref=None,
                span=statement.span,
            )
        )
    if keyword == "witness" and len(parts) == 4:
        _, name, freshness, contract_ref = parts
        contract = _resolve_contract_ref(contract_ref, contracts=contracts, span=statement.span)
        return FireZplWitnessStmt(
            witness=FireZplWitness(
                name=name,
                freshness=freshness,
                unit=contract.unit,
                lower=contract.lower,
                upper=contract.upper,
                contract_ref=contract.name,
                span=statement.span,
            )
        )
    raise FireZplDiagnosticError(f"unsupported or malformed ZPL statement: {statement.text}", span=statement.span)


def _assign_once(current: str | None, value: str, field_name: str, *, span: FireZplSpan) -> str:
    if current is not None:
        raise FireZplDiagnosticError(f"duplicate ZPL statement: {field_name}", span=span)
    return value


def _validate_program_references(program: FireZplProgram) -> None:
    exact_names = {item.name for item in program.term_fields}
    source_names = {item.name for item in program.source_bounds} | {item.name for item in program.imports}

    def walk(expr: FireZplExpr) -> None:
        if isinstance(expr, FireZplConstExpr):
            return
        if isinstance(expr, FireZplExactParamExpr):
            if expr.name not in exact_names:
                raise FireZplDiagnosticError(f"unknown exact_param reference: {expr.name}", span=expr.span)
            return
        if isinstance(expr, FireZplSourceBoundExpr):
            if expr.name not in source_names:
                raise FireZplDiagnosticError(f"unknown source_bound reference: {expr.name}", span=expr.span)
            return
        if isinstance(expr, FireZplBinaryExpr):
            walk(expr.left)
            walk(expr.right)
            return
        if isinstance(expr, FireZplPositivePartExpr):
            walk(expr.inner)
            return
        if isinstance(expr, FireZplCapExpr):
            walk(expr.inner)
            walk(expr.upper)
            return
        if isinstance(expr, FireZplClampExpr):
            walk(expr.inner)
            walk(expr.lower)
            walk(expr.upper)
            return
        raise TypeError(f"unsupported ZPL expression type: {type(expr)!r}")

    for output in program.outputs:
        walk(output.expression)
    walk(program.expression)


def _find_duplicate_declaration_span(items: tuple[object, ...], name_getter) -> FireZplSpan | None:
    seen: set[str] = set()
    for item in items:
        name = name_getter(item)
        if name in seen:
            return getattr(item, "span", None)
        seen.add(name)
    return None


def _find_named_declaration_span(items: tuple[object, ...], name: str) -> FireZplSpan | None:
    for item in items:
        if getattr(item, "name", None) == name:
            return getattr(item, "span", None)
    return None


def _find_contract_span(program: FireZplProgram, contract_name: str | None) -> FireZplSpan | None:
    if contract_name is None:
        return None
    return _find_named_declaration_span(program.contracts, contract_name)


def _first_contract_span(items: tuple[object, ...], program: FireZplProgram) -> FireZplSpan | None:
    for item in items:
        span = _find_contract_span(program, getattr(item, "contract_ref", None))
        if span is not None:
            return span
    return None


def _contract_use_label(item: object) -> str | None:
    if isinstance(item, FireZplSource):
        return f"source {item.name}"
    if isinstance(item, FireZplImport):
        return f"import {item.name} <- {item.interface_object_id}.{item.interface_output}"
    if isinstance(item, FireZplWitness):
        return f"witness {item.name}"
    return None


def _first_contract_detail(items: tuple[object, ...], program: FireZplProgram) -> tuple[FireZplSpan | None, str | None]:
    for item in items:
        contract_name = getattr(item, "contract_ref", None)
        if contract_name is None:
            continue
        span = _find_contract_span(program, contract_name)
        use_label = _contract_use_label(item)
        if use_label is None:
            return span, f"contract {contract_name}"
        return span, f"contract {contract_name} for {use_label}"
    return None, None


def _contract_detail_for_name(
    items: tuple[object, ...],
    *,
    name: str,
    program: FireZplProgram,
) -> tuple[FireZplSpan | None, str | None]:
    for item in items:
        if getattr(item, "name", None) != name:
            continue
        contract_name = getattr(item, "contract_ref", None)
        if contract_name is None:
            return None, None
        span = _find_contract_span(program, contract_name)
        use_label = _contract_use_label(item)
        if use_label is None:
            return span, f"contract {contract_name}"
        return span, f"contract {contract_name} for {use_label}"
    return None, None


def _decorate_fmos_validation_error(program: FireZplProgram, err: str | None) -> tuple[FireZplSpan | None, str]:
    prefix = "compiled ZPL payload failed FIRE FMOS validation"
    if err is None:
        return None, f"{prefix}: unknown error"

    if err == "duplicate_term_field":
        return _find_duplicate_declaration_span(program.term_fields, lambda item: item.name), f"{prefix}: {err}"
    if err == "duplicate_contract":
        return _find_duplicate_declaration_span(program.contracts, lambda item: item.name), f"{prefix}: {err}"
    if err == "duplicate_source_bound":
        return _find_duplicate_declaration_span(program.source_bounds, lambda item: item.name), f"{prefix}: {err}"
    if err == "duplicate_import":
        return _find_duplicate_declaration_span(program.imports, lambda item: item.name), f"{prefix}: {err}"
    if err == "duplicate_witness":
        return _find_duplicate_declaration_span(program.witnesses, lambda item: item.name), f"{prefix}: {err}"
    if err == "duplicate_output":
        return _find_duplicate_declaration_span(program.outputs, lambda item: item.name), f"{prefix}: {err}"

    named_groups = (
        ("term_field_unit_invalid:", program.term_fields),
        ("source_bound_unit_invalid:", program.source_bounds),
        ("unknown_term_ref_in_source_bound:", program.source_bounds),
        ("source_bound_unit_mismatch:", program.source_bounds),
        ("import_unit_invalid:", program.imports),
        ("unknown_term_ref_in_import:", program.imports),
        ("import_unit_mismatch:", program.imports),
        ("witness_unit_invalid:", program.witnesses),
        ("unknown_term_ref_in_witness:", program.witnesses),
        ("witness_unit_mismatch:", program.witnesses),
        ("output_unit_invalid:", program.outputs),
        ("unknown_output_exact_params:", program.outputs),
        ("unknown_output_source_bounds:", program.outputs),
        ("output_expression_invalid:", program.outputs),
        ("output_expression_unit_invalid:", program.outputs),
        ("output_expression_unit_mismatch:", program.outputs),
    )
    for err_prefix, items in named_groups:
        if err.startswith(err_prefix):
            name = err[len(err_prefix) :].split(":", 1)[0]
            return _find_named_declaration_span(items, name), f"{prefix}: {err}"

    if err.startswith("unknown_import_interface:"):
        interface_object_id = err.split(":", 1)[1]
        for imported in program.imports:
            if imported.interface_object_id == interface_object_id:
                return imported.span, f"{prefix}: {err}"
        return None, f"{prefix}: {err}"

    if err.startswith("import_invalid:"):
        interface_object_id = err.split(":", 2)[1]
        for imported in program.imports:
            if imported.interface_object_id == interface_object_id:
                return imported.span, f"{prefix}: {err}"
        return None, f"{prefix}: {err}"

    if err.startswith("unknown_import_output:") or err.startswith("import_output_unit_mismatch:"):
        import_name = err.split(":", 2)[1]
        return _find_named_declaration_span(program.imports, import_name), f"{prefix}: {err}"

    if err.startswith("expression_"):
        if program.outputs:
            return program.outputs[0].span, f"{prefix}: {err}"
        return getattr(program.expression, "span", None), f"{prefix}: {err}"

    return None, f"{prefix}: {err}"


def parse_fire_zpl_source(text: str) -> FireZplProgram:
    object_id: str | None = None
    object_name: str | None = None
    cli_help: str | None = None
    object_version: str | None = None
    object_family: str | None = None
    settlement_asset: str | None = None
    payoff_summary: str | None = None
    ir_hash: str | None = None
    term_fields: list[FireZplTerm] = []
    contracts: list[FireZplContract] = []
    source_bounds: list[FireZplSource] = []
    imports: list[FireZplImport] = []
    witnesses: list[FireZplWitness] = []
    outputs: list[FireZplOutput] = []
    expression: FireZplExpr | None = None
    statement_spans: dict[str, FireZplSpan] = {}
    saw_end = False

    for statement in _split_zpl_statements(text):
        if saw_end:
            raise FireZplDiagnosticError(f"unexpected ZPL statement after end: {statement.text}", span=statement.span)
        parsed = _parse_fire_zpl_statement(statement, contracts={item.name: item for item in contracts})
        if isinstance(parsed, FireZplEndStmt):
            saw_end = True
        elif isinstance(parsed, FireZplObjectStmt):
            object_id = _assign_once(object_id, parsed.object_id, "object", span=statement.span)
            statement_spans["object"] = statement.span
        elif isinstance(parsed, FireZplNameStmt):
            object_name = _assign_once(object_name, parsed.object_name, "name", span=statement.span)
            statement_spans["name"] = statement.span
        elif isinstance(parsed, FireZplCliHelpStmt):
            cli_help = _assign_once(cli_help, parsed.cli_help, "cli_help", span=statement.span)
            statement_spans["cli_help"] = statement.span
        elif isinstance(parsed, FireZplVersionStmt):
            object_version = _assign_once(object_version, parsed.object_version, "version", span=statement.span)
            statement_spans["version"] = statement.span
        elif isinstance(parsed, FireZplFamilyStmt):
            object_family = _assign_once(object_family, parsed.object_family, "family", span=statement.span)
            statement_spans["family"] = statement.span
        elif isinstance(parsed, FireZplSettlementStmt):
            settlement_asset = _assign_once(settlement_asset, parsed.settlement_asset, "settlement", span=statement.span)
            statement_spans["settlement"] = statement.span
        elif isinstance(parsed, FireZplSummaryStmt):
            payoff_summary = _assign_once(payoff_summary, parsed.payoff_summary, "summary", span=statement.span)
            statement_spans["summary"] = statement.span
        elif isinstance(parsed, FireZplIrHashStmt):
            ir_hash = _assign_once(ir_hash, parsed.ir_hash, "ir_hash", span=statement.span)
            statement_spans["ir_hash"] = statement.span
        elif isinstance(parsed, FireZplTermStmt):
            term_fields.append(parsed.term)
        elif isinstance(parsed, FireZplContractStmt):
            if any(item.name == parsed.contract.name for item in contracts):
                raise FireZplDiagnosticError("duplicate ZPL statement: contract", span=statement.span)
            contracts.append(parsed.contract)
        elif isinstance(parsed, FireZplSourceStmt):
            source_bounds.append(parsed.source)
        elif isinstance(parsed, FireZplImportStmt):
            imports.append(parsed.imported)
        elif isinstance(parsed, FireZplWitnessStmt):
            witnesses.append(parsed.witness)
        elif isinstance(parsed, FireZplOutputStmt):
            outputs.append(parsed.output)
        elif isinstance(parsed, FireZplExpressionStmt):
            if expression is not None:
                raise FireZplDiagnosticError("duplicate ZPL statement: expression", span=statement.span)
            expression = parsed.expression
            statement_spans["expression"] = statement.span
        else:
            raise AssertionError(f"unhandled ZPL statement type: {type(parsed)!r}")

    required = {
        "object": object_id,
        "name": object_name,
        "cli_help": cli_help,
        "version": object_version,
        "family": object_family,
        "settlement": settlement_asset,
        "summary": payoff_summary,
        "ir_hash": ir_hash,
        "expression": expression,
    }
    missing = [name for name, value in required.items() if value is None]
    if missing:
        raise ValueError(f"missing required ZPL fields: {', '.join(missing)}")
    if not saw_end:
        raise ValueError("ZPL program must terminate with end")
    if not outputs:
        raise ValueError("ZPL program must declare at least one output")
    program = FireZplProgram(
        object_id=object_id,
        object_name=object_name,
        cli_help=cli_help,
        object_version=object_version,
        object_family=object_family,
        settlement_asset=settlement_asset,
        payoff_summary=payoff_summary,
        ir_hash=ir_hash,
        term_fields=tuple(term_fields),
        contracts=tuple(contracts),
        source_bounds=tuple(source_bounds),
        imports=tuple(imports),
        witnesses=tuple(witnesses),
        outputs=tuple(outputs),
        expression=expression,
        statement_spans=statement_spans,
    )
    _validate_program_references(program)
    return program


def compile_fire_zpl_program_to_fmos_payload(program: FireZplProgram) -> dict[str, object]:
    payload = program.to_fmos_payload()
    spec_file = FireMathObjectSpecFile.from_dict(payload)
    ok, err = verify_fire_math_object_spec_file(spec_file)
    if not ok:
        span, message = _decorate_fmos_validation_error(program, err)
        raise FireZplDiagnosticError(message, span=span)
    return payload


def compile_fire_zpl_to_fmos_payload(text: str) -> dict[str, object]:
    program = parse_fire_zpl_source(text)
    return compile_fire_zpl_program_to_fmos_payload(program)


def compile_fire_zpl_file(path: str | Path) -> dict[str, object]:
    return compile_fire_zpl_to_fmos_payload(Path(path).read_text(encoding="utf-8"))


def write_compiled_fire_zpl(path: str | Path, payload: dict[str, object], *, pretty: bool = True) -> None:
    output_path = Path(path)
    if pretty:
        output_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    else:
        output_path.write_text(json.dumps(payload, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")


__all__ = [
    "FIRE_FMOS_FILE_SCHEMA",
    "FireZplBinaryExpr",
    "FireZplCapExpr",
    "FireZplClampExpr",
    "FireZplConstExpr",
    "FireZplDiagnosticError",
    "FireZplExactParamExpr",
    "FireZplPositivePartExpr",
    "FireZplProgram",
    "FireZplSourceBoundExpr",
    "compile_fire_zpl_file",
    "compile_fire_zpl_program_to_fmos_payload",
    "compile_fire_zpl_to_fmos_payload",
    "parse_fire_zpl_source",
    "parse_zpl_expression",
    "parse_zpl_expression_ast",
    "write_compiled_fire_zpl",
    "zpl_expr_to_fire_expr",
]
