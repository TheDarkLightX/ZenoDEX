from __future__ import annotations

from dataclasses import dataclass
from typing import Literal, Mapping

from src.fire.verifier.cert_v1 import (
    FireCertEnv,
    FireCertNode,
    FireIntervalCertificate,
    binary_node,
    const_node,
    exact_param_node,
    source_bound_node,
)


FireExprOp = Literal["add", "sub", "mul", "min", "max"]
_DIMENSIONLESS_UNITS = {"Scalar", "Index", "Rate", "Bool"}


@dataclass(frozen=True)
class FireUnit:
    label: str
    dims: tuple[tuple[str, int], ...]
    is_zero: bool = False

    @property
    def is_dimensionless(self) -> bool:
        return not self.dims


@dataclass(frozen=True)
class FireConstExpr:
    value: int


@dataclass(frozen=True)
class FireExactParamExpr:
    name: str

    def __post_init__(self) -> None:
        if not isinstance(self.name, str) or not self.name:
            raise ValueError("exact param name must be a non-empty string")


@dataclass(frozen=True)
class FireSourceBoundExpr:
    name: str

    def __post_init__(self) -> None:
        if not isinstance(self.name, str) or not self.name:
            raise ValueError("source bound name must be a non-empty string")


@dataclass(frozen=True)
class FireBinaryExpr:
    op: FireExprOp
    left: "FireExpr"
    right: "FireExpr"

    def __post_init__(self) -> None:
        if self.op not in {"add", "sub", "mul", "min", "max"}:
            raise ValueError(f"unsupported fire expression op: {self.op}")


FireExpr = FireConstExpr | FireExactParamExpr | FireSourceBoundExpr | FireBinaryExpr


def _normalize_fire_expr(expr: object) -> FireExpr:
    if isinstance(expr, (FireConstExpr, FireExactParamExpr, FireSourceBoundExpr, FireBinaryExpr)):
        return expr

    kind = type(expr).__name__
    if kind == "FireConstExpr" and hasattr(expr, "value"):
        return FireConstExpr(value=getattr(expr, "value"))
    if kind == "FireExactParamExpr" and hasattr(expr, "name"):
        return FireExactParamExpr(name=getattr(expr, "name"))
    if kind == "FireSourceBoundExpr" and hasattr(expr, "name"):
        return FireSourceBoundExpr(name=getattr(expr, "name"))
    if kind == "FireBinaryExpr" and all(hasattr(expr, field) for field in ("op", "left", "right")):
        return FireBinaryExpr(
            op=getattr(expr, "op"),
            left=_normalize_fire_expr(getattr(expr, "left")),
            right=_normalize_fire_expr(getattr(expr, "right")),
        )
    raise TypeError(f"unsupported fire expression type: {type(expr)!r}")


def _canonical_dims(raw_dims: Mapping[str, int]) -> tuple[tuple[str, int], ...]:
    return tuple(sorted((asset, power) for asset, power in raw_dims.items() if power != 0))


def _render_unit_from_dims(dims: tuple[tuple[str, int], ...]) -> str:
    if not dims:
        return "Scalar"
    if len(dims) == 1 and dims[0][1] == 1:
        return f"Amount[{dims[0][0]}]"
    if len(dims) == 2:
        positive = [asset for asset, power in dims if power == 1]
        negative = [asset for asset, power in dims if power == -1]
        if len(positive) == 1 and len(negative) == 1:
            return f"Price[{negative[0]}/{positive[0]}]"
    pieces = [f"{asset}^{power}" for asset, power in dims]
    return "Unit[" + "*".join(pieces) + "]"


def parse_fire_unit(unit: str) -> FireUnit:
    if not isinstance(unit, str) or not unit:
        raise ValueError("fire unit must be a non-empty string")
    if unit in _DIMENSIONLESS_UNITS:
        return FireUnit(label=unit, dims=())
    if unit.startswith("Amount[") and unit.endswith("]"):
        asset = unit[len("Amount[") : -1]
        if not asset:
            raise ValueError("Amount unit must include an asset")
        return FireUnit(label=unit, dims=((asset, 1),))
    if unit.startswith("Price[") and unit.endswith("]"):
        pair = unit[len("Price[") : -1]
        if "/" not in pair:
            raise ValueError("Price unit must use A/B form")
        base, quote = pair.split("/", 1)
        if not base or not quote:
            raise ValueError("Price unit must include both assets")
        return FireUnit(label=unit, dims=_canonical_dims({base: -1, quote: 1}))
    raise ValueError(f"unsupported FIRE unit syntax: {unit}")


def zero_fire_unit() -> FireUnit:
    return FireUnit(label="Zero", dims=(), is_zero=True)


def _require_same_additive_unit(op: str, left: FireUnit, right: FireUnit) -> FireUnit:
    if left.is_zero:
        return right
    if right.is_zero:
        return left
    if left.label != right.label:
        raise ValueError(f"{op} requires matching units, got {left.label} and {right.label}")
    return left


def _multiply_units(left: FireUnit, right: FireUnit) -> FireUnit:
    if left.is_zero:
        return right
    if right.is_zero:
        return left
    if left.is_dimensionless and right.is_dimensionless:
        return parse_fire_unit("Scalar")
    if left.is_dimensionless:
        return right
    if right.is_dimensionless:
        return left
    dims_map: dict[str, int] = {}
    for asset, power in left.dims:
        dims_map[asset] = dims_map.get(asset, 0) + power
    for asset, power in right.dims:
        dims_map[asset] = dims_map.get(asset, 0) + power
    dims = _canonical_dims(dims_map)
    return FireUnit(label=_render_unit_from_dims(dims), dims=dims)


def const_expr(value: int) -> FireConstExpr:
    return FireConstExpr(value=value)


def exact_param_expr(name: str) -> FireExactParamExpr:
    return FireExactParamExpr(name=name)


def source_bound_expr(name: str) -> FireSourceBoundExpr:
    return FireSourceBoundExpr(name=name)


def add_expr(left: FireExpr, right: FireExpr) -> FireBinaryExpr:
    return FireBinaryExpr(op="add", left=left, right=right)


def sub_expr(left: FireExpr, right: FireExpr) -> FireBinaryExpr:
    return FireBinaryExpr(op="sub", left=left, right=right)


def mul_expr(left: FireExpr, right: FireExpr) -> FireBinaryExpr:
    return FireBinaryExpr(op="mul", left=left, right=right)


def min_expr(left: FireExpr, right: FireExpr) -> FireBinaryExpr:
    return FireBinaryExpr(op="min", left=left, right=right)


def max_expr(left: FireExpr, right: FireExpr) -> FireBinaryExpr:
    return FireBinaryExpr(op="max", left=left, right=right)


def positive_part_expr(expr: FireExpr) -> FireExpr:
    return max_expr(expr, const_expr(0))


def cap_expr(expr: FireExpr, cap: FireExpr) -> FireExpr:
    return min_expr(expr, cap)


def clamp_expr(expr: FireExpr, lower: FireExpr, upper: FireExpr) -> FireExpr:
    return min_expr(max_expr(expr, lower), upper)


def capped_call_expr(*, underlying: FireExpr, strike: FireExpr, cap: FireExpr, notional: FireExpr) -> FireExpr:
    return mul_expr(notional, cap_expr(positive_part_expr(sub_expr(underlying, strike)), cap))


def capped_index_note_expr(*, underlying: FireExpr, cap: FireExpr, notional: FireExpr) -> FireExpr:
    return mul_expr(notional, cap_expr(underlying, cap))


def lp_loss_cover_expr(
    *,
    hodl_value: FireExpr,
    lp_value: FireExpr,
    deductible: FireExpr,
    cap: FireExpr,
    notional: FireExpr,
) -> FireExpr:
    return mul_expr(
        notional,
        cap_expr(
            positive_part_expr(
                sub_expr(
                    sub_expr(hodl_value, lp_value),
                    deductible,
                )
            ),
            cap,
        ),
    )


def infer_fire_expr_unit(
    expr: FireExpr,
    *,
    exact_units: Mapping[str, str],
    source_units: Mapping[str, str],
) -> str:
    return _infer_fire_expr_unit(expr, exact_units=exact_units, source_units=source_units).label


def _infer_fire_expr_unit(
    expr: FireExpr,
    *,
    exact_units: Mapping[str, str],
    source_units: Mapping[str, str],
) -> FireUnit:
    expr = _normalize_fire_expr(expr)
    if isinstance(expr, FireConstExpr):
        if expr.value == 0:
            return zero_fire_unit()
        return parse_fire_unit("Scalar")
    if isinstance(expr, FireExactParamExpr):
        if expr.name not in exact_units:
            raise KeyError(f"missing exact unit: {expr.name}")
        return parse_fire_unit(exact_units[expr.name])
    if isinstance(expr, FireSourceBoundExpr):
        if expr.name not in source_units:
            raise KeyError(f"missing source unit: {expr.name}")
        return parse_fire_unit(source_units[expr.name])
    if isinstance(expr, FireBinaryExpr):
        left = _infer_fire_expr_unit(expr.left, exact_units=exact_units, source_units=source_units)
        right = _infer_fire_expr_unit(expr.right, exact_units=exact_units, source_units=source_units)
        if expr.op in {"add", "sub", "min", "max"}:
            return _require_same_additive_unit(expr.op, left, right)
        if expr.op == "mul":
            return _multiply_units(left, right)
        raise ValueError(f"unsupported fire expression op: {expr.op}")
    raise TypeError(f"unsupported fire expression type: {type(expr)!r}")


def compile_interval_expression_node(expr: FireExpr, env: FireCertEnv) -> FireCertNode:
    expr = _normalize_fire_expr(expr)
    if isinstance(expr, FireConstExpr):
        return const_node(expr.value)
    if isinstance(expr, FireExactParamExpr):
        return exact_param_node(expr.name, env.exact(expr.name))
    if isinstance(expr, FireSourceBoundExpr):
        return source_bound_node(expr.name, env.source_bound(expr.name))
    if isinstance(expr, FireBinaryExpr):
        return binary_node(
            expr.op,
            compile_interval_expression_node(expr.left, env),
            compile_interval_expression_node(expr.right, env),
        )
    raise TypeError(f"unsupported fire expression type: {type(expr)!r}")


def compile_interval_expression_certificate(expr: FireExpr, env: FireCertEnv) -> FireIntervalCertificate:
    return FireIntervalCertificate(root=compile_interval_expression_node(expr, env))


__all__ = [
    "FireBinaryExpr",
    "FireConstExpr",
    "FireExactParamExpr",
    "FireExpr",
    "FireSourceBoundExpr",
    "FireUnit",
    "add_expr",
    "cap_expr",
    "capped_call_expr",
    "capped_index_note_expr",
    "clamp_expr",
    "compile_interval_expression_certificate",
    "compile_interval_expression_node",
    "const_expr",
    "exact_param_expr",
    "infer_fire_expr_unit",
    "lp_loss_cover_expr",
    "max_expr",
    "min_expr",
    "mul_expr",
    "parse_fire_unit",
    "positive_part_expr",
    "source_bound_expr",
    "sub_expr",
]
