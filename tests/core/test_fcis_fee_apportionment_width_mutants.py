from __future__ import annotations

import ast
import inspect
import textwrap
from dataclasses import replace

import pytest

from src.core.fcis_fee_apportionment_transition import (
    FeeQuotaV2,
    compute_fee_quota_v2,
)
from src.core.fcis_fee_apportionment_values import (
    BPS_DENOMINATOR_V2,
    MAX_FEE_AMOUNT_V2,
)


def test_primitive_does_not_form_the_full_amount_weight_product() -> None:
    source = textwrap.dedent(inspect.getsource(compute_fee_quota_v2))
    tree = ast.parse(source)
    for node in ast.walk(tree):
        if not isinstance(node, ast.BinOp) or not isinstance(node.op, ast.Mult):
            continue
        if isinstance(node.left, ast.Name) and isinstance(node.right, ast.Name):
            names = {node.left.id, node.right.id}
            assert names != {"amount", "weight"}


def test_u256_maximum_is_exact_at_the_width_boundary() -> None:
    result = compute_fee_quota_v2(
        amount=MAX_FEE_AMOUNT_V2,
        weight=BPS_DENOMINATOR_V2 - 1,
    )
    assert type(result) is FeeQuotaV2
    quotient, residual = divmod(MAX_FEE_AMOUNT_V2, BPS_DENOMINATOR_V2)
    residual_product = residual * (BPS_DENOMINATOR_V2 - 1)
    assert result.base == quotient * (BPS_DENOMINATOR_V2 - 1) + (
        residual_product // BPS_DENOMINATOR_V2
    )
    assert result.remainder == residual_product % BPS_DENOMINATOR_V2


def test_quota_value_rejects_unchecked_base_growth() -> None:
    result = compute_fee_quota_v2(
        amount=MAX_FEE_AMOUNT_V2,
        weight=BPS_DENOMINATOR_V2,
    )
    assert type(result) is FeeQuotaV2
    with pytest.raises(ValueError, match="decomposition is inconsistent|base is outside"):
        replace(result, base=result.base + 1)
