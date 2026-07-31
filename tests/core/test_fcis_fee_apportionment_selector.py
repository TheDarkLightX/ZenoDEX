from __future__ import annotations

import ast
import inspect
import textwrap

import pytest

from src.core.fcis_fee_apportionment_selector import (
    FeeBonusSelectionV2,
    FeeBonusSelectorRejectCodeV2,
    FeeBonusSelectorRejectV2,
    select_fee_bonuses_v2,
)


def test_exact_three_role_vectors_and_fixed_ties() -> None:
    vectors = (
        ((0, 0, 0), (0, 0, 0), (0, 0, 0)),
        ((0, 0, 0), (1, 1, 2), (0, 0, 1)),
        ((0, 0, 0), (2, 2, 0), (1, 0, 0)),
        ((0, 0, 0), (1, 3, 0), (0, 1, 0)),
        ((0, 0, 0), (3, 3, 2), (1, 1, 0)),
        ((-2, 1, 1), (0, 1, 3), (0, 0, 1)),
    )

    for deficits, fractions, expected in vectors:
        result = select_fee_bonuses_v2(
            deficits=deficits,
            fractions=fractions,
            denominator=4,
        )
        assert type(result) is FeeBonusSelectionV2
        assert result.bonuses == expected
        assert sum(result.bonuses) == sum(fractions) // 4
        assert all(
            not bonus or fraction > 0
            for bonus, fraction in zip(result.bonuses, fractions, strict=True)
        )


@pytest.mark.parametrize(
    ("deficits", "fractions", "denominator", "code", "path"),
    (
        (
            [0, 0, 0],
            (1, 1, 2),
            4,
            FeeBonusSelectorRejectCodeV2.WRONG_EXACT_TYPE,
            ("deficits",),
        ),
        (
            (0, 0),
            (1, 1, 2),
            4,
            FeeBonusSelectorRejectCodeV2.WRONG_ARITY,
            ("deficits",),
        ),
        (
            (True, 0, 0),
            (1, 1, 2),
            4,
            FeeBonusSelectorRejectCodeV2.WRONG_EXACT_TYPE,
            ("deficits",),
        ),
        (
            (4, 0, 0),
            (1, 1, 2),
            4,
            FeeBonusSelectorRejectCodeV2.DEFICIT_OUT_OF_RANGE,
            ("deficits",),
        ),
        (
            (0, 0, 0),
            (4, 0, 0),
            4,
            FeeBonusSelectorRejectCodeV2.FRACTION_OUT_OF_RANGE,
            ("fractions",),
        ),
        (
            (0, 0, 0),
            (1, 0, 0),
            4,
            FeeBonusSelectorRejectCodeV2.NONDIVISIBLE_RESIDUALS,
            ("fractions",),
        ),
        (
            (0, 0, 0),
            (1, 1, 2),
            0,
            FeeBonusSelectorRejectCodeV2.INVALID_DENOMINATOR,
            ("denominator",),
        ),
    ),
)
def test_selector_rejects_invalid_shapes_and_relation_inputs(
    deficits: object,
    fractions: object,
    denominator: object,
    code: FeeBonusSelectorRejectCodeV2,
    path: tuple[str, ...],
) -> None:
    result = select_fee_bonuses_v2(
        deficits=deficits,
        fractions=fractions,
        denominator=denominator,
    )
    assert result == FeeBonusSelectorRejectV2(code, path)


def test_positive_support_excludes_zero_remainder_role() -> None:
    result = select_fee_bonuses_v2(
        deficits=(0, 0, 0),
        fractions=(0, 2, 2),
        denominator=4,
    )
    assert type(result) is FeeBonusSelectionV2
    assert result.bonuses == (0, 1, 0)


def test_selector_source_has_no_unordered_mapping_comprehension() -> None:
    source = textwrap.dedent(inspect.getsource(select_fee_bonuses_v2))
    tree = ast.parse(source)
    assert not any(isinstance(node, (ast.Dict, ast.DictComp)) for node in ast.walk(tree))
