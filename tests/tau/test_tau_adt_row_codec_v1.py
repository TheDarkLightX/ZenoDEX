from __future__ import annotations

from pathlib import Path

import pytest

from experiments.tau_adt_rows_v1.row_codec import (
    INPUT_BANNER_V1,
    MAX_ATOMS_V2,
    MAX_BV1280_VALUE_V1,
    MAX_IDENTITY_BYTES_V1,
    MAX_ROWS_V1,
    MAX_STDOUT_BYTES_V1,
    OUTPUT_BANNER_V1,
    TYPE_BANNER_V1,
    decode_output_v1,
    encode_rows_v1,
)
from src.core.global_settlement_primitives_v2 import EconomicAmountV2

ROOT = Path(__file__).resolve().parents[2]


def _pack_identity(identity: str) -> str:
    return str(
        int.from_bytes(
            identity.encode("ascii").ljust(MAX_IDENTITY_BYTES_V1, b"\x00"),
            "big",
        )
    )


def _row(index: int, amount_atoms: int = 0) -> EconomicAmountV2:
    return EconomicAmountV2(
        owner=f"owner-{index:02d}",
        asset=f"asset-{index:02d}",
        custody_domain="custody-main",
        amount_atoms=amount_atoms,
    )


def _line(row: EconomicAmountV2, index: int) -> str:
    return (
        f'o[{index}] := {{ owner: "{_pack_identity(row.owner)}", '
        f'asset: "{_pack_identity(row.asset)}", '
        f'custody_domain: "{_pack_identity(row.custody_domain)}", '
        f'amount_atoms: "{row.amount_atoms}" }}'
    )


def _input_line(row: EconomicAmountV2) -> str:
    return _line(row, 0).split(" := ", 1)[1]


def _stdout(rows: tuple[EconomicAmountV2, ...], *, timing: bool = True) -> str:
    lines = [TYPE_BANNER_V1, INPUT_BANNER_V1, OUTPUT_BANNER_V1]
    for index, row in enumerate(rows):
        lines.append(_line(row, index))
        if timing:
            lines.append("\tstep: 1.25 ms")
    return "\n".join(lines) + "\n\n"


@pytest.mark.parametrize(
    ("count", "amounts"),
    (
        (0, ()),
        (1, (MAX_ATOMS_V2,)),
        (4, (0, 1, MAX_ATOMS_V2 - 1, MAX_ATOMS_V2)),
        (8, (0, 1, 2, 3, MAX_ATOMS_V2 - 2, MAX_ATOMS_V2 - 1, MAX_ATOMS_V2, 7)),
    ),
)
def test_fixed_row_vectors_round_trip(count: int, amounts: tuple[int, ...]) -> None:
    rows = tuple(_row(index, amounts[index]) for index in range(count))

    encoded = encode_rows_v1(rows)
    assert encoded == "".join(_input_line(row) + "\n" for row in rows)
    assert decode_output_v1(_stdout(rows), "", expected_count=count) == rows


def test_full_width_ascii_identity_is_lossless() -> None:
    row = EconomicAmountV2("!" * 160, "~" * 160, "A" * 160, 0)
    encoded = encode_rows_v1((row,))
    assert _pack_identity(row.owner) in encoded
    assert _pack_identity(row.asset) in encoded
    assert _pack_identity(row.custody_domain) in encoded
    assert decode_output_v1(_stdout((row,)), "", expected_count=1) == (row,)


def test_single_ascii_identity_matches_independent_fixed_width_integer() -> None:
    row = EconomicAmountV2("A", "B", "C", 0)
    expected = (
        '{ owner: "'
        + str(65 * (256**159))
        + '", asset: "'
        + str(66 * (256**159))
        + '", custody_domain: "'
        + str(67 * (256**159))
        + '", amount_atoms: "0" }\n'
    )
    assert encode_rows_v1((row,)) == expected


def test_contract_is_the_exact_research_adt_shape() -> None:
    contract = (ROOT / "experiments" / "tau_adt_rows_v1" / "row_contract.tau").read_text(
        encoding="utf-8"
    )
    assert contract == (
        "type Row = {owner: bv[1280], asset: bv[1280], "
        "custody_domain: bv[1280], amount_atoms: bv[128]}.\n"
        'i:Row := in file("/dev/stdin").\n'
        "o:Row := out console.\n"
        "run o[t] = i[t].\n"
    )


def test_zero_rows_require_banners_but_need_no_timing() -> None:
    assert decode_output_v1(_stdout((), timing=False), "", expected_count=0) == ()
    with pytest.raises(ValueError):
        decode_output_v1("", "", expected_count=0)


def test_encode_requires_exact_owned_tuple_and_cap_precedes_item_validation() -> None:
    with pytest.raises(TypeError):
        encode_rows_v1([])
    with pytest.raises(ValueError, match="8-row"):
        encode_rows_v1((object(),) * (MAX_ROWS_V1 + 1))
    with pytest.raises(TypeError, match="exact EconomicAmountV2"):
        encode_rows_v1((object(),))

    class TupleSubclass(tuple[object, ...]):
        pass

    with pytest.raises(TypeError):
        encode_rows_v1(TupleSubclass())


def test_encode_rejects_duplicate_and_noncanonical_keys() -> None:
    duplicate = _row(0)
    with pytest.raises(ValueError, match="ordered and unique"):
        encode_rows_v1((duplicate, duplicate))
    with pytest.raises(ValueError, match="ordered and unique"):
        encode_rows_v1((_row(1), _row(0)))


def test_encode_rejects_forged_exact_rows_with_typed_errors() -> None:
    missing = object.__new__(EconomicAmountV2)
    with pytest.raises(TypeError, match="malformed"):
        encode_rows_v1((missing,))

    forged = object.__new__(EconomicAmountV2)
    object.__setattr__(forged, "owner", ["owner-00"])
    object.__setattr__(forged, "asset", "asset-00")
    object.__setattr__(forged, "custody_domain", "custody-main")
    object.__setattr__(forged, "amount_atoms", 0)
    with pytest.raises(TypeError, match="owner"):
        encode_rows_v1((forged,))


def test_decode_requires_empty_stderr_exact_count_and_exact_types() -> None:
    rows = (_row(0, 1),)
    with pytest.raises(ValueError, match="stderr"):
        decode_output_v1(_stdout(rows), "diagnostic", expected_count=1)
    with pytest.raises(TypeError):
        decode_output_v1(_stdout(rows).encode(), "", expected_count=1)
    with pytest.raises(TypeError):
        decode_output_v1(_stdout(rows), "", expected_count=True)
    with pytest.raises(ValueError):
        decode_output_v1(_stdout(rows), "", expected_count=MAX_ROWS_V1 + 1)
    with pytest.raises(ValueError):
        decode_output_v1(_stdout(rows), "", expected_count=0)


@pytest.mark.parametrize("mutation", ("missing", "extra", "duplicate", "reordered"))
def test_decode_rejects_missing_extra_duplicate_or_reordered_timestep(mutation: str) -> None:
    rows = (_row(0, 1), _row(1, 2))
    rendered = [_line(row, index) for index, row in enumerate(rows)]
    if mutation == "missing":
        rendered = rendered[:1]
    elif mutation == "extra":
        rendered.append(_line(_row(2, 3), 2))
    elif mutation == "duplicate":
        rendered[1] = _line(rows[1], 0)
    else:
        rendered[0], rendered[1] = rendered[1].replace("o[0]", "o[1]"), rendered[0].replace(
            "o[1]", "o[0]"
        )
    output = "\n".join((TYPE_BANNER_V1, INPUT_BANNER_V1, OUTPUT_BANNER_V1, *rendered))
    with pytest.raises(ValueError):
        decode_output_v1(output, "", expected_count=2)


def test_decode_rejects_noncanonical_timestep_index() -> None:
    row = _row(0, 1)
    line = _line(row, 0).replace("o[0]", "o[00]", 1)
    output = "\n".join((TYPE_BANNER_V1, INPUT_BANNER_V1, OUTPUT_BANNER_V1, line))
    with pytest.raises(ValueError, match="indices"):
        decode_output_v1(output, "", expected_count=1)


def test_decode_rejects_duplicate_or_noncanonical_keys_after_timestep_checks() -> None:
    duplicate_key = (_row(0, 1), EconomicAmountV2("owner-00", "asset-00", "custody-main", 2))
    with pytest.raises(ValueError, match="ordered and unique"):
        decode_output_v1(_stdout(duplicate_key), "", expected_count=2)
    reversed_keys = (_row(1, 1), _row(0, 2))
    with pytest.raises(ValueError, match="ordered and unique"):
        decode_output_v1(_stdout(reversed_keys), "", expected_count=2)


@pytest.mark.parametrize(
    "bad_field",
    (
        "0",
        "01",
        "-1",
        "+1",
        "1.0",
        str(MAX_BV1280_VALUE_V1 + 1),
    ),
)
def test_decode_rejects_bad_or_overflowing_identity_decimal(bad_field: str) -> None:
    row = _row(0, 1)
    line = _line(row, 0).replace(_pack_identity(row.owner), bad_field, 1)
    output = "\n".join((TYPE_BANNER_V1, INPUT_BANNER_V1, OUTPUT_BANNER_V1, line))
    with pytest.raises(ValueError):
        decode_output_v1(output, "", expected_count=1)


def test_decode_rejects_interior_nul_identity_and_amount_overflow() -> None:
    row = _row(0, 1)
    interior_nul = str(int.from_bytes(b"A\x00B".ljust(160, b"\x00"), "big"))
    line = _line(row, 0).replace(_pack_identity(row.owner), interior_nul, 1)
    output = "\n".join((TYPE_BANNER_V1, INPUT_BANNER_V1, OUTPUT_BANNER_V1, line))
    with pytest.raises(ValueError):
        decode_output_v1(output, "", expected_count=1)

    amount_line = _line(row, 0).replace('amount_atoms: "1"', f'amount_atoms: "{MAX_ATOMS_V2 + 1}"')
    amount_output = "\n".join((TYPE_BANNER_V1, INPUT_BANNER_V1, OUTPUT_BANNER_V1, amount_line))
    with pytest.raises(ValueError):
        decode_output_v1(amount_output, "", expected_count=1)


def test_decode_rejects_diagnostics_bad_timing_and_resource_overflow() -> None:
    rows = (_row(0, 1),)
    prefix = "\n".join((TYPE_BANNER_V1, INPUT_BANNER_V1, OUTPUT_BANNER_V1))
    bad_timing = "\n".join((prefix, _line(rows[0], 0), "\tstep: NaN ms"))
    with pytest.raises(ValueError):
        decode_output_v1(bad_timing, "", expected_count=1)
    with pytest.raises(ValueError):
        decode_output_v1("x" * (MAX_STDOUT_BYTES_V1 + 1), "", expected_count=0)
    with pytest.raises(ValueError):
        decode_output_v1("\n".join((prefix, "Error: unresolved predicate")), "", expected_count=0)
