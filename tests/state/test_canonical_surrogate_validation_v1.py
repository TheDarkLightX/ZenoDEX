"""Differential controls for the bounded canonical surrogate fast path.

The loop in ``_legacy_reject_surrogates`` is an independent frozen copy of the
pre-change implementation.  It remains the oracle for semantic comparisons;
the candidate is never used to derive expected outcomes.
"""

from __future__ import annotations

import random
from collections.abc import Callable, Iterator
from typing import Any

import pytest

import src.state.canonical as canonical_mod


def _legacy_reject_surrogates(value: str) -> None:
    """Frozen pre-change loop used as the independent semantic oracle."""
    for ch in value:
        ordinal = ord(ch)
        if 0xD800 <= ordinal <= 0xDFFF:
            raise TypeError("surrogate code points are not allowed in canonical encoding")


_CANDIDATE_REJECT_SURROGATES = canonical_mod._reject_surrogates
_Validator = Callable[[Any], None]


def _validator_outcome(validator: _Validator, value: Any) -> tuple[object, ...]:
    try:
        validator(value)
    except BaseException as exc:  # noqa: BLE001 - compare hostile iterator behavior exactly
        return ("raise", type(exc), str(exc))
    return ("return", None)


def _canonical_outcome(value: Any, validator: _Validator) -> tuple[object, ...]:
    previous = canonical_mod._reject_surrogates
    canonical_mod._reject_surrogates = validator  # type: ignore[assignment]
    try:
        try:
            return ("bytes", canonical_mod.canonical_json_bytes(value))
        except BaseException as exc:  # noqa: BLE001 - preserve exact error class/message
            return ("raise", type(exc), str(exc))
    finally:
        canonical_mod._reject_surrogates = previous


def _fixed_values() -> tuple[Any, ...]:
    return (
        "",
        "ascii",
        'quote"backslash\\newline\nreturn\rtab\t',
        "\x00\x01\x1f",
        "éΩ漢字😀",
        "\uD7FF",
        "\uD800",
        "\uDFFF",
        "\uE000",
        "\U0010FFFF",
        "prefix\uD800suffix",
        "\uD800prefix",
        "suffix\uDFFF",
        "\uD83D\uDE00",
        {"ascii": "", "controls": "\x00\n\\\"", "scalar": "Ω😀"},
        {"surrogate": "\uD800"},
        {"\uDFFF": "value"},
        {"outer": ["ok", {"inner": "\uD800"}, "tail"]},
        {"outer": [{"\uD800": "bad key"}]},
        {"float": 1.5, "surrogate": "\uD800"},
        {"surrogate": "\uD800", "float": 1.5},
        {1: "\uD800"},
        {"nested": {1: "value"}},
        ["ok", ["nested", "\uD800"], {"key": "value"}],
        ("tuple", "\uDFFF", {"ok": True}),
    )


def _seeded_string(rng: random.Random, *, length: int) -> str:
    alphabet = (
        "a",
        "z",
        "é",
        "Ω",
        "漢",
        "😀",
        "\x00",
        '"',
        "\\",
        "\uD7FF",
        "\uE000",
        "\U0010FFFF",
        "\uD800",
        "\uDFFF",
    )
    return "".join(rng.choice(alphabet) for _ in range(length))


def _seeded_values() -> Iterator[Any]:
    rng = random.Random(0xC4A001C)
    for index in range(128):
        first = _seeded_string(rng, length=rng.randrange(0, 48))
        second = _seeded_string(rng, length=rng.randrange(0, 24))
        yield {
            f"key-{index:03d}": first,
            "nested": [second, {"leaf": first[::-1]}, (first, second)],
        }


def test_all_unicode_codepoints_agree_with_frozen_loop_streaming() -> None:
    checked = 0
    accepted = 0
    rejected = 0
    for codepoint in range(0x110000):
        value = chr(codepoint)
        expected = _validator_outcome(_legacy_reject_surrogates, value)
        observed = _validator_outcome(_CANDIDATE_REJECT_SURROGATES, value)
        if observed != expected:
            raise AssertionError(
                f"U+{codepoint:04X} disagreed: expected {expected!r}, observed {observed!r}"
            )
        if expected[0] == "return":
            accepted += 1
        else:
            rejected += 1
        checked += 1
    assert checked == 0x110000
    assert accepted == 0x110000 - 0x800
    assert rejected == 0x800


@pytest.mark.parametrize("value", _fixed_values())
def test_nested_canonical_bytes_and_errors_match_frozen_loop(value: Any) -> None:
    expected = _canonical_outcome(value, _legacy_reject_surrogates)
    observed = _canonical_outcome(value, _CANDIDATE_REJECT_SURROGATES)
    assert observed == expected


def test_seeded_longer_nested_values_match_frozen_loop() -> None:
    for value in _seeded_values():
        expected = _canonical_outcome(value, _legacy_reject_surrogates)
        observed = _canonical_outcome(value, _CANDIDATE_REJECT_SURROGATES)
        assert observed == expected


class _IsAsciiRaises(str):
    def isascii(self) -> bool:
        raise AssertionError("hostile isascii override was called")

    def __iter__(self) -> Iterator[str]:
        return iter("ascii")


class _AsciiIteratorInjectsSurrogate(str):
    def isascii(self) -> bool:
        return True

    def __iter__(self) -> Iterator[str]:
        return iter("prefix\uD800suffix")


class _IteratorRaises(str):
    def isascii(self) -> bool:
        raise AssertionError("hostile isascii override was called")

    def __iter__(self) -> Iterator[str]:
        raise RuntimeError("hostile iterator was called")


@pytest.mark.parametrize(
    "value",
    (
        _IsAsciiRaises("ascii"),
        _AsciiIteratorInjectsSurrogate("ascii"),
        _IteratorRaises("ascii"),
    ),
)
def test_str_subclasses_preserve_legacy_isascii_and_iterator_behavior(value: str) -> None:
    expected = _canonical_outcome(value, _legacy_reject_surrogates)
    observed = _canonical_outcome(value, _CANDIDATE_REJECT_SURROGATES)
    assert observed == expected


@pytest.mark.parametrize("value", (None, b"ascii", 7, object(), ["ascii"]))
def test_non_str_inputs_preserve_legacy_type_errors(value: Any) -> None:
    expected = _validator_outcome(_legacy_reject_surrogates, value)
    observed = _validator_outcome(_CANDIDATE_REJECT_SURROGATES, value)
    assert observed == expected


def _mutant_skips_all_scanning(_value: Any) -> None:
    return None


def _mutant_removes_exact_type_guard(value: str) -> None:
    if value.isascii():
        return
    _legacy_reject_surrogates(value)


def test_fixed_oracle_kills_mutant_that_skips_all_scanning() -> None:
    value = "\uD800"
    expected = _validator_outcome(_legacy_reject_surrogates, value)
    mutant = _validator_outcome(_mutant_skips_all_scanning, value)
    assert expected == ("raise", TypeError, "surrogate code points are not allowed in canonical encoding")
    assert mutant != expected


def test_fixed_oracle_kills_mutant_that_removes_exact_type_guard() -> None:
    value = _AsciiIteratorInjectsSurrogate("ascii")
    expected = _validator_outcome(_legacy_reject_surrogates, value)
    mutant = _validator_outcome(_mutant_removes_exact_type_guard, value)
    assert expected == ("raise", TypeError, "surrogate code points are not allowed in canonical encoding")
    assert mutant != expected
