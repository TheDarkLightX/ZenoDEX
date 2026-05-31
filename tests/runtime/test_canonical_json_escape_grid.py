"""Canonical JSON escaping grid with an independent string encoder oracle.

The Kani contracts on canonical primitives deliberately avoid heap-heavy
`String`/`Vec` serialization. This test pins the highest-risk part of that
surface: JSON string escaping and object-key ordering across Python and Rust.
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[2]
if str(REPO) not in sys.path:
    sys.path.insert(0, str(REPO))

from src.state.canonical import canonical_json_bytes  # noqa: E402
from tools.runtime import canonical_primitives_lib as lib  # noqa: E402


def _escape_json_string_ref(value: str) -> str:
    out = ['"']
    for ch in value:
        code = ord(ch)
        if ch == '"':
            out.append('\\"')
        elif ch == "\\":
            out.append("\\\\")
        elif ch == "\b":
            out.append("\\b")
        elif ch == "\t":
            out.append("\\t")
        elif ch == "\n":
            out.append("\\n")
        elif ch == "\f":
            out.append("\\f")
        elif ch == "\r":
            out.append("\\r")
        elif code < 0x20:
            out.append(f"\\u{code:04x}")
        else:
            out.append(ch)
    out.append('"')
    return "".join(out)


def _json_ref(value):
    if value is None:
        return "null"
    if value is True:
        return "true"
    if value is False:
        return "false"
    if isinstance(value, int) and not isinstance(value, bool):
        return str(value)
    if isinstance(value, str):
        return _escape_json_string_ref(value)
    if isinstance(value, list):
        return "[" + ",".join(_json_ref(item) for item in value) + "]"
    if isinstance(value, dict):
        return "{" + ",".join(
            _escape_json_string_ref(key) + ":" + _json_ref(value[key])
            for key in sorted(value)
        ) + "}"
    raise TypeError(f"unsupported reference value {value!r}")


@pytest.fixture(scope="module")
def rust_bin():
    try:
        return lib.locate_or_build_cli()
    except lib.CanonicalShadowError as exc:  # pragma: no cover - environment dependent
        pytest.skip(f"rust shadow unavailable: {exc}")


def _assert_python_and_rust_match_ref(rust_bin, values: list) -> None:
    cases = [{"op": "json_bytes", "value": value} for value in values]
    rust = lib.run_rust(rust_bin, cases)
    for i, value in enumerate(values):
        expected = _json_ref(value).encode("utf-8")
        assert canonical_json_bytes(value) == expected, value
        assert rust[i] == {
            "index": i,
            "ok": True,
            "bytes": "0x" + expected.hex(),
            "hash": lib.sha256_hex(expected),
        }


def test_control_character_string_escaping_grid(rust_bin):
    values = [chr(code) for code in range(0x20)]
    values.extend(
        [
            '"',
            "\\",
            'quote"backslash\\',
            "".join(chr(code) for code in range(0x20)),
            "\x00middle\x1f",
            "é",
            "漢字",
            "😀",
        ]
    )
    _assert_python_and_rust_match_ref(rust_bin, values)


def test_object_key_order_and_key_escaping_grid(rust_bin):
    keys = [
        "\x00",
        "\x01",
        "\t",
        "\n",
        '"',
        "\\",
        "a",
        "aa",
        "b",
        "é",
        "漢",
        "😀",
    ]
    scrambled = {key: i for i, key in enumerate(reversed(keys))}
    nested = {
        "z": [scrambled, {"\x1f": "last-control", "plain": True}],
        "a": {"\n": "line", '"': "quote", "\\": "slash"},
    }
    _assert_python_and_rust_match_ref(rust_bin, [scrambled, nested])

    encoded = canonical_json_bytes(scrambled).decode("utf-8")
    expected_prefix = "{"
    assert encoded.startswith(expected_prefix + _escape_json_string_ref("\x00") + ":")
    assert encoded == _json_ref(scrambled)


def test_escape_grid_oracle_has_teeth():
    correct = _escape_json_string_ref("\n")
    planted_raw_newline = '"' + "\n" + '"'
    assert correct == '"\\n"'
    assert planted_raw_newline != correct
