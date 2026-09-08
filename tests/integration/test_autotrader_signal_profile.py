from __future__ import annotations

import hashlib
from dataclasses import FrozenInstanceError
from itertools import product
from pathlib import Path

import pytest

from src.integration.autotrader_signal_profile import (
    ADVISORY_ONLY_TYPE,
    AUTH_TYPE,
    CODE_RANGE,
    CODE_RESERVED,
    CODE_TYPE,
    FRESHNESS_TYPE,
    PROFILE_TYPE,
    SOURCE_INDEX_RANGE,
    SOURCE_INDEX_TYPE,
    TRUST_INDEX_RANGE,
    TRUST_INDEX_TYPE,
    SignalProfile,
    decode_profile,
    encode_profile,
)
from src.tau_workbench.models import Stage, Task
from src.tau_workbench.native import replay_bundles
from src.tau_workbench.programs import Program, analyze

_ROOT = Path(__file__).parents[2]
_KERNEL_PATHS = (
    _ROOT / "src/kernels/python/external_signal_profile_encode_v2.py",
    _ROOT / "src/kernels/python/external_signal_profile_decode_v2.py",
)


def _profile(
    source_index: int,
    trust_index: int,
    freshness_ok: bool,
    auth_ok: bool,
    advisory_only: bool,
) -> SignalProfile:
    return SignalProfile(
        source_index=source_index,
        trust_index=trust_index,
        freshness_ok=freshness_ok,
        auth_ok=auth_ok,
        advisory_only=advisory_only,
    )


def test_all_128_profiles_have_distinct_canonical_roundtrips() -> None:
    profiles = tuple(
        _profile(source, trust, fresh, auth, advisory)
        for source, trust, fresh, auth, advisory in product(
            range(4), range(4), (False, True), (False, True), (False, True)
        )
    )
    assert len(profiles) == 128
    encoded = tuple(encode_profile(profile) for profile in profiles)
    assert set(encoded) == set(range(128))
    assert tuple(decode_profile(code) for code in encoded) == profiles


def test_wire_encoding_matches_the_canonical_bit_layout() -> None:
    profile = _profile(3, 2, True, False, True)
    semantic_word = (3 << 5) | (2 << 3) | (1 << 2) | 1
    expected_wire = (3) | (2 << 2) | (1 << 4) | (1 << 6)
    assert semantic_word == 0b1110101
    assert encode_profile(profile) == expected_wire
    assert decode_profile(expected_wire) == profile


@pytest.mark.parametrize("code", range(128, 256))
def test_reserved_bit_codes_reject_with_stable_code(code: int) -> None:
    with pytest.raises(ValueError, match=f"^{CODE_RESERVED}$"):
        decode_profile(code)


@pytest.mark.parametrize(
    ("value", "error_type", "error_code"),
    [
        (True, TypeError, CODE_TYPE),
        (1.0, TypeError, CODE_TYPE),
        ("1", TypeError, CODE_TYPE),
        (None, TypeError, CODE_TYPE),
        (-1, ValueError, CODE_RANGE),
        (256, ValueError, CODE_RANGE),
    ],
)
def test_decode_rejects_non_u8_inputs_with_stable_codes(
    value: object, error_type: type[Exception], error_code: str
) -> None:
    with pytest.raises(error_type, match=f"^{error_code}$"):
        decode_profile(value)


@pytest.mark.parametrize(
    ("field", "error_type", "error_code"),
    [
        ("source_index", TypeError, SOURCE_INDEX_TYPE),
        ("trust_index", TypeError, TRUST_INDEX_TYPE),
        ("freshness_ok", TypeError, FRESHNESS_TYPE),
        ("auth_ok", TypeError, AUTH_TYPE),
        ("advisory_only", TypeError, ADVISORY_ONLY_TYPE),
    ],
)
def test_profile_fields_require_exact_types(
    field: str, error_type: type[Exception], error_code: str
) -> None:
    values: dict[str, object] = {
        "source_index": 0,
        "trust_index": 0,
        "freshness_ok": False,
        "auth_ok": False,
        "advisory_only": False,
    }
    values[field] = "0" if field.endswith("index") else 1
    with pytest.raises(error_type, match=f"^{error_code}$"):
        SignalProfile(**values)  # type: ignore[arg-type]


@pytest.mark.parametrize(
    ("field", "error_code"),
    [("source_index", SOURCE_INDEX_RANGE), ("trust_index", TRUST_INDEX_RANGE)],
)
def test_profile_indices_reject_out_of_range_values(field: str, error_code: str) -> None:
    values: dict[str, object] = {
        "source_index": 0,
        "trust_index": 0,
        "freshness_ok": False,
        "auth_ok": False,
        "advisory_only": False,
    }
    values[field] = 4
    with pytest.raises(ValueError, match=f"^{error_code}$"):
        SignalProfile(**values)  # type: ignore[arg-type]


def test_profile_is_exact_and_frozen() -> None:
    profile = _profile(0, 0, False, False, False)
    assert type(profile) is SignalProfile
    with pytest.raises(FrozenInstanceError):
        profile.source_index = 1  # type: ignore[misc]
    with pytest.raises((AttributeError, TypeError)):
        profile.extra = 1  # type: ignore[attr-defined]

    class DerivedSignalProfile(SignalProfile):
        pass

    derived = DerivedSignalProfile(0, 0, False, False, False)
    with pytest.raises(TypeError, match=f"^{PROFILE_TYPE}$"):
        encode_profile(derived)


def test_kernel_source_bytes_are_the_only_native_inputs_and_cover_all_256_values() -> None:
    expected_by_path = (
        tuple(
            (
                (value >> 5)
                | ((value & 24) >> 1)
                | ((value & 4) << 2)
                | ((value & 2) << 4)
                | ((value & 1) << 6)
            )
            if value < 128
            else 255
            for value in range(256)
        ),
        tuple(
            (
                ((value & 3) << 5)
                | ((value & 12) << 1)
                | ((value & 16) >> 2)
                | ((value & 32) >> 4)
                | ((value & 64) >> 6)
            )
            if value < 128
            else 255
            for value in range(256)
        ),
    )
    for path, expected in zip(_KERNEL_PATHS, expected_by_path, strict=True):
        source = path.read_bytes()
        program = Program(path.stem, source)
        assert analyze(program, 8).outputs == expected
        task = Task(
            name=f"{path.stem}_task",
            bits=8,
            stages=(Stage(path.stem, (program,)),),
            inputs=tuple(range(256)),
            expected=expected,
            anchor=(path.stem,),
        )
        replay = replay_bundles(task, ((0,),))
        assert replay.outcomes == (None,)
        assert replay.component_inputs_checked == 256
        assert replay.pipeline_inputs_checked == 256
        assert replay.source_hashes == ((hashlib.sha256(source).hexdigest(),),)
