"""Exact transcripts and source binding for the bounded economic replay."""

import fcntl
import os
from pathlib import Path
from subprocess import CompletedProcess

import pytest

from experiments.tau_economic_qualification_v1.runner import (
    Variant,
    decode_trace,
    encode_inputs,
    prepare,
    sealed_inputs,
    stream_banners,
)

ROOT = Path(__file__).resolve().parents[2]


def _prepared():
    path = ROOT / "src/tau_specs/recommended/nonce_replay_guard_v1.tau"
    return prepare("nonce_replay_guard_v1", path.read_bytes(), Variant.ORIGINAL)


def _result(tail: str, *, status: int = 0, stderr: str = ""):
    banners = stream_banners(_prepared(), (3, 4, 5))
    return CompletedProcess((), status, "\n".join(banners) + "\n" + tail, stderr)


def test_full_output_vector_and_independent_steps_are_retained():
    tail = "".join(f"o{i}[0] := 1\n" for i in range(1, 5))
    tail += "\tstep: 1.25 ms\n\n"
    tail += "".join(f"o{i}[1] := {int(i == 1)}\n" for i in range(1, 5))
    assert decode_trace(_result(tail), stream_banners(_prepared(), (3, 4, 5)), 4, 2) == (
        (1, 1, 1, 1), (1, 0, 0, 0),
    )


@pytest.mark.parametrize("tail", (
    "", "Error: incomplete\n", "o1[0] := 1\n",
    "o1[00] := 1\no2[0] := 1\no3[0] := 1\no4[0] := 1\n",
    "o1[0] := 1\no3[0] := 1\no2[0] := 1\no4[0] := 1\n",
    "o1[0] := 1\no2[0] := 1\no3[0] := 1\no4[0] := 01\n",
    "o1[0] := 1\no2[0] := 1\no3[0] := 1\no4[0] := a\n",
    "o1[0] := 1\no2[0] := 1\no3[0] := 1\no4[0] := 1\nError\n",
    "o1[0] := 1\no2[0] := 1\no3[0] := 1\no4[0] := 1\no1[1] := 1\n",
    "\tstep: 1 ms\no1[0] := 1\no2[0] := 1\no3[0] := 1\no4[0] := 1\n",
    "o1[0] := 1\no2[0] := 1\no3[0] := 1\no4[0] := 1\n\tstep: 1 ms\n\tstep: 1 ms\n",
))
def test_missing_reordered_noncanonical_or_diagnostic_output_rejects(tail):
    with pytest.raises(ValueError):
        decode_trace(_result(tail), stream_banners(_prepared(), (3, 4, 5)), 4, 1)


@pytest.mark.parametrize(("status", "stderr"), ((-11, ""), (1, ""), (0, "Error")))
def test_complete_output_does_not_hide_process_failure(status, stderr):
    tail = "".join(f"o{i}[0] := 1\n" for i in range(1, 5))
    with pytest.raises(ValueError):
        decode_trace(_result(tail, status=status, stderr=stderr),
                     stream_banners(_prepared(), (3, 4, 5)), 4, 1)


def test_source_drift_and_wrong_variant_cannot_be_qualified():
    source = (ROOT / "src/tau_specs/recommended/nonce_replay_guard_v1.tau").read_bytes()
    with pytest.raises(ValueError, match="source"):
        prepare("nonce_replay_guard_v1", source + b"\n", Variant.ORIGINAL)
    with pytest.raises(ValueError):
        prepare("nonce_replay_guard_v1", source, Variant.CONSERVATION_ELISION)
    with pytest.raises(ValueError):
        prepare("unknown", source, Variant.ORIGINAL)


def test_exact_banners_and_raw_newlines_are_required():
    tail = "".join(f"o{i}[0] := 1\n" for i in range(1, 5))
    original = _result(tail)
    for text in (original.stdout.replace("fd/3", "fd/9"),
                 original.stdout.replace("\n", "\r\n"), original.stdout + "x" * 65536):
        with pytest.raises(ValueError):
            decode_trace(CompletedProcess((), 0, text, ""),
                         stream_banners(_prepared(), (3, 4, 5)), 4, 1)


@pytest.mark.parametrize("rows", (
    (), ((1, 0),), ((1, 0, True),), ((-1, 0, 1),), ((2**32, 0, 1),),
    ((1, 0, 1),) * 9, [[1, 0, 1]],
))
def test_input_encoding_rejects_shape_type_and_width_drift(rows):
    with pytest.raises(ValueError):
        encode_inputs(_prepared(), rows)


def test_inputs_are_separate_sealed_streams_and_close_after_failure():
    payloads = encode_inputs(_prepared(), ((1, 0, 1), (2, 1, 2)))
    assert payloads == (b"1\n2\n", b"0\n1\n", b"1\n2\n")
    retained = ()
    with pytest.raises(ValueError, match="injected failure"):
        with sealed_inputs(payloads) as descriptors:
            retained = descriptors
            assert len(set(descriptors)) == 3
            for descriptor, expected in zip(descriptors, payloads, strict=True):
                assert os.read(descriptor, 100) == expected
                assert fcntl.fcntl(descriptor, fcntl.F_GET_SEALS) & fcntl.F_SEAL_WRITE
                with pytest.raises(OSError):
                    os.write(descriptor, b"0\n")
            raise ValueError("injected failure")
    for descriptor in retained:
        with pytest.raises(OSError):
            os.fstat(descriptor)
