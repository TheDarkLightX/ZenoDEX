"""Measured, bounded research execution of four existing Tau economic contracts.

Each input stream receives its own sealed file. The returned Boolean traces
are observations on supplied values, with no authenticated state or authority.
"""

from __future__ import annotations

import fcntl
import hashlib
import os
import re
from contextlib import contextmanager
from dataclasses import dataclass
from enum import Enum
from subprocess import CompletedProcess
from time import perf_counter_ns
from typing import Iterator

from experiments.tau_adt_rows_v1.execution import run_bounded
from src.integration.tau_runner import (
    extract_always_exprs,
    extract_stream_types,
    inline_definitions,
    normalize_spec_text,
    parse_definitions,
)

ENGINE_OPTIONS = (
    "--severity", "error", "--charvar", "false", "--blasting", "false",
    "--max-flag-search-steps", "0", "--color", "false", "--evaluate",
)
NORMALIZER_SHA256 = "d2aeba75d26f5b28e7aa01890da4ab2c54678fc8a891c6bdac231a4b7bed3298"
SPEC_SUBJECTS = (
    ("nonce_replay_guard_v1", "231f592b53e567c04951afff0aee5f5d9021a1d6a77ba0d9e68e866f0123a15a",
     ("bv[32]",) * 3, 4),
    ("nonce_manager_v1", "23fd3ca529ea8ed601ab21a97bc83cf97c74d949b6d51b11cdc4b893b25e1f73",
     ("bv[32]",) * 2, 1),
    ("transfer_hook_guard_v1", "64fa492391e9138b6d44bd39a0cdc4d1bba0f8c0b79d6d753a076838946a67c6",
     ("bv[32]",) * 5 + ("sbf",), 4),
    ("zusd_transfer_guard_v1", "6dcdde96e8c5a80b3392fd22b41d255a87f7293d8b1f79a817712730c33413ef",
     ("sbf",) * 6, 4),
)
_TIMING = re.compile(r"\tstep: [0-9]{1,12}(?:\.[0-9]{1,12})? ms")
_OUTPUT = re.compile(r"o([1-4])\[([0-7])\] := ([01])")


class Variant(Enum):
    ORIGINAL = "original"
    CONSERVATION_ELISION = "conservation_elision"


@dataclass(frozen=True)
class PreparedSpec:
    spec_id: str
    variant: Variant
    source_sha256: str
    selected_source_sha256: str
    expression: str
    input_types: tuple[str, ...]
    output_count: int


@dataclass(frozen=True)
class TraceObservation:
    outputs: tuple[tuple[int, ...], ...]
    elapsed_ns: int
    program_sha256: str
    input_sha256: tuple[str, ...]
    stdout_sha256: str
    stderr_sha256: str


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def prepare(spec_id: str, source: bytes, variant: Variant) -> PreparedSpec:
    """Inline the exact pinned source through the existing Tau normalizer.

    The experimental elision retains every output relation and removes only
    the two arithmetic conjuncts checked by the independent QF_BV miter.
    """
    subject = next((item for item in SPEC_SUBJECTS if item[0] == spec_id), None)
    if subject is None or type(source) is not bytes or sha256(source) != subject[1]:
        raise ValueError("unknown or changed Tau source subject")
    if type(variant) is not Variant:
        raise ValueError("unknown Tau variant")
    selected = source.decode("ascii")
    if variant is Variant.CONSERVATION_ELISION:
        if spec_id != "transfer_hook_guard_v1":
            raise ValueError("conservation elision is only defined for the transfer hook")
        from .conservation_equivalence import candidate_source
        selected = candidate_source(selected)
    normalized = normalize_spec_text(selected)
    clauses = extract_always_exprs(normalized)
    if len(clauses) != 1:
        raise ValueError("expected one complete always clause")
    expected_types = {f"i{i}": kind for i, kind in enumerate(subject[2], 1)}
    expected_types.update({f"o{i}": "sbf" for i in range(1, subject[3] + 1)})
    if extract_stream_types(normalized) != expected_types:
        raise ValueError("Tau stream ABI drift")
    expression = inline_definitions(clauses[0], parse_definitions(normalized))
    if len(expression) > 16384:
        raise ValueError("Tau expression exceeds research ceiling")
    return PreparedSpec(spec_id, variant, subject[1], sha256(selected.encode("ascii")),
                        expression, subject[2], subject[3])


def stream_banners(spec: PreparedSpec, inputs: tuple[int, ...]) -> tuple[str, ...]:
    if len(inputs) != len(spec.input_types):
        raise ValueError("input descriptor cardinality mismatch")
    banners = tuple(f"[{i}] i{i}:{kind} := in /proc/self/fd/{fd}."
                    for i, (kind, fd) in enumerate(zip(spec.input_types, inputs, strict=True), 1))
    return banners + tuple(f"[{len(inputs) + i}] o{i}:sbf := out console."
                           for i in range(1, spec.output_count + 1))


def decode_trace(
    result: CompletedProcess[str], banners: tuple[str, ...], output_count: int, steps: int,
) -> tuple[tuple[int, ...], ...]:
    """Require exact nonempty lines and a normal exit, ignoring blank LF lines.

    This checks the complete Boolean trace; the raw transcript hash separately
    retains timing and blank lines. CR and non-ASCII text always reject.
    """
    if (type(output_count) is not int or type(steps) is not int
            or not 1 <= output_count <= 4 or not 1 <= steps <= 8):
        raise ValueError("unsupported trace dimensions")
    if (result.returncode != 0 or result.stderr or type(result.stdout) is not str
            or len(result.stdout) > 65536 or not result.stdout.isascii() or "\r" in result.stdout):
        raise ValueError("failed or noncanonical Tau process result")
    lines = tuple(line for line in result.stdout.split("\n") if line)
    if lines[:len(banners)] != banners:
        raise ValueError("unexpected Tau stream banners")
    values: list[int] = []
    timing_allowed = False
    for line in lines[len(banners):]:
        if _TIMING.fullmatch(line):
            if not timing_allowed:
                raise ValueError("misplaced Tau timing")
            timing_allowed = False
            continue
        match = _OUTPUT.fullmatch(line)
        if (match is None or len(values) >= output_count * steps
                or int(match[1]) != len(values) % output_count + 1
                or int(match[2]) != len(values) // output_count):
            raise ValueError("unexpected, missing or extra Tau output")
        values.append(int(match[3]))
        timing_allowed = len(values) % output_count == 0
    if len(values) != output_count * steps:
        raise ValueError("incomplete Tau output trace")
    return tuple(tuple(values[i:i + output_count]) for i in range(0, len(values), output_count))


def encode_inputs(spec: PreparedSpec, rows: tuple[tuple[int, ...], ...]) -> tuple[bytes, ...]:
    if type(rows) is not tuple or not 1 <= len(rows) <= 8:
        raise ValueError("expected one to eight immutable input rows")
    for row in rows:
        if type(row) is not tuple or len(row) != len(spec.input_types):
            raise ValueError("input row does not match the exact stream ABI")
        for value, kind in zip(row, spec.input_types, strict=True):
            if type(value) is not int or not 0 <= value <= (1 if kind == "sbf" else 2**32 - 1):
                raise ValueError("input outside the bounded Boolean/uint32 domain")
    return tuple("".join(f"{row[i]}\n" for row in rows).encode("ascii")
                 for i in range(len(spec.input_types)))


@contextmanager
def sealed_inputs(payloads: tuple[bytes, ...]) -> Iterator[tuple[int, ...]]:
    """Separate immutable streams avoid shared-stdin read-ahead losses."""
    descriptors: list[int] = []
    try:
        for payload in payloads:
            fd = os.memfd_create("zenodex-tau-input", os.MFD_ALLOW_SEALING | os.MFD_CLOEXEC)
            descriptors.append(fd)
            if os.write(fd, payload) != len(payload):
                raise ValueError("incomplete research input copy")
            os.lseek(fd, 0, os.SEEK_SET)
            fcntl.fcntl(fd, fcntl.F_ADD_SEALS,
                        fcntl.F_SEAL_SEAL | fcntl.F_SEAL_WRITE | fcntl.F_SEAL_GROW | fcntl.F_SEAL_SHRINK)
        yield tuple(descriptors)
    finally:
        for fd in descriptors:
            os.close(fd)


def run_trace(executable_fd: int, spec: PreparedSpec, rows: tuple[tuple[int, ...], ...]) -> TraceObservation:
    payloads = encode_inputs(spec, rows)
    with sealed_inputs(payloads) as descriptors:
        declarations = "".join(f'i{i}:{kind} := in file("/proc/self/fd/{fd}").\n'
                               for i, (kind, fd) in enumerate(zip(spec.input_types, descriptors, strict=True), 1))
        declarations += "".join(f"o{i}:sbf := out console.\n" for i in range(1, spec.output_count + 1))
        program = declarations + "run " + spec.expression + ".\n"
        start = perf_counter_ns()
        result = run_bounded((f"/proc/self/fd/{executable_fd}", *ENGINE_OPTIONS, program),
                             b"", pass_fds=(executable_fd, *descriptors))
        elapsed_ns = perf_counter_ns() - start
        outputs = decode_trace(result, stream_banners(spec, descriptors), spec.output_count, len(rows))
    return TraceObservation(outputs, elapsed_ns, sha256(program.encode("ascii")),
                            tuple(sha256(payload) for payload in payloads),
                            sha256(result.stdout.encode("ascii")), sha256(result.stderr.encode("ascii")))
