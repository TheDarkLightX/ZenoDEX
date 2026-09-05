"""Explicit, bounded execution probe for a measured Tau ADT research adapter.

Run with ``python -m experiments.tau_adt_rows_v1.qualify --tau-binary PATH``.
This checks transport and scalar/ADT agreement. It establishes no economic
predicate, receipt authenticity, reproducible source build, or publication right.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path
from time import perf_counter_ns

from experiments.tau_adt_rows_v1.execution import frozen_executable, run_bounded
from experiments.tau_adt_rows_v1.row_codec import (
    INPUT_BANNER_V1,
    OUTPUT_BANNER_V1,
    TYPE_BANNER_V1,
    decode_output_v1,
    encode_rows_v1,
)
from src.core.global_settlement_primitives_v2 import EconomicAmountV2
from tools.current_tau_replay_io_v1 import _read_bounded_regular_file_v1

MEASURED_TAU_SHA256 = "c061c870b47fa1a6089dac59285e8473b7b789dc600157704007f2d67fd90950"
DIRECTORY = Path(__file__).resolve().parent
CONTRACT = (
    "type Row = {owner: bv[1280], asset: bv[1280], custody_domain: bv[1280], amount_atoms: bv[128]}.\n"
    'i:Row := in file("/dev/stdin").\n'
    "o:Row := out console.\nrun o[t] = i[t].\n"
)
_TIMING = re.compile(r"\tstep: [0-9]{1,12}(?:\.[0-9]{1,12})? ms")
_ERROR_PREFIX = "(\x1b[31;1mError\x1b[0m) "
_OVERFLOW = str(2**128)
_EXPECTED_DIAGNOSTICS = {
    "missing_field": ("ADT wire: missing key 'amount_atoms' at ''", "Failed to read from input stream 'i.amount_atoms'"),
    "extra_field": ("ADT wire: unknown key 'extra' at ''", "Failed to read from input stream 'i.amount_atoms'"),
    "u128_overflow": (
        f"Error creating bitvector constant from string '{_OVERFLOW}': overflow in bit-vector construction (specified bit-vector size 128 too small to hold value {_OVERFLOW})",
        f"Failed to parse bitvector constant: {_OVERFLOW}",
        f"Failed to parse input value '{_OVERFLOW}' for stream 'i.amount_atoms:bv[128]'",
    ),
}


def _sha256(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def _invoke(executable_fd: int, contract: str, stdin: str) -> tuple[subprocess.CompletedProcess[str], int]:
    start = perf_counter_ns()
    result = run_bounded(
        (f"/proc/self/fd/{executable_fd}", "--severity", "error", "--charvar", "false", "--blasting", "false",
         "--max-flag-search-steps", "0", "--color", "false", "--evaluate", contract),
        stdin.encode("ascii"), pass_fds=(executable_fd,),
    )
    return result, perf_counter_ns() - start


def _scalar_values(stdout: str, stderr: str, width: int, count: int) -> tuple[int, ...]:
    if width not in (128, 1280) or not 0 <= count <= 8:
        raise ValueError("unsupported scalar probe bounds")
    if stderr or len(stdout) > 65536 or not stdout.isascii():
        raise ValueError("invalid scalar transcript")
    banners = [f"[1] i:bv[{width}] := in /dev/stdin.", f"[2] o:bv[{width}] := out console."]
    lines = [line for line in stdout.split("\n") if line]
    if lines[:2] != banners:
        raise ValueError("missing exact scalar banners")
    values: list[int] = []
    last_was_row = False
    for line in lines[2:]:
        if len(line) > 2048:
            raise ValueError("scalar line exceeds bound")
        if _TIMING.fullmatch(line):
            if not last_was_row:
                raise ValueError("misplaced scalar timing")
            last_was_row = False
            continue
        match = re.fullmatch(r"o\[([0-7])\] := (0|[1-9][0-9]{0,385})", line)
        if match is None or int(match[1]) != len(values) or len(values) >= count:
            raise ValueError("invalid scalar output or diagnostic")
        value = int(match[2])
        if value >= 1 << width:
            raise ValueError("scalar output overflows width")
        values.append(value)
        last_was_row = True
    if len(values) != count:
        raise ValueError("scalar output count mismatch")
    return tuple(values)


def _reference_identity(value: str) -> int:
    # Independent positional arithmetic, without the codec's byte-packing call.
    return sum(ord(char) * 256 ** (159 - index) for index, char in enumerate(value))


def _corpus() -> tuple[tuple[EconomicAmountV2, ...], ...]:
    amounts = (0, 1, 2**64 - 1, 2**64, 2**128 - 2, 2**128 - 1, 7, 19)
    rows = tuple(EconomicAmountV2(f"owner-{i}", f"asset-{i}", "pool", amount)
                 for i, amount in enumerate(amounts))
    return ((), rows[:1], rows[:4], rows, (EconomicAmountV2("!" * 160, "~" * 160, "A" * 160, 2**128 - 1),))


def _require_malformed_rejection(result: subprocess.CompletedProcess[str], case: str) -> None:
    # This pinned engine emits an Error diagnostic with exit zero. A crash,
    # startup error, or missing transcript is failed qualification evidence.
    if case not in _EXPECTED_DIAGNOSTICS:
        raise ValueError("undeclared malformed-input case")
    expected = [TYPE_BANNER_V1, INPUT_BANNER_V1, OUTPUT_BANNER_V1]
    expected += [_ERROR_PREFIX + message for message in _EXPECTED_DIAGNOSTICS[case]]
    if (result.returncode != 0 or result.stderr
            or [line for line in result.stdout.split("\n") if line] != expected):
        raise ValueError("malformed probe lacks a normal pinned-engine error diagnostic")
    try:
        decode_output_v1(result.stdout, result.stderr, expected_count=1)
    except (ValueError, TypeError):
        return
    raise ValueError("adapter accepted malformed ADT input")


def _source_subject() -> dict[str, str]:
    root = DIRECTORY.parents[1]
    paths = {Path(__file__).resolve(), DIRECTORY / "row_contract.tau"}
    for module in tuple(sys.modules.values()):
        filename = getattr(module, "__file__", None)
        if type(filename) is str:
            path = Path(filename).resolve()
            if path.is_relative_to(root) and path.suffix == ".py":
                paths.add(path)
    return {str(path.relative_to(root)): _sha256(_read_bounded_regular_file_v1(path, 2 * 1024 * 1024, "source"))
            for path in sorted(paths)}


def run_qualification(binary: Path) -> dict[str, object]:
    before = _source_subject()
    contract_bytes = _read_bounded_regular_file_v1(DIRECTORY / "row_contract.tau", 4096, "contract")
    if (contract_bytes != CONTRACT.encode("ascii")
            or before["experiments/tau_adt_rows_v1/row_contract.tau"] != _sha256(contract_bytes)):
        raise ValueError("ADT contract drift")
    with frozen_executable(binary, MEASURED_TAU_SHA256) as executable_fd:
        report = _qualify_frozen(executable_fd, contract_bytes.decode("ascii"))
    if _source_subject() != before:
        raise ValueError("repository source changed during qualification")
    report["sources_sha256"] = before
    return report


def _qualify_frozen(executable_fd: int, contract: str) -> dict[str, object]:
    cases: list[dict[str, object]] = []
    for index, rows in enumerate(_corpus()):
        stdin = encode_rows_v1(rows)
        result, elapsed = _invoke(executable_fd, contract, stdin)
        if result.returncode != 0 or decode_output_v1(result.stdout, result.stderr, expected_count=len(rows)) != rows:
            raise ValueError(f"ADT positive case {index} failed")
        scalar_ns = 0
        scalar_hashes = []
        for field, width in (("owner", 1280), ("asset", 1280), ("custody_domain", 1280), ("amount_atoms", 128)):
            expected = tuple(row.amount_atoms if field == "amount_atoms"
                             else _reference_identity(getattr(row, field)) for row in rows)
            scalar_contract = f'i:bv[{width}] := in file("/dev/stdin"). o:bv[{width}] := out console. run o[t] = i[t].'
            scalar, duration = _invoke(executable_fd, scalar_contract, "".join(f"{value}\n" for value in expected))
            if scalar.returncode != 0 or _scalar_values(scalar.stdout, scalar.stderr, width, len(rows)) != expected:
                raise ValueError(f"scalar comparison case {index}/{field} failed")
            scalar_ns += duration
            scalar_hashes.append(_sha256(scalar.stdout.encode()))
        cases.append({"case": index, "rows": len(rows), "full_row_equal": True, "scalar_equal": True,
                      "input_sha256": _sha256(stdin.encode()), "adt_output_sha256": _sha256(result.stdout.encode()),
                      "input_bytes": len(stdin), "adt_stdout_bytes": len(result.stdout), "adt_stderr_bytes": len(result.stderr),
                      "scalar_output_sha256": scalar_hashes, "adt_process_ns": elapsed, "four_scalar_processes_ns": scalar_ns})
    valid = encode_rows_v1(_corpus()[1])
    bad_inputs = {
        "missing_field": re.sub(r', amount_atoms: "[0-9]+"', "", valid),
        "extra_field": valid.replace(" }", ', extra: "1" }'),
        "u128_overflow": valid.replace('amount_atoms: "0"', f'amount_atoms: "{2**128}"'),
    }
    negatives = []
    for name, stdin in bad_inputs.items():
        result, _ = _invoke(executable_fd, contract, stdin)
        _require_malformed_rejection(result, name)
        negatives.append({"case": name, "returncode": result.returncode, "adapter_rejected": True,
                          "rejection_class": "NORMAL_ENGINE_DIAGNOSTIC_AND_ADAPTER_REJECTION",
                          "input_sha256": _sha256(stdin.encode()), "stdout_sha256": _sha256(result.stdout.encode()),
                          "stderr_sha256": _sha256(result.stderr.encode())})
    return {
        "schema": "tau-adt-rows-qualification-v1", "status": "PASS", "authority": "NONE",
        "production_security_claim": False, "binary_sha256": MEASURED_TAU_SHA256,
        "execution": "sealed memfd ELF; raw bounded ASCII IO; empty inherited environment except LC_ALL=C",
        "contract_sha256": _sha256(contract.encode("ascii")),
        "engine_options": ["--severity", "error", "--charvar", "false", "--blasting", "false",
                           "--max-flag-search-steps", "0", "--color", "false", "--evaluate"],
        "positive_cases": cases, "negative_cases": negatives,
        "nonclaims": ["economic predicate verification", "authenticated store snapshot", "reproducible Tau source build",
                      "publisher authority", "general performance improvement", "peak memory measurement", "production readiness"],
        "trusted_host": "Python loaded modules, OS, dynamic loader and system libraries; source hashes are not process attestation",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tau-binary", required=True, type=Path)
    parser.add_argument("--output", type=Path)
    arguments = parser.parse_args()
    try:
        report = run_qualification(arguments.tau_binary)
    except (ValueError, TypeError, OSError, subprocess.TimeoutExpired) as exc:
        report = {"status": "FAIL", "authority": "NONE", "error": str(exc)}
    rendered = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if arguments.output is not None:
        try:
            arguments.output.write_text(rendered, encoding="utf-8")
        except OSError as exc:
            report = {"status": "FAIL", "authority": "NONE", "error": str(exc)}
            rendered = json.dumps(report, sort_keys=True) + "\n"
    print(rendered, end="")
    return 0 if report["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
