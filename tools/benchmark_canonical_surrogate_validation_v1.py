#!/usr/bin/env python3
"""Measure the canonical ASCII fast path on the custody composition fixture.

The baseline validator is an independent frozen copy of the pre-change loop.
The benchmark patches only ``src.state.canonical._reject_surrogates`` in this
process and restores it with ``finally``; it never rewrites source files.

This is an advisory Python fixture measurement.  It grants no native, guest,
proof, release, publication, or production authority.
"""

from __future__ import annotations

import argparse
import hashlib
import inspect
import json
import platform
import subprocess
import sys
import time
from collections.abc import Sequence
from dataclasses import dataclass, replace
from pathlib import Path
from statistics import median
from typing import Any, Protocol

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

import src.state.canonical as canonical_mod  # noqa: E402
from src.core.asset_lane_coordinator_v1 import compose_asset_lane_single_v1  # noqa: E402
from src.core.asset_lane_projection_v1 import (  # noqa: E402
    AssetLaneCompositionAcceptedV1,
)
from src.core.asset_transfer_lane_module_custody_v1 import (  # noqa: E402
    transition_asset_transfer_lane_module_custody_v1,
)
from src.core.asset_transfer_lane_module_v1 import (  # noqa: E402
    AssetTransferLaneModuleAcceptedV1,
)
from src.core.global_settlement_types_v1 import (  # noqa: E402
    EconomicAmountV1,
    canonical_global_bytes_v1,
)
from tests.core.test_asset_transfer_lane_module_custody_v1 import (  # noqa: E402
    _custody_input,
)
from tests.core.test_asset_transfer_lane_module_v1 import _coordinator_context  # noqa: E402


class _Validator(Protocol):
    def __call__(self, s: str) -> None: ...


_CANDIDATE_REJECT_SURROGATES: _Validator = canonical_mod._reject_surrogates
_MAX_CUSTODY_ROWS = 4096


def _legacy_reject_surrogates(s: str) -> None:
    """Frozen pre-change loop retained as an independent baseline oracle."""
    for ch in s:
        ordinal = ord(ch)
        if 0xD800 <= ordinal <= 0xDFFF:
            raise TypeError("surrogate code points are not allowed in canonical encoding")


def _custody_value(count: int) -> Any:
    module_input = _custody_input(count)
    custody = tuple(
        EconomicAmountV1(f"vault-{index:04d}", "USD", "escrow", 1)
        for index in range(count)
    )
    return replace(module_input, custody=custody)


@dataclass(frozen=True)
class _PreparedCase:
    custody_rows: int
    module_input: Any
    fixture_input_bytes: int
    fixture_input_sha256: str
    expected_output: bytes
    candidate_output: bytes


def _compose_bytes(module_input: Any, validator: _Validator) -> bytes:
    previous = canonical_mod._reject_surrogates
    vars(canonical_mod)["_reject_surrogates"] = validator
    try:
        module = transition_asset_transfer_lane_module_custody_v1(module_input)
        if type(module) is not AssetTransferLaneModuleAcceptedV1:
            raise RuntimeError("custody fixture unexpectedly rejected at module transition")
        lane = compose_asset_lane_single_v1(
            _coordinator_context(),
            module.module_journal,
            module.private_port,
            module.effects,
        )
        if type(lane) is not AssetLaneCompositionAcceptedV1:
            raise RuntimeError("custody fixture unexpectedly rejected at composition")
        return canonical_global_bytes_v1(
            {
                "post_state": lane.post_state,
                "effects": lane.effects,
                "lane_journal": lane.lane_journal,
            }
        )
    finally:
        vars(canonical_mod)["_reject_surrogates"] = previous


def _timed(module_input: Any, validator: _Validator) -> tuple[float, bytes]:
    began_ns = time.perf_counter_ns()
    result = _compose_bytes(module_input, validator)
    elapsed_ms = (time.perf_counter_ns() - began_ns) / 1_000_000
    return elapsed_ms, result


def _repository_source_manifest() -> tuple[tuple[str, str, str], ...]:
    """Hash loaded repository Python modules using only root-relative paths."""
    root = ROOT.resolve()
    entries: list[tuple[str, str, str]] = []
    for module_name, module in sorted(sys.modules.items()):
        filename = getattr(module, "__file__", None)
        if type(filename) is not str or not filename.endswith(".py"):
            continue
        source_path = Path(filename)
        if not source_path.is_absolute():
            source_path = root / source_path
        try:
            resolved_path = source_path.resolve(strict=False)
            relative_path = resolved_path.relative_to(root)
        except ValueError:
            continue
        if resolved_path.suffix != ".py":
            continue
        if not resolved_path.is_file():
            raise RuntimeError(
                f"loaded repository Python source is unavailable: {relative_path.as_posix()}"
            )
        source_hash = hashlib.sha256(resolved_path.read_bytes()).hexdigest()
        entries.append((module_name, relative_path.as_posix(), source_hash))
    return tuple(entries)


def _manifest_sha256(manifest: tuple[tuple[str, str, str], ...]) -> str:
    encoded = json.dumps(
        [
            {"module": module, "path": path, "sha256": source_hash}
            for module, path, source_hash in manifest
        ],
        ensure_ascii=True,
        separators=(",", ":"),
        sort_keys=True,
    ).encode("ascii")
    return hashlib.sha256(encoded).hexdigest()


def _source_hashes() -> dict[str, str]:
    source_path = ROOT / "src/state/canonical.py"
    tool_path = Path(__file__).resolve()
    baseline_source = inspect.getsource(_legacy_reject_surrogates).encode("utf-8")
    candidate_source = inspect.getsource(_CANDIDATE_REJECT_SURROGATES).encode("utf-8")
    return {
        "canonical_py_sha256": hashlib.sha256(source_path.read_bytes()).hexdigest(),
        "benchmark_py_sha256": hashlib.sha256(tool_path.read_bytes()).hexdigest(),
        "baseline_oracle_function_sha256": hashlib.sha256(baseline_source).hexdigest(),
        "candidate_function_sha256": hashlib.sha256(candidate_source).hexdigest(),
    }


def _git_head() -> str:
    completed = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    return completed.stdout.strip()


def _prepare_case(count: int) -> _PreparedCase:
    module_input = _custody_value(count)
    fixture_input = canonical_global_bytes_v1(module_input.to_canonical())
    baseline_warm = _compose_bytes(module_input, _legacy_reject_surrogates)
    candidate_warm = _compose_bytes(module_input, _CANDIDATE_REJECT_SURROGATES)
    if baseline_warm != candidate_warm:
        raise RuntimeError(f"canonical bytes disagreed for custody_rows={count}")
    return _PreparedCase(
        custody_rows=count,
        module_input=module_input,
        fixture_input_bytes=len(fixture_input),
        fixture_input_sha256=hashlib.sha256(fixture_input).hexdigest(),
        expected_output=baseline_warm,
        candidate_output=candidate_warm,
    )


def _measure_case(prepared: _PreparedCase, *, repeats: int) -> dict[str, object]:
    module_input = prepared.module_input
    baseline_warm = prepared.expected_output
    candidate_warm = prepared.candidate_output
    count = prepared.custody_rows
    samples: dict[str, list[float]] = {"baseline": [], "candidate": []}
    for repeat in range(repeats):
        order: Sequence[tuple[str, _Validator]]
        if repeat % 2 == 0:
            order = (
                ("baseline", _legacy_reject_surrogates),
                ("candidate", _CANDIDATE_REJECT_SURROGATES),
            )
        else:
            order = (
                ("candidate", _CANDIDATE_REJECT_SURROGATES),
                ("baseline", _legacy_reject_surrogates),
            )
        for name, validator in order:
            elapsed_ms, observed = _timed(module_input, validator)
            if observed != baseline_warm:
                raise RuntimeError(f"canonical bytes drifted for custody_rows={count}")
            samples[name].append(elapsed_ms)

    baseline_median = float(median(samples["baseline"]))
    candidate_median = float(median(samples["candidate"]))
    reduction_percent = (1 - candidate_median / baseline_median) * 100
    return {
        "custody_rows": count,
        "fixture_input": {
            "bytes": prepared.fixture_input_bytes,
            "sha256": prepared.fixture_input_sha256,
        },
        "baseline": {
            "samples_ms": samples["baseline"],
            "median_ms": baseline_median,
            "sha256": hashlib.sha256(baseline_warm).hexdigest(),
            "bytes": len(baseline_warm),
        },
        "candidate": {
            "samples_ms": samples["candidate"],
            "median_ms": candidate_median,
            "sha256": hashlib.sha256(candidate_warm).hexdigest(),
            "bytes": len(candidate_warm),
        },
        "canonical_bytes_equal": baseline_warm == candidate_warm,
        "canonical_bytes_sha256": hashlib.sha256(baseline_warm).hexdigest(),
        "canonical_bytes": len(baseline_warm),
        "median_reduction_percent": reduction_percent,
        "small_case_regression_within_5_percent": (
            candidate_median <= baseline_median * 1.05
        ),
        "large_case_reduction_at_least_15_percent": (
            count != 4096 or reduction_percent >= 15
        ),
    }


def _build_report(counts: Sequence[int], repeats: int) -> dict[str, object]:
    original = canonical_mod._reject_surrogates
    try:
        # Warm all requested fixtures and both paths before freezing the source
        # closure.  This covers repository modules imported lazily by a route.
        prepared_cases = [_prepare_case(count) for count in counts]
        source_manifest_before = _repository_source_manifest()
        cases = [
            _measure_case(prepared, repeats=repeats) for prepared in prepared_cases
        ]
        source_manifest_after = _repository_source_manifest()
        if source_manifest_after != source_manifest_before:
            raise RuntimeError(
                "loaded repository Python source closure changed during measurements"
            )
        source_manifest_before_sha256 = _manifest_sha256(source_manifest_before)
        source_manifest_after_sha256 = _manifest_sha256(source_manifest_after)
    finally:
        vars(canonical_mod)["_reject_surrogates"] = original

    return {
        "tool": "benchmark_canonical_surrogate_validation_v1",
        "subject_head": _git_head(),
        "python": {
            "implementation": platform.python_implementation(),
            "version": platform.python_version(),
            "build": platform.python_build(),
        },
        "repeats": repeats,
        "cases": cases,
        "source_closure": {
            "root_relative_py_modules": [
                {"module": module, "path": path, "sha256": source_hash}
                for module, path, source_hash in source_manifest_before
            ],
            "module_count": len(source_manifest_before),
            "manifest_sha256": source_manifest_before_sha256,
            "manifest_sha256_after": source_manifest_after_sha256,
            "verified_unchanged_after_measurements": True,
        },
        "source_hashes": _source_hashes(),
        "claim_scope": {
            "measured": [
                "Python custody module transition plus single-lane composition",
                "Canonical post_state, effects, and lane_journal bytes",
                "Fixture custody row counts selected by this tool",
            ],
            "nonclaims": [
                "No native or Rust throughput or parity claim",
                "No guest, proof image, verifier, release, publication, or runtime claim",
                "No production readiness, authority, security, or economic claim",
                "Synthetic fixture timings do not represent arbitrary workload distributions",
            ],
        },
    }


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--repeats",
        type=int,
        default=5,
        help="measured samples per path and case (minimum 3; default: 5)",
    )
    parser.add_argument(
        "--counts",
        type=int,
        nargs="+",
        default=(0, 256, 4096),
        help="custody row counts (default: 0 256 4096)",
    )
    args = parser.parse_args()
    if args.repeats < 3:
        parser.error("--repeats must be at least 3")
    if any(count < 0 or count > _MAX_CUSTODY_ROWS for count in args.counts):
        parser.error("--counts must be between 0 and 4096")
    return args


def main() -> int:
    args = _parse_args()
    report = _build_report(args.counts, args.repeats)
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
