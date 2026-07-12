#!/usr/bin/env python3
"""Build the canonical partial-liquidation arithmetic parity corpus.

The corpus is generated from the live Python runtime. Independent Julia replay
and Lean proofs consume the pinned artifact through the companion checker. This
builder is the only supported mutation path for the generated files.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import sys
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path
from typing import Any, Iterable

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))


from src.core.perp_v2.math import (  # noqa: E402
    _is_partial_fraction_sufficient,
    compute_partial_close_fraction,
    is_liquidatable,
)

SCHEMA = "zenodex/perp-partial-liquidation-semantics/v1"
DEFAULT_OUT_DIR = ROOT / "tests" / "fixtures" / "perp_partial_liquidation_semantics_v1"
DEFAULT_CORPUS = DEFAULT_OUT_DIR / "corpus.tsv"
DEFAULT_MANIFEST = DEFAULT_OUT_DIR / "manifest.json"
CORPUS_COLUMNS = (
    "case_id",
    "position_base",
    "collateral_after_pnl",
    "settle_price_e8",
    "maintenance_margin_bps",
    "depeg_buffer_bps",
    "liquidation_penalty_bps",
    "min_notional_for_bounty",
    "liquidatable",
    "selected_fraction_bps",
)
GRID = {
    "position_base": (1, 2, 3, 10, 100, 1_000),
    "collateral_after_pnl": (0, 1, 10, 60, 100),
    "settle_price_e8": (100_000_000, 200_000_000),
    "maintenance_margin_bps": (500, 1_000),
    "depeg_buffer_bps": (0, 100),
    "liquidation_penalty_bps": (0, 50, 500),
    "min_notional_for_bounty": (0, 5, 500),
}
SOURCE_PATHS = (
    ".github/workflows/ci.yml",
    "lean-mathlib/Proofs/PerpMarginRoundingSafety.lean",
    "lean-mathlib/Proofs/PerpPartialLiquidationExact.lean",
    "src/core/perp_v2/math.py",
    "tests/core/test_perp_v2/test_partial_liquidate.py",
    "tests/formal/test_lean_perp_partial_liquidation_exact.py",
    "tests/formal/test_lean_perp_margin_rounding_safety.py",
    "tests/test_check_perp_partial_liquidation_semantics_v1.py",
    "tools/build_perp_partial_liquidation_semantics_v1.py",
    "tools/check_perp_partial_liquidation_semantics_v1.py",
    "tools/perp_partial_liquidation_semantics_v1.jl",
    "tools/run_perp_partial_liquidation_semantics_v1_gate.sh",
)


@dataclass(frozen=True)
class CorpusCase:
    case_id: int
    position_base: int
    collateral_after_pnl: int
    settle_price_e8: int
    maintenance_margin_bps: int
    depeg_buffer_bps: int
    liquidation_penalty_bps: int
    min_notional_for_bounty: int
    liquidatable: bool
    selected_fraction_bps: int

    def tsv_row(self) -> str:
        values = (
            self.case_id,
            self.position_base,
            self.collateral_after_pnl,
            self.settle_price_e8,
            self.maintenance_margin_bps,
            self.depeg_buffer_bps,
            self.liquidation_penalty_bps,
            self.min_notional_for_bounty,
            int(self.liquidatable),
            self.selected_fraction_bps,
        )
        return "\t".join(str(value) for value in values)


def _sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def _sha256_file(path: Path) -> str:
    return _sha256_bytes(path.read_bytes())


def iter_corpus_cases() -> Iterable[CorpusCase]:
    keys = tuple(GRID)
    domains = tuple(GRID[key] for key in keys)
    for case_id, values in enumerate(itertools.product(*domains)):
        params = dict(zip(keys, values, strict=True))
        position_base = int(params["position_base"])
        collateral_after_pnl = int(params["collateral_after_pnl"])
        settle_price_e8 = int(params["settle_price_e8"])
        maintenance_margin_bps = int(params["maintenance_margin_bps"])
        depeg_buffer_bps = int(params["depeg_buffer_bps"])
        liquidation_penalty_bps = int(params["liquidation_penalty_bps"])
        min_notional_for_bounty = int(params["min_notional_for_bounty"])
        liquidatable = is_liquidatable(
            position_base,
            collateral_after_pnl,
            settle_price_e8,
            maintenance_margin_bps,
            depeg_buffer_bps,
        )
        selected_fraction_bps = compute_partial_close_fraction(
            position_base,
            collateral_after_pnl,
            settle_price_e8,
            maintenance_margin_bps,
            depeg_buffer_bps,
            liquidation_penalty_bps,
            min_notional_for_bounty,
        )
        yield CorpusCase(
            case_id=case_id,
            position_base=position_base,
            collateral_after_pnl=collateral_after_pnl,
            settle_price_e8=settle_price_e8,
            maintenance_margin_bps=maintenance_margin_bps,
            depeg_buffer_bps=depeg_buffer_bps,
            liquidation_penalty_bps=liquidation_penalty_bps,
            min_notional_for_bounty=min_notional_for_bounty,
            liquidatable=bool(liquidatable),
            selected_fraction_bps=int(selected_fraction_bps),
        )


def render_corpus(cases: Iterable[CorpusCase]) -> bytes:
    lines = [f"# schema={SCHEMA}", "\t".join(CORPUS_COLUMNS)]
    lines.extend(case.tsv_row() for case in cases)
    return ("\n".join(lines) + "\n").encode("ascii")


def build_manifest(corpus: bytes, cases: tuple[CorpusCase, ...]) -> dict[str, Any]:
    witness_args = {
        "position_base": 1_000,
        "collateral_after_pnl": 60,
        "settle_price_e8": 100_000_000,
        "maintenance_margin_bps": 1_000,
        "depeg_buffer_bps": 0,
        "liquidation_penalty_bps": 500,
        "min_notional_for_bounty": 500,
    }
    selected = compute_partial_close_fraction(**witness_args)
    sufficient_4_999 = _is_partial_fraction_sufficient(
        fraction_bps=4_999, **witness_args
    )
    sufficient_5_000 = _is_partial_fraction_sufficient(
        fraction_bps=5_000, **witness_args
    )
    source_files = []
    for relative_path in SOURCE_PATHS:
        path = ROOT / relative_path
        if not path.is_file():
            raise FileNotFoundError(f"required semantics source is missing: {relative_path}")
        source_files.append(
            {"path": relative_path, "sha256": _sha256_file(path)}
        )
    return {
        "schema": SCHEMA,
        "generator_command": "python3 tools/build_perp_partial_liquidation_semantics_v1.py",
        "corpus": {
            "path": "tests/fixtures/perp_partial_liquidation_semantics_v1/corpus.tsv",
            "sha256": _sha256_bytes(corpus),
            "case_count": len(cases),
            "columns": list(CORPUS_COLUMNS),
            "grid": {key: list(values) for key, values in GRID.items()},
        },
        "formal_claims": [
            "selected fraction is in [1, 10000] on liquidatable natural-number inputs",
            "selected fraction is sufficient",
            "every earlier admissible fraction is insufficient",
            "the contract does not assume monotonicity of the sufficiency predicate",
            "single-step ceiling margin is the least integer requirement covering raw scaled risk",
        ],
        "lean_theorems": [
            "Proofs.PerpPartialLiquidationExact.runtimeFraction_contract_of_liquidatable",
            "Proofs.PerpPartialLiquidationExact.witness_nonmonotone",
            "Proofs.PerpPartialLiquidationExact.witness_runtime_fraction",
            "Proofs.PerpMarginRoundingSafety.safeCeilMargin_covers_raw",
            "Proofs.PerpMarginRoundingSafety.safeCeilMargin_minimal",
            "Proofs.PerpMarginRoundingSafety.nested_floor_dust_witness",
        ],
        "known_nonmonotone_witness": {
            **witness_args,
            "selected_fraction_bps": selected,
            "sufficient_4999": bool(sufficient_4_999),
            "sufficient_5000": bool(sufficient_5_000),
        },
        "nonclaims": [
            "The corpus is bounded differential evidence, not an exhaustive proof over Python integers.",
            "The Lean arithmetic model covers unsigned position magnitude and nonnegative collateral.",
            "The runtime and v3 YAML still use nested-floor margin; the safe ceiling formula is not deployed.",
            "The gate does not grant settlement or production authority.",
        ],
        "source_files": source_files,
    }


def render_manifest(payload: dict[str, Any]) -> bytes:
    return (json.dumps(payload, indent=2, sort_keys=True) + "\n").encode("utf-8")


@lru_cache(maxsize=1)
def expected_artifacts() -> tuple[bytes, bytes]:
    cases = tuple(iter_corpus_cases())
    corpus = render_corpus(cases)
    manifest = render_manifest(build_manifest(corpus, cases))
    return corpus, manifest


def _check_exact(path: Path, expected: bytes) -> bool:
    return path.is_file() and path.read_bytes() == expected


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Build or check the v1 partial-liquidation semantics corpus."
    )
    parser.add_argument("--out-dir", type=Path, default=DEFAULT_OUT_DIR)
    parser.add_argument(
        "--check",
        action="store_true",
        help="Fail when checked-in artifacts differ; do not write files.",
    )
    args = parser.parse_args()

    corpus, manifest = expected_artifacts()
    corpus_path = args.out_dir / "corpus.tsv"
    manifest_path = args.out_dir / "manifest.json"
    if args.check:
        stale = []
        if not _check_exact(corpus_path, corpus):
            stale.append(str(corpus_path))
        if not _check_exact(manifest_path, manifest):
            stale.append(str(manifest_path))
        if stale:
            for path in stale:
                print(f"ERROR: stale or missing generated artifact: {path}", file=sys.stderr)
            return 1
        case_count = json.loads(manifest)["corpus"]["case_count"]
        print(f"OK schema={SCHEMA} cases={case_count}")
        return 0

    args.out_dir.mkdir(parents=True, exist_ok=True)
    corpus_path.write_bytes(corpus)
    manifest_path.write_bytes(manifest)
    print(f"wrote {corpus_path}")
    print(f"wrote {manifest_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
