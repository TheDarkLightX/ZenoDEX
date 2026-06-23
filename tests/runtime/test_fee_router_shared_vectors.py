"""Validate the shared SPARK/Rust/Python fee-split vectors against the reference.

The vectors in ``spark-kernels/fee_router/test_vectors.json`` are the common
oracle for the Python reference, the Rust shadow, and the advisory SPARK kernel.
These tests pin that every vector matches the authoritative Python runtime and
that the committed file is up to date.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
VECTORS = REPO / "spark-kernels" / "fee_router" / "test_vectors.json"
GEN = REPO / "spark-kernels" / "fee_router"

for _p in (str(REPO), str(GEN)):
    if _p not in sys.path:
        sys.path.insert(0, _p)

import export_test_vectors  # noqa: E402

from src.core.fee_router import (  # noqa: E402
    FeeAccumulator,
    FeeSplitTable,
    RouteAccepted,
    route_fee,
)


def test_vectors_match_reference():
    data = json.loads(VECTORS.read_text(encoding="utf-8"))
    assert data["kernel"] == "fee_split_conservation"
    assert data["cases"], "vector file is empty"
    for case in data["cases"]:
        split = FeeSplitTable(
            buyburn_bps=case["split"]["buyburn_bps"],
            stakers_bps=case["split"]["stakers_bps"],
            reserve_bps=case["split"]["reserve_bps"],
            hosts_bps=case["split"]["hosts_bps"],
        )
        result = route_fee(
            source=case["domain"],
            asset="zUSD",
            amount=case["amount"],
            split_table=split,
            accumulator=FeeAccumulator(),
        )
        assert isinstance(result, RouteAccepted), case
        r = result.receipt
        exp = case["expected"]
        assert (r.buyburn, r.stakers, r.reserve, r.hosts, r.dust) == (
            exp["buyburn"],
            exp["stakers"],
            exp["reserve"],
            exp["hosts"],
            exp["dust"],
        ), case
        # Conservation (dust_in == 0 here, matching the SPARK postcondition).
        assert case["amount"] == r.buyburn + r.stakers + r.reserve + r.hosts + r.dust


def test_vectors_file_is_up_to_date():
    on_disk = VECTORS.read_text(encoding="utf-8")
    fresh = export_test_vectors.serialize(export_test_vectors.build_vectors())
    assert on_disk == fresh, (
        "spark-kernels/fee_router/test_vectors.json is stale; regenerate with:\n"
        "  python3 spark-kernels/fee_router/export_test_vectors.py "
        "--out spark-kernels/fee_router/test_vectors.json"
    )
