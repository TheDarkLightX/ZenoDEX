#!/usr/bin/env python3
"""Replay: python3 tools/render_asset_transfer_epoch_position_v1_golden.py --check.

Omit --check to regenerate. Source-bound pure-relation vectors use mock receipt
ports only when constructing accepted module preimages. Authority remains NONE.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from dataclasses import replace
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.core.asset_transfer_epoch_position_v1 import AssetTransferEpochPositionV1  # noqa: E402
from src.core.asset_transfer_global_allocation_v1 import (  # noqa: E402
    _epoch_allocation_binding_reject_v1,
)
from src.core.global_settlement_types_v1 import canonical_global_bytes_v1  # noqa: E402
from tests.core.test_asset_transfer_epoch_allocation_v1 import _fixture  # noqa: E402
from tests.core.test_asset_transfer_epoch_position_v1 import _pair  # noqa: E402
from tools.render_asset_transfer_global_allocation_v1_golden import _accepted_value  # noqa: E402

FIXTURE = ROOT / "tests/data/asset_transfer_epoch_position_v1_golden.json"
SOURCES = (
    "src/core/asset_transfer_epoch_position_v1.py",
    "src/core/asset_transfer_global_allocation_v1.py",
    "src/core/asset_transfer_receipt_admission_v1.py",
    "src/core/asset_transfer_epoch_allocation_v1.py",
    "zk/global_settlement_abi_v1/src/asset_transfer_global_allocation.rs",
    "zk/global_settlement_abi_v1/src/asset_transfer_receipt_admission.rs",
)


def _cases():
    candidate, evidence = _fixture(count=2)
    source = candidate.pre_state
    first, second = (_pair(candidate, evidence, index) for index in (0, 1))
    drift, context = "GLOBAL_OCCURRENCE_DRIFT", "GLOBAL_CONTEXT_DRIFT"
    foreign = "0x" + "99" * 32
    return (
        ("first", first, source, 0, None),
        ("second", second, source, 1, None),
        ("first_as_second", first, source, 1, drift),
        ("second_as_first", second, source, 0, drift),
        ("wrong_source_height", second, replace(source, height=1), 1, drift),
        ("source_height_overflow", second, replace(source, height=(1 << 64) - 1), 1, drift),
        ("wrong_source_context", second, replace(source, chain_id="foreign"), 1, context),
        ("wrong_first_source", first, replace(source, history_root=foreign), 0, drift),
        (
            "hidden_height_increment",
            replace(second, current=replace(second.current, height=2)),
            source,
            1,
            drift,
        ),
        ("wrong_predecessor", replace(second, predecessor=first.predecessor), source, 1, drift),
        (
            "history_drift",
            replace(second, current=replace(second.current, history_root=foreign)),
            source,
            1,
            "GLOBAL_UNSUPPORTED_STATE",
        ),
    )


def render() -> str:
    rows = []
    for name, pair, source, index, expected in _cases():
        result = _epoch_allocation_binding_reject_v1(
            pair, AssetTransferEpochPositionV1(source, index)
        )
        actual = None if result is None else result.code.value
        if actual != expected:
            raise ValueError(f"independent epoch-position outcome drift: {name}: {actual}")
        rows.append(
            {
                "name": name,
                "accepted": _accepted_value(pair.accepted),
                "occurrence": pair.occurrence,
                "predecessor": pair.predecessor,
                "current": pair.current,
                "source": source,
                "index": index,
                "expected_code": expected,
            }
        )
    payload = json.loads(canonical_global_bytes_v1({"cases": tuple(rows)}))
    payload.update(schema="zenodex/asset-transfer-epoch-position-golden/v1", authority="NONE")
    payload["source_sha256"] = {
        name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest() for name in SOURCES
    }
    return json.dumps(payload, sort_keys=True, indent=2) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    content = render()
    if args.check:
        if FIXTURE.read_text() != content:
            raise SystemExit("epoch-position fixture is stale")
    else:
        FIXTURE.write_text(content)


if __name__ == "__main__":
    main()
