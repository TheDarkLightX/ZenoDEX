#!/usr/bin/env python3
"""Replay: python3 tools/render_asset_transfer_epoch_projection_v1_golden.py --check.

Omit --check to regenerate these proposal-construction vectors. Actual Python
custody-module outputs feed the new runtime projector; independently constructed
test states check both successful endpoints. Mock receipts supply no authority.
The subsequent allocation relation has separate, fixed expected reject codes.
This is finite Python/Rust evidence, with no mounted or cryptographic claim.
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
from src.core.asset_transfer_epoch_projection_v1 import (  # noqa: E402
    project_asset_transfer_epoch_position_v1,
)
from src.core.asset_transfer_global_allocation_v1 import (  # noqa: E402
    AssetTransferGlobalAllocationCandidateV1,
    _epoch_allocation_binding_reject_v1,
)
from src.core.global_settlement_types_v1 import (  # noqa: E402
    MAX_U64_V1,
    EconomicAmountV1,
    GlobalEconomicStateV1,
    LaneIdV1,
    OutboxStateV1,
    OutboxStatusV1,
    TerminalObligationStatusV1,
    TerminalObligationV1,
    canonical_global_bytes_v1,
)
from tests.formal.test_lean_asset_transfer_epoch_economic_tables_v1 import (  # noqa: E402
    RuntimeProjectedPair,
)
from tests.formal.test_lean_asset_transfer_epoch_state_closure_v1 import (  # noqa: E402
    SharedHeightPair,
)
from tools.render_asset_transfer_global_allocation_v1_golden import _accepted_value  # noqa: E402

FIXTURE = ROOT / "tests/data/asset_transfer_epoch_projection_v1_golden.json"
SOURCES = (
    "src/core/asset_transfer_epoch_projection_v1.py",
    "src/core/asset_transfer_epoch_position_v1.py",
    "src/core/asset_transfer_global_allocation_v1.py",
    "src/core/asset_transfer_lane_module_custody_v1.py",
    "src/core/global_economic_refinement_snapshot_v1.py",
    "src/core/global_settlement_types_v1.py",
    "tests/formal/test_lean_asset_transfer_epoch_state_closure_v1.py",
    "tests/formal/test_lean_asset_transfer_epoch_economic_tables_v1.py",
    "tools/render_asset_transfer_global_allocation_v1_golden.py",
    "tools/render_asset_transfer_epoch_projection_v1_golden.py",
    "zk/global_settlement_abi_v1/src/asset_transfer_epoch_projection.rs",
    "zk/global_settlement_abi_v1/src/asset_transfer_global_allocation.rs",
)


def _row(
    name: str,
    candidate: AssetTransferGlobalAllocationCandidateV1,
    position: AssetTransferEpochPositionV1,
    expected: str | None,
) -> dict[str, object]:
    proposal = project_asset_transfer_epoch_position_v1(
        position=position,
        predecessor=candidate.predecessor,
        occurrence=candidate.occurrence,
        accepted=candidate.accepted,
    )
    if proposal.post_state != candidate.current:
        raise ValueError(f"independent full-state projection drift: {name}")
    result = _epoch_allocation_binding_reject_v1(candidate, position)
    actual = None if result is None else result.code.value
    if actual != expected:
        raise ValueError(f"independent allocation outcome drift: {name}: {actual}")
    return {
        "name": name,
        "source": position.epoch_source,
        "index": position.occurrence_index,
        "predecessor": candidate.predecessor,
        "occurrence": candidate.occurrence,
        "accepted": _accepted_value(candidate.accepted),
        "current": candidate.current,
        "current_root": candidate.current.state_root,
        "canonical_current_hex": canonical_global_bytes_v1(candidate.current).hex(),
        "expected_code": expected,
    }


def _pair(height: int) -> RuntimeProjectedPair:
    runtime = RuntimeProjectedPair(height=height)
    reference = SharedHeightPair(height=height)
    if (runtime.source, runtime.first_post, runtime.second_post) != (
        reference.source, reference.first_post, reference.second_post,
    ):
        raise ValueError("runtime endpoints differ from the independent test construction")
    return runtime


def _rich_frame_case(
    first: AssetTransferGlobalAllocationCandidateV1, source: GlobalEconomicStateV1,
) -> dict[str, object]:
    reserves = (EconomicAmountV1("treasury", "USD", "reserve", 3),)
    terminal_obligations = (
        TerminalObligationV1(
            "terminal-0001", LaneIdV1.ZUSD_MONETARY, "claimant", "USD", 2,
            TerminalObligationStatusV1.OPEN,
        ),
    )
    outbox = (
        OutboxStateV1(
            "0x" + "a1" * 32, "bridge:epoch-projection", "0x" + "a2" * 32,
            "0x" + "a3" * 32, OutboxStatusV1.PENDING,
        ),
    )
    rich_source = replace(source, reserves=reserves, terminal_obligations=terminal_obligations, outbox=outbox)
    candidate = replace(
        first, predecessor=rich_source,
        current=replace(first.current, reserves=reserves, terminal_obligations=terminal_obligations, outbox=outbox),
    )
    # The untouched occurrence still names the original predecessor root. This
    # demonstrates complete-frame construction without claiming admission.
    return _row(
        "populated_frame_unadmitted", candidate,
        AssetTransferEpochPositionV1(rich_source, 0), "GLOBAL_OCCURRENCE_DRIFT",
    )


def _cases() -> list[dict[str, object]]:
    rows = []
    for height in (7, MAX_U64_V1 - 1):
        pair = _pair(height)
        for index, (witness, accepted, prior, current) in enumerate((
            (pair.first, pair.first_accepted, pair.source, pair.first_post),
            (pair.second, pair.second_accepted, pair.first_post, pair.second_post),
        )):
            candidate = AssetTransferGlobalAllocationCandidateV1(
                accepted, witness.occurrence, prior, current,
            )
            rows.append(_row(
                f"height_{height}_position_{index}", candidate,
                AssetTransferEpochPositionV1(pair.source, index), None,
            ))
    pair = _pair(7)
    first = AssetTransferGlobalAllocationCandidateV1(
        pair.first_accepted, pair.first.occurrence, pair.source, pair.first_post,
    )
    second = AssetTransferGlobalAllocationCandidateV1(
        pair.second_accepted, pair.second.occurrence, pair.first_post, pair.second_post,
    )
    drift = "GLOBAL_OCCURRENCE_DRIFT"
    for name, candidate, source, index, expected in (
        ("first_as_second", first, pair.source, 1, drift),
        ("second_as_first", second, pair.source, 0, drift),
        ("source_height_drift", second, replace(pair.source, height=6), 1, drift),
        ("source_height_overflow", second, replace(pair.source, height=MAX_U64_V1), 1, drift),
        ("source_context_drift", second, replace(pair.source, chain_id="foreign"), 1,
         "GLOBAL_CONTEXT_DRIFT"),
        ("first_source_history_drift", first,
         replace(pair.source, history_root="0x" + "99" * 32), 0, drift),
    ):
        rows.append(_row(name, candidate, AssetTransferEpochPositionV1(source, index), expected))
    rows.append(_rich_frame_case(first, pair.source))
    return rows


def render() -> str:
    payload = json.loads(canonical_global_bytes_v1({"cases": tuple(_cases())}))
    payload.update(schema="zenodex/asset-transfer-epoch-projection-golden/v1", authority="NONE")
    payload["source_sha256"] = {
        path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest() for path in SOURCES
    }
    return json.dumps(payload, indent=2, sort_keys=True) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    content = render()
    if args.check:
        if FIXTURE.read_text() != content:
            raise SystemExit("epoch-projection fixture is stale")
    else:
        FIXTURE.write_text(content)


if __name__ == "__main__":
    main()
