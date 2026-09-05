#!/usr/bin/env python3
"""Render the public allocation projection's deterministic Python/Rust vectors.

Replay: python3 tools/render_global_accounting_allocation_projection_v1_golden.py --check
Regenerate by omitting --check. These are synthetic, non-authoritative states with
empty witness slots; receipt-bearing cases live in the Rust receipt harness and
retained Python tests. No fixture receipt establishes cryptographic verification.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from dataclasses import replace
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.core.global_accounting_allocation_certificate_v1 import (  # noqa: E402
    LANE_ALLOCATION_PRODUCER_REGISTRY_V1,
    GlobalAccountingAllocationCertificateV1,
)
from src.core.global_accounting_allocation_projection_v1 import (  # noqa: E402
    ALLOCATION_PROJECTION_REJECT_CODES_V1,
    AllocationProjectionRejectedV1,
    project_allocation_certificate_v1,
)
from src.core.global_settlement_types_v1 import (  # noqa: E402
    ALL_LANE_IDS_V1,
    EconomicAmountV1,
    GlobalEconomicStateV1,
    LaneIdV1,
    OutboxStateV1,
    OutboxStatusV1,
    TerminalObligationStatusV1,
    TerminalObligationV1,
    canonical_global_bytes_v1,
)
from tools.render_global_accounting_allocation_certificate_v1_golden import (  # noqa: E402
    build_state_v1,
)

FIXTURE_PATH_V1 = ROOT / "tests/data/global_accounting_allocation_projection_v1_golden.json"
FIXTURE_SCHEMA_V1 = "zenodex/global-accounting-allocation-projection-v1-golden/v1"
MAX_ATOMS = (1 << 128) - 1
BINDING_ROOT = "0x" + "42" * 32


def _row(owner: str, amount: int, asset: str = "USD") -> EconomicAmountV1:
    return EconomicAmountV1(owner, asset, "vault", amount)


def _states() -> dict[str, GlobalEconomicStateV1]:
    empty = build_state_v1({})
    enabled = replace(
        empty, lane_roots=(replace(empty.lane_roots[0], enabled=True), *empty.lane_roots[1:])
    )
    states = {"empty": empty, "enabled_empty": enabled}
    for index, lane in enumerate(ALL_LANE_IDS_V1):
        roots = tuple(replace(row, enabled=i == index) for i, row in enumerate(empty.lane_roots))
        states[f"single_lane_{lane.value}"] = replace(empty, lane_roots=roots)
    states["two_enabled"] = replace(
        empty,
        lane_roots=tuple(replace(row, enabled=i < 2) for i, row in enumerate(empty.lane_roots)),
    )
    for lane in (LaneIdV1.PROOF_REWARDS, LaneIdV1.EXTERNAL_CUSTODY):
        states[f"foreign_empty_root_{lane.value}"] = replace(
            empty,
            lane_roots=tuple(
                replace(row, state_root=BINDING_ROOT) if row.lane_id is lane else row
                for row in empty.lane_roots
            ),
        )
    for custody in (0, 1, 2, MAX_ATOMS - 1, MAX_ATOMS):
        for liability in (0, 1, 2, MAX_ATOMS - 1, MAX_ATOMS):
            states[f"partition_{custody}_{liability}"] = replace(
                enabled,
                custody=(_row("custodian", custody),),
                liabilities=(_row("alice", liability),),
            )
    states.update(
        {
            "rows_without_enabled_lane": replace(empty, custody=(_row("custodian", 1),)),
            "custody_zero_only": replace(enabled, custody=(_row("custodian", 0),)),
            "liability_zero_only": replace(enabled, liabilities=(_row("alice", 0),)),
            "custody_fold_overflow": replace(enabled, custody=(_row("a", MAX_ATOMS), _row("b", 1))),
            "liability_fold_above_u128": replace(
                enabled,
                custody=(_row("a", MAX_ATOMS),),
                liabilities=(_row("a", MAX_ATOMS), _row("b", 1)),
            ),
            "zero_support_precedes_negative": replace(
                enabled, custody=(_row("a", 0, "AAA"),), liabilities=(_row("alice", 1),)
            ),
            "multiple_residual_cells": replace(
                enabled, custody=(_row("a", 1, "AAA"), _row("a", 1))
            ),
            "split_claimants_same_control": replace(
                enabled,
                custody=(_row("custodian", 3),),
                liabilities=(_row("alice", 1), _row("bob", 2)),
            ),
            "reserve_beyond_producer": replace(enabled, reserves=(_row("treasury", 1),)),
        }
    )
    for status in OutboxStatusV1:
        states[f"outbox_{status.value}"] = replace(
            enabled,
            outbox=(
                OutboxStateV1(BINDING_ROOT, "destination", BINDING_ROOT, BINDING_ROOT, status),
            ),
        )
    for terminal_status in TerminalObligationStatusV1:
        states[f"terminal_{terminal_status.value}"] = replace(
            enabled,
            terminal_obligations=(
                TerminalObligationV1(
                    "terminal-1", LaneIdV1.ASSET_TRANSFER, "alice", "USD", 1, terminal_status
                ),
            ),
        )
    return states


def render_fixture_v1() -> dict[str, Any]:
    vectors: dict[str, Any] = {}
    for name, state in _states().items():
        roots = ((LaneIdV1.ASSET_TRANSFER, BINDING_ROOT),) if state.lane_roots[0].enabled else ()
        projected = project_allocation_certificate_v1(state, roots)
        if isinstance(projected, AllocationProjectionRejectedV1):
            expected = {
                "status": "REJECT",
                "code": projected.code.value,
                "detail": projected.detail,
            }
        elif isinstance(projected, GlobalAccountingAllocationCertificateV1):
            expected = {
                "status": "DERIVED",
                "certificate_sha256": hashlib.sha256(
                    canonical_global_bytes_v1(projected)
                ).hexdigest(),
            }
        else:
            raise TypeError("projection returned an unsupported outcome")
        vectors[name] = {
            "state": json.loads(canonical_global_bytes_v1(state)),
            "state_root": state.state_root,
            "binding_roots": [[lane.value, root] for lane, root in roots],
            "expected": expected,
        }
    enabled = _states()["enabled_empty"]
    for name, state, roots in (
        ("missing_binding_root", enabled, ()),
        ("unexpected_binding_root", _states()["empty"], ((LaneIdV1.ASSET_TRANSFER, BINDING_ROOT),)),
    ):
        projected = project_allocation_certificate_v1(state, roots)
        if not isinstance(projected, AllocationProjectionRejectedV1):
            raise ValueError("binding-root negative control derived a certificate")
        vectors[name] = {
            "state": json.loads(canonical_global_bytes_v1(state)),
            "state_root": state.state_root,
            "binding_roots": [[lane.value, root] for lane, root in roots],
            "expected": {
                "status": "REJECT",
                "code": projected.code.value,
                "detail": projected.detail,
            },
        }
    return {
        "fixture_schema": FIXTURE_SCHEMA_V1,
        "authority": "NONE",
        "witness_scope": "empty slots only; receipt cases replay separately",
        "reject_codes": ALLOCATION_PROJECTION_REJECT_CODES_V1,
        "producer_registry": [
            [lane.value, LANE_ALLOCATION_PRODUCER_REGISTRY_V1[lane][0].value]
            for lane in ALL_LANE_IDS_V1
        ],
        "vectors": vectors,
    }


def render_bytes_v1() -> bytes:
    return (json.dumps(render_fixture_v1(), sort_keys=True, indent=2) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--output", type=Path, default=FIXTURE_PATH_V1)
    args = parser.parse_args()
    rendered = render_bytes_v1()
    if args.check:
        ok = args.output.is_file() and args.output.read_bytes() == rendered
        print(json.dumps({"ok": ok, "mode": "check", "authority": "NONE"}))
        return 0 if ok else 1
    args.output.write_bytes(rendered)
    print(json.dumps({"ok": True, "mode": "write", "authority": "NONE"}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
