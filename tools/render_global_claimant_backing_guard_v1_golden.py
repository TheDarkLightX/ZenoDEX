#!/usr/bin/env python3
"""Render or check the research-only claimant-backing guard parity vector.

The fixture binds one closed set of V1 states to the Python claimant-backing
view, its root, and its exact reject code and message, so the Rust
implementation can replay the same states and must derive identical bytes,
roots, and outcomes. Each state is described by a small builder spec (Python
rebuilds it; Rust decodes the recorded canonical state) and the canonical
state bytes are hashed on both sides so the two constructions cannot drift.

JSON contract:
    stdout  one status line.
    exit 0  fixture written, or ``--check`` found the on-disk fixture byte-identical.
    exit 1  ``--check`` found drift.

The fixture grants no proof, runtime, settlement, migration, publisher, or
production authority.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from collections.abc import Mapping, Sequence
from pathlib import Path
from typing import Any, Final

REPO_ROOT: Final = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.core.global_economic_state_effect_refinement_v1 import (  # noqa: E402
    CLAIMANT_BACKING_MESSAGE_BY_CODE_V1,
    CLAIMANT_BACKING_VIEW_HASH_DOMAIN_V1,
    ClaimantBackingViewV1,
    classify_claimant_backing_error_v1,
    derive_claimant_backing_view_v1,
    require_claimant_backing_v1,
)
from src.core.global_settlement_types_v1 import (  # noqa: E402
    ALL_LANE_IDS_V1,
    MAX_ATOMS_V1,
    AssetSupplyV1,
    EconomicAmountV1,
    GlobalEconomicStateV1,
    LaneIdV1,
    LaneStateRootV1,
    TerminalObligationStatusV1,
    TerminalObligationV1,
    canonical_global_bytes_v1,
)

FIXTURE_SCHEMA_V1: Final = "zenodex/global-claimant-backing-guard-v1-golden/v1"
FIXTURE_PATH_V1: Final = REPO_ROOT / "tests/data/global_claimant_backing_guard_v1_golden.json"
CHAIN_ID_V1: Final = "zeno-claimant-backing-golden"
MAX: Final = MAX_ATOMS_V1

Row = tuple[str, str, str, int]
Terminal = tuple[str, str, str, int, str]


def _root(value: int) -> str:
    if not 0 < value < 1 << 256:
        raise ValueError("fixture root ordinal is out of range")
    return f"0x{value:064x}"


def _amounts(rows: Sequence[Sequence[object]]) -> tuple[EconomicAmountV1, ...]:
    typed = [
        EconomicAmountV1(str(owner), str(asset), str(domain), int(str(atoms)))
        for owner, asset, domain, atoms in rows
    ]
    return tuple(sorted(typed, key=lambda row: row.key))


def _lane_roots() -> tuple[LaneStateRootV1, ...]:
    return tuple(
        LaneStateRootV1(
            lane_id,
            _root(100 + index),
            True,
            _root(31_002 if lane_id is LaneIdV1.ASSET_TRANSFER else 2_000 + index),
        )
        for index, lane_id in enumerate(ALL_LANE_IDS_V1, start=1)
    )


def _terminals(rows: Sequence[Sequence[object]]) -> tuple[TerminalObligationV1, ...]:
    typed = [
        TerminalObligationV1(
            str(obligation_id),
            LaneIdV1.PERPS_MARKET,
            str(claimant),
            str(asset),
            int(str(atoms)),
            TerminalObligationStatusV1(str(status)),
        )
        for obligation_id, claimant, asset, atoms, status in rows
    ]
    return tuple(sorted(typed, key=lambda row: row.obligation_id))


def build_state_v1(spec: Mapping[str, Any]) -> GlobalEconomicStateV1:
    """Build the fixed-context V1 state described by a builder spec."""

    custody = list(spec.get("custody", ()))
    reserves = list(spec.get("reserves", ()))
    balances = list(spec.get("balances", ()))
    liabilities = list(spec.get("liabilities", ()))
    owned = [*custody, *reserves, *balances]
    supplies = tuple(
        AssetSupplyV1(asset, sum(int(str(row[3])) for row in owned if row[1] == asset))
        for asset in sorted({str(row[1]) for row in owned})
    )
    return GlobalEconomicStateV1(
        chain_id=CHAIN_ID_V1,
        deployment_root=_root(31_000),
        writer_epoch=1,
        height=1,
        profile_root=_root(31_001),
        lane_roots=_lane_roots(),
        balances=_amounts(balances),
        supplies=supplies,
        custody=_amounts(custody),
        liabilities=_amounts(liabilities),
        reserves=_amounts(reserves),
        terminal_obligations=_terminals(list(spec.get("terminals", ()))),
    )


def evaluate_v1(
    state: GlobalEconomicStateV1,
) -> tuple[ClaimantBackingViewV1 | None, dict[str, str]]:
    """Run derive then require; return the view (if derived) and the exact outcome."""

    try:
        view = derive_claimant_backing_view_v1(state)
    except ValueError as error:
        return None, _reject_outcome(error)
    try:
        require_claimant_backing_v1(view)
    except ValueError as error:
        return view, _reject_outcome(error)
    return view, {"status": "ACCEPT"}


def _reject_outcome(error: ValueError) -> dict[str, str]:
    code = classify_claimant_backing_error_v1(error)
    if code is None:
        raise ValueError(f"unclassified claimant-backing error: {error}") from error
    return {"status": "REJECT", "code": code.value, "message": str(error)}


def _spec(
    *,
    custody: Sequence[Row] = (),
    liabilities: Sequence[Row] = (),
    reserves: Sequence[Row] = (),
    balances: Sequence[Row] = (),
    terminals: Sequence[Terminal] = (),
) -> dict[str, list[list[object]]]:
    return {
        "custody": [list(row) for row in custody],
        "liabilities": [list(row) for row in liabilities],
        "reserves": [list(row) for row in reserves],
        "balances": [list(row) for row in balances],
        "terminals": [list(row) for row in terminals],
    }


OPEN: Final = TerminalObligationStatusV1.OPEN.value
DRAINED: Final = TerminalObligationStatusV1.DRAINED.value
TOMBSTONED: Final = TerminalObligationStatusV1.TOMBSTONED.value

# Named obligations. Every reject names the exact code and message; every accept
# is a bounded refutation that the guard does not over-reject.
VECTORS_V1: Final[dict[str, tuple[str, dict[str, list[list[object]]]]]] = {
    "accepts_empty_state": (
        "zero rows: no entitlement, no custody, no terminal, ACCEPT (BVA zero)",
        _spec(),
    ),
    "rejects_unbacked_liability": (
        "one entitlement atom with no custody in its control domain rejects R1",
        _spec(liabilities=[("alice", "USD", "perps-margin", 1)]),
    ),
    "rejects_cross_domain_backing": (
        "custody in another control domain cannot back the entitlement (R1)",
        _spec(custody=[("pool", "USD", "amm-pool", 1)], liabilities=[("alice", "USD", "perps-margin", 1)]),
    ),
    "excludes_balances_from_backing": (
        "a key-controlled balance in the same domain label is not backing (R1)",
        _spec(balances=[("protocol", "USD", "perps-margin", 1)], liabilities=[("alice", "USD", "perps-margin", 1)]),
    ),
    "excludes_reserves_from_backing": (
        "an unencumbered reserve in the same domain label is not backing (R1); reserve masking is refused",
        _spec(reserves=[("protocol", "USD", "perps-margin", 1)], liabilities=[("alice", "USD", "perps-margin", 1)]),
    ),
    "rejects_claimant_swap_hidden_by_asset_aggregate": (
        "Bob's entitlement cannot cover Alice's OPEN terminal (R2) even though the asset aggregate balances",
        _spec(
            custody=[("account-bob", "USD", "perps-margin", 1)],
            liabilities=[("bob", "USD", "perps-margin", 1)],
            terminals=[("alice-claim", "alice", "USD", 1, OPEN)],
        ),
    ),
    "accepts_exact_cross_domain_claimant_coverage": (
        "one claimant's entitlements across two control domains cover one OPEN terminal exactly",
        _spec(
            custody=[("account-a", "USD", "domain-a", 2), ("account-b", "USD", "domain-b", 3)],
            liabilities=[("alice", "USD", "domain-a", 2), ("alice", "USD", "domain-b", 3)],
            terminals=[("alice-claim", "alice", "USD", 5, OPEN)],
        ),
    ),
    "accepts_domainless_terminal_ambiguity_known_gap": (
        "V1 terminals carry no control domain, so two hidden domain preimages are indistinguishable (accepted known gap)",
        _spec(
            custody=[("custody-0", "USD", "perps-domain-0", 1), ("custody-1", "USD", "perps-domain-1", 1)],
            liabilities=[("alice", "USD", "perps-domain-0", 1), ("alice", "USD", "perps-domain-1", 1)],
            terminals=[("terminal-1", "alice", "USD", 2, OPEN)],
        ),
    ),
    "ignores_drained_terminal_amount": (
        "a DRAINED terminal at u128 max contributes no OPEN claim",
        _spec(terminals=[("drained-claim", "alice", "USD", MAX, DRAINED)]),
    ),
    "ignores_tombstoned_terminal_amount": (
        "a TOMBSTONED terminal at u128 max contributes no OPEN claim",
        _spec(terminals=[("tombstoned-claim", "alice", "USD", MAX, TOMBSTONED)]),
    ),
    "accepts_open_zero_amount_terminal": (
        "an OPEN terminal of zero atoms needs no entitlement",
        _spec(terminals=[("zero-open-claim", "alice", "USD", 0, OPEN)]),
    ),
    "accepts_u128_backing_boundary": (
        "custody, entitlement, and OPEN terminal all at u128 max are exact and accepted",
        _spec(
            custody=[("account", "USD", "perps-margin", MAX)],
            liabilities=[("alice", "USD", "perps-margin", MAX)],
            terminals=[("maximum-claim", "alice", "USD", MAX, OPEN)],
        ),
    ),
    "rejects_entitlement_aggregate_overflow": (
        "two entitlement rows summing past u128 max reject with the overflow code",
        _spec(
            custody=[("account", "USD", "perps-margin", MAX)],
            liabilities=[("alice", "USD", "perps-margin", MAX), ("bob", "USD", "perps-margin", 1)],
        ),
    ),
    "rejects_open_terminal_aggregate_overflow": (
        "two OPEN terminals of one claimant summing past u128 max reject with the overflow code",
        _spec(
            custody=[("account", "USD", "perps-margin", MAX)],
            liabilities=[("alice", "USD", "perps-margin", MAX)],
            terminals=[("claim-a", "alice", "USD", MAX, OPEN), ("claim-b", "alice", "USD", 1, OPEN)],
        ),
    ),
    "one_atom_short_rejects": (
        "custody 7 against entitlement 8 in one control domain rejects R1 (BVA one atom)",
        _spec(custody=[("account", "USD", "perps-margin", 7)], liabilities=[("alice", "USD", "perps-margin", 8)]),
    ),
    "exact_equality_accepts": (
        "custody 7 against entitlement 7 is the exact current-profile relation and accepted",
        _spec(custody=[("account", "USD", "perps-margin", 7)], liabilities=[("alice", "USD", "perps-margin", 7)]),
    ),
    "open_terminal_one_atom_over_rejects": (
        "an OPEN terminal one atom above the claimant's entitlements rejects R2 (BVA one atom)",
        _spec(
            custody=[("account", "USD", "perps-margin", 5)],
            liabilities=[("alice", "USD", "perps-margin", 5)],
            terminals=[("alice-claim", "alice", "USD", 6, OPEN)],
        ),
    ),
    "open_terminal_exact_accepts": (
        "an OPEN terminal equal to the claimant's entitlements is accepted",
        _spec(
            custody=[("account", "USD", "perps-margin", 5)],
            liabilities=[("alice", "USD", "perps-margin", 5)],
            terminals=[("alice-claim", "alice", "USD", 5, OPEN)],
        ),
    ),
    "precedence_domain_before_claimant": (
        "when R1 and R2 both fail, R1 is reported (precedence)",
        _spec(liabilities=[("alice", "USD", "perps-margin", 1)], terminals=[("alice-claim", "alice", "USD", 2, OPEN)]),
    ),
    "precedence_entitlement_overflow_before_domain": (
        "an entitlement fold overflow is reported before the R1 failure it also implies",
        _spec(liabilities=[("alice", "USD", "perps-margin", MAX), ("bob", "USD", "perps-margin", 1)]),
    ),
    "precedence_terminal_overflow_before_domain": (
        "an OPEN-terminal fold overflow is reported before an R1 failure elsewhere in the state",
        _spec(
            liabilities=[("alice", "USD", "perps-margin", 1)],
            terminals=[("claim-a", "alice", "USD", MAX, OPEN), ("claim-b", "alice", "USD", 1, OPEN)],
        ),
    ),
    "multi_asset_domains_are_independent": (
        "USD and EUR entitlements in one control domain are each backed by their own asset custody",
        _spec(
            custody=[("account", "USD", "perps-margin", 1), ("account", "EUR", "perps-margin", 1)],
            liabilities=[("alice", "USD", "perps-margin", 1), ("alice", "EUR", "perps-margin", 1)],
        ),
    ),
    "multi_asset_rejects_other_asset_shortfall": (
        "USD custody cannot back an EUR entitlement in the same control domain (R1)",
        _spec(custody=[("account", "USD", "perps-margin", 2)], liabilities=[("alice", "EUR", "perps-margin", 1)]),
    ),
    "history_1_after_deposit_5": (
        "stateful history step 1: deposit 5 into custody, entitlement, and OPEN terminal",
        _spec(
            custody=[("account", "USD", "perps-margin", 5)],
            liabilities=[("alice", "USD", "perps-margin", 5)],
            terminals=[("alice-claim", "alice", "USD", 5, OPEN)],
        ),
    ),
    "history_2_after_deposit_3": (
        "stateful history step 2: a second exact deposit of 3 keeps the relation",
        _spec(
            custody=[("account", "USD", "perps-margin", 8)],
            liabilities=[("alice", "USD", "perps-margin", 8)],
            terminals=[("alice-claim", "alice", "USD", 8, OPEN)],
        ),
    ),
    "history_3_after_drain_4": (
        "stateful history step 3: an exact drain of 4 keeps the relation",
        _spec(
            custody=[("account", "USD", "perps-margin", 4)],
            liabilities=[("alice", "USD", "perps-margin", 4)],
            terminals=[("alice-claim", "alice", "USD", 4, OPEN)],
        ),
    ),
    "history_4_custody_only_drain_rejects": (
        "stateful history step 4: draining custody without the entitlement leaves R1 violated",
        _spec(
            custody=[("account", "USD", "perps-margin", 3)],
            liabilities=[("alice", "USD", "perps-margin", 4)],
            terminals=[("alice-claim", "alice", "USD", 4, OPEN)],
        ),
    ),
}

HISTORIES_V1: Final[dict[str, list[str]]] = {
    "deposit_deposit_drain_overdrain": [
        "accepts_empty_state",
        "history_1_after_deposit_5",
        "history_2_after_deposit_3",
        "history_3_after_drain_4",
        "history_4_custody_only_drain_rejects",
    ],
}

# Bounded refutations: mutations that cannot be reached by any valid V1 state.
UNREACHABLE_MUTATIONS_V1: Final[dict[str, str]] = {
    "custody fold overflow within one asset": (
        "supply = custody + reserves + balances is validated as u128 at state construction,"
        " so custody rows of one asset cannot sum past u128 in a valid GlobalEconomicStateV1;"
        " the custody fold's checked addition is retained as defence in depth"
    ),
}

MUTATION_KILLERS_V1: Final[dict[str, str]] = {
    "count reserves as custody backing": "excludes_reserves_from_backing",
    "count balances as custody backing": "excludes_balances_from_backing",
    "key claimant coverage by control domain instead of claimant": "rejects_claimant_swap_hidden_by_asset_aggregate",
    "drop the OPEN status filter": "ignores_drained_terminal_amount",
    "use unchecked addition": "rejects_entitlement_aggregate_overflow",
    "swap the R1/R2 precedence": "precedence_domain_before_claimant",
    "evaluate R1 before folding the terminal table": "precedence_terminal_overflow_before_domain",
    "key backing by asset only": "multi_asset_rejects_other_asset_shortfall",
    "compare with >= instead of >": "exact_equality_accepts",
}


def render_fixture_v1() -> dict[str, object]:
    vectors: dict[str, object] = {}
    for name, (obligation, spec) in VECTORS_V1.items():
        state = build_state_v1(spec)
        canonical_bytes = canonical_global_bytes_v1(state)
        view, outcome = evaluate_v1(state)
        vectors[name] = {
            "obligation": obligation,
            "spec": spec,
            "state": json.loads(canonical_bytes),
            "state_bytes_sha256": hashlib.sha256(canonical_bytes).hexdigest(),
            "expected_state_root": state.state_root,
            "expected_view": None if view is None else view.to_canonical(),
            "expected_view_root": None if view is None else view.view_root,
            "expected_outcome": outcome,
        }
    return {
        "fixture_schema": FIXTURE_SCHEMA_V1,
        "authority": "NONE",
        "hash_domain": CLAIMANT_BACKING_VIEW_HASH_DOMAIN_V1,
        "reject_messages": {
            code.value: message for code, message in CLAIMANT_BACKING_MESSAGE_BY_CODE_V1.items()
        },
        "vectors": vectors,
        "histories": HISTORIES_V1,
        "mutation_killers": MUTATION_KILLERS_V1,
        "unreachable_mutations": UNREACHABLE_MUTATIONS_V1,
    }


def render_bytes_v1() -> bytes:
    return (json.dumps(render_fixture_v1(), indent=2, sort_keys=True) + "\n").encode("utf-8")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--output", type=Path, default=FIXTURE_PATH_V1)
    args = parser.parse_args(argv)
    rendered = render_bytes_v1()
    if args.check:
        current = args.output.read_bytes() if args.output.is_file() else b""
        ok = current == rendered
        sys.stdout.write(json.dumps({"ok": ok, "mode": "check", "path": str(args.output)}) + "\n")
        return 0 if ok else 1
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_bytes(rendered)
    sys.stdout.write(
        json.dumps({"ok": True, "mode": "write", "path": str(args.output), "vectors": len(VECTORS_V1)}) + "\n"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
