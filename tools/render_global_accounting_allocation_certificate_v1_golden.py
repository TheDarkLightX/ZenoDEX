#!/usr/bin/env python3
"""Render the shared Python/Rust golden vector for GlobalAccountingAllocationCertificateV1.

Each vector records one V1 state, one certificate (both as canonical JSON), the exact
outcome (ACCEPT or a closed reject code with detail and message), and the derived
roots (lane fragment roots, field-ownership, terminal-binding, allocation). Rust
replays every vector through its own implementation, so a divergence in row hashing,
fold order, checked arithmetic, precedence, or message bytes fails on one side.

The registry has no receipt-backed producer, so the only accepted certificate is the
registered-empty one over a state whose lanes are all disabled and whose economic
tables are empty. Vectors with non-empty fragments are still recorded: they pin the
cross-language roots of every row type even though the checker rejects them.

Deterministic: no clock, no randomness, no policy values selected from a fixture.
Authority: NONE.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from collections.abc import Sequence
from dataclasses import replace
from pathlib import Path
from typing import Any, Final

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.core import global_accounting_allocation_certificate_v1 as cert  # noqa: E402
from src.core.global_settlement_types_v1 import (  # noqa: E402
    ALL_LANE_IDS_V1,
    AssetSupplyV1,
    EconomicAmountV1,
    GlobalEconomicStateV1,
    LaneIdV1,
    LaneStateRootV1,
    OutboxStateV1,
    OutboxStatusV1,
    TerminalObligationStatusV1,
    TerminalObligationV1,
    canonical_global_bytes_v1,
)

FIXTURE_PATH_V1: Final = ROOT / "tests" / "data" / "global_accounting_allocation_certificate_v1_golden.json"
FIXTURE_SCHEMA_V1: Final = "zenodex/global-accounting-allocation-certificate-v1-golden/v2"

# Opus P15 P2-2: the overflow folds are unreachable through the top-level checker while no
# receipt-backed producer is registered, so their reject details cannot be pinned by recorded
# vectors; both language sides instead exercise the fold sites directly against these shared
# literals ({lane} is the lane id value).
FOLD_OVERFLOW_LABELS_V1: Final = (
    "{lane} controlled",
    "{lane} assignments",
    "reserves",
    "terminal totals",
    "custody",
)
CHAIN_ID_V1: Final = "zeno-allocation-certificate-golden"
MAX: Final = (1 << 128) - 1
Row = tuple[str, str, str, int]


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _lane_roots(enabled: Sequence[bool], foreign_registered_empty_root: bool = False) -> tuple[LaneStateRootV1, ...]:
    """Lane roots: registered-empty lanes sit at their empty state root unless a foreign root is requested."""

    roots: list[LaneStateRootV1] = []
    for index, (lane_id, flag) in enumerate(zip(ALL_LANE_IDS_V1, enabled, strict=True), start=1):
        registered = cert.REGISTERED_EMPTY_LANE_ROOTS_V1.get(lane_id)
        root = _root(3_000 + index) if registered is None or foreign_registered_empty_root else registered
        roots.append(LaneStateRootV1(lane_id, _root(200 + index), flag, root))
    return tuple(roots)


def _amounts(rows: Sequence[Row]) -> tuple[EconomicAmountV1, ...]:
    typed = [EconomicAmountV1(owner, asset, domain, atoms) for owner, asset, domain, atoms in rows]
    return tuple(sorted(typed, key=lambda row: row.key))


def build_state_v1(spec: dict[str, Any]) -> GlobalEconomicStateV1:
    """Build a V1 state: lanes disabled by default; economic tables from the spec."""

    enabled = [bool(flag) for flag in spec.get("lanes_enabled", [False] * 12)]
    custody = [tuple(row) for row in spec.get("custody", ())]
    liabilities = [tuple(row) for row in spec.get("liabilities", ())]
    reserves = [tuple(row) for row in spec.get("reserves", ())]
    owned = [*custody, *reserves]
    supplies = tuple(
        AssetSupplyV1(asset, sum(int(row[3]) for row in owned if row[1] == asset))
        for asset in sorted({str(row[1]) for row in owned})
    )
    terminals = tuple(
        sorted(
            (
                TerminalObligationV1(str(o), LaneIdV1(str(lane)), str(c), str(a), int(n), TerminalObligationStatusV1(str(s)))
                for o, lane, c, a, n, s in spec.get("terminals", ())
            ),
            key=lambda row: row.obligation_id,
        )
    )
    outbox = tuple(
        sorted(
            (OutboxStateV1(str(e), str(d), str(p), str(c), OutboxStatusV1(str(s))) for e, d, p, c, s in spec.get("outbox", ())),
            key=lambda row: row.effect_id,
        )
    )
    return GlobalEconomicStateV1(
        chain_id=CHAIN_ID_V1,
        deployment_root=_root(41_000),
        writer_epoch=3,
        height=7,
        profile_root=_root(41_001),
        lane_roots=_lane_roots(enabled, bool(spec.get("foreign_registered_empty_root", False))),
        supplies=supplies,
        custody=_amounts([(r[0], r[1], r[2], int(r[3])) for r in custody]),
        liabilities=_amounts([(r[0], r[1], r[2], int(r[3])) for r in liabilities]),
        reserves=_amounts([(r[0], r[1], r[2], int(r[3])) for r in reserves]),
        terminal_obligations=terminals,
        outbox=outbox,
    )


def _spec(**fields: Any) -> dict[str, Any]:
    spec: dict[str, Any] = {"lanes_enabled": [False] * 12}
    spec.update(fields)
    return spec


ALL_ENABLED: Final = [True] * 12
ONE_ENABLED: Final = [False] * 12
ONE_ENABLED[0] = True
# The first lane without a receipt-backed producer (SPOT_LIQUIDITY): the BLOCKED exemplar since C9b-2b.
SECOND_ENABLED: Final = [False] * 12
SECOND_ENABLED[1] = True


def _fragment_with_rows(fragment: cert.LaneAllocationFragmentV1, **rows: Any) -> cert.LaneAllocationFragmentV1:
    return replace(fragment, **rows)


def _certificate_with_fragments(
    certificate: cert.GlobalAccountingAllocationCertificateV1, fragments: tuple[cert.LaneAllocationFragmentV1, ...]
) -> cert.GlobalAccountingAllocationCertificateV1:
    rows = cert.derive_canonical_allocation_rows_v1(fragments)
    return replace(
        certificate,
        ordered_lane_fragments=fragments,
        canonical_allocation_rows=rows,
        field_ownership_root=cert.derive_field_ownership_root_v1(fragments),
        terminal_binding_root=cert.derive_terminal_binding_root_v1(fragments),
        allocation_root=cert.derive_allocation_root_v1(fragments, rows),
    )


def _synthetic_rows(fragment: cert.LaneAllocationFragmentV1) -> cert.LaneAllocationFragmentV1:
    """A well-formed, fully classified fragment: pins every row type's cross-language root."""

    return _fragment_with_rows(
        fragment,
        controlled_locations=(cert.ControlledLocationRowV1("USD", "pool-a", "spot-pool", 10),),
        claimant_entitlements=(cert.ClaimantEntitlementRowV1("USD", "alice", "spot-pool", 7),),
        unencumbered_reserves=(cert.UnencumberedReserveRowV1("USD", "protocol:fee-unallocated-reserve", "spot-pool", 2),),
        pending_external_obligations=(
            cert.PendingExternalObligationRowV1(_root(9_001), "USD", 1, "dest-1", _root(9_002), "spot-pool", "pool-a"),
        ),
        terminal_bindings=(
            cert.TerminalBindingRowV1("terminal-1", "alice", "USD", 3, "spot-pool", "pool-a", fragment.lane_id, fragment.lane_state_root),
        ),
    )


# name -> (obligation, state spec, certificate mutation name)
VECTORS_V1: Final[dict[str, tuple[str, dict[str, Any], str]]] = {
    "accepts_registered_empty_certificate_over_empty_state": (
        "all lanes disabled, empty economic tables: the registered-empty certificate is accepted with derived roots",
        _spec(),
        "identity",
    ),
    "rejects_enabled_receipt_backed_lane_without_witness": (
        "an enabled lane whose registered producer is receipt-backed rejects RECEIPT_WITNESS_REQUIRED when no sealed witness fills its slot (a JSON vector carries no witness, so this is the only witness code the fixture renders)",
        _spec(lanes_enabled=ONE_ENABLED),
        "identity",
    ),
    "rejects_enabled_lane_without_receipt_backed_producer": (
        "an enabled lane without a receipt-backed producer rejects BLOCKED_LANE_PRODUCER_MISSING naming the lane and the blocking obligation",
        _spec(lanes_enabled=SECOND_ENABLED),
        "identity",
    ),
    "rejects_all_lanes_enabled_at_the_first_unregistered_lane": (
        "precedence: with every lane enabled the first lane in canonical order without a receipt-backed producer is named; the receipt-backed first lane passes the producer gate and its missing witness would be reported only by the later witness pass",
        _spec(lanes_enabled=ALL_ENABLED),
        "identity",
    ),
    "rejects_header_writer_epoch_drift": ("a certificate for another writer epoch rejects HEADER_BINDING_DRIFT", _spec(), "writer_epoch_plus_one"),
    "rejects_header_profile_root_drift": ("a certificate for another profile rejects HEADER_BINDING_DRIFT", _spec(), "profile_root_forged"),
    "rejects_header_chain_context_drift": ("a certificate for another deployment rejects HEADER_BINDING_DRIFT", _spec(), "chain_context_forged"),
    "rejects_lane_order_swap": ("swapping two fragments rejects LANE_ORDER_DRIFT", _spec(), "swap_first_two_fragments"),
    "rejects_lane_order_missing_lane": ("eleven fragments reject LANE_ORDER_DRIFT", _spec(), "drop_last_fragment"),
    "rejects_lane_state_root_forged": ("a fragment bound to another lane root rejects LANE_STATE_ROOT_DRIFT", _spec(), "forge_first_lane_root"),
    "rejects_lane_enabled_flag_forged": ("a fragment claiming a disabled lane is enabled rejects LANE_STATE_ROOT_DRIFT", _spec(), "forge_first_enabled_flag"),
    "rejects_producer_kind_drift": ("a fragment claiming RECEIPT_BACKED for a lane registered without a producer rejects PRODUCER_KIND_DRIFT", _spec(), "claim_receipt_backed_second"),
    "rejects_disabled_lane_with_rows": ("a disabled lane fragment carrying rows rejects DISABLED_LANE_NOT_EMPTY", _spec(), "synthetic_rows_first"),
    "rejects_registered_empty_lane_with_foreign_root": ("a registered-empty lane committed at a root other than its empty state root rejects REGISTERED_EMPTY_ROOT_DRIFT", _spec(foreign_registered_empty_root=True), "identity"),
    "rejects_later_lane_root_drift_before_earlier_lane_rows": ("a forged root on the second lane outranks rows on the disabled first lane: LANE_STATE_ROOT_DRIFT precedes DISABLED_LANE_NOT_EMPTY (check-major)", _spec(), "synthetic_rows_first_then_forge_second_lane_root"),
    "rejects_disabled_lane_with_single_reserve_row": ("even one reserve row on a disabled lane rejects DISABLED_LANE_NOT_EMPTY", _spec(), "single_reserve_row_first"),
    "rejects_liabilities_without_entitlement_rows": ("V1 liabilities with empty fragments reject ENTITLEMENT_ROWS_DRIFT", _spec(liabilities=[("alice", "USD", "spot-pool", 5)]), "identity"),
    "rejects_reserves_without_reserve_rows": ("V1 reserves with empty fragments reject RESERVE_ROWS_DRIFT", _spec(reserves=[("protocol:fee-unallocated-reserve", "USD", "zenoledger:protocol-fee-residue", 2)]), "identity"),
    "rejects_pending_outbox_without_external_rows": ("a PENDING outbox row with empty fragments rejects EXTERNAL_OBLIGATION_BINDING_DRIFT", _spec(outbox=[(_root(9_001), "dest-1", _root(9_002), _root(9_003), "PENDING")]), "identity"),
    "accepts_acknowledged_outbox_without_external_rows": ("an ACKNOWLEDGED outbox row is not a pending obligation; the empty certificate is accepted", _spec(outbox=[(_root(9_001), "dest-1", _root(9_002), _root(9_003), "ACKNOWLEDGED")]), "identity"),
    "rejects_open_terminal_without_binding_row": ("an OPEN terminal with empty fragments rejects TERMINAL_BINDING_DRIFT", _spec(terminals=[("terminal-1", "ASSET_TRANSFER", "alice", "USD", 3, "OPEN")]), "identity"),
    "accepts_drained_terminal_without_binding_row": ("a DRAINED terminal needs no binding row; the empty certificate is accepted", _spec(terminals=[("terminal-1", "ASSET_TRANSFER", "alice", "USD", 3, "DRAINED")]), "identity"),
    "rejects_custody_without_controlled_locations": ("V1 custody with empty fragments rejects LANE_AGGREGATE_DRIFT", _spec(custody=[("pool-a", "USD", "spot-pool", 10)]), "identity"),
    "rejects_forged_allocation_root": ("a forged allocation root rejects DERIVED_ROOT_DRIFT", _spec(), "forge_allocation_root"),
    "rejects_forged_field_ownership_root": ("a forged field-ownership root rejects DERIVED_ROOT_DRIFT", _spec(), "forge_field_ownership_root"),
    "rejects_forged_terminal_binding_root": ("a forged terminal-binding root rejects DERIVED_ROOT_DRIFT", _spec(), "forge_terminal_binding_root"),
    "pins_roots_of_a_fully_classified_synthetic_fragment": ("a well-formed fragment with every row type pins cross-language roots (rejected only because the lane is disabled)", _spec(), "synthetic_rows_last"),
    "rejects_forged_binding_root": ("a binding root that is not the committed lane state root rejects BINDING_ROOT_DRIFT", _spec(), "forge_binding_root"),
    "pins_roots_of_u128_boundary_rows": ("u128 maximum atoms in every row type hash identically in both languages", _spec(), "u128_rows_last"),
}


def _mutate(
    name: str, certificate: cert.GlobalAccountingAllocationCertificateV1, state: GlobalEconomicStateV1
) -> cert.GlobalAccountingAllocationCertificateV1:
    fragments = certificate.ordered_lane_fragments
    if name == "identity":
        return certificate
    if name == "writer_epoch_plus_one":
        return replace(certificate, writer_epoch=certificate.writer_epoch + 1)
    if name == "profile_root_forged":
        return replace(certificate, profile_root=_root(77))
    if name == "chain_context_forged":
        return replace(certificate, chain_context=cert.ChainContextV1(state.chain_id, _root(78)))
    if name == "swap_first_two_fragments":
        return _certificate_with_fragments(certificate, (fragments[1], fragments[0], *fragments[2:]))
    if name == "drop_last_fragment":
        return _certificate_with_fragments(certificate, fragments[:-1])
    if name == "forge_first_lane_root":
        return _certificate_with_fragments(certificate, (replace(fragments[0], lane_state_root=_root(79)), *fragments[1:]))
    if name == "synthetic_rows_first_then_forge_second_lane_root":
        return _certificate_with_fragments(
            certificate, (_synthetic_rows(fragments[0]), replace(fragments[1], lane_state_root=_root(83)), *fragments[2:])
        )
    if name == "forge_first_enabled_flag":
        return _certificate_with_fragments(certificate, (replace(fragments[0], enabled=True), *fragments[1:]))
    if name == "claim_receipt_backed_second":
        return _certificate_with_fragments(
            certificate, (fragments[0], replace(fragments[1], producer_kind=cert.LaneProducerKindV1.RECEIPT_BACKED), *fragments[2:])
        )
    if name == "synthetic_rows_first":
        return _certificate_with_fragments(certificate, (_synthetic_rows(fragments[0]), *fragments[1:]))
    if name == "synthetic_rows_last":
        return _certificate_with_fragments(certificate, (*fragments[:-1], _synthetic_rows(fragments[-1])))
    if name == "single_reserve_row_first":
        first = _fragment_with_rows(
            fragments[0], unencumbered_reserves=(cert.UnencumberedReserveRowV1("USD", "protocol:fee-unallocated-reserve", "spot-pool", 1),)
        )
        return _certificate_with_fragments(certificate, (first, *fragments[1:]))
    if name == "u128_rows_last":
        last = _fragment_with_rows(
            fragments[-1],
            controlled_locations=(cert.ControlledLocationRowV1("USD", "pool-a", "spot-pool", MAX),),
            claimant_entitlements=(cert.ClaimantEntitlementRowV1("USD", "alice", "spot-pool", MAX),),
            terminal_bindings=(
                cert.TerminalBindingRowV1("terminal-max", "alice", "USD", MAX, "spot-pool", "pool-a", fragments[-1].lane_id, fragments[-1].lane_state_root),
            ),
        )
        return _certificate_with_fragments(certificate, (*fragments[:-1], last))
    if name == "forge_binding_root":
        return _certificate_with_fragments(certificate, (replace(fragments[0], binding_root=_root(84)), *fragments[1:]))
    if name == "forge_allocation_root":
        return replace(certificate, allocation_root=_root(80))
    if name == "forge_field_ownership_root":
        return replace(certificate, field_ownership_root=_root(81))
    if name == "forge_terminal_binding_root":
        return replace(certificate, terminal_binding_root=_root(82))
    raise ValueError(f"unknown certificate mutation {name}")


def evaluate_v1(
    certificate: cert.GlobalAccountingAllocationCertificateV1, state: GlobalEconomicStateV1
) -> dict[str, object]:
    # Every rendered vector is witness-less: the fixture carries no sealed witness (C9b-2a).
    outcome = cert.check_global_accounting_allocation_certificate_v1(certificate, state, cert.EMPTY_LANE_WITNESS_SLOTS_V1)
    if isinstance(outcome, cert.AllocationCertificateAcceptedV1):
        return {"status": "ACCEPT", "lane_fragment_roots": list(outcome.lane_fragment_roots)}
    return {"status": "REJECT", "code": outcome.code.value, "detail": outcome.detail, "message": outcome.message}


# mutation -> (vector, expected outcome code or ACCEPT); the render step checks each polarity.
MUTATION_KILLERS_V1: Final[dict[str, tuple[str, str]]] = {
    "accept an enabled lane without a receipt-backed producer": ("rejects_enabled_lane_without_receipt_backed_producer", "BLOCKED_LANE_PRODUCER_MISSING"),
    "accept an enabled receipt-backed lane without its sealed witness": ("rejects_enabled_receipt_backed_lane_without_witness", "RECEIPT_WITNESS_REQUIRED"),
    "skip the header binding": ("rejects_header_writer_epoch_drift", "HEADER_BINDING_DRIFT"),
    "accept fragments out of canonical lane order": ("rejects_lane_order_swap", "LANE_ORDER_DRIFT"),
    "accept a fragment bound to a foreign lane root": ("rejects_lane_state_root_forged", "LANE_STATE_ROOT_DRIFT"),
    "trust the fragment's producer kind instead of the registry": ("rejects_producer_kind_drift", "PRODUCER_KIND_DRIFT"),
    "let a disabled lane carry rows": ("rejects_disabled_lane_with_rows", "DISABLED_LANE_NOT_EMPTY"),
    "accept a registered-empty lane at a foreign root": ("rejects_registered_empty_lane_with_foreign_root", "REGISTERED_EMPTY_ROOT_DRIFT"),
    "check the lane bindings lane-major instead of check-major": ("rejects_later_lane_root_drift_before_earlier_lane_rows", "LANE_STATE_ROOT_DRIFT"),
    "skip the liabilities equality": ("rejects_liabilities_without_entitlement_rows", "ENTITLEMENT_ROWS_DRIFT"),
    "skip the reserve partition equality": ("rejects_reserves_without_reserve_rows", "RESERVE_ROWS_DRIFT"),
    "ignore PENDING outbox rows": ("rejects_pending_outbox_without_external_rows", "EXTERNAL_OBLIGATION_BINDING_DRIFT"),
    "count ACKNOWLEDGED outbox rows as pending": ("accepts_acknowledged_outbox_without_external_rows", "ACCEPT"),
    "ignore OPEN terminal obligations": ("rejects_open_terminal_without_binding_row", "TERMINAL_BINDING_DRIFT"),
    "count DRAINED terminals as open": ("accepts_drained_terminal_without_binding_row", "ACCEPT"),
    "skip the custody aggregate equality": ("rejects_custody_without_controlled_locations", "LANE_AGGREGATE_DRIFT"),
    "trust the recorded allocation root": ("rejects_forged_allocation_root", "DERIVED_ROOT_DRIFT"),
    "trust the fragment's binding root": ("rejects_forged_binding_root", "BINDING_ROOT_DRIFT"),
    "trust the recorded field-ownership root": ("rejects_forged_field_ownership_root", "DERIVED_ROOT_DRIFT"),
    "trust the recorded terminal-binding root": ("rejects_forged_terminal_binding_root", "DERIVED_ROOT_DRIFT"),
    "accept the registered-empty certificate over a non-empty state": ("rejects_custody_without_controlled_locations", "LANE_AGGREGATE_DRIFT"),
}


def _mutation_killers_v1(vectors: dict[str, dict[str, object]]) -> dict[str, dict[str, str]]:
    table: dict[str, dict[str, str]] = {}
    for mutation, (vector_name, expected_code) in MUTATION_KILLERS_V1.items():
        outcome = vectors[vector_name]["expected_outcome"]
        if not isinstance(outcome, dict):
            raise TypeError(f"rendered vector {vector_name} has no outcome")
        actual = "ACCEPT" if outcome["status"] == "ACCEPT" else str(outcome["code"])
        if actual != expected_code:
            raise ValueError(f"mutation killer polarity drift: {mutation}: {vector_name} yields {actual}, declared {expected_code}")
        table[mutation] = {"vector": vector_name, "expected_code": expected_code}
    return table


def render_fixture_v1() -> dict[str, object]:
    vectors: dict[str, dict[str, object]] = {}
    for name, (obligation, spec, mutation) in VECTORS_V1.items():
        state = build_state_v1(spec)
        certificate = _mutate(mutation, cert.build_registered_empty_certificate_v1(state), state)
        state_bytes = canonical_global_bytes_v1(state)
        certificate_bytes = canonical_global_bytes_v1(certificate)
        fragments = certificate.ordered_lane_fragments
        vectors[name] = {
            "obligation": obligation,
            "spec": spec,
            "certificate_mutation": mutation,
            "state": json.loads(state_bytes),
            "state_bytes_sha256": hashlib.sha256(state_bytes).hexdigest(),
            "expected_state_root": state.state_root,
            "certificate": json.loads(certificate_bytes),
            "certificate_bytes_sha256": hashlib.sha256(certificate_bytes).hexdigest(),
            "derived": {
                "lane_fragment_roots": [fragment.fragment_root for fragment in fragments],
                "field_ownership_root": cert.derive_field_ownership_root_v1(fragments),
                "terminal_binding_root": cert.derive_terminal_binding_root_v1(fragments),
                "allocation_root": cert.derive_allocation_root_v1(fragments, cert.derive_canonical_allocation_rows_v1(fragments)),
            },
            "expected_outcome": evaluate_v1(certificate, state),
        }
    return {
        "fixture_schema": FIXTURE_SCHEMA_V1,
        "fold_overflow_labels": list(FOLD_OVERFLOW_LABELS_V1),
        "authority": "NONE",
        "certificate_schema": cert.GLOBAL_ACCOUNTING_ALLOCATION_CERTIFICATE_SCHEMA_V1,
        "reject_messages": {code.value: message for code, message in cert.ALLOCATION_CERTIFICATE_REJECT_MESSAGE_BY_CODE_V1.items()},
        "check_order": list(cert.CHECK_ORDER_V1),
        "producer_registry": dict(cert.certificate_registry_view_v1()),
        "vectors": vectors,
        "mutation_killers": _mutation_killers_v1(vectors),
    }


def render_bytes_v1() -> bytes:
    return (json.dumps(render_fixture_v1(), indent=2, sort_keys=True) + "\n").encode("utf-8")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--output", type=Path, default=FIXTURE_PATH_V1)
    parser.add_argument("--check", action="store_true", help="compare the committed fixture instead of writing")
    args = parser.parse_args(argv)
    rendered = render_bytes_v1()
    if args.check:
        current = args.output.read_bytes() if args.output.is_file() else None
        ok = current == rendered
        print(json.dumps({"ok": ok, "mode": "check", "path": str(args.output)}))
        return 0 if ok else 1
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_bytes(rendered)
    print(json.dumps({"ok": True, "mode": "write", "path": str(args.output), "vectors": len(VECTORS_V1)}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
