#!/usr/bin/env python3
"""Generate and check the research-only G1 burn-to-claim auction packet."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import sys
import tempfile
from collections.abc import Mapping
from functools import lru_cache
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUTPUT = REPO_ROOT / "docs/research/PRODUCTION_READINESS_G1_BUYBURN_AUCTION_V1.json"
SCHEMA = "zenodex/production-readiness-g1-buyburn-auction/v1"
RESEARCH_SOURCE_SUBJECT = "73a68acc88cb243ed25e5075ca5e75e3a143e5ca"
CONTRACT_PATH = "tools/production_readiness_g1_buyburn_auction_contract_v1.py"
CHECKER_PATH = "tools/check_production_readiness_g1_buyburn_auction_v1.py"

sys.path.insert(0, str(REPO_ROOT))

from tools import (  # noqa: E402
    production_readiness_g1_buyburn_auction_contract_v1 as contract,
)


def _encoded(value: Mapping[str, Any]) -> bytes:
    return json.dumps(value, indent=2, sort_keys=True).encode("utf-8") + b"\n"


def _sha256(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _git_bytes(repo_root: Path, *args: str) -> bytes:
    return subprocess.run(
        ["git", *args],
        cwd=repo_root,
        check=True,
        capture_output=True,
    ).stdout


def _source_pins(repo_root: Path) -> list[dict[str, str]]:
    pins: list[dict[str, str]] = []
    for path in contract.RESEARCH_SOURCE_PATHS:
        frozen = _git_bytes(repo_root, "show", f"{RESEARCH_SOURCE_SUBJECT}:{path}")
        if (repo_root / path).read_bytes() != frozen:
            raise ValueError(f"buyburn-auction research source drift: {path}")
        pins.append(
            {
                "path": path,
                "sha256": _sha256(frozen),
                "subject": RESEARCH_SOURCE_SUBJECT,
            }
        )
    return pins


def _validate_source_markers(repo_root: Path) -> None:
    markers = {
        "docs/research/PRODUCTION_READINESS_G1_PARTIAL_POLICY_V2.json": (
            '"whole_token_supply": 2000000000',
            '"decimals": 18',
            '"launch_active_floor_atoms": 200000000000000000000000000',
            '"absolute_floor_atoms": 1',
            '"zeno_cap_atoms": "floor(excess_atoms / 2)"',
        ),
        "docs/research/PRODUCTION_READINESS_G1_CLBF_MODEL_V1.json": (
            '"buyback_execution + buyback_carry = eligible_surplus"',
            '"activation_allowed": false',
        ),
        "tools/production_readiness_g1_clbf_contract_v1.py": (
            "UNRESTRICTED_PROTOCOL_REVENUE",
            "BUYBACK_CARRY",
            "X_BUYBACK_EXECUTION",
        ),
        "docs/research/PRODUCTION_READINESS_G1_PROFILE_INPUTS_V1.json": (
            '"id": "protocol_buy_burn_policy"',
            '"selected_profile": null',
        ),
        "src/core/m6_safe_mount_transition_v1.py": (
            "def _apply_protocol_buy_and_burn",
            "has no typed protocol-asset identity, purchase",
            "UNSUPPORTED_OPERATION",
        ),
    }
    for path, required in markers.items():
        source = (repo_root / path).read_text(encoding="utf-8")
        missing = [marker for marker in required if marker not in source]
        if missing:
            raise ValueError(f"buyburn-auction source marker drift: {path}: {missing}")


def _validate_contract() -> None:
    if contract.SELECTED_BUYBURN_ROUTE_V1 is not None:
        raise ValueError("buyburn route must remain unselected")
    if contract.ACTIVATION_AUTHORIZED or contract.SETTLEMENT_AUTHORIZED:
        raise ValueError("research buyburn contract gained runtime authority")
    expected = {
        "whole_supply": 2_000_000_000,
        "unit_scale": 10**18,
        "genesis_atoms": 2_000_000_000 * 10**18,
        "launch_floor_atoms": 200_000_000 * 10**18,
        "absolute_floor_atoms": 1,
        "maximum_research_bids": 32,
    }
    observed = {
        "whole_supply": contract.ZDEX_WHOLE_TOKEN_SUPPLY,
        "unit_scale": contract.ZDEX_UNIT_SCALE,
        "genesis_atoms": contract.ZDEX_GENESIS_SUPPLY_ATOMS,
        "launch_floor_atoms": contract.ZDEX_LAUNCH_ACTIVE_FLOOR_ATOMS,
        "absolute_floor_atoms": contract.ZDEX_ABSOLUTE_FLOOR_ATOMS,
        "maximum_research_bids": contract.MAX_RESEARCH_BIDS,
    }
    if observed != expected:
        raise ValueError("selected specification supply constants drifted")


@lru_cache(maxsize=1)
def bounded_buyburn_evidence() -> dict[str, Any]:
    nonarrival_counterexample: dict[str, int] | None = None
    nonarrival_cases = 0
    for floor_atoms in range(33):
        for supply_atoms in range(floor_atoms, 65):
            cap = contract.zeno_burn_cap_v1(supply_atoms, floor_atoms)
            nonarrival_cases += 1
            if (
                cap < 0
                or cap > supply_atoms - floor_atoms
                or (cap > 0 and supply_atoms - cap <= floor_atoms)
            ):
                nonarrival_counterexample = {
                    "floor_atoms": floor_atoms,
                    "supply_atoms": supply_atoms,
                    "cap_atoms": cap,
                }
                break

    recurrence_counterexample: dict[str, int] | None = None
    recurrence_cases = 0
    for excess_atoms in range(1, 257):
        cap = contract.zeno_burn_cap_v1(excess_atoms, 0)
        observed_next = excess_atoms - cap
        expected_next = (excess_atoms + 1) // 2
        recurrence_cases += 1
        if observed_next != expected_next:
            recurrence_counterexample = {
                "excess_atoms": excess_atoms,
                "cap_atoms": cap,
                "observed_next": observed_next,
                "expected_next": expected_next,
            }
            break

    reserve_counterexample: dict[str, int] | None = None
    reserve_cases = 0
    for burn_atoms in range(1, 9):
        for reference_quote_atoms in range(1, 9):
            for lot_value_atoms in range(1, 9):
                for reference_zdex_atoms in range(1, 9):
                    for reserve_bps in (0, 2_500, 5_000, 10_000):
                        left, right = contract.reserve_value_cross_products_v1(
                            burn_bid_atoms=burn_atoms,
                            reference_quote_atoms=reference_quote_atoms,
                            certified_lot_value_quote_atoms=lot_value_atoms,
                            reference_zdex_atoms=reference_zdex_atoms,
                            reserve_value_bps=reserve_bps,
                        )
                        expected = (
                            burn_atoms * reference_quote_atoms * contract.BPS_SCALE
                            >= lot_value_atoms * reference_zdex_atoms * reserve_bps
                        )
                        observed = left >= right
                        reserve_cases += 1
                        if expected != observed:
                            reserve_counterexample = {
                                "burn_atoms": burn_atoms,
                                "reference_quote_atoms": reference_quote_atoms,
                                "lot_value_atoms": lot_value_atoms,
                                "reference_zdex_atoms": reference_zdex_atoms,
                                "reserve_bps": reserve_bps,
                            }
                            break

    reconciliation_counterexample: dict[str, int] | None = None
    reconciliation_cases = 0
    for ceiling_atoms in range(1, 65):
        for supply_atoms in range(ceiling_atoms + 1):
            cumulative_burn_atoms = ceiling_atoms - supply_atoms
            maximum_burn = contract.zeno_burn_cap_v1(supply_atoms, 0)
            for burn_atoms in range(maximum_burn + 1):
                reconciliation_cases += 1
                successor_supply = supply_atoms - burn_atoms
                successor_cumulative_burn = cumulative_burn_atoms + burn_atoms
                if successor_supply + successor_cumulative_burn != ceiling_atoms:
                    reconciliation_counterexample = {
                        "ceiling_atoms": ceiling_atoms,
                        "supply_atoms": supply_atoms,
                        "cumulative_burn_atoms": cumulative_burn_atoms,
                        "burn_atoms": burn_atoms,
                    }
                    break

    return {
        "zeno_nonarrival_search": {
            "domain": "active floor=0..32 atoms; supply=floor..64 atoms",
            "cases": nonarrival_cases,
            "counterexample": nonarrival_counterexample,
            "predicate": (
                "cap=floor((supply-floor)/2); positive accepted burn leaves "
                "successor supply strictly above active floor"
            ),
        },
        "maximal_recurrence_search": {
            "domain": "excess supply=1..256 atoms",
            "cases": recurrence_cases,
            "counterexample": recurrence_counterexample,
            "predicate": ("after a maximal Zeno burn, successor excess=ceil(excess/2)"),
        },
        "reserve_cross_product_search": {
            "domain": (
                "burn, reference quote, lot value, reference ZDEX=1..8 atoms; "
                "reserve bps in {0,2500,5000,10000}"
            ),
            "cases": reserve_cases,
            "counterexample": reserve_counterexample,
            "predicate": ("burn*reference_quote*10000 >= lot_value*reference_zdex*reserve_bps"),
        },
        "supply_reconciliation_search": {
            "domain": ("ceiling=1..64 atoms; supply=0..ceiling; burn=0..strict Zeno cap"),
            "cases": reconciliation_cases,
            "counterexample": reconciliation_counterexample,
            "predicate": ("successor_supply + successor_cumulative_burn = supply_ceiling"),
        },
        "named_mutant_witnesses": [
            {
                "id": "CEIL_HALF_REACHES_ACTIVE_FLOOR",
                "witness": "excess=1 and ceil(excess/2)=1 reaches the active floor",
            },
            {
                "id": "NO_ZENO_CAP_CROSSES_FLOOR",
                "witness": "supply=202, floor=200, burn=2 crosses strict nonarrival",
            },
            {
                "id": "PARTIAL_ESCROW_WINNER_DEFAULT",
                "witness": "burn bid=100 and escrow=99 cannot settle atomically",
            },
            {
                "id": "MISSING_LOSER_ESCROW_RETURN",
                "witness": "every nonwinning admitted escrow needs one exact return disposition",
            },
            {
                "id": "OMITTED_REVEAL_BEATS_CANONICAL_WINNER",
                "witness": "complete reveal count differs from supplied bid tuple",
            },
            {
                "id": "STALE_OR_SELF_REFERENTIAL_PRICE",
                "witness": "same-epoch or over-age valuation occurrence",
            },
            {
                "id": "POST_COMMIT_LOT_OR_VALUATION",
                "witness": "a source lot or reference fixed after commit close changes bidder terms",
            },
            {
                "id": "UNRECONCILED_SUPPLY_STATE",
                "witness": "supply=1000 and cumulative burn=1 cannot share ceiling=1000",
            },
            {
                "id": "SERVICE_PREFUND_SWEPT_TO_AUCTION",
                "witness": "lot type outside unrestricted revenue or buyback carry",
            },
            {
                "id": "ZDEX_AS_ITS_OWN_SURPLUS_LOT",
                "witness": "burning ZDEX to receive a ZDEX lot defeats the stated value flow",
            },
            {
                "id": "TREASURY_MARKET_ORDER_FRONT_RUN",
                "witness": "direct buyback exposes treasury route, timing, and custody",
            },
            {
                "id": "DECIMALS_CREATE_MORE_ATOMS",
                "witness": "changing display scale cannot create integer supply atoms",
            },
        ],
        "claim_ceiling": (
            "Exact only for the declared bounded integer domains and direct typed "
            "settlement-candidate arithmetic. It is not an auction-equilibrium, "
            "oracle-independence, inclusion-completeness, or production proof."
        ),
    }


def build_document(repo_root: Path = REPO_ROOT) -> dict[str, Any]:
    _validate_contract()
    _validate_source_markers(repo_root)
    return {
        "schema": SCHEMA,
        "status": "RESEARCH_ONLY_UNSELECTED",
        "production_promotion": False,
        "reviewed_subject": RESEARCH_SOURCE_SUBJECT,
        "research_source_pins": _source_pins(repo_root),
        "implementation_source_pins": [
            {
                "path": CONTRACT_PATH,
                "sha256": _sha256((repo_root / CONTRACT_PATH).read_bytes()),
            },
            {
                "path": CHECKER_PATH,
                "sha256": _sha256((repo_root / CHECKER_PATH).read_bytes()),
            },
        ],
        "external_context": [
            {
                "source": "ERC-20 token standard",
                "url": "https://eips.ethereum.org/EIPS/eip-20",
                "checked_on": "2026-08-16",
                "observation": (
                    "decimals defines user representation by a power-of-ten divisor; "
                    "it does not add consensus atoms"
                ),
                "selection_effect": "NONE",
            },
            {
                "source": "OpenZeppelin ERC-20 documentation",
                "url": "https://docs.openzeppelin.com/contracts/5.x/erc20",
                "checked_on": "2026-08-16",
                "observation": (
                    "token arithmetic remains integer arithmetic and decimals is a "
                    "display convention"
                ),
                "selection_effect": "NONE",
            },
            {
                "source": "Uniswap protocol-fee overview",
                "url": ("https://developers.uniswap.org/docs/protocols/protocol-fee/overview"),
                "checked_on": "2026-08-16",
                "observation": (
                    "fee sources are collected into typed custody and a releaser can "
                    "give collected assets to a participant that burns UNI"
                ),
                "selection_effect": "ADVISORY_ANALOGY_ONLY",
            },
            {
                "source": "Uniswap protocol-fee integration best practices",
                "url": (
                    "https://developers.uniswap.org/docs/protocols/"
                    "protocol-fee/guides/best-practices"
                ),
                "checked_on": "2026-08-16",
                "observation": (
                    "nonce, exact approval, and pre/post balance checks address "
                    "front-running and unexpected burn-amount changes"
                ),
                "selection_effect": "ADVISORY_ANALOGY_ONLY",
            },
        ],
        "decision": {
            "recommended_research_candidate": ("SEALED_COMPETITIVE_BURN_TO_CLAIM_AUCTION"),
            "selection_status": "UNSELECTED_REQUIRES_USER_AND_RELEASE_APPROVAL",
            "reason": (
                "Bidders bring and fully escrow ZDEX, then compete to burn the most "
                "for an eligible surplus lot. This removes a predictable protocol "
                "market order, protocol slippage, and acquired-ZDEX custody."
            ),
            "direct_buyback_fallback_status": "UNSELECTED",
        },
        "game_surface": {
            "players": [
                "protocol surplus-lot custodian",
                "ZDEX burn bidders and coalitions",
                "commit, reveal, admission, valuation, and settlement verifiers",
                "validators, ordering actors, and censors",
                "oracle and reference-source operators",
                "ZDEX holders and fee-lot asset holders",
            ],
            "actions": [
                "create or carry an eligible surplus lot",
                "commit, reveal, escrow, omit, censor, or duplicate a burn bid",
                "manipulate lot valuation or ZDEX reference price",
                "select the highest bid, burn escrow, and transfer the lot atomically",
                "lower an active floor only through a delayed successor profile",
            ],
            "information_sets": [
                "hidden bids before reveal and public reveals after close",
                "private bidder valuation, inventory, hedges, and coalition membership",
                "source-lot lineage, reference occurrences, supply, floor, and caps",
            ],
            "payoff": (
                "received surplus-lot value minus burned ZDEX value, escrow cost, "
                "fees, censorship risk, and any admitted non-reveal penalty"
            ),
        },
        "attack_query": {
            "query": (
                "Can a bidder or operator receive an eligible surplus lot while "
                "burning too little, omitting a better admitted reveal, using stale "
                "valuation, defaulting after selection, or crossing the active floor?"
            ),
            "disaster_states": [
                "RESTRICTED_LOT_AUCTIONED",
                "ZDEX_LOT_OFFSETS_BURN",
                "WINNER_NOT_FULLY_ESCROWED",
                "LOSER_ESCROW_STRANDED",
                "BETTER_ADMITTED_REVEAL_OMITTED",
                "STALE_OR_SELF_REFERENTIAL_VALUATION",
                "POST_COMMIT_LOT_OR_VALUATION_SUBSTITUTION",
                "BELOW_RESERVE_SETTLEMENT",
                "ACTIVE_FLOOR_REACHED_OR_CROSSED",
                "SUPPLY_AND_CUMULATIVE_BURN_DIVERGE",
                "LOT_OR_AUCTION_REPLAY",
                "MID_COMMAND_FLOOR_CHANGE",
            ],
        },
        "bounded_model": {
            "integer_domain": "all accounting amounts are atoms in [0, 2^256 - 1]",
            "selected_supply_specification": {
                "whole_token_supply": contract.ZDEX_WHOLE_TOKEN_SUPPLY,
                "unit_scale": contract.ZDEX_UNIT_SCALE,
                "genesis_supply_atoms": contract.ZDEX_GENESIS_SUPPLY_ATOMS,
                "launch_active_floor_atoms": (contract.ZDEX_LAUNCH_ACTIVE_FLOOR_ATOMS),
                "absolute_floor_atoms": contract.ZDEX_ABSOLUTE_FLOOR_ATOMS,
                "decimals_rule": (
                    "E18 is fixed display metadata over integer atoms; redenomination "
                    "requires a separately versioned migration"
                ),
            },
            "auction_rule": (
                "among the complete canonical reveal set, choose maximum burn atoms; "
                "break ties by smallest commitment id; require escrow=burn bid; "
                "burn the winner and return every loser escrow exactly"
            ),
            "reserve_rule": (
                "burn_bid*reference_quote*10000 >= "
                "certified_lot_value*reference_zdex*reserve_value_bps"
            ),
            "burn_cap": (
                "min(floor((supply-active_floor)/2), "
                "floor(supply*epoch_burn_bps/10000), epoch_burn_atoms)"
            ),
            "atomic_candidate": (
                "winner escrow burn + every loser escrow return + exact lot transfer + "
                "lot/auction nullifiers + supply successor in one candidate publication"
            ),
            "conservation_rule": (
                "supply + cumulative_burn = supply_ceiling before and after settlement"
            ),
            "selected_route": contract.SELECTED_BUYBURN_ROUTE_V1,
        },
        "funding_and_value_flow": {
            "eligible_lot_types": [member.value for member in contract.BurnAuctionLotTypeV1],
            "excluded": [
                "third-party or LP property",
                "service, operations, safety, credit, genesis, or refundable-bond prefund",
                "forecast revenue and unadmitted slash proceeds",
            ],
            "source": (
                "only finalized CLBF eligible surplus already assigned to buyback "
                "execution or same-purpose buyback carry"
            ),
            "winner_flow": (
                "fully escrowed winner ZDEX is burned; the exact surplus lot moves "
                "to the authenticated winner recipient"
            ),
            "loser_flow": "every nonwinning admitted escrow is returned exactly once",
            "protocol_acquired_zdex_atoms": 0,
            "no_reserve_bid": (
                "auction is nullified, every bid escrow returns, and the unconsumed lot "
                "remains same-purpose carry"
            ),
        },
        "manipulation_analysis": {
            "removed_relative_to_direct_market_buyback": [
                "predictable protocol market order",
                "protocol price impact and slippage",
                "protocol custody of purchased ZDEX before burn",
                "route adapter choosing a market counterparty",
            ],
            "retained": [
                "valuation and reference-price manipulation",
                "bid omission, censorship, and coalition underbidding",
                "commit-reveal liveness and non-reveal handling",
                "oracle-source beneficial ownership and external hedges",
            ],
            "closures": [
                "complete reveal-set root and exact admitted count",
                "fully escrowed bids before winner selection",
                "source lot and valuation fixed no later than commit close",
                "lagged, bounded-age, multi-source valuation profile",
                "reserve-value floor; otherwise carry",
                "canonical winner and tie rule",
                "exact escrow disposition for every admitted reveal",
                "supply and cumulative-burn reconciliation",
                "source-lot and auction nullifiers",
                "strict Zeno cap plus separately delayed floor-profile releases",
            ],
        },
        "staged_floor_candidate": {
            "status": "UNSELECTED",
            "rule": (
                "a successor floor requires a new profile and release root, exact "
                "predecessor binding, delay, unchanged E18 scale and absolute floor, "
                "and a selected maximum reduction per step"
            ),
            "research_default_for_tests_only": (
                "maximum 5000 bps floor reduction per successor profile"
            ),
            "nonarrival": (
                "at a fixed floor F, maximal accepted burn changes excess E to "
                "ceil(E/2), so positive execution never reaches F"
            ),
        },
        "bounded_buyburn_evidence": bounded_buyburn_evidence(),
        "evidence_lane": {
            "current": [
                "typed first-price burn-bid selection and reserve cross products",
                "exact full-escrow, commitment, pre-commit timing, cap, and replay rejection",
                "candidate supply, burn, escrow-return, lot transfer, and nullifier plan",
                "bounded strict-floor, recurrence, reserve, and reconciliation searches",
                "delayed successor-floor profile candidate",
                "named market-order, custody, stale-price, escrow, and sweep mutants",
            ],
            "required_before_selection": [
                "choose auction versus direct-buyback route",
                "select reserve bps, epoch caps, cadence, source lag, and valuation profile",
                "select commit/reveal windows, non-reveal bond, admission, and censorship rules",
                "independent economic simulations under bidder concentration and low competition",
                "legal, tax, treasury, disclosure, and market-structure review",
            ],
            "required_before_production": [
                "complete sealed-auction lifecycle and terminal carry paths",
                "opaque verifier-created lot, reveal-set, valuation, escrow, and burn witnesses",
                "shared Rust transition and canonical codec",
                "Lean conservation and strict-floor proofs plus ESSO lifecycle checks",
                "mounted atomic ZenoLedger settlement with reject-no-commit and no-bypass tests",
            ],
        },
        "promotion_boundary": {
            "claim": (
                "Inside the declared typed model, the candidate selects the largest "
                "fully escrowed reserve-clearing burn bid and preserves the strict "
                "active-floor invariant without a protocol market purchase."
            ),
            "nonclaims": [
                "No buyburn route or numeric auction policy is selected.",
                "The model does not prove truthful bidding, competition, censorship resistance, or complete reveal inclusion.",
                "Reference-source independence and lot valuation are explicit external premises.",
                "Caller-constructible Python records are not opaque authority witnesses.",
                "The model omits complete commit, cancellation, non-reveal, replacement, and migration lifecycles.",
                "A display-decimal change cannot create more atoms or remove the need for an atom floor.",
                "This artifact cannot burn ZDEX, transfer a lot, change a floor, mount a command, or promote production.",
            ],
        },
        "activation_gate": {
            "selected_route_count": 0,
            "numeric_policy_selected": False,
            "complete_reveal_inclusion_proved": False,
            "valuation_authority_selected": False,
            "opaque_witnesses_implemented": False,
            "complete_lifecycle_implemented": False,
            "rust_transition_implemented": False,
            "formal_proofs_complete": False,
            "mounted": False,
            "settlement_allowed": False,
            "floor_change_allowed": False,
            "activation_allowed": False,
            "production_ready": False,
        },
    }


def _load_json_no_duplicates(path: Path) -> object:
    def pairs_hook(pairs: list[tuple[str, object]]) -> dict[str, object]:
        result: dict[str, object] = {}
        duplicates: list[str] = []
        for key, value in pairs:
            if key in result:
                duplicates.append(key)
            result[key] = value
        if duplicates:
            raise ValueError("duplicate JSON keys: " + ", ".join(sorted(set(duplicates))))
        return result

    return json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=pairs_hook)


def check_artifact(
    path: Path = DEFAULT_OUTPUT,
    repo_root: Path = REPO_ROOT,
) -> dict[str, Any]:
    errors: list[str] = []
    try:
        expected = build_document(repo_root)
        observed = _load_json_no_duplicates(path)
        if not isinstance(observed, dict):
            errors.append("artifact root must be an object")
        elif path.read_bytes() != _encoded(expected):
            errors.append("artifact bytes or semantics differ from generated buyburn model")
    except (
        OSError,
        ValueError,
        json.JSONDecodeError,
        subprocess.SubprocessError,
    ) as exc:
        errors.append(str(exc))
    return {
        "ok": not errors,
        "artifact": str(path),
        "errors": errors,
        "selected_route_count": 0,
        "settlement_allowed": False,
        "activation_allowed": False,
        "production_ready": False,
    }


def _write_atomic(path: Path, payload: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary_name = tempfile.mkstemp(
        dir=path.parent,
        prefix=f".{path.name}.",
        suffix=".tmp",
    )
    temporary_path = Path(temporary_name)
    try:
        with os.fdopen(descriptor, "wb") as handle:
            handle.write(payload)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary_path, path)
        directory_descriptor = os.open(path.parent, os.O_RDONLY)
        try:
            os.fsync(directory_descriptor)
        finally:
            os.close(directory_descriptor)
    finally:
        if temporary_path.exists():
            temporary_path.unlink()


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args(argv)

    if args.write:
        _write_atomic(args.output, _encoded(build_document()))
    report: dict[str, Any] = (
        check_artifact(args.output)
        if args.check
        else {
            "ok": True,
            "settlement_allowed": False,
            "activation_allowed": False,
            "production_ready": False,
        }
    )
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    elif args.check:
        print("PASS" if report["ok"] else "FAIL")
        for error in report.get("errors", []):
            print(f"- {error}")
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
