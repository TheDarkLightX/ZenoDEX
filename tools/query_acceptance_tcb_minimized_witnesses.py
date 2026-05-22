#!/usr/bin/env python3
"""Query minimized witnesses emitted by acceptance TCB fuzz campaigns."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any, Sequence


REPO_ROOT = Path(__file__).resolve().parents[1]


def _default_index_for_lane(gate_lane: str) -> Path:
    return REPO_ROOT / "internal" / "fuzz_campaigns" / gate_lane / "minimized_witness_index.json"


def _load_index(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _matches(
    witness: dict[str, Any],
    *,
    witness_id: str | None,
    target: str | None,
    outcome_substr: str | None,
    path_id: str | None,
    campaign_dir_substr: str | None,
) -> bool:
    if witness_id is not None and witness.get("id") != witness_id:
        return False
    if target is not None and witness.get("target") != target:
        return False
    if outcome_substr is not None and outcome_substr not in str(witness.get("outcome_label", "")):
        return False
    if path_id is not None and witness.get("path_id") != path_id:
        return False
    if campaign_dir_substr is not None and campaign_dir_substr not in str(witness.get("campaign_dir", "")):
        return False
    return True


def _query_witnesses(
    payload: dict[str, Any],
    *,
    witness_id: str | None,
    target: str | None,
    outcome_substr: str | None,
    path_id: str | None,
    campaign_dir_substr: str | None,
    latest_only: bool,
) -> list[dict[str, Any]]:
    witnesses = [
        witness
        for witness in payload.get("witnesses", [])
        if _matches(
            witness,
            witness_id=witness_id,
            target=target,
            outcome_substr=outcome_substr,
            path_id=path_id,
            campaign_dir_substr=campaign_dir_substr,
        )
    ]
    witnesses.sort(key=lambda item: (str(item.get("campaign_dir", "")), str(item.get("id", "")), str(item.get("path_id", ""))))
    if not latest_only:
        return witnesses

    latest: dict[str, dict[str, Any]] = {}
    for witness in witnesses:
        latest[str(witness.get("id", ""))] = witness
    return [latest[key] for key in sorted(latest)]


def _print_text(index_path: Path, payload: dict[str, Any], matches: list[dict[str, Any]]) -> None:
    print("Acceptance TCB Minimized Witness Query")
    print(f"index: {index_path}")
    print(f"campaign_count: {payload.get('campaign_count', 0)}")
    print(f"witness_count: {payload.get('witness_count', 0)}")
    print(f"matched: {len(matches)}")
    for witness in matches:
        print(f"- {witness['id']}: {witness['target']} {witness['outcome_label']} path={witness['path_id']}")
        print(f"  campaign_dir={witness['campaign_dir']}")
        print(f"  witness_out={witness['witness_out']}")


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--index", help="shared minimized witness index JSON")
    parser.add_argument("--gate-lane", choices=("fast", "deep"), default="deep", help="choose the default lane-specific shared index when --index is omitted")
    parser.add_argument("--id", dest="witness_id", help="exact witness id filter")
    parser.add_argument("--target", help="exact target filter")
    parser.add_argument("--outcome-substr", help="substring match on outcome_label")
    parser.add_argument("--path-id", help="exact path id filter")
    parser.add_argument("--campaign-dir-substr", help="substring match on campaign_dir")
    parser.add_argument("--latest-only", action="store_true", help="return only the latest witness per id")
    parser.add_argument("--format", choices=("text", "json"), default="text")
    args = parser.parse_args(argv)

    index_path = Path(args.index) if args.index else _default_index_for_lane(args.gate_lane)
    payload = _load_index(index_path)
    matches = _query_witnesses(
        payload,
        witness_id=args.witness_id,
        target=args.target,
        outcome_substr=args.outcome_substr,
        path_id=args.path_id,
        campaign_dir_substr=args.campaign_dir_substr,
        latest_only=bool(args.latest_only),
    )
    out = {
        "schema": "zenodex/acceptance-tcb-fuzz-minimized-witness-query/v1",
        "index": str(index_path),
        "matched": len(matches),
        "witnesses": matches,
    }
    if args.format == "json":
        print(json.dumps(out, indent=2, sort_keys=True))
    else:
        _print_text(index_path, payload, matches)
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
