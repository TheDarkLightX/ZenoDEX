#!/usr/bin/env python3
from __future__ import annotations

import json
import subprocess
import sys
from collections import Counter, defaultdict
from dataclasses import dataclass
from hashlib import sha256
from itertools import groupby
from pathlib import Path
from typing import Any, Iterable, Mapping

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from src.core.sealed_bid_auction import (  # noqa: E402
    MAX_UNITS,
    RevealedSealedBid,
    make_sealed_bid_commit_receipt,
    settle_uniform_price_sealed_bids,
    verify_commit_receipt,
)
from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps  # noqa: E402


OUT_DIR = REPO_ROOT / "generated" / "zenodex_sealed_bid_apportionment_breakthrough_20260628"
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = REPO_ROOT / "docs" / "research" / "ZENODEX_SEALED_BID_APPORTIONMENT_BREAKTHROUGH_20260628.md"
TAU_SPEC = REPO_ROOT / "src" / "tau_specs" / "recommended" / "sealed_bid_marginal_bucket_certificate_v1.tau"


@dataclass(frozen=True)
class TauCase:
    case_id: str
    step: dict[str, int]
    expected: dict[str, int]


@dataclass(frozen=True)
class MarginalBucket:
    clearing_price: int
    remaining_before_bucket: int
    prefix_filled_quantity: int
    bucket: tuple[tuple[int, RevealedSealedBid], ...]


TAU_CASES = (
    TauCase(
        "research_and_production_scope_pass",
        {"i1": 1, "i2": 1, "i3": 1, "i4": 1, "i5": 1, "i6": 1, "i7": 1, "i8": 1, "i9": 1, "i10": 1, "i11": 1},
        {"o1": 1, "o2": 1, "o3": 1, "o4": 1, "o5": 0},
    ),
    TauCase(
        "split_risk_research_only",
        {"i1": 1, "i2": 1, "i3": 1, "i4": 1, "i5": 1, "i6": 1, "i7": 1, "i8": 1, "i9": 0, "i10": 1, "i11": 1},
        {"o1": 1, "o2": 1, "o3": 1, "o4": 0},
    ),
    TauCase(
        "privacy_reject",
        {"i1": 1, "i2": 1, "i3": 1, "i4": 1, "i5": 1, "i6": 0, "i7": 1, "i8": 1, "i9": 1, "i10": 1, "i11": 1},
        {"o2": 0, "o3": 0, "o4": 0},
    ),
    TauCase(
        "unclassified_risk_reject",
        {"i1": 1, "i2": 1, "i3": 1, "i4": 1, "i5": 1, "i6": 1, "i7": 1, "i8": 0, "i9": 1, "i10": 1, "i11": 1},
        {"o1": 1, "o2": 1, "o3": 0, "o4": 0},
    ),
    TauCase(
        "inactive_safe",
        {"i1": 0, "i2": 1, "i3": 1, "i4": 1, "i5": 1, "i6": 1, "i7": 1, "i8": 1, "i9": 1, "i10": 1, "i11": 1},
        {"o3": 0, "o4": 0, "o5": 1},
    ),
)


def _stable_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def _stable_hash(value: Any) -> str:
    return sha256(_stable_json(value).encode("utf-8")).hexdigest()


def _bid_key(bid: RevealedSealedBid) -> tuple[str, str]:
    return (str(bid.bidder_id), str(bid.commitment))


def _ordered_bids(bids: Iterable[RevealedSealedBid]) -> tuple[tuple[int, RevealedSealedBid], ...]:
    return tuple(
        (index, bid)
        for index, bid in sorted(
            enumerate(bids),
            key=lambda item: (-int(item[1].limit_price), _bid_key(item[1]), item[0]),
        )
    )


def find_marginal_bucket(*, units_for_sale: int, bids: Iterable[RevealedSealedBid]) -> MarginalBucket:
    if not isinstance(units_for_sale, int) or isinstance(units_for_sale, bool) or units_for_sale < 0 or units_for_sale > MAX_UNITS:
        raise ValueError("units_for_sale out of range")
    remaining = int(units_for_sale)
    prefix_filled = 0
    ordered = _ordered_bids(tuple(bids))
    for price, group in groupby(ordered, key=lambda item: int(item[1].limit_price)):
        bucket = tuple(group)
        bucket_quantity = sum(int(bid.quantity) for _index, bid in bucket)
        if bucket_quantity <= 0:
            continue
        if bucket_quantity <= remaining:
            prefix_filled += int(bucket_quantity)
            remaining -= int(bucket_quantity)
            continue
        return MarginalBucket(
            clearing_price=int(price),
            remaining_before_bucket=int(remaining),
            prefix_filled_quantity=int(prefix_filled),
            bucket=bucket,
        )
    raise ValueError("no oversubscribed marginal bucket")


def _receipt_for_bid(*, case_id: str, units_for_sale: int, bid: RevealedSealedBid) -> dict[str, Any]:
    return make_sealed_bid_commit_receipt(
        batch_id=f"{case_id}:batch",
        bidder_id=str(bid.bidder_id),
        commitment=str(bid.commitment),
        commit_epoch=1,
        reveal_deadline_epoch=2,
        units_for_sale=int(units_for_sale),
    )


def _bucket_rows(bucket: MarginalBucket) -> list[dict[str, Any]]:
    total_requested = sum(int(bid.quantity) for _index, bid in bucket.bucket)
    if total_requested <= 0:
        raise ValueError("empty marginal bucket")
    rows: list[dict[str, Any]] = []
    base_total = 0
    for occurrence_index, bid in bucket.bucket:
        numerator = int(bid.quantity) * int(bucket.remaining_before_bucket)
        base = numerator // total_requested
        remainder = numerator % total_requested
        base_total += int(base)
        rows.append(
            {
                "occurrence_index": int(occurrence_index),
                "bidder_id": str(bid.bidder_id),
                "commitment": str(bid.commitment),
                "quantity": int(bid.quantity),
                "limit_price": int(bid.limit_price),
                "numerator": int(numerator),
                "base": int(base),
                "remainder": int(remainder),
                "tie_key": [str(bid.bidder_id), str(bid.commitment), int(occurrence_index)],
            }
        )
    leftover = int(bucket.remaining_before_bucket) - int(base_total)
    ranked = sorted(rows, key=lambda row: (-int(row["remainder"]), row["tie_key"]))
    bonus_keys = {tuple(row["tie_key"]) for row in ranked[: max(0, leftover)]}
    for row in rows:
        bonus = 1 if tuple(row["tie_key"]) in bonus_keys else 0
        row["bonus"] = int(bonus)
        row["fill_quantity"] = int(row["base"]) + int(bonus)
        row["lower_quota"] = int(row["base"])
        row["upper_quota"] = int(row["base"]) + (1 if int(row["remainder"]) > 0 else 0)
    return rows


def _settlement_fill_counter(settlement: Any) -> Counter[tuple[str, str, int, int]]:
    return Counter(
        (str(fill.bidder_id), str(fill.commitment), int(fill.filled_quantity), int(fill.paid_price))
        for fill in settlement.fills
    )


def _expected_counter_from_certificate(certificate: Mapping[str, Any]) -> Counter[tuple[str, str, int, int]]:
    clearing_price = int(certificate["clearing_price"])
    rows = certificate["marginal_rows"]
    prefix_rows = certificate["prefix_rows"]
    counter: Counter[tuple[str, str, int, int]] = Counter()
    for row in prefix_rows:
        counter[(str(row["bidder_id"]), str(row["commitment"]), int(row["quantity"]), clearing_price)] += 1
    for row in rows:
        fill_quantity = int(row["fill_quantity"])
        if fill_quantity > 0:
            counter[(str(row["bidder_id"]), str(row["commitment"]), fill_quantity, clearing_price)] += 1
    return counter


def _single_bidder_scope_ok(rows: list[dict[str, Any]]) -> bool:
    counts: Counter[str] = Counter(str(row["bidder_id"]) for row in rows)
    return all(count == 1 for count in counts.values())


def build_certificate(*, case_id: str, units_for_sale: int, bids: tuple[RevealedSealedBid, ...]) -> dict[str, Any]:
    bucket = find_marginal_bucket(units_for_sale=units_for_sale, bids=bids)
    rows = _bucket_rows(bucket)
    ordered = _ordered_bids(bids)
    prefix_rows = [
        {
            "occurrence_index": int(index),
            "bidder_id": str(bid.bidder_id),
            "commitment": str(bid.commitment),
            "quantity": int(bid.quantity),
            "limit_price": int(bid.limit_price),
        }
        for index, bid in ordered
        if int(bid.limit_price) > int(bucket.clearing_price)
    ]
    public_receipts = [
        _receipt_for_bid(case_id=case_id, units_for_sale=units_for_sale, bid=bid)
        for _index, bid in ordered
    ]
    domain = {
        "case_id": case_id,
        "units_for_sale": int(units_for_sale),
        "ordered_public_bid_refs": [
            {
                "occurrence_index": int(index),
                "bidder_id": str(bid.bidder_id),
                "commitment": str(bid.commitment),
            }
            for index, bid in ordered
        ],
        "apportionment_method": "largest_remainder_with_bidder_commitment_occurrence_tie",
    }
    settlement = settle_uniform_price_sealed_bids(units_for_sale=units_for_sale, bids=bids)
    return {
        "schema": "zenodex/sealed-bid-marginal-bucket-certificate/v1",
        "case_id": case_id,
        "domain": domain,
        "domain_hash": _stable_hash(domain),
        "clearing_price": int(bucket.clearing_price),
        "remaining_before_bucket": int(bucket.remaining_before_bucket),
        "prefix_filled_quantity": int(bucket.prefix_filled_quantity),
        "prefix_rows": prefix_rows,
        "marginal_rows": rows,
        "settlement_fills": [
            {
                "bidder_id": str(fill.bidder_id),
                "commitment": str(fill.commitment),
                "filled_quantity": int(fill.filled_quantity),
                "paid_price": int(fill.paid_price),
            }
            for fill in settlement.fills
        ],
        "total_filled": int(settlement.total_filled),
        "public_receipts": public_receipts,
        "single_bidder_scope_ok": _single_bidder_scope_ok(rows),
        "split_bid_risk_classified": True,
    }


def verify_certificate(certificate: Mapping[str, Any]) -> bool:
    if certificate.get("schema") != "zenodex/sealed-bid-marginal-bucket-certificate/v1":
        raise ValueError("schema mismatch")
    domain = certificate.get("domain")
    if not isinstance(domain, Mapping):
        raise ValueError("domain must be an object")
    if certificate.get("domain_hash") != _stable_hash(domain):
        raise ValueError("domain hash mismatch")

    rows = certificate.get("marginal_rows")
    if not isinstance(rows, list) or not rows:
        raise ValueError("marginal rows missing")
    remaining = int(certificate.get("remaining_before_bucket"))
    if sum(int(row["fill_quantity"]) for row in rows) != remaining:
        raise ValueError("marginal fill total mismatch")
    for row in rows:
        fill_quantity = int(row["fill_quantity"])
        if fill_quantity < int(row["lower_quota"]) or fill_quantity > int(row["upper_quota"]):
            raise ValueError("quota bound mismatch")
    leftover = remaining - sum(int(row["base"]) for row in rows)
    expected_bonus_keys = {
        tuple(row["tie_key"])
        for row in sorted(rows, key=lambda item: (-int(item["remainder"]), item["tie_key"]))[: max(0, leftover)]
    }
    actual_bonus_keys = {tuple(row["tie_key"]) for row in rows if int(row["bonus"]) == 1}
    if actual_bonus_keys != expected_bonus_keys:
        raise ValueError("largest remainder tie order mismatch")
    if _expected_counter_from_certificate(certificate) != Counter(
        (str(row["bidder_id"]), str(row["commitment"]), int(row["filled_quantity"]), int(row["paid_price"]))
        for row in certificate.get("settlement_fills", [])
    ):
        raise ValueError("settlement parity mismatch")
    for receipt in certificate.get("public_receipts", []):
        ok, err = verify_commit_receipt(receipt)
        if not ok:
            raise ValueError(f"public receipt rejected: {err}")
    if certificate.get("split_bid_risk_classified") is not True:
        raise ValueError("split-bid risk not classified")
    return True


def _bid(bidder: str, commitment: str, quantity: int, price: int) -> RevealedSealedBid:
    return RevealedSealedBid(str(bidder), str(commitment), int(quantity), int(price))


def build_cases() -> dict[str, tuple[int, tuple[RevealedSealedBid, ...]]]:
    return {
        "quota_parity": (
            5,
            (
                _bid("alice", "alice-commitment", 3, 110),
                _bid("bob", "bob-commitment", 4, 110),
            ),
        ),
        "same_remainder_tie_order": (
            2,
            (
                _bid("alice", "a-commitment", 1, 100),
                _bid("bob", "b-commitment", 1, 100),
                _bid("carol", "c-commitment", 1, 100),
            ),
        ),
        "full_prefix_then_marginal": (
            5,
            (
                _bid("dave", "dave-high", 3, 120),
                _bid("alice", "alice-mid", 2, 100),
                _bid("bob", "bob-mid", 3, 100),
                _bid("carol", "carol-mid", 3, 100),
            ),
        ),
        "duplicate_occurrence_index": (
            2,
            (
                _bid("alice", "same-commitment", 1, 110),
                _bid("alice", "same-commitment", 1, 110),
                _bid("alice", "same-commitment", 1, 110),
            ),
        ),
        "split_bid_witness": (
            2,
            (
                _bid("alice", "a-commitment", 1, 100),
                _bid("alice", "b-commitment", 1, 100),
                _bid("bob", "n-commit", 1, 100),
                _bid("carol", "o-commit", 1, 100),
            ),
        ),
    }


def owner_consolidated_fill_totals(*, units_for_sale: int, bids: tuple[RevealedSealedBid, ...]) -> dict[str, int]:
    bucket = find_marginal_bucket(units_for_sale=units_for_sale, bids=bids)
    prefix_totals: dict[str, int] = defaultdict(int)
    for index, bid in _ordered_bids(bids):
        if int(bid.limit_price) > int(bucket.clearing_price):
            prefix_totals[str(bid.bidder_id)] += int(bid.quantity)
    grouped: dict[str, int] = defaultdict(int)
    first_commitment: dict[str, str] = {}
    for _index, bid in bucket.bucket:
        grouped[str(bid.bidder_id)] += int(bid.quantity)
        first_commitment.setdefault(str(bid.bidder_id), str(bid.commitment))
    synthetic = tuple(
        _bid(bidder, first_commitment[bidder], quantity, bucket.clearing_price)
        for bidder, quantity in sorted(grouped.items())
    )
    synthetic_bucket = MarginalBucket(
        clearing_price=bucket.clearing_price,
        remaining_before_bucket=bucket.remaining_before_bucket,
        prefix_filled_quantity=bucket.prefix_filled_quantity,
        bucket=tuple(enumerate(synthetic)),
    )
    rows = _bucket_rows(synthetic_bucket)
    totals = dict(prefix_totals)
    for row in rows:
        totals[str(row["bidder_id"])] = totals.get(str(row["bidder_id"]), 0) + int(row["fill_quantity"])
    return totals


def split_bid_witness() -> dict[str, Any]:
    base_bids = (
        _bid("alice", "m-commit", 2, 100),
        _bid("bob", "n-commit", 1, 100),
        _bid("carol", "o-commit", 1, 100),
    )
    split_bids = build_cases()["split_bid_witness"][1]
    base = settle_uniform_price_sealed_bids(units_for_sale=2, bids=base_bids)
    split = settle_uniform_price_sealed_bids(units_for_sale=2, bids=split_bids)
    base_alice = sum(fill.filled_quantity for fill in base.fills if fill.bidder_id == "alice")
    split_alice = sum(fill.filled_quantity for fill in split.fills if fill.bidder_id == "alice")
    consolidated = owner_consolidated_fill_totals(units_for_sale=2, bids=split_bids)
    return {
        "units_for_sale": 2,
        "base_alice_fill": int(base_alice),
        "split_alice_fill": int(split_alice),
        "owner_consolidated_alice_fill": int(consolidated.get("alice", 0)),
        "base_fills": [
            {"bidder_id": fill.bidder_id, "commitment": fill.commitment, "filled_quantity": fill.filled_quantity}
            for fill in base.fills
        ],
        "split_fills": [
            {"bidder_id": fill.bidder_id, "commitment": fill.commitment, "filled_quantity": fill.filled_quantity}
            for fill in split.fills
        ],
        "risk": "largest-remainder marginal buckets are not split-bid invariant when multiple commitments per bidder are admitted independently",
        "mitigation": "Require one marginal-bucket reveal per bidder or apportion by bidder_id before distributing owner fills across commitments.",
    }


def mutation_checks(certificates: list[dict[str, Any]]) -> list[dict[str, Any]]:
    base = certificates[0]
    mutations: list[tuple[str, dict[str, Any], str]] = []
    bad_hash = json.loads(json.dumps(base))
    bad_hash["domain_hash"] = "0" * 64
    mutations.append(("bad_domain_hash", bad_hash, "domain hash mismatch"))
    bad_quota = json.loads(json.dumps(base))
    bad_quota["marginal_rows"][0]["fill_quantity"] = int(bad_quota["marginal_rows"][0]["upper_quota"]) + 1
    mutations.append(("bad_quota_bound", bad_quota, "marginal fill total mismatch"))
    leaked_receipt = json.loads(json.dumps(base))
    leaked_receipt["public_receipts"][0]["body"]["quantity"] = 3
    mutations.append(("private_quantity_leak", leaked_receipt, "public receipt rejected: private_field_leaked_quantity"))
    no_risk = json.loads(json.dumps(base))
    no_risk["split_bid_risk_classified"] = False
    mutations.append(("unclassified_split_risk", no_risk, "split-bid risk not classified"))

    out: list[dict[str, Any]] = []
    for mutation_id, mutated, expected_error in mutations:
        try:
            verify_certificate(mutated)
        except ValueError as exc:
            accepted = False
            error = str(exc)
        else:
            accepted = True
            error = None
        out.append(
            {
                "mutation_id": mutation_id,
                "accepted": accepted,
                "error": error,
                "expected_error": expected_error,
                "ok": (not accepted) and error == expected_error,
            }
        )
    return out


def _tau_version(tau_bin: str | None) -> str | None:
    if not tau_bin:
        return None
    proc = subprocess.run([tau_bin, "--version"], cwd=REPO_ROOT, capture_output=True, text=True, timeout=10, check=False)
    return (proc.stdout + proc.stderr).strip()


def tau_trace_check() -> dict[str, Any]:
    tau_bin = find_tau_bin(REPO_ROOT, profile="latest")
    if not tau_bin:
        return {"ok": False, "error": "latest Tau binary not found", "spec_path": str(TAU_SPEC.relative_to(REPO_ROOT)), "cases": []}
    outputs = run_tau_spec_steps(tau_bin=tau_bin, spec_path=TAU_SPEC, steps=[case.step for case in TAU_CASES], timeout_s=10.0)
    cases: list[dict[str, Any]] = []
    ok = True
    for idx, case in enumerate(TAU_CASES):
        got = outputs.get(idx, {})
        mismatches = {
            key: {"expected": value, "got": got.get(key)}
            for key, value in case.expected.items()
            if got.get(key) != value
        }
        if mismatches:
            ok = False
        cases.append({"case_id": case.case_id, "ok": not mismatches, "expected": case.expected, "got": got, "mismatches": mismatches})
    return {
        "ok": ok,
        "spec_path": str(TAU_SPEC.relative_to(REPO_ROOT)),
        "tau_bin": tau_bin,
        "tau_version": _tau_version(tau_bin),
        "cases": cases,
    }


def build_report() -> dict[str, Any]:
    certificates: list[dict[str, Any]] = []
    rows: list[dict[str, Any]] = []
    for case_id, (units_for_sale, bids) in build_cases().items():
        certificate = build_certificate(case_id=case_id, units_for_sale=units_for_sale, bids=bids)
        verified = verify_certificate(certificate)
        certificates.append(certificate)
        rows.append(
            {
                "case_id": case_id,
                "verified": verified,
                "clearing_price": certificate["clearing_price"],
                "remaining_before_bucket": certificate["remaining_before_bucket"],
                "single_bidder_scope_ok": certificate["single_bidder_scope_ok"],
                "marginal_fills": [
                    [row["bidder_id"], row["commitment"], row["fill_quantity"]]
                    for row in certificate["marginal_rows"]
                    if int(row["fill_quantity"]) > 0
                ],
            }
        )
    mutations = mutation_checks(certificates)
    tau = tau_trace_check()
    witness = split_bid_witness()
    ok = bool(
        tau["ok"]
        and all(row["verified"] for row in rows)
        and all(check["ok"] for check in mutations)
        and witness["split_alice_fill"] > witness["base_alice_fill"]
        and witness["owner_consolidated_alice_fill"] == witness["base_alice_fill"]
    )
    return {
        "schema": "zenodex.sealed_bid_apportionment_breakthrough_report.v1",
        "date": "2026-06-28",
        "ok": ok,
        "breakthrough": {
            "name": "Sealed-bid marginal bucket apportionment certificate and split-bid refuter",
            "summary": "The marginal bucket can be certified as largest-remainder apportionment with quota bounds and deterministic tie order, and the same certificate exposes a split-bid vulnerability when multiple commitments per bidder are admitted independently.",
            "authority_boundary": "This is a research certificate and mechanism-design refuter. Runtime sealed-bid settlement is unchanged.",
        },
        "tau": tau,
        "case_rows": rows,
        "mutation_checks": mutations,
        "split_bid_witness": witness,
        "certificate_hashes": [_stable_hash(certificate) for certificate in certificates],
        "replay_command": "python3 tools/zenodex_sealed_bid_apportionment_breakthrough_20260628.py",
    }


def _write_markdown(report: Mapping[str, Any]) -> None:
    lines: list[str] = []
    lines.append("# ZenoDEX Sealed-Bid Apportionment Breakthrough - 2026-06-28")
    lines.append("")
    lines.append("## Executive Result")
    lines.append("")
    lines.append(str(report["breakthrough"]["summary"]))
    lines.append("")
    lines.append(str(report["breakthrough"]["authority_boundary"]))
    lines.append("")
    lines.append(f"- Spec: `{report['tau']['spec_path']}`")
    lines.append(f"- Tau replay ok: `{report['tau']['ok']}`")
    lines.append(f"- Tau version: `{report['tau'].get('tau_version')}`")
    lines.append(f"- Certificate cases: `{len(report['case_rows'])}`")
    lines.append(f"- Mutation rejections: `{sum(1 for check in report['mutation_checks'] if check['ok'])}`")
    lines.append("")
    lines.append("## Certificate Cases")
    lines.append("")
    lines.append("| case | verified | clearing price | marginal supply | single-bidder scope | marginal fills |")
    lines.append("| --- | --- | ---: | ---: | --- | --- |")
    for row in report["case_rows"]:
        lines.append(
            f"| `{row['case_id']}` | `{row['verified']}` | `{row['clearing_price']}` | `{row['remaining_before_bucket']}` | `{row['single_bidder_scope_ok']}` | `{row['marginal_fills']}` |"
        )
    lines.append("")
    lines.append("## Split-Bid Witness")
    lines.append("")
    witness = report["split_bid_witness"]
    lines.append(f"- Base Alice fill: `{witness['base_alice_fill']}`")
    lines.append(f"- Split Alice fill: `{witness['split_alice_fill']}`")
    lines.append(f"- Owner-consolidated Alice fill: `{witness['owner_consolidated_alice_fill']}`")
    lines.append("")
    lines.append(str(witness["risk"]))
    lines.append("")
    lines.append(str(witness["mitigation"]))
    lines.append("")
    lines.append("## Mutation Checks")
    lines.append("")
    lines.append("| mutation | rejected | error |")
    lines.append("| --- | --- | --- |")
    for check in report["mutation_checks"]:
        lines.append(f"| `{check['mutation_id']}` | `{not check['accepted']}` | `{check['error']}` |")
    lines.append("")
    lines.append("## Non-Claims")
    lines.append("")
    lines.append("- This artifact does not change sealed-bid runtime settlement semantics.")
    lines.append("- The owner-consolidated mitigation is a design candidate, not an activated rule.")
    lines.append("- Tau does not inspect private bids, compute apportionment, or authorize settlement.")
    lines.append("- Privacy still depends on commitment nonce quality outside this certificate.")
    lines.append("")
    lines.append("## Replay")
    lines.append("")
    lines.append("```bash")
    lines.append(str(report["replay_command"]))
    lines.append("```")
    lines.append("")
    REPORT_MD.parent.mkdir(parents=True, exist_ok=True)
    REPORT_MD.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    report = build_report()
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    REPORT_JSON.write_text(_stable_json(report) + "\n", encoding="utf-8")
    _write_markdown(report)
    print(
        json.dumps(
            {
                "ok": report["ok"],
                "report": str(REPORT_MD),
                "json": str(REPORT_JSON),
                "tau_ok": report["tau"]["ok"],
                "certificate_cases": len(report["case_rows"]),
                "split_lift": report["split_bid_witness"]["split_alice_fill"] - report["split_bid_witness"]["base_alice_fill"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
