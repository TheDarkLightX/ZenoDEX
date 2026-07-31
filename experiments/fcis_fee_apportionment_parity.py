#!/usr/bin/env python3
"""Run the unmounted Python/Rust/Julia FCIS fee-kernel parity campaigns."""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Final

REPO: Final = Path(__file__).resolve().parents[1]
if str(REPO) not in sys.path:
    sys.path.insert(0, str(REPO))

from src.core.fcis_fee_apportionment_allocator import (  # noqa: E402
    apply_fee_apportionment_v2,
)
from src.core.fcis_fee_apportionment_codec import (  # noqa: E402
    encode_fcis_fee_apportionment_v2,
)
from src.core.fcis_fee_apportionment_values import (  # noqa: E402
    ASSET_FEE_ALLOCATION_BATCH_SCHEMA_ID_V2,
    BPS_DENOMINATOR_V2,
    COMMITTED_FEE_APPORTIONMENT_STATE_SCHEMA_ID_V2,
    FEE_APPORTIONMENT_TRANSITION_RESULT_SCHEMA_ID_V2,
    MAX_FEE_AMOUNT_V2,
    SRGD_ALGORITHM_VERSION_V1,
    CommittedFeeApportionmentStateV2,
    FeeAmountCandidateV2,
    FeeApportionmentKeyV2,
    FeeApportionmentTransitionOkV2,
    FeeApportionmentTransitionRejectV2,
    FeeDeficitEntryV2,
    FeeDistributionPolicyV2,
)

BASE_RECEIPT_HEAD: Final = "aca4c441aef978ee74d145202c55c556700cbfa3"
SOURCE_HEAD: Final = "476ec022e755ff049c39bf9f08c6606ac87532ca"
RUST_MANIFEST: Final = (
    REPO / "formal" / "fcis_m6_b09_rust_parity" / "Cargo.toml"
)
JULIA_ORACLE: Final = REPO / "experiments" / "julia" / "fcis_fee_apportionment_oracle.jl"
FIXTURE: Final = REPO / "tests" / "fixtures" / "fcis_fee_apportionment_v2_golden.json"


@dataclass(frozen=True, slots=True)
class ProductionRecord:
    record_id: str
    candidates: tuple[tuple[str, str, int], ...]
    weights: tuple[int, int, int]
    destinations: tuple[str, str, str]
    deficit_buyback: int = 0
    deficit_treasury: int = 0


def _sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _state_for(record: ProductionRecord) -> CommittedFeeApportionmentStateV2:
    if record.deficit_buyback == 0 and record.deficit_treasury == 0:
        return CommittedFeeApportionmentStateV2(SRGD_ALGORITHM_VERSION_V1, ())
    domain, asset, _ = record.candidates[0]
    key = FeeApportionmentKeyV2(domain, asset)
    entry = FeeDeficitEntryV2(
        key,
        record.deficit_buyback,
        record.deficit_treasury,
    )
    return CommittedFeeApportionmentStateV2(SRGD_ALGORITHM_VERSION_V1, (entry,))


def _python_result(record: ProductionRecord) -> object:
    contributions = tuple(
        FeeAmountCandidateV2(
            FeeApportionmentKeyV2(domain, asset),
            amount,
        )
        for domain, asset, amount in record.candidates
    )
    policy = FeeDistributionPolicyV2(
        *record.weights,
        *record.destinations,
    )
    return apply_fee_apportionment_v2(
        contributions=contributions,
        policy=policy,
        state=_state_for(record),
    )


def _render_production_line(record: ProductionRecord) -> str:
    result = _python_result(record)
    prefix = record.record_id
    if type(result) is FeeApportionmentTransitionRejectV2:
        return (
            f"{prefix}|R|{result.code.value}|"
            f"{'/'.join(result.path)}"
        )
    if type(result) is not FeeApportionmentTransitionOkV2:
        raise AssertionError("unexpected Python transition result")
    state_bytes = encode_fcis_fee_apportionment_v2(
        COMMITTED_FEE_APPORTIONMENT_STATE_SCHEMA_ID_V2,
        result.state,
    )
    allocation_bytes = encode_fcis_fee_apportionment_v2(
        ASSET_FEE_ALLOCATION_BATCH_SCHEMA_ID_V2,
        result.allocations,
    )
    result_bytes = encode_fcis_fee_apportionment_v2(
        FEE_APPORTIONMENT_TRANSITION_RESULT_SCHEMA_ID_V2,
        result,
    )

    def allocation_field(name: str) -> str:
        values = []
        for allocation in result.allocations:
            if name == "fractions":
                item = allocation.fractions
            elif name == "bonuses":
                item = allocation.bonuses
            elif name == "amounts":
                item = allocation.amounts
            elif name == "deficits_post":
                item = allocation.deficits_post
            else:
                raise AssertionError(f"unknown allocation field {name}")
            values.append(",".join(str(value) for value in item))
        return ";".join(values)

    return "|".join(
        (
            prefix,
            "A",
            allocation_field("fractions"),
            allocation_field("bonuses"),
            allocation_field("amounts"),
            allocation_field("deficits_post"),
            state_bytes.hex(),
            allocation_bytes.hex(),
            result_bytes.hex(),
            f"0x{_sha256(result_bytes)}",
        )
    )


def _fixture_records() -> list[ProductionRecord]:
    document = json.loads(FIXTURE.read_text(encoding="utf-8"))
    records: list[ProductionRecord] = []
    for case in document["cases"]:
        raw_input = case["input"]
        candidates = tuple(
            (
                item["key"]["fee_distribution_domain_id"],
                item["key"]["asset"],
                item["amount"],
            )
            for item in raw_input["contributions"]
        )
        policy = raw_input["policy"]
        state_entries = raw_input["state"]["entries"]
        if state_entries:
            deficit_buyback = state_entries[0]["deficit_buyback"]
            deficit_treasury = state_entries[0]["deficit_treasury"]
        else:
            deficit_buyback = 0
            deficit_treasury = 0
        records.append(
            ProductionRecord(
                record_id=case["id"],
                candidates=candidates,
                weights=(
                    policy["buyback_bps"],
                    policy["treasury_bps"],
                    policy["rewards_bps"],
                ),
                destinations=(
                    policy["buyback_destination"],
                    policy["treasury_destination"],
                    policy["rewards_destination"],
                ),
                deficit_buyback=deficit_buyback,
                deficit_treasury=deficit_treasury,
            )
        )
    return records


def _edge_records() -> list[ProductionRecord]:
    amounts = (
        ("edge_zero", 0),
        ("edge_one", 1),
        ("edge_denominator_minus_one", BPS_DENOMINATOR_V2 - 1),
        ("edge_denominator", BPS_DENOMINATOR_V2),
        ("edge_denominator_plus_one", BPS_DENOMINATOR_V2 + 1),
        ("edge_2pow128", 2**128),
        ("edge_2pow255", 2**255),
        ("edge_u256_minus_one", MAX_FEE_AMOUNT_V2 - 1),
        ("edge_u256_max", MAX_FEE_AMOUNT_V2),
    )
    records = []
    for index, (record_id, amount) in enumerate(amounts):
        first = 1_000 + (index * 1_777) % 4_000
        second = 2_000 + (index * 1_231) % 3_000
        third = BPS_DENOMINATOR_V2 - first - second
        records.append(
            ProductionRecord(
                record_id=record_id,
                candidates=(("edge-domain", "edge-asset", amount),),
                weights=(first, second, third),
                destinations=(
                    f"buyback-edge-{index}",
                    f"treasury-edge-{index}",
                    f"rewards-edge-{index}",
                ),
            )
        )
    records.append(
        ProductionRecord(
            record_id="edge_aggregate_overflow",
            candidates=(
                ("edge-domain", "edge-asset", MAX_FEE_AMOUNT_V2),
                ("edge-domain", "edge-asset", 1),
            ),
            weights=(3_333, 3_333, 3_334),
            destinations=("buyback-edge-overflow", "treasury-edge-overflow", "rewards-edge-overflow"),
        )
    )
    return records


def _adaptive_records() -> list[ProductionRecord]:
    records: list[ProductionRecord] = []
    seed = 0x123456789ABCDEF
    deficit_buyback = 0
    deficit_treasury = 0
    for index in range(1_000):
        seed = (
            seed * 6_364_136_223_846_793_005
            + 1_442_695_040_888_963_407
        ) & MAX_FEE_AMOUNT_V2
        first = 1_500 + (index * 37) % 3_000
        second = 2_500 + (index * 53) % 2_500
        third = BPS_DENOMINATOR_V2 - first - second
        record = ProductionRecord(
            record_id=f"adaptive-{index:04d}",
            candidates=(("adaptive-domain", "adaptive-asset", seed),),
            weights=(first, second, third),
            destinations=(
                f"buyback-{index % 5}",
                f"treasury-{index % 7}",
                f"rewards-{index % 11}",
            ),
            deficit_buyback=deficit_buyback,
            deficit_treasury=deficit_treasury,
        )
        result = _python_result(record)
        if type(result) is not FeeApportionmentTransitionOkV2:
            raise AssertionError(f"adaptive record rejected: {record.record_id}")
        allocation = result.allocations[0]
        deficit_buyback, deficit_treasury, _ = allocation.deficits_post
        records.append(record)
    return records


def _production_line(record: ProductionRecord) -> str:
    domains = ";".join(candidate[0] for candidate in record.candidates)
    assets = ";".join(candidate[1] for candidate in record.candidates)
    amounts = ",".join(str(candidate[2]) for candidate in record.candidates)
    weights = ",".join(str(value) for value in record.weights)
    destinations = ",".join(record.destinations)
    return "\t".join(
        (
            record.record_id,
            domains,
            assets,
            amounts,
            weights,
            destinations,
            str(record.deficit_buyback),
            str(record.deficit_treasury),
        )
    )


def _small_reference(
    denominator: int,
    amount: int,
    weights: tuple[int, int, int],
    deficits_pre: tuple[int, int, int],
) -> tuple[tuple[int, int, int], tuple[int, int, int], tuple[int, int, int], tuple[int, int, int]]:
    quotas = []
    for weight in weights:
        quotient, residual = divmod(amount, denominator)
        product = residual * weight
        quotas.append(
            (
                quotient * weight + product // denominator,
                product % denominator,
            )
        )
    fractions = tuple(quota[1] for quota in quotas)
    seat_count = sum(fractions) // denominator
    eligible = [index for index, fraction in enumerate(fractions) if fraction > 0]
    order = sorted(
        eligible,
        key=lambda index: (-(deficits_pre[index] + fractions[index]), index),
    )
    bonuses_list = [0, 0, 0]
    for index in order[:seat_count]:
        if fractions[index] > 0:
            bonuses_list[index] = 1
    bonuses = tuple(bonuses_list)
    amounts = tuple(quotas[index][0] + bonuses[index] for index in range(3))
    deficits_post = tuple(
        deficits_pre[index] + fractions[index] - denominator * bonuses[index]
        for index in range(3)
    )
    return fractions, bonuses, amounts, deficits_post


def _small_line(
    record_id: str,
    denominator: int,
    amount: int,
    weights: tuple[int, int, int],
    deficits_pre: tuple[int, int, int],
) -> tuple[str, str]:
    fractions, bonuses, amounts, deficits_post = _small_reference(
        denominator,
        amount,
        weights,
        deficits_pre,
    )
    input_line = "\t".join(
        (
            record_id,
            str(denominator),
            str(amount),
            ",".join(str(value) for value in weights),
            "a,b,c",
            "unused",
            str(deficits_pre[0]),
            str(deficits_pre[1]),
        )
    )
    output_line = "|".join(
        (
            record_id,
            "A",
            ",".join(str(value) for value in fractions),
            ",".join(str(value) for value in bonuses),
            ",".join(str(value) for value in amounts),
            ",".join(str(value) for value in deficits_post),
        )
    )
    return input_line, output_line


def _small_domain() -> tuple[list[str], list[str], dict[str, int]]:
    input_lines: list[str] = []
    output_lines: list[str] = []
    counts: dict[str, int] = {}
    for denominator in range(1, 13):
        count = 0
        for weight_buyback in range(denominator + 1):
            for weight_treasury in range(denominator - weight_buyback + 1):
                weight_rewards = denominator - weight_buyback - weight_treasury
                weights = (weight_buyback, weight_treasury, weight_rewards)
                for amount in range(denominator + 1):
                    for deficit_buyback in range(-denominator + 1, denominator):
                        for deficit_treasury in range(-denominator + 1, denominator):
                            deficit_rewards = -deficit_buyback - deficit_treasury
                            if not -denominator < deficit_rewards < denominator:
                                continue
                            record_id = (
                                f"d{denominator}-w{weight_buyback}-{weight_treasury}-"
                                f"{weight_rewards}-a{amount}-q{count}"
                            )
                            input_line, output_line = _small_line(
                                record_id,
                                denominator,
                                amount,
                                weights,
                                (deficit_buyback, deficit_treasury, deficit_rewards),
                            )
                            input_lines.append(input_line)
                            output_lines.append(output_line)
                            count += 1
        counts[str(denominator)] = count
    return input_lines, output_lines, counts


def _run(command: list[str], *, cwd: Path) -> tuple[int, bytes, bytes]:
    completed = subprocess.run(
        command,
        cwd=cwd,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    return completed.returncode, completed.stdout, completed.stderr


def _write(path: Path, data: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(data)


def _campaign(artifact_dir: Path) -> dict[str, object]:
    baseline = _fixture_records()
    edges = _edge_records()
    adaptive = _adaptive_records()
    production = baseline + edges + adaptive
    production_input = (
        "\n".join(_production_line(record) for record in production) + "\n"
    ).encode()
    production_python = (
        "\n".join(_render_production_line(record) for record in production) + "\n"
    ).encode()
    _write(artifact_dir / "TASK_B09_PRODUCTION_INPUT.tsv", production_input)
    _write(artifact_dir / "TASK_B09_PYTHON_OUTPUT.txt", production_python)

    rust_output_path = artifact_dir / "TASK_B09_RUST_OUTPUT.txt"
    rust_command = [
        "cargo",
        "run",
        "--quiet",
        "--manifest-path",
        str(RUST_MANIFEST),
        "--",
        str(artifact_dir / "TASK_B09_PRODUCTION_INPUT.tsv"),
        str(rust_output_path),
    ]
    rust_code, rust_stdout, rust_stderr = _run(rust_command, cwd=REPO)
    _write(artifact_dir / "TASK_B09_RUST_STDOUT.txt", rust_stdout)
    _write(artifact_dir / "TASK_B09_RUST_STDERR.txt", rust_stderr)
    if rust_code != 0:
        raise RuntimeError(f"Rust parity harness failed with exit {rust_code}")
    rust_output = rust_output_path.read_bytes()
    if rust_output != production_python:
        raise AssertionError("Python and Rust production outputs differ")

    julia_output_path = artifact_dir / "TASK_B09_JULIA_OUTPUT.txt"
    julia_command = [
        "/home/trevormoc/.local/bin/julia",
        "--startup-file=no",
        str(JULIA_ORACLE),
        str(artifact_dir / "TASK_B09_PRODUCTION_INPUT.tsv"),
        str(julia_output_path),
    ]
    julia_code, julia_stdout, julia_stderr = _run(julia_command, cwd=REPO)
    _write(artifact_dir / "TASK_B09_JULIA_STDOUT.txt", julia_stdout)
    _write(artifact_dir / "TASK_B09_JULIA_STDERR.txt", julia_stderr)
    if julia_code != 0:
        raise RuntimeError(f"Julia parity harness failed with exit {julia_code}")
    julia_output = julia_output_path.read_bytes()
    if julia_output != production_python:
        raise AssertionError("Python and Julia production outputs differ")

    small_input_lines, small_python_lines, small_counts = _small_domain()
    small_input = ("\n".join(small_input_lines) + "\n").encode()
    small_python = ("\n".join(small_python_lines) + "\n").encode()
    small_input_path = artifact_dir / "TASK_B09_SMALL_DOMAIN_INPUT.tsv"
    small_python_path = artifact_dir / "TASK_B09_SMALL_DOMAIN_PYTHON_OUTPUT.txt"
    _write(small_input_path, small_input)
    _write(small_python_path, small_python)
    small_julia_path = artifact_dir / "TASK_B09_SMALL_DOMAIN_JULIA_OUTPUT.txt"
    small_command = [
        "/home/trevormoc/.local/bin/julia",
        "--startup-file=no",
        str(JULIA_ORACLE),
        "--small-domain",
        str(small_input_path),
        str(small_julia_path),
    ]
    small_code, small_stdout, small_stderr = _run(small_command, cwd=REPO)
    _write(artifact_dir / "TASK_B09_SMALL_DOMAIN_JULIA_STDOUT.txt", small_stdout)
    _write(artifact_dir / "TASK_B09_SMALL_DOMAIN_JULIA_STDERR.txt", small_stderr)
    if small_code != 0:
        raise RuntimeError(f"Julia small-domain oracle failed with exit {small_code}")
    small_julia = small_julia_path.read_bytes()
    if small_julia != small_python:
        raise AssertionError("Python and Julia small-domain outputs differ")

    result: dict[str, object] = {
        "base_b08_receipt_commit": BASE_RECEIPT_HEAD,
        "source_head": SOURCE_HEAD,
        "production": {
            "baseline_shared_vectors": len(baseline),
            "production_edge_vectors": len(edges),
            "adaptive_steps": len(adaptive),
            "total_vectors": len(production),
            "python_sha256": _sha256(production_python),
            "rust_sha256": _sha256(rust_output),
            "julia_sha256": _sha256(julia_output),
            "exact_byte_match": True,
            "rust_command": rust_command,
            "julia_command": julia_command,
        },
        "small_domain": {
            "denominator_min": 1,
            "denominator_max": 12,
            "vectors": len(small_input_lines),
            "vectors_by_denominator": small_counts,
            "python_sha256": _sha256(small_python),
            "julia_sha256": _sha256(small_julia),
            "exact_byte_match": True,
            "julia_command": small_command,
        },
        "nonclaims": [
            "The campaigns exercise an unmounted research kernel only.",
            "Small-domain Rust production-D parity is outside scope because the Rust profile is fixed at D=10000.",
            "Agreement does not prove requirements completeness, runtime mounting, datastore refinement, or economic correctness.",
        ],
    }
    _write(
        artifact_dir / "TASK_B09_PARITY_RESULT.json",
        (json.dumps(result, indent=2, sort_keys=True) + "\n").encode(),
    )
    return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--artifact-dir",
        type=Path,
        default=REPO / "docs" / "research" / "m6_tasks" / "TASK_B09_ARTIFACTS",
    )
    args = parser.parse_args()
    result = _campaign(args.artifact_dir)
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
