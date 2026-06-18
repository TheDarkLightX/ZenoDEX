from __future__ import annotations

import json
import subprocess
from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps
from tools.gpu_jobs.improvement_bounty_round_route_v1 import _build_payout_plan, _compute_payout_amount
from tools.proof_verifiers.route_improvement_v1 import verify_route_improvement_witness


def _run_tau(spec_path: str, *, steps: list[dict[str, int]]) -> list[int]:
    tau_bin = find_tau_bin()
    if not tau_bin:
        pytest.skip("tau not found")
    outputs = run_tau_spec_steps(
        tau_bin=tau_bin,
        spec_path=Path(spec_path),
        steps=steps,
        timeout_s=10.0,
    )
    return [int(outputs.get(i, {}).get("o1", -1)) for i in range(len(steps))]


def test_improvement_bounty_round_selects_best_and_emits_tau_argmax_cert(tmp_path: Path) -> None:
    # Reuse the route-improvement witness generator to create one improving witness,
    # and one valid non-improving witness (proposal==baseline).
    job_path = tmp_path / "job.json"
    w1_path = tmp_path / "w1.json"
    w2_path = tmp_path / "w2.json"
    round_path = tmp_path / "round.json"
    cert_path = tmp_path / "argmax_cert.json"

    A = "0x" + f"{1:064x}"
    B = "0x" + f"{2:064x}"
    C = "0x" + f"{3:064x}"

    # Pools are encoded as plain dicts; the generator parses them into PoolState.
    # A->C direct is made intentionally bad so 2-hop is improving.
    pools = [
        {
            "pool_id": "0x" + "11" * 32,
            "asset0": min(A, B),
            "asset1": max(A, B),
            "reserve0": 1_000_000,
            "reserve1": 1_000_000,
            "fee_bps": 30,
            "curve_tag": "CPMM",
            "curve_params": "",
            "lp_supply": 0,
            "status": "ACTIVE",
            "created_at": 0,
        },
        {
            "pool_id": "0x" + "22" * 32,
            "asset0": min(B, C),
            "asset1": max(B, C),
            "reserve0": 1_000_000,
            "reserve1": 1_000_000,
            "fee_bps": 30,
            "curve_tag": "CPMM",
            "curve_params": "",
            "lp_supply": 0,
            "status": "ACTIVE",
            "created_at": 0,
        },
        {
            "pool_id": "0x" + "33" * 32,
            "asset0": min(A, C),
            "asset1": max(A, C),
            "reserve0": 1_000_000,
            "reserve1": 100_000,
            "fee_bps": 30,
            "curve_tag": "CPMM",
            "curve_params": "",
            "lp_supply": 0,
            "status": "ACTIVE",
            "created_at": 0,
        },
    ]

    job = {"asset_in": A, "asset_out": C, "amount_in": 10_000, "pools": pools}
    job_path.write_text(json.dumps(job, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    subprocess.check_call(
        [
            "python3",
            "tools/gpu_jobs/route_2hop_search_cpmm.py",
            "--input",
            str(job_path),
            "--output",
            str(w1_path),
            "--topk",
            "64",
        ]
    )
    w1 = json.loads(w1_path.read_text(encoding="utf-8"))
    assert w1["improves"] is True
    w1_string_flag = dict(w1)
    w1_string_flag["improves"] = "yes"
    ok, err = verify_route_improvement_witness(w1_string_flag)
    assert not ok
    assert err == "improves must be a bool"

    # Make a second, valid submission that does not improve: proposal==baseline, improves=false.
    w2 = dict(w1)
    w2["improves"] = False
    w2["proposal"] = dict(w1["baseline"])
    w2_path.write_text(json.dumps(w2, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    subprocess.check_call(
        [
            "python3",
            "tools/gpu_jobs/improvement_bounty_round_route_v1.py",
            "--submission",
            f"alice={w1_path}",
            "--submission",
            f"bob={w2_path}",
            "--output",
            str(round_path),
            "--emit-argmax-steps",
            str(cert_path),
            "--require-positive-improvement",
        ]
    )

    rnd = json.loads(round_path.read_text(encoding="utf-8"))
    assert rnd["ok"] is True
    assert rnd["winner"]["miner_id"] == "alice"
    assert int(rnd["winner"]["improvement_u64"]) > 0

    cert = json.loads(cert_path.read_text(encoding="utf-8"))
    steps = cert["steps"]
    assert steps and isinstance(steps, list)

    # If Tau is present, verify the argmax stream certificate steps.
    outs = _run_tau("src/tau_specs/recommended/argmax_stream_certificate_v1.tau", steps=steps)
    assert outs and all(v == 1 for v in outs)


def test_improvement_bounty_round_bva_job_digest_mismatch_is_rejected(tmp_path: Path) -> None:
    # Boundary: same submission format, but *different job digest* must be rejected
    # (exactly one constraint violated: job equality).
    job1_path = tmp_path / "job1.json"
    job2_path = tmp_path / "job2.json"
    w1_path = tmp_path / "w1.json"
    w2_path = tmp_path / "w2.json"
    round_path = tmp_path / "round.json"

    A = "0x" + f"{101:064x}"
    B = "0x" + f"{102:064x}"
    C = "0x" + f"{103:064x}"

    pools = [
        {
            "pool_id": "0x" + "aa" * 32,
            "asset0": min(A, B),
            "asset1": max(A, B),
            "reserve0": 1_000_000,
            "reserve1": 1_000_000,
            "fee_bps": 30,
            "curve_tag": "CPMM",
            "curve_params": "",
            "lp_supply": 0,
            "status": "ACTIVE",
            "created_at": 0,
        },
        {
            "pool_id": "0x" + "bb" * 32,
            "asset0": min(B, C),
            "asset1": max(B, C),
            "reserve0": 1_000_000,
            "reserve1": 1_000_000,
            "fee_bps": 30,
            "curve_tag": "CPMM",
            "curve_params": "",
            "lp_supply": 0,
            "status": "ACTIVE",
            "created_at": 0,
        },
        {
            "pool_id": "0x" + "cc" * 32,
            "asset0": min(A, C),
            "asset1": max(A, C),
            "reserve0": 1_000_000,
            "reserve1": 100_000,
            "fee_bps": 30,
            "curve_tag": "CPMM",
            "curve_params": "",
            "lp_supply": 0,
            "status": "ACTIVE",
            "created_at": 0,
        },
    ]

    # job2 differs only by amount_in (just-above boundary relative to job1's amount_in).
    job1 = {"asset_in": A, "asset_out": C, "amount_in": 10_000, "pools": pools}
    job2 = {"asset_in": A, "asset_out": C, "amount_in": 10_001, "pools": pools}
    job1_path.write_text(json.dumps(job1, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    job2_path.write_text(json.dumps(job2, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    subprocess.check_call(
        [
            "python3",
            "tools/gpu_jobs/route_2hop_search_cpmm.py",
            "--input",
            str(job1_path),
            "--output",
            str(w1_path),
            "--topk",
            "64",
        ]
    )
    subprocess.check_call(
        [
            "python3",
            "tools/gpu_jobs/route_2hop_search_cpmm.py",
            "--input",
            str(job2_path),
            "--output",
            str(w2_path),
            "--topk",
            "64",
        ]
    )

    subprocess.check_call(
        [
            "python3",
            "tools/gpu_jobs/improvement_bounty_round_route_v1.py",
            "--submission",
            f"alice={w1_path}",
            "--submission",
            f"bob={w2_path}",
            "--output",
            str(round_path),
        ]
    )

    rnd = json.loads(round_path.read_text(encoding="utf-8"))
    assert rnd["ok"] is True
    assert rnd["winner"]["miner_id"] == "alice"
    # Bob should be marked invalid because it is for a different job digest.
    bob = next(c for c in rnd["candidates"] if c["miner_id"] == "bob")
    assert bob["ok"] is False
    assert "job_digest mismatch" in bob["error"]


def test_improvement_bounty_round_bva_no_valid_submissions_outputs_ok_false(tmp_path: Path) -> None:
    # Boundary: single submission, but malformed witness (schema wrong) => no valid submissions.
    bad_path = tmp_path / "bad.json"
    out_path = tmp_path / "round.json"
    bad_path.write_text(json.dumps({"schema": "not-a-witness"}, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    subprocess.check_call(
        [
            "python3",
            "tools/gpu_jobs/improvement_bounty_round_route_v1.py",
            "--submission",
            f"mallory={bad_path}",
            "--output",
            str(out_path),
        ]
    )
    rnd = json.loads(out_path.read_text(encoding="utf-8"))
    assert rnd["ok"] is False
    assert "no valid submissions" in rnd["error"]


def test_build_payout_plan_rejects_truthy_string_round_ok() -> None:
    # Payout admission is evidence-gated: only the literal JSON bool true may
    # unlock a plan. Truthy strings are malformed evidence, not success.
    with pytest.raises(ValueError, match="round must be ok"):
        _build_payout_plan(
            round_obj={
                "ok": "true",
                "job_digest": "digest",
                "winner": {
                    "miner_id": "alice",
                    "witness_sha256": "0" * 64,
                    "improvement_u64": 1,
                },
            },
            round_id="route-round-1",
            reward_pool_before=10,
            base_reward=1,
            improvement_reward_bps=0,
            max_reward=10,
        )


def test_improvement_bounty_round_emits_capped_payout_plan(tmp_path: Path) -> None:
    job_path = tmp_path / "job.json"
    witness_path = tmp_path / "w1.json"
    round_path = tmp_path / "round.json"
    payout_path = tmp_path / "payout.json"

    A = "0x" + f"{201:064x}"
    B = "0x" + f"{202:064x}"
    C = "0x" + f"{203:064x}"
    pools = [
        {
            "pool_id": "0x" + "41" * 32,
            "asset0": min(A, B),
            "asset1": max(A, B),
            "reserve0": 1_000_000,
            "reserve1": 1_000_000,
            "fee_bps": 30,
            "curve_tag": "CPMM",
            "curve_params": "",
            "lp_supply": 0,
            "status": "ACTIVE",
            "created_at": 0,
        },
        {
            "pool_id": "0x" + "42" * 32,
            "asset0": min(B, C),
            "asset1": max(B, C),
            "reserve0": 1_000_000,
            "reserve1": 1_000_000,
            "fee_bps": 30,
            "curve_tag": "CPMM",
            "curve_params": "",
            "lp_supply": 0,
            "status": "ACTIVE",
            "created_at": 0,
        },
        {
            "pool_id": "0x" + "43" * 32,
            "asset0": min(A, C),
            "asset1": max(A, C),
            "reserve0": 1_000_000,
            "reserve1": 100_000,
            "fee_bps": 30,
            "curve_tag": "CPMM",
            "curve_params": "",
            "lp_supply": 0,
            "status": "ACTIVE",
            "created_at": 0,
        },
    ]
    job = {"asset_in": A, "asset_out": C, "amount_in": 10_000, "pools": pools}
    job_path.write_text(json.dumps(job, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    subprocess.check_call(
        [
            "python3",
            "tools/gpu_jobs/route_2hop_search_cpmm.py",
            "--input",
            str(job_path),
            "--output",
            str(witness_path),
            "--topk",
            "64",
        ]
    )

    subprocess.check_call(
        [
            "python3",
            "tools/gpu_jobs/improvement_bounty_round_route_v1.py",
            "--submission",
            f"alice={witness_path}",
            "--output",
            str(round_path),
            "--emit-payout-plan",
            str(payout_path),
            "--round-id",
            "route-round-1",
            "--reward-pool-before",
            "7",
            "--base-reward",
            "5",
            "--improvement-reward-bps",
            "10000",
            "--max-reward",
            "9",
            "--require-positive-improvement",
        ]
    )

    payout = json.loads(payout_path.read_text(encoding="utf-8"))
    assert payout["body"]["schema"] == "zenodex/permissionless_solver_payout_plan/v1"
    assert payout["body"]["round_id"] == "route-round-1"
    assert payout["body"]["winner"]["miner_id"] == "alice"
    assert payout["body"]["winner"]["payout_amount"] == 7
    assert payout["body"]["budget"]["reward_pool_after"] == 0
    assert payout["plan_hash"]


@pytest.mark.parametrize(
    ("improvement_u64", "reward_pool_before", "base_reward", "improvement_reward_bps", "max_reward", "expected"),
    [
        (0, 100, 5, 2500, 10, 0),
        (1, 100, 5, 0, 10, 5),
        (20, 100, 5, 1000, 6, 6),
        (20, 3, 5, 1000, 9, 3),
    ],
)
def test_compute_payout_amount_bva(
    improvement_u64: int,
    reward_pool_before: int,
    base_reward: int,
    improvement_reward_bps: int,
    max_reward: int,
    expected: int,
) -> None:
    got = _compute_payout_amount(
        improvement_u64=improvement_u64,
        reward_pool_before=reward_pool_before,
        base_reward=base_reward,
        improvement_reward_bps=improvement_reward_bps,
        max_reward=max_reward,
    )
    assert got == expected
