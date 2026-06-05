# [TESTER] v1

from __future__ import annotations

import json
import math
import os
import shutil
import subprocess
from pathlib import Path

import pytest

from src.kernels.python.lp_math_v7 import (
    U128_MAX,
    burn_liquidity,
    mint_liquidity,
    mint_liquidity_initial,
    mint_liquidity_initial_witness,
    optimal_liquidity,
)


ROOT = Path(__file__).resolve().parents[2]
RUST_MANIFEST = ROOT / "src/kernels/rust/lp_math_v7/Cargo.toml"


def test_mint_liquidity_rejects_inconsistent_initial_state() -> None:
    with pytest.raises(ValueError, match="initial liquidity"):
        mint_liquidity(
            reserve0=1,
            reserve1=1,
            total_supply=0,
            amount0_desired=10,
            amount1_desired=10,
        )


@pytest.fixture(scope="session")
def rust_lp_math_cli(tmp_path_factory: pytest.TempPathFactory) -> Path:
    if shutil.which("cargo") is None:
        pytest.fail("cargo is required for lp_math_v7 Python-to-Rust differential coverage")

    target_dir = tmp_path_factory.mktemp("lp_math_v7_rust_target")
    subprocess.check_call(
        [
            "cargo",
            "build",
            "--quiet",
            "--manifest-path",
            str(RUST_MANIFEST),
            "--bin",
            "lp_math_v7_cli",
            "--target-dir",
            str(target_dir),
        ],
        cwd=ROOT,
    )
    suffix = ".exe" if os.name == "nt" else ""
    binary = target_dir / "debug" / f"lp_math_v7_cli{suffix}"
    assert binary.exists()
    return binary


def _rust(cli: Path, *args: object) -> dict[str, object]:
    proc = subprocess.run(
        [str(cli), *(str(arg) for arg in args)],
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=False,
    )
    assert proc.returncode == 0, proc.stderr or proc.stdout
    return json.loads(proc.stdout)


def _rust_exit(cli: Path, *args: object) -> tuple[int, dict[str, object]]:
    proc = subprocess.run(
        [str(cli), *(str(arg) for arg in args)],
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=False,
    )
    return proc.returncode, json.loads(proc.stdout)


def _optimal_dict(*, reserve0: int, reserve1: int, amount0_desired: int, amount1_desired: int) -> dict[str, int]:
    res = optimal_liquidity(
        reserve0=reserve0,
        reserve1=reserve1,
        amount0_desired=amount0_desired,
        amount1_desired=amount1_desired,
    )
    return {
        "amount0_used": res.amount0_used,
        "amount1_used": res.amount1_used,
        "amount0_refund": res.amount0_refund,
        "amount1_refund": res.amount1_refund,
    }


def _mint_dict(
    *,
    reserve0: int,
    reserve1: int,
    total_supply: int,
    amount0_desired: int,
    amount1_desired: int,
    min_liquidity: int,
) -> dict[str, int]:
    res = mint_liquidity(
        reserve0=reserve0,
        reserve1=reserve1,
        total_supply=total_supply,
        amount0_desired=amount0_desired,
        amount1_desired=amount1_desired,
        min_liquidity=min_liquidity,
    )
    return {
        "liquidity_minted": res.liquidity_minted,
        "amount0_used": res.amount0_used,
        "amount1_used": res.amount1_used,
        "amount0_refund": res.amount0_refund,
        "amount1_refund": res.amount1_refund,
        "new_reserve0": res.new_reserve0,
        "new_reserve1": res.new_reserve1,
        "new_total_supply": res.new_total_supply,
    }


def test_lp_math_v7_python_reject_edges() -> None:
    with pytest.raises(TypeError, match="reserve0 must be an int"):
        optimal_liquidity(reserve0=True, reserve1=1, amount0_desired=1, amount1_desired=1)
    with pytest.raises(ValueError, match="reserves must be non-negative"):
        optimal_liquidity(reserve0=-1, reserve1=1, amount0_desired=1, amount1_desired=1)
    with pytest.raises(ValueError, match="desired amounts must be positive"):
        optimal_liquidity(reserve0=1, reserve1=1, amount0_desired=0, amount1_desired=1)
    with pytest.raises(OverflowError, match="reserve0 exceeds u128"):
        optimal_liquidity(reserve0=U128_MAX + 1, reserve1=1, amount0_desired=1, amount1_desired=1)

    with pytest.raises(ValueError, match="min_lp_lock must be positive"):
        mint_liquidity_initial(amount0=10, amount1=10, min_lp_lock=0)
    sqrt_product = math.isqrt(12_345 * 67_890)
    with pytest.raises(ValueError, match="too large"):
        mint_liquidity_initial_witness(amount0=12_345, amount1=67_890, sqrt_product=sqrt_product + 1)
    with pytest.raises(ValueError, match="too small"):
        mint_liquidity_initial_witness(amount0=12_345, amount1=67_890, sqrt_product=sqrt_product - 1)

    with pytest.raises(ValueError, match="empty pool"):
        mint_liquidity(
            reserve0=0,
            reserve1=10,
            total_supply=1,
            amount0_desired=10,
            amount1_desired=10,
        )
    with pytest.raises(ValueError, match="deposit too small"):
        mint_liquidity(
            reserve0=1_000_000,
            reserve1=1_000_000,
            total_supply=1,
            amount0_desired=1,
            amount1_desired=1,
        )
    with pytest.raises(ValueError, match="below min_liquidity"):
        mint_liquidity(
            reserve0=1000,
            reserve1=2000,
            total_supply=10_000,
            amount0_desired=400,
            amount1_desired=900,
            min_liquidity=4001,
        )

    with pytest.raises(ValueError, match="lp_amount must be positive"):
        burn_liquidity(lp_amount=0, reserve0=1, reserve1=1, total_supply=1)
    with pytest.raises(ValueError, match="cannot burn more"):
        burn_liquidity(lp_amount=2, reserve0=1, reserve1=1, total_supply=1)


def test_lp_math_v7_python_rust_optimal_liquidity_differential(rust_lp_math_cli: Path) -> None:
    cases = [
        (0, 0, 1, 1),
        (0, 20, 3, 4),
        (20, 0, 3, 4),
        (1000, 2000, 400, 900),
        (1000, 2000, 800, 300),
        (1000, 2000, 3, 1),
        (7, 11, 13, 17),
        (11, 7, 13, 17),
        (5, 1000, 1, 1),
        (1000, 5, 1, 1),
        (3_000_000_000, 1, 1_000_000_000, 1),
    ]

    for reserve0 in (2, 3, 5, 11, 97):
        for reserve1 in (2, 7, 13, 89):
            for amount0, amount1 in ((1, 1), (3, 17), (19, 5)):
                cases.append((reserve0, reserve1, amount0, amount1))

    saw_empty = saw_token0_limited = saw_token1_limited = False
    for reserve0, reserve1, amount0, amount1 in cases:
        expected = _optimal_dict(
            reserve0=reserve0,
            reserve1=reserve1,
            amount0_desired=amount0,
            amount1_desired=amount1,
        )
        got = _rust(rust_lp_math_cli, "optimal", reserve0, reserve1, amount0, amount1)
        assert got == {"ok": True, "result": expected}
        saw_empty |= reserve0 == 0 or reserve1 == 0
        saw_token0_limited |= expected["amount0_refund"] == 0 and expected["amount1_refund"] > 0
        saw_token1_limited |= expected["amount1_refund"] == 0 and expected["amount0_refund"] > 0

    assert saw_empty
    assert saw_token0_limited
    assert saw_token1_limited


def test_lp_math_v7_python_rust_mint_initial_and_witness_differential(rust_lp_math_cli: Path) -> None:
    for amount0, amount1 in [(1001, 1001), (10_000, 10_000), (12_345, 67_890), (1_000_000, 999_983)]:
        minted, total_supply = mint_liquidity_initial(amount0=amount0, amount1=amount1)
        got = _rust(rust_lp_math_cli, "mint_initial", amount0, amount1)
        assert got == {
            "ok": True,
            "result": {"liquidity_minted": minted, "total_supply": total_supply},
        }

        sqrt_product = math.isqrt(amount0 * amount1)
        minted, total_supply = mint_liquidity_initial_witness(
            amount0=amount0,
            amount1=amount1,
            sqrt_product=sqrt_product,
        )
        got = _rust(rust_lp_math_cli, "mint_initial_witness", amount0, amount1, sqrt_product)
        assert got == {
            "ok": True,
            "result": {"liquidity_minted": minted, "total_supply": total_supply},
        }
        assert _rust(rust_lp_math_cli, "mint_initial_witness", amount0, amount1, sqrt_product + 1) == {
            "ok": False,
            "error": "invalid_sqrt_witness_too_large",
        }
        assert _rust(rust_lp_math_cli, "mint_initial_witness", amount0, amount1, sqrt_product - 1) == {
            "ok": False,
            "error": "invalid_sqrt_witness_too_small",
        }

    assert _rust(rust_lp_math_cli, "mint_initial", 1000, 1000) == {
        "ok": False,
        "error": "insufficient_initial_liquidity",
    }


def test_lp_math_v7_python_rust_mint_and_burn_differential(rust_lp_math_cli: Path) -> None:
    mint_cases = [
        (0, 0, 0, 10_000, 10_000, 999_999),
        (1000, 2000, 10_000, 400, 900, 0),
        (1000, 2000, 10_000, 800, 300, 1000),
        (7, 11, 10_003, 13, 17, 1),
        (11, 7, 10_003, 13, 17, 1),
        (1_000_000, 3_000_000, 4_000_000, 999, 5000, 100),
    ]
    for reserve0, reserve1 in ((3, 5), (5, 3), (7, 11), (11, 7), (97, 89)):
        for amount0, amount1 in ((6, 10), (10, 6), (13, 19), (19, 13)):
            mint_cases.append((reserve0, reserve1, 10_003, amount0, amount1, 1))

    for reserve0, reserve1, total_supply, amount0, amount1, min_liquidity in mint_cases:
        expected = _mint_dict(
            reserve0=reserve0,
            reserve1=reserve1,
            total_supply=total_supply,
            amount0_desired=amount0,
            amount1_desired=amount1,
            min_liquidity=min_liquidity,
        )
        got = _rust(rust_lp_math_cli, "mint", reserve0, reserve1, total_supply, amount0, amount1, min_liquidity)
        assert got == {"ok": True, "result": expected}

    burn_cases = [
        (1, 1000, 2000, 1000),
        (333, 1000, 2000, 1000),
        (999, 7, 11, 1000),
        (1_000_000, 3_000_000_000, 1, 1_000_000),
    ]
    for lp_amount, reserve0, reserve1, total_supply in burn_cases:
        res = burn_liquidity(
            lp_amount=lp_amount,
            reserve0=reserve0,
            reserve1=reserve1,
            total_supply=total_supply,
        )
        got = _rust(rust_lp_math_cli, "burn", lp_amount, reserve0, reserve1, total_supply)
        assert got == {"ok": True, "result": {"amount0_out": res.amount0_out, "amount1_out": res.amount1_out}}


def test_lp_math_v7_python_rust_high_width_boundary_differential(rust_lp_math_cli: Path) -> None:
    x = 1 << 64
    assert _rust(rust_lp_math_cli, "optimal", x, x, x, x) == {
        "ok": True,
        "result": _optimal_dict(reserve0=x, reserve1=x, amount0_desired=x, amount1_desired=x),
    }

    minted, total_supply = mint_liquidity_initial(amount0=x, amount1=x)
    assert _rust(rust_lp_math_cli, "mint_initial", x, x) == {
        "ok": True,
        "result": {"liquidity_minted": minted, "total_supply": total_supply},
    }
    minted, total_supply = mint_liquidity_initial(amount0=U128_MAX, amount1=U128_MAX)
    assert _rust(rust_lp_math_cli, "mint_initial", U128_MAX, U128_MAX) == {
        "ok": True,
        "result": {"liquidity_minted": minted, "total_supply": total_supply},
    }
    minted, total_supply = mint_liquidity_initial_witness(
        amount0=U128_MAX,
        amount1=U128_MAX,
        sqrt_product=U128_MAX,
    )
    assert _rust(rust_lp_math_cli, "mint_initial_witness", U128_MAX, U128_MAX, U128_MAX) == {
        "ok": True,
        "result": {"liquidity_minted": minted, "total_supply": total_supply},
    }

    expected_mint = _mint_dict(
        reserve0=x,
        reserve1=x,
        total_supply=x,
        amount0_desired=x,
        amount1_desired=x,
        min_liquidity=0,
    )
    assert _rust(rust_lp_math_cli, "mint", x, x, x, x, x, 0) == {"ok": True, "result": expected_mint}

    burn = burn_liquidity(lp_amount=x, reserve0=x, reserve1=x, total_supply=x)
    assert _rust(rust_lp_math_cli, "burn", x, x, x, x) == {
        "ok": True,
        "result": {"amount0_out": burn.amount0_out, "amount1_out": burn.amount1_out},
    }

    with pytest.raises(OverflowError, match="liquidity_minted exceeds u128"):
        mint_liquidity(
            reserve0=1,
            reserve1=1,
            total_supply=U128_MAX,
            amount0_desired=2,
            amount1_desired=2,
        )
    assert _rust(rust_lp_math_cli, "mint", 1, 1, U128_MAX, 2, 2, 0) == {
        "ok": False,
        "error": "overflow",
    }

    with pytest.raises(OverflowError, match="new_reserve0 exceeds u128"):
        mint_liquidity(
            reserve0=U128_MAX,
            reserve1=U128_MAX,
            total_supply=U128_MAX,
            amount0_desired=1,
            amount1_desired=1,
        )
    assert _rust(rust_lp_math_cli, "mint", U128_MAX, U128_MAX, U128_MAX, 1, 1, 0) == {
        "ok": False,
        "error": "overflow",
    }
    assert _rust(rust_lp_math_cli, "burn", 1001, 1000, 2000, 1000) == {
        "ok": False,
        "error": "burn_amount_exceeds_supply",
    }


def test_lp_math_v7_cli_parse_errors_are_deterministic_json(rust_lp_math_cli: Path) -> None:
    assert _rust_exit(rust_lp_math_cli, 'bad"op') == (2, {"ok": False, "error": "unknown_operation"})
    assert _rust_exit(rust_lp_math_cli, "bad\\\nop") == (2, {"ok": False, "error": "unknown_operation"})
    assert _rust_exit(rust_lp_math_cli, "optimal", '1"', 2, 3, 4) == (2, {"ok": False, "error": "invalid_u128"})
    assert _rust_exit(rust_lp_math_cli, "optimal", 1, 2, 3) == (2, {"ok": False, "error": "wrong_arity"})
