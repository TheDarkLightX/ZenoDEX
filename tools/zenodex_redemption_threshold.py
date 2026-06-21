#!/usr/bin/env python3
"""ZenoDEX Redemption Profitability Threshold Verifier.

Verifies that a redemption is profitable given market price, oracle price,
and redemption fee. Uses exact integer arithmetic scaled by E8 and BPS.

Mathematical model:
  - gross_collateral = amount * E8 // oracle_price  (floor)
  - fee = ceil(gross_collateral * fee_bps / BPS)   (ceil)
  - net_collateral = gross_collateral - fee
  - payout_value = net_collateral * oracle_price // E8  (floor)
  - market_cost = ceil(amount * market_price / E8)      (ceil)
  - profit = payout_value - market_cost

In exact arithmetic, the oracle price cancels in the round-trip:
  payout = (amount * E8 / oracle) * (BPS - fee) / BPS * oracle / E8
         = amount * (BPS - fee) / BPS

So the exact profitability condition (no rounding) is:
  market_price * BPS < E8 * (BPS - fee_bps)

The threshold is independent of oracle_price.

CLI:
  python3 tools/zenodex_redemption_threshold.py sample
  python3 tools/zenodex_redemption_threshold.py verify <file.json>
"""

from __future__ import annotations

import json
import sys
from dataclasses import dataclass, asdict
from typing import Any, Mapping

E8 = 100_000_000
BPS_SCALE = 10_000
MAX_AMOUNT_E8 = 10**18


def _ceil_div(a: int, b: int) -> int:
    if b <= 0:
        raise ValueError("divisor must be positive")
    return (a + b - 1) // b


def _safe_int(v: Any) -> int:
    """Safely extract an int from any value. Returns 0 for non-int inputs."""
    if isinstance(v, int) and not isinstance(v, bool):
        return v
    return 0


def gross_collateral(amount_e8: int, oracle_price_e8: int) -> int:
    if oracle_price_e8 <= 0:
        return 0
    return (amount_e8 * E8) // oracle_price_e8


def fee_collateral(gross_e8: int, fee_bps: int) -> int:
    return _ceil_div(gross_e8 * fee_bps, BPS_SCALE)


def net_collateral(gross_e8: int, fee_bps: int) -> int:
    return gross_e8 - fee_collateral(gross_e8, fee_bps)


def payout_value(amount_e8: int, oracle_price_e8: int, fee_bps: int) -> int:
    gross = gross_collateral(amount_e8, oracle_price_e8)
    if gross <= 0:
        return 0
    net = net_collateral(gross, fee_bps)
    if net <= 0:
        return 0
    return (net * oracle_price_e8) // E8


def market_cost(amount_e8: int, market_price_e8: int) -> int:
    return _ceil_div(amount_e8 * market_price_e8, E8)


def redeemer_profit_e8(
    amount_e8: int,
    market_price_e8: int,
    oracle_price_e8: int,
    fee_bps: int,
) -> int:
    if amount_e8 <= 0 or market_price_e8 <= 0 or oracle_price_e8 <= 0:
        return 0
    payout = payout_value(amount_e8, oracle_price_e8, fee_bps)
    cost = market_cost(amount_e8, market_price_e8)
    return payout - cost


def exact_payout_per_unit(fee_bps: int) -> int:
    """Exact payout per unit (E8): E8 * (BPS - fee_bps) / BPS.

    Independent of oracle price because oracle cancels in the round-trip.
    """
    return (E8 * (BPS_SCALE - fee_bps)) // BPS_SCALE


def redemption_profitable_exact(
    market_price_e8: int,
    fee_bps: int,
) -> bool:
    """Exact profitability: market * BPS < E8 * (BPS - fee_bps).

    Independent of oracle price.
    """
    return market_price_e8 * BPS_SCALE < E8 * (BPS_SCALE - fee_bps)


def redemption_profitable_threshold(fee_bps: int) -> int:
    """Peg floor: E8 * (BPS - fee_bps) / BPS. Independent of oracle."""
    return exact_payout_per_unit(fee_bps)


def largest_profitable_market_e8(fee_bps: int) -> int:
    """Largest integer market price (E8) at which redemption is still profitable.

    Profitable when market * BPS < E8 * (BPS - fee).
    Largest profitable: (E8 * (BPS - fee) - 1) // BPS.
    """
    rhs = E8 * (BPS_SCALE - fee_bps)
    if rhs <= 0:
        return 0
    return (rhs - 1) // BPS_SCALE


def first_nonprofitable_market_e8(fee_bps: int) -> int:
    """Smallest integer market price (E8) at which redemption is NOT profitable.

    This is ceil(E8 * (BPS - fee) / BPS).
    """
    rhs = E8 * (BPS_SCALE - fee_bps)
    return _ceil_div(rhs, BPS_SCALE)


@dataclass(frozen=True)
class RedemptionResult:
    status: str
    errors: list[str]
    amount_e8: int
    market_price_e8: int
    oracle_price_e8: int
    fee_bps: int
    gross_collateral_e8: int
    fee_collateral_e8: int
    net_collateral_e8: int
    payout_value_e8: int
    market_cost_e8: int
    redeemer_profit_e8: int
    exact_payout_per_unit_e8: int
    exact_profitable: bool
    rounded_profitable: bool
    threshold_e8: int
    largest_profitable_market_e8: int
    first_nonprofitable_market_e8: int


def _validate_envelope(env: Mapping[str, Any]) -> list[str]:
    errors: list[str] = []
    required = {
        "amount_e8", "market_price_e8", "oracle_price_e8", "fee_bps",
    }
    for field in required:
        if field not in env:
            errors.append(f"missing_required_field:{field}")
    if errors:
        return errors

    for field in required:
        v = env[field]
        if not isinstance(v, int) or isinstance(v, bool):
            errors.append(f"{field}_must_be_int")
    if errors:
        return errors

    if env["amount_e8"] <= 0:
        errors.append("amount_must_be_positive")
    if env["market_price_e8"] <= 0:
        errors.append("market_price_must_be_positive")
    if env["oracle_price_e8"] <= 0:
        errors.append("oracle_price_must_be_positive")
    if env["fee_bps"] < 0:
        errors.append("fee_bps_must_be_nonneg")
    if env["fee_bps"] >= BPS_SCALE:
        errors.append("fee_bps_must_be_below_bps")
    if env["amount_e8"] > MAX_AMOUNT_E8:
        errors.append("amount_exceeds_max")
    if env["oracle_price_e8"] > MAX_AMOUNT_E8:
        errors.append("oracle_price_exceeds_max")
    if env["market_price_e8"] > MAX_AMOUNT_E8:
        errors.append("market_price_exceeds_max")
    return errors


def _empty_result(status: str, errors: list[str], amount: int, market: int, oracle: int, fee: int) -> RedemptionResult:
    return RedemptionResult(
        status=status,
        errors=errors,
        amount_e8=amount,
        market_price_e8=market,
        oracle_price_e8=oracle,
        fee_bps=fee,
        gross_collateral_e8=0,
        fee_collateral_e8=0,
        net_collateral_e8=0,
        payout_value_e8=0,
        market_cost_e8=0,
        redeemer_profit_e8=0,
        exact_payout_per_unit_e8=0,
        exact_profitable=False,
        rounded_profitable=False,
        threshold_e8=0,
        largest_profitable_market_e8=0,
        first_nonprofitable_market_e8=0,
    )


def verify_redemption_envelope(env: Mapping[str, Any]) -> RedemptionResult:
    if not isinstance(env, dict):
        return _empty_result("rejected", ["envelope_must_be_object"], 0, 0, 0, 0)

    errors = _validate_envelope(env)

    amount = _safe_int(env.get("amount_e8", 0))
    market_price = _safe_int(env.get("market_price_e8", 0))
    oracle_price = _safe_int(env.get("oracle_price_e8", 0))
    fee_bps = _safe_int(env.get("fee_bps", 0))

    if errors:
        return _empty_result("rejected", errors, amount, market_price, oracle_price, fee_bps)

    gross = gross_collateral(amount, oracle_price) if oracle_price > 0 else 0
    fee = fee_collateral(gross, fee_bps) if gross > 0 else 0
    net = gross - fee if gross > 0 else 0
    payout = payout_value(amount, oracle_price, fee_bps) if oracle_price > 0 else 0
    cost = market_cost(amount, market_price) if market_price > 0 else 0
    profit = payout - cost

    exact_per_unit = exact_payout_per_unit(fee_bps) if fee_bps < BPS_SCALE else 0
    profitable = redemption_profitable_exact(market_price, fee_bps) if fee_bps < BPS_SCALE else False
    rounded_profitable = profit > 0
    threshold = redemption_profitable_threshold(fee_bps) if fee_bps < BPS_SCALE else 0
    largest_profit = largest_profitable_market_e8(fee_bps) if fee_bps < BPS_SCALE else 0
    first_nonprofit = first_nonprofitable_market_e8(fee_bps) if fee_bps < BPS_SCALE else 0

    if gross <= 0 and not errors:
        errors.append("gross_collateral_too_small")
    if fee >= gross and gross > 0 and not errors:
        errors.append("fee_consumes_all_collateral")

    if errors:
        status = "rejected"
    elif profitable:
        status = "accepted_exact_profitable"
    else:
        status = "accepted_not_exact_profitable"

    return RedemptionResult(
        status=status,
        errors=errors,
        amount_e8=amount,
        market_price_e8=market_price,
        oracle_price_e8=oracle_price,
        fee_bps=fee_bps,
        gross_collateral_e8=gross,
        fee_collateral_e8=fee,
        net_collateral_e8=net,
        payout_value_e8=payout,
        market_cost_e8=cost,
        redeemer_profit_e8=profit,
        exact_payout_per_unit_e8=exact_per_unit,
        exact_profitable=profitable,
        rounded_profitable=rounded_profitable,
        threshold_e8=threshold,
        largest_profitable_market_e8=largest_profit,
        first_nonprofitable_market_e8=first_nonprofit,
    )


def _sample_envelope() -> dict[str, Any]:
    return {
        "amount_e8": 1_000_000_000,
        "market_price_e8": 99_000_000,
        "oracle_price_e8": 100_000_000,
        "fee_bps": 50,
    }


def _print_json(result: RedemptionResult) -> None:
    print(json.dumps(asdict(result), indent=2))


def main() -> int:
    if len(sys.argv) < 2:
        print("Usage: zenodex_redemption_threshold.py [sample|verify <file>]", file=sys.stderr)
        return 1

    cmd = sys.argv[1]

    if cmd == "sample":
        env = _sample_envelope()
        result = verify_redemption_envelope(env)
        _print_json(result)
        return 0

    if cmd == "verify":
        if len(sys.argv) < 3:
            print("Usage: verify <file.json>", file=sys.stderr)
            return 1
        path = sys.argv[2]
        try:
            with open(path) as f:
                env = json.load(f)
        except FileNotFoundError:
            print(f"File not found: {path}", file=sys.stderr)
            return 1
        except json.JSONDecodeError as e:
            print(f"Malformed JSON: {e}", file=sys.stderr)
            return 1
        if not isinstance(env, dict):
            print("Top-level JSON must be an object", file=sys.stderr)
            return 1
        result = verify_redemption_envelope(env)
        _print_json(result)
        return 0 if not result.errors else 1

    print(f"Unknown command: {cmd}", file=sys.stderr)
    return 1


if __name__ == "__main__":
    sys.exit(main())
