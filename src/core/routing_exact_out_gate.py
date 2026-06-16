"""Deterministic exact-out routing gate.

This module owns the fixed-point policy that decides whether the exact-out
router should pay the extra cost to evaluate 2-hop candidates.
"""

from __future__ import annotations

from dataclasses import dataclass

from ..state.balances import Amount

_EXACT_OUT_GATE_SCALE = 10_000


@dataclass(frozen=True)
class ExactOutTwoHopGateConfig:
    """
    Deterministic gate for deciding whether exact-out 2-hop evaluation should run.

    Policies:
    - "stress":          amount_out / direct_reserve_out >= stress_threshold
    - "pressure":        direct_amount_in / amount_out >= pressure_threshold
    - "stress_or_pressure": (stress condition) OR (pressure condition)
    - "stress_or_pressure_adaptive": (stress condition) OR
      (pressure >= pressure_threshold + pressure_slope * max(0, stress_threshold - stress))
    - "stress_or_pressure_piecewise":
      if stress >= stress_threshold then True
      elif stress >= piecewise_stress_cutoff then pressure >= piecewise_pressure_mid
      else pressure >= piecewise_pressure_low
    - "stress_or_pressure_piecewise_fee":
      if stress >= stress_threshold then True
      elif stress >= fee_piecewise_stress_cutoff then pressure >= fee_piecewise_pressure_mid
      else pressure >= fee_piecewise_pressure_low + fee_piecewise_fee_slope * (direct_fee_bps / 10_000)
    - "stress_or_pressure_tripiece":
      if stress >= stress_threshold then True
      elif stress >= tripiece_stress_upper_cutoff then pressure >= tripiece_pressure_upper_band
      elif stress >= tripiece_stress_lower_cutoff then pressure >= tripiece_pressure_mid_band
      else pressure >= tripiece_pressure_low_base + tripiece_fee_slope * (direct_fee_bps / 10_000)

    Units (fixed-point, integer-only):
    - stress thresholds/cutoffs use `*_bps` where 10_000 == 1.0
    - pressure thresholds use `*_e4` where 10_000 == 1.0
    - slopes use `*_e4` where 10_000 == 1.0
    """

    policy: str = "stress_or_pressure"
    stress_threshold_bps: int = 4000
    pressure_threshold_e4: int = 16000
    pressure_slope_e4: int = 12000
    piecewise_stress_cutoff_bps: int = 1500
    piecewise_pressure_mid_e4: int = 15000
    piecewise_pressure_low_e4: int = 22000
    fee_piecewise_stress_cutoff_bps: int = 1200
    fee_piecewise_pressure_mid_e4: int = 15000
    fee_piecewise_pressure_low_e4: int = 23000
    fee_piecewise_fee_slope_e4: int = 120000
    tripiece_stress_lower_cutoff_bps: int = 1400
    tripiece_stress_upper_cutoff_bps: int = 2000
    tripiece_pressure_mid_band_e4: int = 16000
    tripiece_pressure_upper_band_e4: int = 14500
    tripiece_pressure_low_base_e4: int = 23000
    tripiece_fee_slope_e4: int = 160000


@dataclass(frozen=True)
class ExactOutTwoHopGateDecision:
    consider_two_hop: bool
    stress_bps: int
    pressure_e4: int
    policy: str


@dataclass(frozen=True)
class _ExactOutGateContext:
    amount_out: int
    direct_reserve_out: int
    direct_amount_in: int
    direct_fee_bps: int

    @property
    def stress_bps(self) -> int:
        return (self.amount_out * _EXACT_OUT_GATE_SCALE) // self.direct_reserve_out

    @property
    def pressure_e4(self) -> int:
        return (self.direct_amount_in * _EXACT_OUT_GATE_SCALE) // self.amount_out

    def stress_ge(self, threshold_bps: int) -> bool:
        # amount_out / reserve_out >= threshold/10_000.
        return self.amount_out * _EXACT_OUT_GATE_SCALE >= self.direct_reserve_out * int(threshold_bps)

    def pressure_ge(self, threshold_e4: int) -> bool:
        # amount_in / amount_out >= threshold/10_000.
        return self.direct_amount_in * _EXACT_OUT_GATE_SCALE >= self.amount_out * int(threshold_e4)

    def fee_slope_increment(self, slope_e4: int) -> int:
        return _ceil_div_nonneg(int(slope_e4) * self.direct_fee_bps, _EXACT_OUT_GATE_SCALE)


def _normalize_exact_out_gate_policy(policy: str) -> str:
    p = str(policy).strip().lower()
    if p in {
        "stress",
        "pressure",
        "stress_or_pressure",
        "stress_or_pressure_adaptive",
        "stress_or_pressure_piecewise",
        "stress_or_pressure_piecewise_fee",
        "stress_or_pressure_tripiece",
    }:
        return p
    raise ValueError(f"unsupported exact-out gate policy: {policy}")


def _require_gate_int(name: str, value: int) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be int")
    return int(value)


def _ceil_div_nonneg(n: int, d: int) -> int:
    if d <= 0:
        raise ValueError("denominator must be positive")
    if n <= 0:
        return 0
    return (int(n) + int(d) - 1) // int(d)


def _clamp_nonneg(v: int) -> int:
    return int(v) if int(v) >= 0 else 0


def _build_exact_out_gate_context(
    *,
    amount_out: Amount,
    direct_reserve_out: Amount,
    direct_amount_in: Amount,
    direct_fee_bps: int,
) -> _ExactOutGateContext:
    amount = _require_gate_int("amount_out", amount_out)
    reserve_out = _require_gate_int("direct_reserve_out", direct_reserve_out)
    amount_in = _require_gate_int("direct_amount_in", direct_amount_in)
    fee_bps = _require_gate_int("direct_fee_bps", direct_fee_bps)
    if amount <= 0:
        raise ValueError("amount_out must be positive")
    if reserve_out <= 0:
        raise ValueError("direct_reserve_out must be positive")
    if amount_in <= 0:
        raise ValueError("direct_amount_in must be positive")
    if fee_bps < 0:
        raise ValueError("direct_fee_bps must be non-negative")
    return _ExactOutGateContext(
        amount_out=amount,
        direct_reserve_out=reserve_out,
        direct_amount_in=amount_in,
        direct_fee_bps=fee_bps,
    )


def _base_exact_out_gate_thresholds(cfg: ExactOutTwoHopGateConfig) -> tuple[int, int, int]:
    stress_threshold_bps = _require_gate_int("stress_threshold_bps", cfg.stress_threshold_bps)
    pressure_threshold_e4 = _require_gate_int("pressure_threshold_e4", cfg.pressure_threshold_e4)
    pressure_slope_e4 = _require_gate_int("pressure_slope_e4", cfg.pressure_slope_e4)
    if stress_threshold_bps < 0 or stress_threshold_bps > _EXACT_OUT_GATE_SCALE:
        raise ValueError("stress_threshold_bps must be in [0, 10_000]")
    if pressure_threshold_e4 < 0:
        raise ValueError("pressure_threshold_e4 must be non-negative")
    if pressure_slope_e4 < 0:
        raise ValueError("pressure_slope_e4 must be non-negative")
    return stress_threshold_bps, pressure_threshold_e4, pressure_slope_e4


def _consider_adaptive_exact_out_gate(
    ctx: _ExactOutGateContext,
    *,
    stress_threshold_bps: int,
    pressure_threshold_e4: int,
    pressure_slope_e4: int,
) -> bool:
    diff = _clamp_nonneg(int(stress_threshold_bps) - int(ctx.stress_bps))
    inc = _ceil_div_nonneg(int(pressure_slope_e4) * int(diff), _EXACT_OUT_GATE_SCALE)
    adaptive_threshold = int(pressure_threshold_e4) + int(inc)
    return bool(ctx.stress_ge(stress_threshold_bps) or ctx.pressure_ge(adaptive_threshold))


def _consider_piecewise_exact_out_gate(
    ctx: _ExactOutGateContext,
    *,
    stress_threshold_bps: int,
    stress_cutoff_bps: int,
    pressure_mid_e4: int,
    pressure_low_e4: int,
) -> bool:
    if ctx.stress_ge(stress_threshold_bps):
        return True
    if ctx.stress_ge(stress_cutoff_bps):
        return bool(ctx.pressure_ge(pressure_mid_e4))
    return bool(ctx.pressure_ge(pressure_low_e4))


def _consider_fee_piecewise_exact_out_gate(
    ctx: _ExactOutGateContext,
    *,
    stress_threshold_bps: int,
    stress_cutoff_bps: int,
    pressure_mid_e4: int,
    pressure_low_e4: int,
    fee_slope_e4: int,
) -> bool:
    if ctx.stress_ge(stress_threshold_bps):
        return True
    if ctx.stress_ge(stress_cutoff_bps):
        return bool(ctx.pressure_ge(pressure_mid_e4))
    threshold = int(pressure_low_e4) + ctx.fee_slope_increment(fee_slope_e4)
    return bool(ctx.pressure_ge(threshold))


def _consider_tripiece_exact_out_gate(
    ctx: _ExactOutGateContext,
    *,
    stress_threshold_bps: int,
    stress_lower_cutoff_bps: int,
    stress_upper_cutoff_bps: int,
    pressure_mid_band_e4: int,
    pressure_upper_band_e4: int,
    pressure_low_base_e4: int,
    fee_slope_e4: int,
) -> bool:
    if ctx.stress_ge(stress_threshold_bps):
        return True
    if ctx.stress_ge(stress_upper_cutoff_bps):
        return bool(ctx.pressure_ge(pressure_upper_band_e4))
    if ctx.stress_ge(stress_lower_cutoff_bps):
        return bool(ctx.pressure_ge(pressure_mid_band_e4))
    threshold = int(pressure_low_base_e4) + ctx.fee_slope_increment(fee_slope_e4)
    return bool(ctx.pressure_ge(threshold))


def _evaluate_exact_out_gate_policy(
    *,
    policy: str,
    cfg: ExactOutTwoHopGateConfig,
    ctx: _ExactOutGateContext,
    stress_threshold_bps: int,
    pressure_threshold_e4: int,
    pressure_slope_e4: int,
) -> bool:
    if policy == "stress":
        return bool(ctx.stress_ge(stress_threshold_bps))
    if policy == "pressure":
        return bool(ctx.pressure_ge(pressure_threshold_e4))
    if policy == "stress_or_pressure_adaptive":
        return _consider_adaptive_exact_out_gate(
            ctx,
            stress_threshold_bps=stress_threshold_bps,
            pressure_threshold_e4=pressure_threshold_e4,
            pressure_slope_e4=pressure_slope_e4,
        )
    if policy == "stress_or_pressure_piecewise":
        return _consider_piecewise_exact_out_gate(
            ctx,
            stress_threshold_bps=stress_threshold_bps,
            stress_cutoff_bps=_require_gate_int("piecewise_stress_cutoff_bps", cfg.piecewise_stress_cutoff_bps),
            pressure_mid_e4=_require_gate_int("piecewise_pressure_mid_e4", cfg.piecewise_pressure_mid_e4),
            pressure_low_e4=_require_gate_int("piecewise_pressure_low_e4", cfg.piecewise_pressure_low_e4),
        )
    if policy == "stress_or_pressure_piecewise_fee":
        return _consider_fee_piecewise_exact_out_gate(
            ctx,
            stress_threshold_bps=stress_threshold_bps,
            stress_cutoff_bps=_require_gate_int(
                "fee_piecewise_stress_cutoff_bps",
                cfg.fee_piecewise_stress_cutoff_bps,
            ),
            pressure_mid_e4=_require_gate_int("fee_piecewise_pressure_mid_e4", cfg.fee_piecewise_pressure_mid_e4),
            pressure_low_e4=_require_gate_int("fee_piecewise_pressure_low_e4", cfg.fee_piecewise_pressure_low_e4),
            fee_slope_e4=_require_gate_int("fee_piecewise_fee_slope_e4", cfg.fee_piecewise_fee_slope_e4),
        )
    if policy == "stress_or_pressure_tripiece":
        return _consider_tripiece_exact_out_gate(
            ctx,
            stress_threshold_bps=stress_threshold_bps,
            stress_lower_cutoff_bps=_require_gate_int(
                "tripiece_stress_lower_cutoff_bps",
                cfg.tripiece_stress_lower_cutoff_bps,
            ),
            stress_upper_cutoff_bps=_require_gate_int(
                "tripiece_stress_upper_cutoff_bps",
                cfg.tripiece_stress_upper_cutoff_bps,
            ),
            pressure_mid_band_e4=_require_gate_int(
                "tripiece_pressure_mid_band_e4",
                cfg.tripiece_pressure_mid_band_e4,
            ),
            pressure_upper_band_e4=_require_gate_int(
                "tripiece_pressure_upper_band_e4",
                cfg.tripiece_pressure_upper_band_e4,
            ),
            pressure_low_base_e4=_require_gate_int(
                "tripiece_pressure_low_base_e4",
                cfg.tripiece_pressure_low_base_e4,
            ),
            fee_slope_e4=_require_gate_int("tripiece_fee_slope_e4", cfg.tripiece_fee_slope_e4),
        )
    return bool(ctx.stress_ge(stress_threshold_bps) or ctx.pressure_ge(pressure_threshold_e4))


def decide_exact_out_two_hop_gate(
    *,
    amount_out: Amount,
    direct_reserve_out: Amount,
    direct_amount_in: Amount,
    direct_fee_bps: int = 0,
    config: ExactOutTwoHopGateConfig | None = None,
) -> ExactOutTwoHopGateDecision:
    cfg = config or ExactOutTwoHopGateConfig()
    policy = _normalize_exact_out_gate_policy(cfg.policy)
    ctx = _build_exact_out_gate_context(
        amount_out=amount_out,
        direct_reserve_out=direct_reserve_out,
        direct_amount_in=direct_amount_in,
        direct_fee_bps=direct_fee_bps,
    )
    stress_threshold_bps, pressure_threshold_e4, pressure_slope_e4 = _base_exact_out_gate_thresholds(cfg)
    consider = _evaluate_exact_out_gate_policy(
        policy=policy,
        cfg=cfg,
        ctx=ctx,
        stress_threshold_bps=stress_threshold_bps,
        pressure_threshold_e4=pressure_threshold_e4,
        pressure_slope_e4=pressure_slope_e4,
    )
    return ExactOutTwoHopGateDecision(
        consider_two_hop=consider,
        stress_bps=int(ctx.stress_bps),
        pressure_e4=int(ctx.pressure_e4),
        policy=policy,
    )


def should_consider_exact_out_two_hop(
    *,
    amount_out: Amount,
    direct_reserve_out: Amount,
    direct_amount_in: Amount,
    direct_fee_bps: int = 0,
    config: ExactOutTwoHopGateConfig | None = None,
) -> bool:
    return decide_exact_out_two_hop_gate(
        amount_out=amount_out,
        direct_reserve_out=direct_reserve_out,
        direct_amount_in=direct_amount_in,
        direct_fee_bps=direct_fee_bps,
        config=config,
    ).consider_two_hop
