from __future__ import annotations

import argparse
import json
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Iterator, Sequence

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.core import cpmm
from src.core import cubic_sum_amm
from src.core import quartic_blend_amm
from src.core import quadratic_cpmm
from src.core import quintic_blend_amm
from src.core import sum_boost_amm


@dataclass(frozen=True)
class ExactInMetrics:
    ok: bool
    amount_out: int
    k_before: int
    k_after: int


@dataclass(frozen=True)
class ExactOutMetrics:
    ok: bool
    amount_in: int
    out_exec: int
    gap: int
    non_minimal: bool
    k_before: int
    k_after: int


def _raise_unknown_curve(name: str) -> None:
    raise ValueError(f"unknown curve: {name}")


def _k_cpmm(x: int, y: int) -> int:
    return int(x) * int(y)


def _k_quadratic(x: int, y: int) -> int:
    return int(x) * int(x) * int(y)


def _k_cubic_sum(x: int, y: int, *, p: int = 1, q: int = 1) -> int:
    return int(x) * int(y) * (int(p) * int(x) + int(q) * int(y))


def _k_sum_boost(x: int, y: int, *, mu_num: int, mu_den: int) -> int:
    s = int(x) + int(y)
    return int(x) * int(y) * s * (int(mu_den) + int(mu_num) * s)


def _k_quartic_blend(x: int, y: int, *, c_num: int, c_den: int) -> int:
    quad_scaled = int(c_den) * (int(x) * int(x) + int(y) * int(y)) + int(c_num) * int(x) * int(y)
    return int(x) * int(y) * quad_scaled


def _k_quintic_blend(x: int, y: int, *, c_num: int, c_den: int) -> int:
    s = int(x) + int(y)
    quad_scaled = int(c_den) * (int(x) * int(x) + int(y) * int(y)) + int(c_num) * int(x) * int(y)
    return int(x) * int(y) * s * quad_scaled


def _iter_pairs_grid(*, min_r: int, max_r: int, step: int) -> Iterator[tuple[int, int]]:
    for x in range(min_r, max_r + 1, step):
        for y in range(min_r, max_r + 1, step):
            yield x, y


def _iter_pairs_balanced(*, reserves: Iterable[int]) -> Iterator[tuple[int, int]]:
    for r in reserves:
        yield int(r), int(r)


def _iter_pairs_ratio(*, reserves: Iterable[int], ratios: Iterable[int]) -> Iterator[tuple[int, int]]:
    for r in reserves:
        for k in ratios:
            yield int(r), int(k) * int(r)
            yield int(k) * int(r), int(r)


def _safe_exact_in(
    name: str,
    *,
    x: int,
    y: int,
    dx: int,
    p: int,
    q: int,
    sum_boost_mu_num: int,
    sum_boost_mu_den: int,
    quartic_c_num: int,
    quartic_c_den: int,
    quintic_c_num: int,
    quintic_c_den: int,
) -> ExactInMetrics:
    try:
        if name == "cpmm":
            k0 = _k_cpmm(x, y)
            out, (x1, y1) = cpmm.swap_exact_in(x, y, dx, fee_bps=0)
            k1 = _k_cpmm(int(x1), int(y1))
        elif name == "quadratic":
            k0 = _k_quadratic(x, y)
            out, (x1, y1) = quadratic_cpmm.swap_exact_in_quadratic(x, y, dx, fee_bps=0)
            k1 = _k_quadratic(int(x1), int(y1))
        elif name == "cubic_sum":
            k0 = _k_cubic_sum(x, y, p=p, q=q)
            out, (x1, y1) = cubic_sum_amm.swap_exact_in_cubic_sum(x, y, dx, p=p, q=q)
            k1 = _k_cubic_sum(int(x1), int(y1), p=p, q=q)
        elif name == "sum_boost":
            k0 = _k_sum_boost(x, y, mu_num=sum_boost_mu_num, mu_den=sum_boost_mu_den)
            out, (x1, y1) = sum_boost_amm.swap_exact_in_sum_boost(
                x, y, dx, mu_num=sum_boost_mu_num, mu_den=sum_boost_mu_den, fee_bps=0
            )
            k1 = _k_sum_boost(int(x1), int(y1), mu_num=sum_boost_mu_num, mu_den=sum_boost_mu_den)
        elif name == "quartic_blend":
            k0 = _k_quartic_blend(x, y, c_num=quartic_c_num, c_den=quartic_c_den)
            out, (x1, y1) = quartic_blend_amm.swap_exact_in_quartic_blend(
                x, y, dx, c_num=quartic_c_num, c_den=quartic_c_den, fee_bps=0
            )
            k1 = _k_quartic_blend(int(x1), int(y1), c_num=quartic_c_num, c_den=quartic_c_den)
        elif name == "quintic_blend":
            k0 = _k_quintic_blend(x, y, c_num=quintic_c_num, c_den=quintic_c_den)
            out, (x1, y1) = quintic_blend_amm.swap_exact_in_quintic_blend(
                x, y, dx, c_num=quintic_c_num, c_den=quintic_c_den, fee_bps=0
            )
            k1 = _k_quintic_blend(int(x1), int(y1), c_num=quintic_c_num, c_den=quintic_c_den)
        else:
            raise ValueError(f"unknown curve: {name}")
        return ExactInMetrics(ok=True, amount_out=int(out), k_before=int(k0), k_after=int(k1))
    except Exception:
        return ExactInMetrics(ok=False, amount_out=0, k_before=0, k_after=0)


def _safe_exact_out(
    name: str,
    *,
    x: int,
    y: int,
    dy: int,
    p: int,
    q: int,
    sum_boost_mu_num: int,
    sum_boost_mu_den: int,
    quartic_c_num: int,
    quartic_c_den: int,
    quintic_c_num: int,
    quintic_c_den: int,
) -> ExactOutMetrics:
    try:
        if name == "cpmm":
            k0 = _k_cpmm(x, y)
            dx, (x1, y1) = cpmm.swap_exact_out(x, y, dy, fee_bps=0)
            out_exec, _ = cpmm.swap_exact_in(x, y, dx, fee_bps=0)
            k1 = _k_cpmm(int(x1), int(y1))
        elif name == "quadratic":
            k0 = _k_quadratic(x, y)
            dx, (x1, y1) = quadratic_cpmm.swap_exact_out_quadratic(x, y, dy, fee_bps=0)
            out_exec, _ = quadratic_cpmm.swap_exact_in_quadratic(x, y, dx, fee_bps=0)
            k1 = _k_quadratic(int(x1), int(y1))
        elif name == "cubic_sum":
            k0 = _k_cubic_sum(x, y, p=p, q=q)
            dx, (x1, y1) = cubic_sum_amm.swap_exact_out_cubic_sum(x, y, dy, p=p, q=q)
            out_exec, _ = cubic_sum_amm.swap_exact_in_cubic_sum(x, y, dx, p=p, q=q)
            k1 = _k_cubic_sum(int(x1), int(y1), p=p, q=q)
        elif name == "sum_boost":
            k0 = _k_sum_boost(x, y, mu_num=sum_boost_mu_num, mu_den=sum_boost_mu_den)
            dx, (x1, y1) = sum_boost_amm.swap_exact_out_sum_boost(
                x, y, dy, mu_num=sum_boost_mu_num, mu_den=sum_boost_mu_den, fee_bps=0
            )
            out_exec, _ = sum_boost_amm.swap_exact_in_sum_boost(
                x, y, dx, mu_num=sum_boost_mu_num, mu_den=sum_boost_mu_den, fee_bps=0
            )
            k1 = _k_sum_boost(int(x1), int(y1), mu_num=sum_boost_mu_num, mu_den=sum_boost_mu_den)
        elif name == "quartic_blend":
            k0 = _k_quartic_blend(x, y, c_num=quartic_c_num, c_den=quartic_c_den)
            dx, (x1, y1) = quartic_blend_amm.swap_exact_out_quartic_blend(
                x, y, dy, c_num=quartic_c_num, c_den=quartic_c_den, fee_bps=0
            )
            out_exec, _ = quartic_blend_amm.swap_exact_in_quartic_blend(
                x, y, dx, c_num=quartic_c_num, c_den=quartic_c_den, fee_bps=0
            )
            k1 = _k_quartic_blend(int(x1), int(y1), c_num=quartic_c_num, c_den=quartic_c_den)
        elif name == "quintic_blend":
            k0 = _k_quintic_blend(x, y, c_num=quintic_c_num, c_den=quintic_c_den)
            dx, (x1, y1) = quintic_blend_amm.swap_exact_out_quintic_blend(
                x, y, dy, c_num=quintic_c_num, c_den=quintic_c_den, fee_bps=0
            )
            out_exec, _ = quintic_blend_amm.swap_exact_in_quintic_blend(
                x, y, dx, c_num=quintic_c_num, c_den=quintic_c_den, fee_bps=0
            )
            k1 = _k_quintic_blend(int(x1), int(y1), c_num=quintic_c_num, c_den=quintic_c_den)
        else:
            raise ValueError(f"unknown curve: {name}")

        out_exec_i = int(out_exec)
        gap = out_exec_i - int(dy)

        non_minimal = False
        if int(dx) > 1:
            try:
                out_prev, _ = (
                    cpmm.swap_exact_in(x, y, int(dx) - 1, fee_bps=0)
                    if name == "cpmm"
                    else quadratic_cpmm.swap_exact_in_quadratic(x, y, int(dx) - 1, fee_bps=0)
                    if name == "quadratic"
                    else cubic_sum_amm.swap_exact_in_cubic_sum(x, y, int(dx) - 1, p=p, q=q)
                    if name == "cubic_sum"
                    else sum_boost_amm.swap_exact_in_sum_boost(
                        x, y, int(dx) - 1, mu_num=sum_boost_mu_num, mu_den=sum_boost_mu_den, fee_bps=0
                    )
                    if name == "sum_boost"
                    else quartic_blend_amm.swap_exact_in_quartic_blend(
                        x, y, int(dx) - 1, c_num=quartic_c_num, c_den=quartic_c_den, fee_bps=0
                    )
                    if name == "quartic_blend"
                    else quintic_blend_amm.swap_exact_in_quintic_blend(
                        x, y, int(dx) - 1, c_num=quintic_c_num, c_den=quintic_c_den, fee_bps=0
                    )
                    if name == "quintic_blend"
                    else (_raise_unknown_curve(name))
                )
                non_minimal = int(out_prev) >= int(dy)
            except Exception:
                non_minimal = False

        return ExactOutMetrics(
            ok=True,
            amount_in=int(dx),
            out_exec=out_exec_i,
            gap=int(gap),
            non_minimal=bool(non_minimal),
            k_before=int(k0),
            k_after=int(k1),
        )
    except Exception:
        return ExactOutMetrics(
            ok=False,
            amount_in=0,
            out_exec=0,
            gap=0,
            non_minimal=False,
            k_before=0,
            k_after=0,
        )


@dataclass
class Agg:
    n: int = 0
    ok: int = 0
    non_minimal: int = 0
    gap_sum: int = 0
    gap_max: int = 0
    k_inc_sum: int = 0
    k_inc_max: int = 0

    def add_exact_in(self, m: ExactInMetrics) -> None:
        self.n += 1
        if not m.ok:
            return
        self.ok += 1
        inc = m.k_after - m.k_before
        self.k_inc_sum += int(inc)
        self.k_inc_max = max(self.k_inc_max, int(inc))

    def add_exact_out(self, m: ExactOutMetrics) -> None:
        self.n += 1
        if not m.ok:
            return
        self.ok += 1
        if m.non_minimal:
            self.non_minimal += 1
        self.gap_sum += int(m.gap)
        self.gap_max = max(self.gap_max, int(m.gap))
        inc = m.k_after - m.k_before
        self.k_inc_sum += int(inc)
        self.k_inc_max = max(self.k_inc_max, int(inc))

    def to_json(self) -> dict[str, object]:
        return {
            "attempts": self.n,
            "ok": self.ok,
            "ok_rate": (self.ok / self.n) if self.n else 0.0,
            "non_minimal": self.non_minimal,
            "non_minimal_rate": (self.non_minimal / self.ok) if self.ok else 0.0,
            "gap_avg": (self.gap_sum / self.ok) if self.ok else 0.0,
            "gap_max": self.gap_max,
            "k_increase_avg": (self.k_inc_sum / self.ok) if self.ok else 0.0,
            "k_increase_max": self.k_inc_max,
        }


def _witness_key(w: dict[str, int], fields: Sequence[str]) -> tuple[int, ...]:
    return tuple(int(w[f]) for f in fields)


def _update_extreme(
    *,
    extreme: dict[str, object],
    value: int,
    witness: dict[str, int],
    better: str,
    key_fields: Sequence[str],
) -> None:
    """
    Track max/min values with deterministic tie-break: lexicographically smallest witness key.

    `better` is either "max" or "min".
    """
    if better not in ("max", "min"):
        raise ValueError("better must be 'max' or 'min'")

    best_value = extreme.get(better)
    best_witness = extreme.get(f"{better}_witness")
    best_key = extreme.get(f"{better}_key")

    if best_value is None:
        extreme[better] = int(value)
        extreme[f"{better}_witness"] = dict(witness)
        extreme[f"{better}_key"] = _witness_key(witness, key_fields)
        return

    best_value_i = int(best_value)
    key = _witness_key(witness, key_fields)
    should_update = False
    if better == "max":
        should_update = (value > best_value_i) or (value == best_value_i and key < best_key)
    else:
        should_update = (value < best_value_i) or (value == best_value_i and key < best_key)

    if should_update:
        extreme[better] = int(value)
        extreme[f"{better}_witness"] = dict(witness)
        extreme[f"{better}_key"] = key


def run_sweep(
    *,
    pairs: Iterable[tuple[int, int]],
    dx_list: list[int],
    dy_list: list[int],
    p: int,
    q: int,
    include_quadratic: bool,
    include_sum_boost: bool,
    include_quartic_blend: bool,
    include_quintic_blend: bool,
    sum_boost_mu_num: int,
    sum_boost_mu_den: int,
    quartic_c_num: int,
    quartic_c_den: int,
    quintic_c_num: int,
    quintic_c_den: int,
    progress_every: int = 0,
) -> dict[str, object]:
    curves = ["cpmm", "cubic_sum"]
    if include_quadratic:
        curves.append("quadratic")
    if include_sum_boost:
        curves.append("sum_boost")
    if include_quartic_blend:
        curves.append("quartic_blend")
    if include_quintic_blend:
        curves.append("quintic_blend")

    exact_in: dict[str, Agg] = {c: Agg() for c in curves}
    exact_out: dict[str, Agg] = {c: Agg() for c in curves}

    slippage_in_sum: dict[str, dict[int, float]] = {c: {dx: 0.0 for dx in dx_list} for c in curves}
    slippage_in_n: dict[str, dict[int, int]] = {c: {dx: 0 for dx in dx_list} for c in curves}
    slippage_out_sum: dict[str, dict[int, float]] = {c: {dy: 0.0 for dy in dy_list} for c in curves}
    slippage_out_n: dict[str, dict[int, int]] = {c: {dy: 0 for dy in dy_list} for c in curves}

    # Simple “which curve gives the most out for same dx” counter (trader-favorability proxy).
    win_out: dict[str, int] = {c: 0 for c in curves}
    win_in: dict[str, int] = {c: 0 for c in curves}
    ties_out = 0
    ties_in = 0

    # Witnesses for per-curve extremes.
    gap_max_witness: dict[str, dict[str, int]] = {}
    k_inc_max_witness_in: dict[str, dict[str, int]] = {}
    k_inc_max_witness_out: dict[str, dict[str, int]] = {}

    # Pairwise comparisons (cubic_sum vs cpmm).
    diff_exact_in_out: dict[str, object] = {}
    diff_exact_out_in: dict[str, object] = {}
    diff_exact_out_gap: dict[str, object] = {}
    diff_exact_out_gap_nonneg = 0
    diff_exact_out_gap_neg = 0
    diff_exact_in_out_pos = 0
    diff_exact_in_out_neg = 0
    diff_exact_in_out_eq = 0
    diff_exact_out_in_pos = 0
    diff_exact_out_in_neg = 0
    diff_exact_out_in_eq = 0

    for pair_i, (x, y) in enumerate(pairs, start=1):
        if progress_every and (pair_i % progress_every == 0):
            print(
                f"[sweep] progressed pairs={pair_i} (x={x}, y={y})",
                file=sys.stderr,
                flush=True,
            )

        # Marginal reference (integer-safe): cost to buy dy=1.
        # This avoids the “dx=1 often yields 0 out” artifact under floor rounding.
        marginal_dx_for_one_out: dict[str, int] = {}
        if y > 1:
            for c in curves:
                m1 = _safe_exact_out(
                    c,
                    x=x,
                    y=y,
                    dy=1,
                    p=p,
                    q=q,
                    sum_boost_mu_num=sum_boost_mu_num,
                    sum_boost_mu_den=sum_boost_mu_den,
                    quartic_c_num=quartic_c_num,
                    quartic_c_den=quartic_c_den,
                    quintic_c_num=quintic_c_num,
                    quintic_c_den=quintic_c_den,
                )
                if m1.ok and m1.amount_in > 0:
                    marginal_dx_for_one_out[c] = int(m1.amount_in)

        for dx in dx_list:
            outs: dict[str, int] = {}
            cpmm_out = None
            cubic_out = None
            for c in curves:
                m = _safe_exact_in(
                    c,
                    x=x,
                    y=y,
                    dx=dx,
                    p=p,
                    q=q,
                    sum_boost_mu_num=sum_boost_mu_num,
                    sum_boost_mu_den=sum_boost_mu_den,
                    quartic_c_num=quartic_c_num,
                    quartic_c_den=quartic_c_den,
                    quintic_c_num=quintic_c_num,
                    quintic_c_den=quintic_c_den,
                )
                prev_k_inc_max = int(exact_in[c].k_inc_max)
                exact_in[c].add_exact_in(m)
                if m.ok:
                    outs[c] = m.amount_out
                    if c == "cpmm":
                        cpmm_out = int(m.amount_out)
                    elif c == "cubic_sum":
                        cubic_out = int(m.amount_out)

                    inc = m.k_after - m.k_before
                    w = {"x": int(x), "y": int(y), "dx": int(dx), "k_inc": int(inc)}
                    prev = k_inc_max_witness_in.get(c)
                    if int(inc) > prev_k_inc_max or (prev is None and int(inc) == prev_k_inc_max):
                        k_inc_max_witness_in[c] = w
                    elif int(inc) == prev_k_inc_max and prev is not None:
                        if _witness_key(w, ["x", "y", "dx"]) < _witness_key(prev, ["x", "y", "dx"]):
                            k_inc_max_witness_in[c] = w

                    if c in marginal_dx_for_one_out and dx > 0:
                        # Ratio of avg out-per-in to the dy=1 marginal out-per-in (1 / dx1):
                        # (out/dx) / (1/dx1) = out * dx1 / dx
                        slippage_in_sum[c][dx] += (float(m.amount_out) * float(marginal_dx_for_one_out[c])) / float(dx)
                        slippage_in_n[c][dx] += 1
            if outs:
                best = max(outs.values())
                winners = [c for c, v in outs.items() if v == best]
                if len(winners) == 1:
                    win_out[winners[0]] += 1
                else:
                    ties_out += 1

            if cpmm_out is not None and cubic_out is not None:
                diff = int(cubic_out) - int(cpmm_out)
                if diff > 0:
                    diff_exact_in_out_pos += 1
                elif diff < 0:
                    diff_exact_in_out_neg += 1
                else:
                    diff_exact_in_out_eq += 1
                _update_extreme(
                    extreme=diff_exact_in_out,
                    value=int(diff),
                    witness={"x": int(x), "y": int(y), "dx": int(dx), "cpmm_out": int(cpmm_out), "cubic_out": int(cubic_out)},
                    better="max",
                    key_fields=["x", "y", "dx"],
                )
                _update_extreme(
                    extreme=diff_exact_in_out,
                    value=int(diff),
                    witness={"x": int(x), "y": int(y), "dx": int(dx), "cpmm_out": int(cpmm_out), "cubic_out": int(cubic_out)},
                    better="min",
                    key_fields=["x", "y", "dx"],
                )

        marginal_in: dict[str, int] = {}
        if y > 1 and 1 in dy_list:
            for c in curves:
                mout1 = _safe_exact_out(
                    c,
                    x=x,
                    y=y,
                    dy=1,
                    p=p,
                    q=q,
                    sum_boost_mu_num=sum_boost_mu_num,
                    sum_boost_mu_den=sum_boost_mu_den,
                    quartic_c_num=quartic_c_num,
                    quartic_c_den=quartic_c_den,
                    quintic_c_num=quintic_c_num,
                    quintic_c_den=quintic_c_den,
                )
                if mout1.ok and mout1.amount_in > 0:
                    marginal_in[c] = int(mout1.amount_in)

        for dy in dy_list:
            if dy <= 0 or dy >= y:
                continue
            ins: dict[str, int] = {}
            cpmm_in = None
            cubic_in = None
            cpmm_gap = None
            cubic_gap = None
            for c in curves:
                m = _safe_exact_out(
                    c,
                    x=x,
                    y=y,
                    dy=dy,
                    p=p,
                    q=q,
                    sum_boost_mu_num=sum_boost_mu_num,
                    sum_boost_mu_den=sum_boost_mu_den,
                    quartic_c_num=quartic_c_num,
                    quartic_c_den=quartic_c_den,
                    quintic_c_num=quintic_c_num,
                    quintic_c_den=quintic_c_den,
                )
                prev_gap_max = int(exact_out[c].gap_max)
                prev_k_inc_max = int(exact_out[c].k_inc_max)
                exact_out[c].add_exact_out(m)
                if m.ok:
                    ins[c] = m.amount_in
                    if c == "cpmm":
                        cpmm_in = int(m.amount_in)
                        cpmm_gap = int(m.gap)
                    elif c == "cubic_sum":
                        cubic_in = int(m.amount_in)
                        cubic_gap = int(m.gap)

                    w_gap = {
                        "x": int(x),
                        "y": int(y),
                        "dy": int(dy),
                        "amount_in": int(m.amount_in),
                        "out_exec": int(m.out_exec),
                        "gap": int(m.gap),
                    }
                    prev_gap = gap_max_witness.get(c)
                    if int(m.gap) > prev_gap_max or (prev_gap is None and int(m.gap) == prev_gap_max):
                        gap_max_witness[c] = w_gap
                    elif int(m.gap) == prev_gap_max and prev_gap is not None:
                        if _witness_key(w_gap, ["x", "y", "dy"]) < _witness_key(prev_gap, ["x", "y", "dy"]):
                            gap_max_witness[c] = w_gap

                    inc = m.k_after - m.k_before
                    w_inc = {"x": int(x), "y": int(y), "dy": int(dy), "k_inc": int(inc)}
                    prev_inc = k_inc_max_witness_out.get(c)
                    if int(inc) > prev_k_inc_max or (prev_inc is None and int(inc) == prev_k_inc_max):
                        k_inc_max_witness_out[c] = w_inc
                    elif int(inc) == prev_k_inc_max and prev_inc is not None:
                        if _witness_key(w_inc, ["x", "y", "dy"]) < _witness_key(prev_inc, ["x", "y", "dy"]):
                            k_inc_max_witness_out[c] = w_inc

                    if c in marginal_in and dy > 0:
                        # Ratio of avg input-per-output (in/out) to the local marginal (dy=1) cost.
                        slippage_out_sum[c][dy] += float(m.amount_in) / float(dy * marginal_in[c])
                        slippage_out_n[c][dy] += 1
            if ins:
                best = min(ins.values())
                winners = [c for c, v in ins.items() if v == best]
                if len(winners) == 1:
                    win_in[winners[0]] += 1
                else:
                    ties_in += 1

            if cpmm_in is not None and cubic_in is not None:
                diff_in = int(cubic_in) - int(cpmm_in)
                if diff_in > 0:
                    diff_exact_out_in_pos += 1
                elif diff_in < 0:
                    diff_exact_out_in_neg += 1
                else:
                    diff_exact_out_in_eq += 1
                _update_extreme(
                    extreme=diff_exact_out_in,
                    value=int(diff_in),
                    witness={"x": int(x), "y": int(y), "dy": int(dy), "cpmm_in": int(cpmm_in), "cubic_in": int(cubic_in)},
                    better="max",
                    key_fields=["x", "y", "dy"],
                )
                _update_extreme(
                    extreme=diff_exact_out_in,
                    value=int(diff_in),
                    witness={"x": int(x), "y": int(y), "dy": int(dy), "cpmm_in": int(cpmm_in), "cubic_in": int(cubic_in)},
                    better="min",
                    key_fields=["x", "y", "dy"],
                )

            if cpmm_gap is not None and cubic_gap is not None:
                diff_gap = int(cubic_gap) - int(cpmm_gap)
                if diff_gap >= 0:
                    diff_exact_out_gap_nonneg += 1
                else:
                    diff_exact_out_gap_neg += 1
                _update_extreme(
                    extreme=diff_exact_out_gap,
                    value=int(diff_gap),
                    witness={
                        "x": int(x),
                        "y": int(y),
                        "dy": int(dy),
                        "cpmm_gap": int(cpmm_gap),
                        "cubic_gap": int(cubic_gap),
                    },
                    better="max",
                    key_fields=["x", "y", "dy"],
                )
                _update_extreme(
                    extreme=diff_exact_out_gap,
                    value=int(diff_gap),
                    witness={
                        "x": int(x),
                        "y": int(y),
                        "dy": int(dy),
                        "cpmm_gap": int(cpmm_gap),
                        "cubic_gap": int(cubic_gap),
                    },
                    better="min",
                    key_fields=["x", "y", "dy"],
                )

    return {
        "params": {"p": p, "q": q, "dx_list": dx_list, "dy_list": dy_list},
        "exact_in": {c: exact_in[c].to_json() for c in curves},
        "exact_out": {c: exact_out[c].to_json() for c in curves},
        "witnesses": {
            "exact_out_gap_max": gap_max_witness,
            "exact_in_k_increase_max": k_inc_max_witness_in,
            "exact_out_k_increase_max": k_inc_max_witness_out,
        },
        "slippage": {
            "exact_in_avg_price_over_marginal": {
                c: {
                    str(dx): (slippage_in_sum[c][dx] / slippage_in_n[c][dx]) if slippage_in_n[c][dx] else None
                    for dx in dx_list
                }
                for c in curves
            },
            "exact_out_avg_in_per_out_over_marginal": {
                c: {
                    str(dy): (slippage_out_sum[c][dy] / slippage_out_n[c][dy]) if slippage_out_n[c][dy] else None
                    for dy in dy_list
                }
                for c in curves
            },
        },
        "wins": {
            "higher_out_for_same_dx": win_out,
            "lower_in_for_same_dy": win_in,
            "ties_out": ties_out,
            "ties_in": ties_in,
        },
        "pairwise_vs_cpmm": {
            "exact_in_out_diff": {
                "count_pos": diff_exact_in_out_pos,
                "count_neg": diff_exact_in_out_neg,
                "count_eq": diff_exact_in_out_eq,
                "max": diff_exact_in_out.get("max"),
                "max_witness": diff_exact_in_out.get("max_witness"),
                "min": diff_exact_in_out.get("min"),
                "min_witness": diff_exact_in_out.get("min_witness"),
            },
            "exact_out_in_diff": {
                "count_pos": diff_exact_out_in_pos,
                "count_neg": diff_exact_out_in_neg,
                "count_eq": diff_exact_out_in_eq,
                "max": diff_exact_out_in.get("max"),
                "max_witness": diff_exact_out_in.get("max_witness"),
                "min": diff_exact_out_in.get("min"),
                "min_witness": diff_exact_out_in.get("min_witness"),
            },
            "exact_out_gap_diff": {
                "count_nonneg": diff_exact_out_gap_nonneg,
                "count_neg": diff_exact_out_gap_neg,
                "max": diff_exact_out_gap.get("max"),
                "max_witness": diff_exact_out_gap.get("max_witness"),
                "min": diff_exact_out_gap.get("min"),
                "min_witness": diff_exact_out_gap.get("min_witness"),
            },
        },
    }


def _parse_int_list(csv: str) -> list[int]:
    out: list[int] = []
    for part in csv.split(","):
        part = part.strip()
        if not part:
            continue
        out.append(int(part))
    if not out:
        raise ValueError("empty list")
    return out


def main() -> int:
    ap = argparse.ArgumentParser(
        description="Deterministic curve comparison sweep (CPMM vs cubic-sum vs quadratic vs sum-boost vs quartic-blend vs quintic-blend)"
    )
    ap.add_argument("--grid-min", type=int, default=5)
    ap.add_argument("--grid-max", type=int, default=50)
    ap.add_argument("--grid-step", type=int, default=1)
    ap.add_argument("--balanced", type=str, default="10,20,50,100,200,500,1000")
    ap.add_argument("--ratios", type=str, default="5,10")
    ap.add_argument("--dx", type=str, default="1,2,5,10")
    ap.add_argument("--dy", type=str, default="1,2,5,10")
    ap.add_argument("--p", type=int, default=1)
    ap.add_argument("--q", type=int, default=1)
    ap.add_argument("--no-quadratic", action="store_true")
    ap.add_argument("--no-sum-boost", action="store_true")
    ap.add_argument("--no-quartic-blend", action="store_true")
    ap.add_argument("--no-quintic-blend", action="store_true")
    ap.add_argument("--sum-boost-mu-num", type=int, default=200)
    ap.add_argument("--sum-boost-mu-den", type=int, default=10_000)
    ap.add_argument("--quartic-c-num", type=int, default=8)
    ap.add_argument("--quartic-c-den", type=int, default=1)
    ap.add_argument("--quintic-c-num", type=int, default=2)
    ap.add_argument("--quintic-c-den", type=int, default=1)
    ap.add_argument("--progress-every", type=int, default=0)
    ap.add_argument("--out", type=str, default="")
    args = ap.parse_args()

    dx_list = _parse_int_list(args.dx)
    dy_list = _parse_int_list(args.dy)
    balanced = _parse_int_list(args.balanced)
    ratios = _parse_int_list(args.ratios)

    if args.grid_min <= 0 or args.grid_max <= 0 or args.grid_step <= 0:
        raise SystemExit("grid values must be positive")
    if args.grid_min > args.grid_max:
        raise SystemExit("grid-min must be <= grid-max")
    if args.p <= 0 or args.q <= 0:
        raise SystemExit("p and q must be positive")

    include_quadratic = not args.no_quadratic
    include_sum_boost = not args.no_sum_boost
    include_quartic_blend = not args.no_quartic_blend
    include_quintic_blend = not args.no_quintic_blend

    if args.sum_boost_mu_num < 0 or args.sum_boost_mu_den <= 0:
        raise SystemExit("sum-boost mu params must satisfy mu_num>=0, mu_den>0")
    if args.quartic_c_num < 0 or args.quartic_c_den <= 0:
        raise SystemExit("quartic c params must satisfy c_num>=0, c_den>0")
    if args.quintic_c_num < 0 or args.quintic_c_den <= 0:
        raise SystemExit("quintic c params must satisfy c_num>=0, c_den>0")
    start = time.perf_counter()

    grid_pairs = list(_iter_pairs_grid(min_r=args.grid_min, max_r=args.grid_max, step=args.grid_step))
    balanced_pairs = list(_iter_pairs_balanced(reserves=balanced))
    ratio_pairs = list(_iter_pairs_ratio(reserves=balanced, ratios=ratios))

    report = {
        "schema": "zenodex/curve-sweep/v1",
        "timestamp_unix": int(time.time()),
        "grid": {
            "min": args.grid_min,
            "max": args.grid_max,
            "step": args.grid_step,
            "pairs": len(grid_pairs),
        },
        "scenarios": {
            "small_grid": run_sweep(
                pairs=grid_pairs,
                dx_list=dx_list,
                dy_list=dy_list,
                p=args.p,
                q=args.q,
                include_quadratic=include_quadratic,
                include_sum_boost=include_sum_boost,
                include_quartic_blend=include_quartic_blend,
                include_quintic_blend=include_quintic_blend,
                sum_boost_mu_num=int(args.sum_boost_mu_num),
                sum_boost_mu_den=int(args.sum_boost_mu_den),
                quartic_c_num=int(args.quartic_c_num),
                quartic_c_den=int(args.quartic_c_den),
                quintic_c_num=int(args.quintic_c_num),
                quintic_c_den=int(args.quintic_c_den),
                progress_every=int(args.progress_every),
            ),
            "balanced": run_sweep(
                pairs=balanced_pairs,
                dx_list=dx_list,
                dy_list=dy_list,
                p=args.p,
                q=args.q,
                include_quadratic=include_quadratic,
                include_sum_boost=include_sum_boost,
                include_quartic_blend=include_quartic_blend,
                include_quintic_blend=include_quintic_blend,
                sum_boost_mu_num=int(args.sum_boost_mu_num),
                sum_boost_mu_den=int(args.sum_boost_mu_den),
                quartic_c_num=int(args.quartic_c_num),
                quartic_c_den=int(args.quartic_c_den),
                quintic_c_num=int(args.quintic_c_num),
                quintic_c_den=int(args.quintic_c_den),
                progress_every=0,
            ),
            "ratio_lines": run_sweep(
                pairs=ratio_pairs,
                dx_list=dx_list,
                dy_list=dy_list,
                p=args.p,
                q=args.q,
                include_quadratic=include_quadratic,
                include_sum_boost=include_sum_boost,
                include_quartic_blend=include_quartic_blend,
                include_quintic_blend=include_quintic_blend,
                sum_boost_mu_num=int(args.sum_boost_mu_num),
                sum_boost_mu_den=int(args.sum_boost_mu_den),
                quartic_c_num=int(args.quartic_c_num),
                quartic_c_den=int(args.quartic_c_den),
                quintic_c_num=int(args.quintic_c_num),
                quintic_c_den=int(args.quintic_c_den),
                progress_every=0,
            ),
        },
        "runtime_s": time.perf_counter() - start,
    }

    payload = json.dumps(report, indent=2, sort_keys=True)
    if args.out:
        out_path = Path(args.out)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(payload + "\n", encoding="utf-8")
        print(f"Wrote {out_path}")
    else:
        print(payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
