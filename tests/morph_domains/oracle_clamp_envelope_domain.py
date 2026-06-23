from __future__ import annotations

"""MORPH domain: conservative oracle-clamp envelope discovery (ZenoDEX).

This domain targets the LP-assisted oracle-manipulation pattern modeled in
`tools/perp_oracle_manipulation_lp_sweep.py`.

Witness schema:
- JSON object with `schema=zenodex/oracle-clamp-envelope-rule/v1`.
- Interpreted as a rule mapping (reserve_quote, fee_bps, protocol_fee_share_bps)
  to a chosen `max_move_bps`.

Acceptance contract (falsify-first):
- For every (rq, fee_bps, pfs_bps) triple on the configured base grid, the rule-chosen
  `max_move_bps` must admit NO profitable attack witness under the bounded sweep.

Check2 is intentionally different (independent):
- Same semantics as Check (same base grid, same max_move_bps choices).
- Alternate loop order for the bounded sweep search, to reduce correlated bugs.
"""

import json
from dataclasses import dataclass
from typing import Iterable

from morph.domain import ProblemState
from morph.proofs import Transition, VerifyResult
from morph.triviality_safe import CertificateOnlyDomain, CheckResult

from tools.perp_oracle_manipulation_lp_sweep import (  # type: ignore[import-not-found]
    OracleManipLPWitness,
    _eval_attack,
    _min_trade_in_for_fee,
    find_profitable_attack,
)


BPS_DENOM = 10_000

_SIGMA0_SCHEMA = "zenodex/oracle-clamp-envelope-sigma0/v1"
_RULE_SCHEMA = "zenodex/oracle-clamp-envelope-rule/v1"


def _as_int_tuple(xs: Iterable[int]) -> tuple[int, ...]:
    out: list[int] = []
    for x in xs:
        out.append(int(x))
    return tuple(out)


@dataclass(frozen=True)
class ClampEnvelopeSigma0:
    reserve_base: int
    reserve_quote_values: tuple[int, ...]
    fee_bps_values: tuple[int, ...]
    protocol_fee_share_values: tuple[int, ...]
    lp_share_bps: int
    max_r: int
    max_pos_abs: int
    target_profit_quote: int
    protocol_fee_rounding: str
    min_claimed_points: int

    # Check2 extensions.
    max_r_check2: int
    max_pos_abs_check2: int

    @classmethod
    def from_problem_state(cls, state: ProblemState) -> "ClampEnvelopeSigma0":
        try:
            obj = json.loads(state.representation.text)
        except Exception as exc:  # pragma: no cover
            raise ValueError(f"bad sigma0 JSON: {exc}") from exc
        if not isinstance(obj, dict) or str(obj.get("schema", "")) != _SIGMA0_SCHEMA:
            raise ValueError("bad sigma0 schema")

        cfg = cls(
            reserve_base=int(obj["reserve_base"]),
            reserve_quote_values=_as_int_tuple(obj["reserve_quote_values"]),
            fee_bps_values=_as_int_tuple(obj["fee_bps_values"]),
            protocol_fee_share_values=_as_int_tuple(obj["protocol_fee_share_values"]),
            lp_share_bps=int(obj["lp_share_bps"]),
            max_r=int(obj["max_r"]),
            max_pos_abs=int(obj["max_pos_abs"]),
            target_profit_quote=int(obj.get("target_profit_quote", 1)),
            protocol_fee_rounding=str(obj.get("protocol_fee_rounding", "ceil")),
            min_claimed_points=int(obj.get("min_claimed_points", 1)),
            max_r_check2=int(obj.get("max_r_check2", obj["max_r"])),
            max_pos_abs_check2=int(obj.get("max_pos_abs_check2", obj["max_pos_abs"])),
        )
        cfg._validate()
        return cfg

    def _validate(self) -> None:
        if self.reserve_base <= 0:
            raise ValueError("reserve_base must be positive")
        if not self.reserve_quote_values:
            raise ValueError("reserve_quote_values must be non-empty")
        if not self.fee_bps_values:
            raise ValueError("fee_bps_values must be non-empty")
        if not self.protocol_fee_share_values:
            raise ValueError("protocol_fee_share_values must be non-empty")
        if not (0 <= self.lp_share_bps <= BPS_DENOM):
            raise ValueError("lp_share_bps out of range")
        if self.max_r < 1 or self.max_r_check2 < 1:
            raise ValueError("max_r must be >= 1")
        if self.max_pos_abs < 1 or self.max_pos_abs_check2 < 1:
            raise ValueError("max_pos_abs must be >= 1")
        if self.target_profit_quote < 1:
            raise ValueError("target_profit_quote must be >= 1")
        pfr = str(self.protocol_fee_rounding).strip().lower()
        if pfr not in {"floor", "ceil"}:
            raise ValueError("bad protocol_fee_rounding")
        if self.min_claimed_points < 1:
            raise ValueError("min_claimed_points must be >= 1")
        for rq in self.reserve_quote_values:
            if rq <= 0:
                raise ValueError("reserve_quote_values must be positive")
        for fee in self.fee_bps_values:
            if not (0 <= fee < BPS_DENOM):
                raise ValueError("fee_bps out of range")
        for pfs in self.protocol_fee_share_values:
            if not (0 <= pfs <= BPS_DENOM):
                raise ValueError("protocol_fee_share_bps out of range")


@dataclass(frozen=True)
class ClampEnvelopeRule:
    rq_le_200: int
    base_bound: int
    pfs_low_threshold: int
    fee_hi_threshold: int
    rq_ge_fee_hi: int
    rq_ge_high: int
    tight_bound: int
    tighten_fee_hi: bool
    tighten_high_rq: bool
    tighten_requires_low_pfs: bool

    @classmethod
    def from_witness(cls, witness: str) -> "ClampEnvelopeRule":
        obj = json.loads(str(witness))
        if not isinstance(obj, dict) or str(obj.get("schema", "")) != _RULE_SCHEMA:
            raise ValueError("bad witness schema")
        rule = cls(
            rq_le_200=int(obj["rq_le_200"]),
            base_bound=int(obj["base_bound"]),
            pfs_low_threshold=int(obj.get("pfs_low_threshold", 5_000)),
            fee_hi_threshold=int(obj.get("fee_hi_threshold", 30)),
            rq_ge_fee_hi=int(obj.get("rq_ge_fee_hi", 17_000)),
            rq_ge_high=int(obj.get("rq_ge_high", 24_000)),
            tight_bound=int(obj.get("tight_bound", 150)),
            tighten_fee_hi=bool(obj.get("tighten_fee_hi", False)),
            tighten_high_rq=bool(obj.get("tighten_high_rq", False)),
            tighten_requires_low_pfs=bool(obj.get("tighten_requires_low_pfs", True)),
        )
        rule._validate()
        return rule

    def _validate(self) -> None:
        if self.rq_le_200 < 0:
            raise ValueError("rq_le_200 must be >= 0")
        for b in (self.base_bound, self.tight_bound):
            if not (0 <= b <= 200):
                raise ValueError("bounds must be within [0,200]")
        if not (0 <= self.pfs_low_threshold <= BPS_DENOM + 1):
            raise ValueError("pfs_low_threshold out of range")
        if not (0 <= self.fee_hi_threshold < BPS_DENOM):
            raise ValueError("fee_hi_threshold out of range")
        if self.rq_ge_fee_hi < 0 or self.rq_ge_high < 0:
            raise ValueError("rq thresholds must be >= 0")

    def bound(self, *, reserve_quote: int, fee_bps: int, protocol_fee_share_bps: int) -> int:
        bound = 200 if reserve_quote <= self.rq_le_200 else self.base_bound

        low_pfs = protocol_fee_share_bps < self.pfs_low_threshold
        tight_ok = (not self.tighten_requires_low_pfs) or low_pfs

        if self.tighten_high_rq and tight_ok and reserve_quote >= self.rq_ge_high:
            bound = min(bound, self.tight_bound)
        if self.tighten_fee_hi and tight_ok and fee_bps >= self.fee_hi_threshold and reserve_quote >= self.rq_ge_fee_hi:
            bound = min(bound, self.tight_bound)
        return int(bound)


def _find_profitable_attack_alt(
    *,
    reserve_base: int,
    reserve_quote: int,
    fee_bps: int,
    protocol_fee_share_bps: int,
    lp_share_bps: int,
    max_r: int,
    max_pos_abs: int,
    max_move_bps: int,
    target_profit_quote: int,
    protocol_fee_rounding: str,
) -> OracleManipLPWitness | None:
    # Alternate loop order vs tools.find_profitable_attack: trade_in outermost.
    if not (0 <= fee_bps < BPS_DENOM):
        raise ValueError("fee_bps out of range")
    if max_r < 1:
        raise ValueError("bad max_r")
    if max_pos_abs < 1:
        raise ValueError("bad max_pos_abs")

    min_trade_in = _min_trade_in_for_fee(fee_bps=fee_bps)
    for trade_in in range(min_trade_in, max_r + 1):
        for abs_pos in range(1, max_pos_abs + 1):
            for sign in (1, -1):
                pos = int(sign * abs_pos)
                try:
                    w = _eval_attack(
                        reserve_base=reserve_base,
                        reserve_quote=reserve_quote,
                        fee_bps=fee_bps,
                        protocol_fee_share_bps=protocol_fee_share_bps,
                        lp_share_bps=lp_share_bps,
                        pos_base=pos,
                        trade_in=trade_in,
                        max_move_bps=max_move_bps,
                        max_pos_abs=max_pos_abs,
                        max_r=max_r,
                        confirm_with_kernel=False,
                        protocol_fee_rounding=protocol_fee_rounding,
                    )
                except Exception:
                    continue
                if w.net_profit_quote < target_profit_quote:
                    continue
                try:
                    w2 = _eval_attack(
                        reserve_base=reserve_base,
                        reserve_quote=reserve_quote,
                        fee_bps=fee_bps,
                        protocol_fee_share_bps=protocol_fee_share_bps,
                        lp_share_bps=lp_share_bps,
                        pos_base=pos,
                        trade_in=trade_in,
                        max_move_bps=max_move_bps,
                        max_pos_abs=max_pos_abs,
                        max_r=max_r,
                        confirm_with_kernel=True,
                        protocol_fee_rounding=protocol_fee_rounding,
                    )
                except Exception:
                    continue
                if w2.net_profit_quote >= target_profit_quote:
                    return w2
    return None


class OracleClampEnvelopeDomain(CertificateOnlyDomain):
    def __init__(self, **_kwargs: object) -> None:
        self._sigma0: ClampEnvelopeSigma0 | None = None
        self._safe_cache_check: dict[tuple[int, int, int, int], bool] = {}
        self._safe_cache_check2: dict[tuple[int, int, int, int], bool] = {}

    def _cfg(self, state: ProblemState) -> ClampEnvelopeSigma0:
        if self._sigma0 is None:
            self._sigma0 = ClampEnvelopeSigma0.from_problem_state(state)
        return self._sigma0

    def checker_backends(self) -> dict[str, str]:
        return {
            "attack_sweep_check": "tools.perp_oracle_manipulation_lp_sweep.find_profitable_attack",
            "attack_sweep_check2": "tests.morph_domains.oracle_clamp_envelope_domain._find_profitable_attack_alt",
        }

    def independence_test(self) -> str:
        return json.dumps(
            {
                "check": "find_profitable_attack (pos-major order)",
                "check2": "alt order (trade-major) + kernel-confirm",
            },
            sort_keys=True,
            separators=(",", ":"),
        )

    def witness_from_solution(self, solution) -> str:  # type: ignore[override]
        return str(getattr(solution, "artifact", "") or "")

    def _is_safe_check(self, cfg: ClampEnvelopeSigma0, *, rq: int, fee_bps: int, pfs_bps: int, max_move_bps: int) -> bool:
        key = (int(rq), int(fee_bps), int(pfs_bps), int(max_move_bps))
        cached = self._safe_cache_check.get(key)
        if cached is not None:
            return cached
        w = find_profitable_attack(
            reserve_base=cfg.reserve_base,
            reserve_quote=int(rq),
            fee_bps=int(fee_bps),
            protocol_fee_share_bps=int(pfs_bps),
            lp_share_bps=int(cfg.lp_share_bps),
            max_r=int(cfg.max_r),
            max_pos_abs=int(cfg.max_pos_abs),
            max_move_bps=int(max_move_bps),
            target_profit_quote=int(cfg.target_profit_quote),
            protocol_fee_rounding=str(cfg.protocol_fee_rounding),
        )
        safe = w is None
        self._safe_cache_check[key] = safe
        return safe

    def _is_safe_check2(self, cfg: ClampEnvelopeSigma0, *, rq: int, fee_bps: int, pfs_bps: int, max_move_bps: int) -> bool:
        key = (int(rq), int(fee_bps), int(pfs_bps), int(max_move_bps))
        cached = self._safe_cache_check2.get(key)
        if cached is not None:
            return cached
        w = _find_profitable_attack_alt(
            reserve_base=cfg.reserve_base,
            reserve_quote=int(rq),
            fee_bps=int(fee_bps),
            protocol_fee_share_bps=int(pfs_bps),
            lp_share_bps=int(cfg.lp_share_bps),
            max_r=int(cfg.max_r_check2),
            max_pos_abs=int(cfg.max_pos_abs_check2),
            max_move_bps=int(max_move_bps),
            target_profit_quote=int(cfg.target_profit_quote),
            protocol_fee_rounding=str(cfg.protocol_fee_rounding),
        )
        safe = w is None
        self._safe_cache_check2[key] = safe
        return safe

    def _claimed_points_count(self, cfg: ClampEnvelopeSigma0) -> int:
        return int(len(cfg.reserve_quote_values) * len(cfg.fee_bps_values) * len(cfg.protocol_fee_share_values))

    def check(self, state: ProblemState, witness: str) -> CheckResult:
        try:
            cfg = self._cfg(state)
            rule = ClampEnvelopeRule.from_witness(witness)
            if self._claimed_points_count(cfg) < cfg.min_claimed_points:
                return CheckResult.FAIL
            for rq in cfg.reserve_quote_values:
                for fee in cfg.fee_bps_values:
                    for pfs in cfg.protocol_fee_share_values:
                        m = rule.bound(reserve_quote=int(rq), fee_bps=int(fee), protocol_fee_share_bps=int(pfs))
                        if not self._is_safe_check(cfg, rq=int(rq), fee_bps=int(fee), pfs_bps=int(pfs), max_move_bps=m):
                            return CheckResult.FAIL
            return CheckResult.PASS
        except Exception:
            return CheckResult.FAIL

    def check2(self, state: ProblemState, witness: str) -> CheckResult:
        try:
            cfg = self._cfg(state)
            rule = ClampEnvelopeRule.from_witness(witness)
            if self._claimed_points_count(cfg) < cfg.min_claimed_points:
                return CheckResult.FAIL
            for rq in cfg.reserve_quote_values:
                for fee in cfg.fee_bps_values:
                    for pfs in cfg.protocol_fee_share_values:
                        m = rule.bound(reserve_quote=int(rq), fee_bps=int(fee), protocol_fee_share_bps=int(pfs))
                        if not self._is_safe_check2(cfg, rq=int(rq), fee_bps=int(fee), pfs_bps=int(pfs), max_move_bps=m):
                            return CheckResult.FAIL
            return CheckResult.PASS
        except Exception:
            return CheckResult.FAIL

    def verify_transition(self, parent: ProblemState, transition: Transition) -> VerifyResult:
        # Witness-only (Solve) tactics must not mutate the ProblemState.
        if transition.child != parent:
            return VerifyResult.FAIL
        return VerifyResult.PASS
