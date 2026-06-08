"""
Fail-closed Tau validation gate (imperative shell).

This module is IO by design: it runs the `tau` binary to validate witnesses
against Tau specs. Any error/timeout/missing tool => reject.

IMPORTANT:
- This relies on an external executable and wall-clock timeouts.
- Treat it as off-chain/operator tooling unless Tau execution is guaranteed
  deterministic and uniformly available across validators.

Internal structure (refactor): `validate_settlement_swaps` is decomposed into
five named concerns, each a thin module-level helper so the assurance-critical
field-level binding stays explicit and reviewable:

  (a) swap projection      -> `_project_swap_bindings`
  (b) Tau input construction -> the `build_*_step` builders (in `tau_witness`)
                                plus `_build_settlement_gate`
  (c) tool invocation      -> `_run_segment_gates` / `_run_settlement_gate`
  (d) result parsing       -> `_require_gate_ok` / `_require_single_gate_ok`
  (e) fallback policy       -> `_resolve_tau_bin` + the top-level `except`

The EXACT keyword->input binding (which value flows to which Tau input) and the
EXACT fail-closed fallback are behavior-preserving relative to the prior inline
implementation.
"""

from __future__ import annotations

import os
from dataclasses import dataclass, field, replace
from typing import Dict, List, Optional, Tuple

from ..core.liquidity import create_pool
from ..core.settlement import Fill, FillAction, Settlement
from ..state.intents import Intent, IntentKind
from ..state.pools import PoolState
from .tau_runner import find_tau_bin, run_tau_spec_steps
from .tau_witness import (
    SETTLEMENT_PRICE_RAILS_ALIGNED_V1,
    SETTLEMENT_V5_ALIGNED_COMPACT_BUNDLE,
    SWAP_BV32_SAFE_RANGE_GUARD_V1,
    SWAP_EXACT_IN_PROOF_GATE_V1,
    SWAP_EXACT_IN_V1,
    SWAP_EXACT_OUT_V1,
    SWAP_EXACT_OUT_PROOF_GATE_V1,
    SWAP_EXACT_IN_V4,
    SWAP_EXACT_OUT_V4,
    TauSpecRef,
    build_settlement_price_rails_aligned_v1_step,
    build_settlement_v5_aligned_compact_bundle_step,
    build_swap_bv32_safe_range_guard_v1_step,
    build_swap_exact_in_proof_gate_v1_step,
    build_swap_exact_in_v1_step,
    build_swap_exact_out_v1_step,
    build_swap_exact_out_proof_gate_v1_step,
    build_swap_exact_in_v4_step,
    build_swap_exact_out_v4_step,
)


@dataclass(frozen=True)
class TauSettlementModuleFlags:
    cpmm_ok: int = 1
    balance_ok: int = 1
    token_ok: int = 1
    buyback_floor_ok: int = 1
    buyback_floor_fixedpoint_ok: int = 1
    rebate_ok: int = 1
    lock_weight_ok: int = 1
    proof_ok: int = 1
    binding_ok: int = 1


@dataclass(frozen=True)
class TauGateConfig:
    """
    Controls whether and how the Tau gate runs.

    Default is disabled to avoid making `tau` a hard runtime dependency.
    When enabled, prefer setting `tau_bin` explicitly for determinism.
    """

    enabled: bool = False
    timeout_s: float = 2.0
    tau_bin: Optional[str] = None
    allow_path_lookup: bool = False
    swap_profile: str = "legacy_auto"
    settlement_profile: str = "off"
    settlement_price_history: Optional[Tuple[int, int, int]] = None
    settlement_module_flags: Optional[TauSettlementModuleFlags] = None


# Sentinel returned by per-fill processing to mean "no Tau bindings, keep going".
_SKIP_FILL: List[Tuple[TauSpecRef, Dict[str, int]]] = []


def _require_gate_ok(
    outputs_by_step: Dict[int, Dict[str, int]],
    *,
    gate_output: str,
    intent_ids: List[str],
) -> Tuple[bool, Optional[str]]:
    for idx, intent_id in enumerate(intent_ids):
        out = outputs_by_step.get(idx, {})
        value = out.get(gate_output)
        if value is None:
            return False, f"Tau missing {gate_output} for step {idx} (intent {intent_id})"
        if int(value) != 1:
            return False, f"Tau gate failed ({gate_output}=0) for step {idx} (intent {intent_id})"
    return True, None


def _require_single_gate_ok(
    outputs_by_step: Dict[int, Dict[str, int]],
    *,
    spec_ref: TauSpecRef,
    label: str,
) -> Tuple[bool, Optional[str]]:
    out = outputs_by_step.get(0, {})
    value = out.get(spec_ref.gate_output)
    if value is None:
        return False, f"Tau missing {spec_ref.gate_output} for {label}"
    if int(value) != 1:
        return False, f"Tau gate failed ({spec_ref.gate_output}=0) for {label}"
    return True, None


def _intent_id_to_u64(intent_id: str) -> int:
    if not isinstance(intent_id, str) or not intent_id.startswith("0x") or len(intent_id) <= 2:
        raise ValueError(f"invalid intent_id for Tau witness: {intent_id!r}")
    return int(intent_id, 16) & 0xFFFFFFFFFFFFFFFF


# ----------------------------------------------------------------------------- #
# Reserve book: the mutable per-pool snapshot used to thread reserve transitions
# through the settlement so each swap sees the reserves left by the prior one.
# ----------------------------------------------------------------------------- #
@dataclass
class _ReserveBook:
    pre_pools: Dict[str, PoolState]
    pools_mut: Dict[str, PoolState] = field(default_factory=dict)

    def get_mut(self, pool_id: str) -> Optional[PoolState]:
        pool = self.pools_mut.get(pool_id)
        if pool is not None:
            return pool
        pre = self.pre_pools.get(pool_id)
        if pre is None:
            return None
        pool = replace(pre)
        self.pools_mut[pool_id] = pool
        return pool

    def exists(self, pool_id: str) -> bool:
        return pool_id in self.pools_mut or pool_id in self.pre_pools


# ----------------------------------------------------------------------------- #
# (b/swap-input) Per-pool segment batching.
#
# Segments preserve per-pool execution order (the only order that can affect
# reserve transitions). They may span across unrelated fills from other pools.
# ----------------------------------------------------------------------------- #
@dataclass
class _SwapSegment:
    pool_id: str
    spec_ref: TauSpecRef
    steps: List[Dict[str, int]]
    intent_ids: List[str]


@dataclass
class _SegmentBuilder:
    segments_in_order: List[_SwapSegment] = field(default_factory=list)
    last_segment_by_pool: Dict[str, _SwapSegment] = field(default_factory=dict)

    def append(self, *, pool_id: str, spec_ref: TauSpecRef, step: Dict[str, int], intent_id: str) -> None:
        seg = self.last_segment_by_pool.get(pool_id)
        if seg is None or seg.spec_ref is not spec_ref:
            seg = _SwapSegment(pool_id=pool_id, spec_ref=spec_ref, steps=[], intent_ids=[])
            self.last_segment_by_pool[pool_id] = seg
            self.segments_in_order.append(seg)
        seg.steps.append(step)
        seg.intent_ids.append(intent_id)


# ----------------------------------------------------------------------------- #
# (a) Reserve application for reserve-affecting NON-swap fills.
#
# We only validate swap transitions, but we must still apply reserve-affecting
# non-swap fills (create pool, add/remove liquidity) to keep the reserve path
# correct for later swaps in the same pool. Returns an error message on reject,
# or None on success (state mutated in place on the reserve book).
# ----------------------------------------------------------------------------- #
def _apply_create_pool(intent: Intent, book: _ReserveBook) -> Optional[str]:
    asset0 = intent.get_field("asset0")
    asset1 = intent.get_field("asset1")
    fee_bps = intent.get_field("fee_bps")
    amount0 = intent.get_field("amount0")
    amount1 = intent.get_field("amount1")
    created_at = intent.get_field("created_at", 0)
    if any(v is None for v in (asset0, asset1, fee_bps, amount0, amount1)):
        return f"CREATE_POOL missing params for intent {intent.intent_id}"
    pool_id, pool_state, _lp_minted = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=amount0,
        amount1=amount1,
        fee_bps=fee_bps,
        creator_pubkey=intent.sender_pubkey,
        created_at=created_at,
    )
    if book.exists(pool_id):
        return f"CREATE_POOL conflicts with existing pool: {pool_id}"
    book.pools_mut[pool_id] = pool_state
    return None


def _apply_add_liquidity(intent: Intent, fill: Fill, pool: PoolState, pool_id: str, book: _ReserveBook) -> Optional[str]:
    amount0_used = getattr(fill, "amount0_used", None)
    amount1_used = getattr(fill, "amount1_used", None)
    if not isinstance(amount0_used, int) or isinstance(amount0_used, bool) or amount0_used <= 0:
        return f"Invalid amount0_used for intent {intent.intent_id}: {amount0_used!r}"
    if not isinstance(amount1_used, int) or isinstance(amount1_used, bool) or amount1_used <= 0:
        return f"Invalid amount1_used for intent {intent.intent_id}: {amount1_used!r}"
    pool.reserve0 = int(pool.reserve0) + int(amount0_used)
    pool.reserve1 = int(pool.reserve1) + int(amount1_used)
    book.pools_mut[pool_id] = pool
    return None


def _apply_remove_liquidity(intent: Intent, fill: Fill, pool: PoolState, pool_id: str, book: _ReserveBook) -> Optional[str]:
    amount0_out = getattr(fill, "amount0_out", None)
    amount1_out = getattr(fill, "amount1_out", None)
    if not isinstance(amount0_out, int) or isinstance(amount0_out, bool) or amount0_out <= 0:
        return f"Invalid amount0_out for intent {intent.intent_id}: {amount0_out!r}"
    if not isinstance(amount1_out, int) or isinstance(amount1_out, bool) or amount1_out <= 0:
        return f"Invalid amount1_out for intent {intent.intent_id}: {amount1_out!r}"
    pool.reserve0 = int(pool.reserve0) - int(amount0_out)
    pool.reserve1 = int(pool.reserve1) - int(amount1_out)
    book.pools_mut[pool_id] = pool
    return None


# ----------------------------------------------------------------------------- #
# (a) Swap projection: bind the swap fill's fields to Tau input steps.
#
# Returns (bindings, None) on success, where `bindings` is a list of
# (spec_ref, step) to validate in order; or (None, error_message) on reject.
#
# CRITICAL: the EXACT keyword->value binding below is the assurance contract.
# A mutation that reorders which value flows to which builder keyword MUST
# change the emitted step dict (and therefore the gate result). Do NOT permute.
# ----------------------------------------------------------------------------- #
def _project_exact_in_bindings(
    *,
    intent: Intent,
    reserve_in: int,
    reserve_out: int,
    amount_in: int,
    amount_out: int,
    fee_bps: int,
    swap_profile: str,
) -> Tuple[Optional[List[Tuple[TauSpecRef, Dict[str, int]]]], Optional[str]]:
    min_amount_out = intent.get_field("min_amount_out", 0)
    if not isinstance(min_amount_out, int) or isinstance(min_amount_out, bool) or min_amount_out < 0:
        return None, f"Invalid min_amount_out for intent {intent.intent_id}: {min_amount_out!r}"
    new_reserve_in = reserve_in + amount_in
    new_reserve_out = reserve_out - amount_out

    if swap_profile == "proof_gate_range_guard":
        return [
            (
                SWAP_EXACT_IN_PROOF_GATE_V1,
                build_swap_exact_in_proof_gate_v1_step(
                    reserve_in=reserve_in,
                    reserve_out=reserve_out,
                    amount_in=amount_in,
                    fee_bps=fee_bps,
                    min_amount_out=min_amount_out,
                    amount_out=amount_out,
                    new_reserve_in=new_reserve_in,
                    new_reserve_out=new_reserve_out,
                ),
            ),
            (
                SWAP_BV32_SAFE_RANGE_GUARD_V1,
                build_swap_bv32_safe_range_guard_v1_step(
                    reserve_in=reserve_in,
                    reserve_out=reserve_out,
                    delta_primary=amount_in,
                    delta_secondary=amount_out,
                    new_reserve_in=new_reserve_in,
                    new_reserve_out=new_reserve_out,
                ),
            ),
        ], None

    # legacy_auto: v4 is sound but intentionally bounded (safe-range guard <= 0xFFFF).
    use_v4 = all(
        isinstance(v, int) and not isinstance(v, bool) and 0 <= v <= 0xFFFF
        for v in (reserve_in, reserve_out, amount_in, min_amount_out, amount_out, new_reserve_in, new_reserve_out)
    )
    spec_ref = SWAP_EXACT_IN_V4 if use_v4 else SWAP_EXACT_IN_V1
    builder = build_swap_exact_in_v4_step if use_v4 else build_swap_exact_in_v1_step
    step = builder(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_in=amount_in,
        fee_bps=fee_bps,
        min_amount_out=min_amount_out,
        amount_out=amount_out,
        new_reserve_in=new_reserve_in,
        new_reserve_out=new_reserve_out,
    )
    return [(spec_ref, step)], None


def _project_exact_out_bindings(
    *,
    intent: Intent,
    reserve_in: int,
    reserve_out: int,
    amount_in: int,
    amount_out: int,
    fee_bps: int,
    swap_profile: str,
) -> Tuple[Optional[List[Tuple[TauSpecRef, Dict[str, int]]]], Optional[str]]:
    max_amount_in = intent.get_field("max_amount_in", 0)
    if not isinstance(max_amount_in, int) or isinstance(max_amount_in, bool) or max_amount_in < 0:
        return None, f"Invalid max_amount_in for intent {intent.intent_id}: {max_amount_in!r}"
    new_reserve_in = reserve_in + amount_in
    new_reserve_out = reserve_out - amount_out

    if swap_profile == "proof_gate_range_guard":
        return [
            (
                SWAP_EXACT_OUT_PROOF_GATE_V1,
                build_swap_exact_out_proof_gate_v1_step(
                    reserve_in=reserve_in,
                    reserve_out=reserve_out,
                    amount_out=amount_out,
                    fee_bps=fee_bps,
                    max_amount_in=max_amount_in,
                    amount_in=amount_in,
                    new_reserve_in=new_reserve_in,
                    new_reserve_out=new_reserve_out,
                ),
            ),
            (
                SWAP_BV32_SAFE_RANGE_GUARD_V1,
                build_swap_bv32_safe_range_guard_v1_step(
                    reserve_in=reserve_in,
                    reserve_out=reserve_out,
                    delta_primary=amount_out,
                    delta_secondary=amount_in,
                    new_reserve_in=new_reserve_in,
                    new_reserve_out=new_reserve_out,
                ),
            ),
        ], None

    use_v4 = all(
        isinstance(v, int) and not isinstance(v, bool) and 0 <= v <= 0xFFFF
        for v in (reserve_in, reserve_out, amount_out, max_amount_in, amount_in, new_reserve_in, new_reserve_out)
    )
    spec_ref = SWAP_EXACT_OUT_V4 if use_v4 else SWAP_EXACT_OUT_V1
    builder = build_swap_exact_out_v4_step if use_v4 else build_swap_exact_out_v1_step
    step = builder(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_out=amount_out,
        fee_bps=fee_bps,
        max_amount_in=max_amount_in,
        amount_in=amount_in,
        new_reserve_in=new_reserve_in,
        new_reserve_out=new_reserve_out,
    )
    return [(spec_ref, step)], None


def _process_swap_fill(
    *,
    intent: Intent,
    fill: Fill,
    pool: PoolState,
    pool_id: str,
    book: _ReserveBook,
    swap_profile: str,
) -> Tuple[Optional[List[Tuple[TauSpecRef, Dict[str, int]]]], Optional[str]]:
    """
    Validate a swap fill and project it to Tau input bindings, then apply its
    reserve transition to the pool snapshot (for subsequent same-pool swaps).

    Returns (bindings, None) on success (possibly the `_SKIP_FILL` empty list for
    COW-netted fills, which touch no reserves), or (None, error) on reject.

    Reject precedence is preserved exactly from the original inline order.
    """
    asset_in = intent.get_field("asset_in")
    asset_out = intent.get_field("asset_out")
    if asset_in not in (pool.asset0, pool.asset1) or asset_out not in (pool.asset0, pool.asset1):
        return None, f"Swap assets not in pool for intent {intent.intent_id}"
    if asset_in == asset_out:
        return None, f"Swap asset_in == asset_out for intent {intent.intent_id}"

    if getattr(fill, "reason", None) == "COW_NETTED":
        # Netting does not touch pool reserves; do not run swap specs.
        return _SKIP_FILL, None

    amount_in = getattr(fill, "amount_in_filled", None)
    amount_out = getattr(fill, "amount_out_filled", None)
    if not isinstance(amount_in, int) or isinstance(amount_in, bool) or amount_in <= 0:
        return None, f"Invalid amount_in_filled for intent {intent.intent_id}: {amount_in!r}"
    if not isinstance(amount_out, int) or isinstance(amount_out, bool) or amount_out <= 0:
        return None, f"Invalid amount_out_filled for intent {intent.intent_id}: {amount_out!r}"

    # Build reserves in/out from current pool snapshot.
    if asset_in == pool.asset0:
        reserve_in = pool.reserve0
        reserve_out = pool.reserve1
    else:
        reserve_in = pool.reserve1
        reserve_out = pool.reserve0

    if intent.kind == IntentKind.SWAP_EXACT_IN:
        bindings, err = _project_exact_in_bindings(
            intent=intent,
            reserve_in=reserve_in,
            reserve_out=reserve_out,
            amount_in=amount_in,
            amount_out=amount_out,
            fee_bps=pool.fee_bps,
            swap_profile=swap_profile,
        )
    else:
        bindings, err = _project_exact_out_bindings(
            intent=intent,
            reserve_in=reserve_in,
            reserve_out=reserve_out,
            amount_in=amount_in,
            amount_out=amount_out,
            fee_bps=pool.fee_bps,
            swap_profile=swap_profile,
        )
    if err is not None:
        return None, err

    # Apply to pool snapshot for subsequent steps.
    if asset_in == pool.asset0:
        pool.reserve0 = pool.reserve0 + amount_in
        pool.reserve1 = pool.reserve1 - amount_out
    else:
        pool.reserve1 = pool.reserve1 + amount_in
        pool.reserve0 = pool.reserve0 - amount_out
    book.pools_mut[pool_id] = pool
    return bindings, None


# ----------------------------------------------------------------------------- #
# Orchestration over the included-intents (semantic execution) order.
#
# Iterates fills in settlement.included_intents order, applies reserve-affecting
# non-swap fills, and projects swap fills into per-pool segments. Returns
# (segment_builder, None) on success or (None, error) on the first reject.
# ----------------------------------------------------------------------------- #
def _collect_swap_segments(
    *,
    intents: List[Intent],
    settlement: Settlement,
    book: _ReserveBook,
    swap_profile: str,
) -> Tuple[Optional[_SegmentBuilder], Optional[str]]:
    intents_by_id = {i.intent_id: i for i in intents}
    fill_by_id: Dict[str, Fill] = {f.intent_id: f for f in settlement.fills}
    builder = _SegmentBuilder()
    seen_filled_intent_ids: set[str] = set()

    for intent_id, action in settlement.included_intents:
        # Only validate filled intents; rejects are fine.
        if action != FillAction.FILL:
            continue

        if intent_id in seen_filled_intent_ids:
            return None, f"Duplicate filled intent_id in settlement: {intent_id}"
        seen_filled_intent_ids.add(intent_id)

        intent = intents_by_id.get(intent_id)
        if intent is None:
            return None, f"Unknown intent_id in fill list: {intent_id}"

        fill = fill_by_id.get(intent_id)
        if fill is None or fill.action != FillAction.FILL:
            return None, f"Missing fill for filled intent_id: {intent_id}"

        if intent.kind == IntentKind.CREATE_POOL:
            err = _apply_create_pool(intent, book)
            if err is not None:
                return None, err
            continue

        pool_id = intent.get_field("pool_id")
        if not isinstance(pool_id, str) or not pool_id:
            return None, f"Missing pool_id for intent {intent.intent_id}"
        pool = book.get_mut(pool_id)
        if pool is None:
            return None, f"Pool not found for intent {intent.intent_id}: {pool_id}"

        if intent.kind == IntentKind.ADD_LIQUIDITY:
            err = _apply_add_liquidity(intent, fill, pool, pool_id, book)
            if err is not None:
                return None, err
            continue

        if intent.kind == IntentKind.REMOVE_LIQUIDITY:
            err = _apply_remove_liquidity(intent, fill, pool, pool_id, book)
            if err is not None:
                return None, err
            continue

        if intent.kind not in (IntentKind.SWAP_EXACT_IN, IntentKind.SWAP_EXACT_OUT):
            return None, f"Tau gate does not support intent kind {intent.kind} (intent {intent.intent_id})"

        bindings, err = _process_swap_fill(
            intent=intent,
            fill=fill,
            pool=pool,
            pool_id=pool_id,
            book=book,
            swap_profile=swap_profile,
        )
        if err is not None:
            return None, err
        for spec_ref, step in bindings or ():
            builder.append(pool_id=pool_id, spec_ref=spec_ref, step=step, intent_id=intent.intent_id)

    return builder, None


# ----------------------------------------------------------------------------- #
# (b) Settlement-level gate construction.
#
# Returns ((spec_ref, step, label), None) when a settlement gate is required,
# (None, None) when settlement_profile is "off", or (None, error) on reject.
# ----------------------------------------------------------------------------- #
def _build_settlement_gate(
    *,
    settlement: Settlement,
    config: TauGateConfig,
) -> Tuple[Optional[Tuple[TauSpecRef, Dict[str, int], str]], Optional[str]]:
    if config.settlement_profile == "off":
        return None, None
    if config.settlement_price_history is None:
        return None, (
            f"Tau settlement_profile={config.settlement_profile} requires "
            "settlement_price_history=(price_pp, price_prev, price_curr)"
        )
    included_intent_ids = [intent_id for intent_id, _action in settlement.included_intents]
    if len(included_intent_ids) != 4:
        return None, (
            f"Tau settlement_profile={config.settlement_profile} requires exactly 4 "
            f"included intents, got {len(included_intent_ids)}"
        )
    a, b, c, d = (_intent_id_to_u64(intent_id) for intent_id in included_intent_ids)
    price_pp, price_prev, price_curr = config.settlement_price_history

    if config.settlement_profile == "aligned_price_rails_v1":
        return (
            SETTLEMENT_PRICE_RAILS_ALIGNED_V1,
            build_settlement_price_rails_aligned_v1_step(
                a=a,
                b=b,
                c=c,
                d=d,
                price_pp=price_pp,
                price_prev=price_prev,
                price_curr=price_curr,
            ),
            "settlement",
        ), None

    flags = config.settlement_module_flags
    if flags is None:
        return None, "Tau settlement_profile=aligned_compact_bundle_v5 requires settlement_module_flags"
    return (
        SETTLEMENT_V5_ALIGNED_COMPACT_BUNDLE,
        build_settlement_v5_aligned_compact_bundle_step(
            a=a,
            b=b,
            c=c,
            d=d,
            price_pp=price_pp,
            price_prev=price_prev,
            price_curr=price_curr,
            cpmm_ok=flags.cpmm_ok,
            balance_ok=flags.balance_ok,
            token_ok=flags.token_ok,
            buyback_floor_ok=flags.buyback_floor_ok,
            buyback_floor_fixedpoint_ok=flags.buyback_floor_fixedpoint_ok,
            rebate_ok=flags.rebate_ok,
            lock_weight_ok=flags.lock_weight_ok,
            proof_ok=flags.proof_ok,
            binding_ok=flags.binding_ok,
        ),
        "settlement",
    ), None


# ----------------------------------------------------------------------------- #
# (e) Fallback policy: resolve the tau binary, fail-closed on any ambiguity.
#
# Returns (tau_bin, None) when a usable binary is resolved, or (None, error)
# when it is not — a missing/invalid binary is a REJECT, never a pass.
# ----------------------------------------------------------------------------- #
def _resolve_tau_bin(config: TauGateConfig) -> Tuple[Optional[str], Optional[str]]:
    if config.tau_bin:
        tau_bin: Optional[str] = config.tau_bin
        if not config.allow_path_lookup:
            if not os.path.isabs(config.tau_bin):
                return None, "tau_bin must be an absolute path when allow_path_lookup=False"
            if not (os.path.isfile(config.tau_bin) and os.access(config.tau_bin, os.X_OK)):
                return None, f"tau_bin is not an executable file: {config.tau_bin}"
    elif config.allow_path_lookup:
        tau_bin = find_tau_bin()
    else:
        return None, "tau_bin not configured (set TauGateConfig.tau_bin)"

    if not tau_bin:
        return None, "tau binary not found (fail-closed)"
    return tau_bin, None


# ----------------------------------------------------------------------------- #
# (c) Tool invocation (thin I/O boundary) + (d) result parsing.
# ----------------------------------------------------------------------------- #
def _run_segment_gates(
    *,
    builder: _SegmentBuilder,
    tau_bin: str,
    timeout_s: float,
) -> Tuple[bool, Optional[str]]:
    for seg in builder.segments_in_order:
        outputs = run_tau_spec_steps(
            tau_bin=tau_bin,
            spec_path=seg.spec_ref.path,
            steps=seg.steps,
            timeout_s=timeout_s,
        )
        ok, err = _require_gate_ok(outputs, gate_output=seg.spec_ref.gate_output, intent_ids=seg.intent_ids)
        if not ok:
            return False, err
    return True, None


def _run_settlement_gate(
    *,
    settlement_gate: Tuple[TauSpecRef, Dict[str, int], str],
    tau_bin: str,
    timeout_s: float,
) -> Tuple[bool, Optional[str]]:
    spec_ref, step, label = settlement_gate
    outputs = run_tau_spec_steps(
        tau_bin=tau_bin,
        spec_path=spec_ref.path,
        steps=[step],
        timeout_s=timeout_s,
    )
    return _require_single_gate_ok(outputs, spec_ref=spec_ref, label=label)


def validate_settlement_swaps(
    *,
    intents: List[Intent],
    settlement: Settlement,
    pre_pools: Dict[str, PoolState],
    config: TauGateConfig = TauGateConfig(),
) -> Tuple[bool, Optional[str]]:
    """
    Validate swap fills in a settlement using Tau specs (fail-closed).

    Profiles:
    - `legacy_auto`:
      preferred `swap_exact_in_v4.tau` / `swap_exact_out_v4.tau` under safe-range,
      fallback to `swap_exact_in_v1.tau` / `swap_exact_out_v1.tau`
    - `proof_gate_range_guard`:
      use the smaller proof-gated swap specs plus the explicit
      `swap_bv32_safe_range_guard_v1.tau` supplemental guard

    Settlement profiles:
    - `off`: no settlement-level Tau gate
    - `aligned_price_rails_v1`: run the aligned canonical-order + price-history rail
    - `aligned_compact_bundle_v5`: run the aligned compact bundle and require
      explicit module flags in `config.settlement_module_flags`
    """
    if not config.enabled:
        return True, None

    try:
        if config.swap_profile not in ("legacy_auto", "proof_gate_range_guard"):
            return False, f"Unsupported Tau swap_profile: {config.swap_profile}"
        if config.settlement_profile not in ("off", "aligned_price_rails_v1", "aligned_compact_bundle_v5"):
            return False, f"Unsupported Tau settlement_profile: {config.settlement_profile}"

        book = _ReserveBook(pre_pools=pre_pools)

        # Project all swap fills into per-pool segments (applies reserve-affecting
        # non-swap fills along the way to keep the reserve path correct).
        builder, err = _collect_swap_segments(
            intents=intents,
            settlement=settlement,
            book=book,
            swap_profile=config.swap_profile,
        )
        if err is not None:
            return False, err
        if builder is None:
            # Fail-closed: _collect_swap_segments must return a builder on success.
            return False, "Tau gate internal error: swap-segment collection returned no builder"

        settlement_gate, err = _build_settlement_gate(settlement=settlement, config=config)
        if err is not None:
            return False, err

        # No Tau work => pass (do not require tau binary).
        if not builder.segments_in_order and settlement_gate is None:
            return True, None

        tau_bin, err = _resolve_tau_bin(config)
        if err is not None:
            return False, err
        if tau_bin is None:
            # Fail-closed: _resolve_tau_bin must return a binary path on success.
            return False, "tau binary not found (fail-closed)"

        ok, err = _run_segment_gates(builder=builder, tau_bin=tau_bin, timeout_s=config.timeout_s)
        if not ok:
            return False, err

        if settlement_gate is not None:
            ok, err = _run_settlement_gate(
                settlement_gate=settlement_gate,
                tau_bin=tau_bin,
                timeout_s=config.timeout_s,
            )
            if not ok:
                return False, err

        return True, None
    except Exception as exc:
        # Fail-closed: convert crashes into deterministic rejection.
        return False, f"{type(exc).__name__}: {exc}"
