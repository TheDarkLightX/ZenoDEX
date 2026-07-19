"""
Fail-closed Tau validation gate (imperative shell).

This module is IO by design: it runs the `tau` binary to validate witnesses
against Tau specs. Any error/timeout/missing tool => reject.

IMPORTANT:
- This relies on an external executable and wall-clock timeouts.
- Treat it as off-chain/operator tooling unless Tau execution is guaranteed
  deterministic and uniformly available across validators.
"""

from __future__ import annotations

import os
from collections.abc import Mapping
from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple

from ..core.liquidity import create_pool
from ..core.settlement import Fill, FillAction, Settlement
from ..state.intents import Intent, IntentKind
from ..state.pools import PoolState, copy_pool_state
from .tau_runner import find_tau_bin, run_tau_spec_steps
from .tau_witness import (
    SETTLEMENT_PRICE_RAILS_ALIGNED_V1,
    SETTLEMENT_V5_ALIGNED_COMPACT_BUNDLE,
    SWAP_BV32_SAFE_RANGE_GUARD_V1,
    SWAP_EXACT_IN_PROOF_GATE_V1,
    SWAP_EXACT_IN_PROTOCOL_FEE_APPLY_V1,
    SWAP_EXACT_IN_V1,
    SWAP_EXACT_IN_V4,
    SWAP_EXACT_OUT_PROOF_GATE_V1,
    SWAP_EXACT_OUT_PROTOCOL_FEE_APPLY_V1,
    SWAP_EXACT_OUT_V1,
    SWAP_EXACT_OUT_V4,
    TauSpecRef,
    build_settlement_price_rails_aligned_v1_step,
    build_settlement_v5_aligned_compact_bundle_step,
    build_swap_bv32_safe_range_guard_v1_step,
    build_swap_exact_in_proof_gate_v1_step,
    build_swap_exact_in_protocol_fee_apply_v1_step,
    build_swap_exact_in_v1_step,
    build_swap_exact_in_v4_step,
    build_swap_exact_out_proof_gate_v1_step,
    build_swap_exact_out_protocol_fee_apply_v1_step,
    build_swap_exact_out_v1_step,
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


DEFAULT_TAU_GATE_CONFIG = TauGateConfig()


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


def validate_settlement_swaps(
    *,
    intents: List[Intent],
    settlement: Settlement,
    pre_pools: Mapping[str, PoolState],
    config: TauGateConfig = DEFAULT_TAU_GATE_CONFIG,
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

        intents_by_id = {i.intent_id: i for i in intents}
        fill_by_id: Dict[str, Fill] = {f.intent_id: f for f in settlement.fills}

        pools_mut: Dict[str, PoolState] = {}

        def _get_pool_mut(pid: str) -> Optional[PoolState]:
            pool = pools_mut.get(pid)
            if pool is not None:
                return pool
            pre = pre_pools.get(pid)
            if pre is None:
                return None
            pool = copy_pool_state(pre)
            pools_mut[pid] = pool
            return pool

        @dataclass
        class _SwapSegment:
            pool_id: str
            spec_ref: TauSpecRef
            steps: List[Dict[str, int]]
            intent_ids: List[str]

        # Validate swaps in settlement order, but batch into per-pool / per-kind segments.
        #
        # Segments preserve per-pool execution order (the only order that can affect
        # reserve transitions). They may span across unrelated fills from other pools.
        segments_in_order: List[_SwapSegment] = []
        last_segment_by_pool: Dict[str, _SwapSegment] = {}

        def _append_swap_segment(
            *,
            pool_id: str,
            spec_ref: TauSpecRef,
            step: Dict[str, int],
            intent_id: str,
        ) -> None:
            seg = last_segment_by_pool.get(pool_id)
            if seg is None or seg.spec_ref is not spec_ref:
                seg = _SwapSegment(pool_id=pool_id, spec_ref=spec_ref, steps=[], intent_ids=[])
                last_segment_by_pool[pool_id] = seg
                segments_in_order.append(seg)
            seg.steps.append(step)
            seg.intent_ids.append(intent_id)

        seen_filled_intent_ids: set[str] = set()
        # Canonical iteration order: use settlement.included_intents order (the semantic execution order).
        #
        # NOTE: We only validate swap transitions, but we must still apply reserve-affecting
        # non-swap fills (add/remove liquidity, create pool) to keep the reserve path correct
        # for later swaps in the same pool.
        for intent_id, action in settlement.included_intents:
            # Only validate filled intents; rejects are fine.
            if action != FillAction.FILL:
                continue

            if intent_id in seen_filled_intent_ids:
                return False, f"Duplicate filled intent_id in settlement: {intent_id}"
            seen_filled_intent_ids.add(intent_id)

            intent = intents_by_id.get(intent_id)
            if intent is None:
                return False, f"Unknown intent_id in fill list: {intent_id}"

            fill = fill_by_id.get(intent_id)
            if fill is None or fill.action != FillAction.FILL:
                return False, f"Missing fill for filled intent_id: {intent_id}"

            if intent.kind == IntentKind.CREATE_POOL:
                # Reconstruct pool state deterministically.
                asset0 = intent.get_field("asset0")
                asset1 = intent.get_field("asset1")
                fee_bps = intent.get_field("fee_bps")
                amount0 = intent.get_field("amount0")
                amount1 = intent.get_field("amount1")
                created_at = intent.get_field("created_at", 0)
                curve_tag = intent.get_field("curve_tag", None)
                curve_params = intent.get_field("curve_params", None)
                if isinstance(curve_params, Mapping):
                    curve_params = dict(curve_params)
                if any(v is None for v in (asset0, asset1, fee_bps, amount0, amount1)):
                    return False, f"CREATE_POOL missing params for intent {intent.intent_id}"
                pool_id, pool_state, _lp_minted = create_pool(
                    asset0=asset0,
                    asset1=asset1,
                    amount0=amount0,
                    amount1=amount1,
                    fee_bps=fee_bps,
                    creator_pubkey=intent.sender_pubkey,
                    created_at=created_at,
                    curve_tag=curve_tag,
                    curve_params=curve_params,
                )
                if pool_id in pools_mut or pool_id in pre_pools:
                    return False, f"CREATE_POOL conflicts with existing pool: {pool_id}"
                pools_mut[pool_id] = pool_state
                continue

            pool_id = intent.get_field("pool_id")
            if not isinstance(pool_id, str) or not pool_id:
                return False, f"Missing pool_id for intent {intent.intent_id}"
            pool = _get_pool_mut(pool_id)
            if pool is None:
                return False, f"Pool not found for intent {intent.intent_id}: {pool_id}"

            if intent.kind == IntentKind.ADD_LIQUIDITY:
                amount0_used = getattr(fill, "amount0_used", None)
                amount1_used = getattr(fill, "amount1_used", None)
                if not isinstance(amount0_used, int) or isinstance(amount0_used, bool) or amount0_used <= 0:
                    return False, f"Invalid amount0_used for intent {intent.intent_id}: {amount0_used!r}"
                if not isinstance(amount1_used, int) or isinstance(amount1_used, bool) or amount1_used <= 0:
                    return False, f"Invalid amount1_used for intent {intent.intent_id}: {amount1_used!r}"
                pool.reserve0 = int(pool.reserve0) + int(amount0_used)
                pool.reserve1 = int(pool.reserve1) + int(amount1_used)
                pools_mut[pool_id] = pool
                continue

            if intent.kind == IntentKind.REMOVE_LIQUIDITY:
                amount0_out = getattr(fill, "amount0_out", None)
                amount1_out = getattr(fill, "amount1_out", None)
                if not isinstance(amount0_out, int) or isinstance(amount0_out, bool) or amount0_out <= 0:
                    return False, f"Invalid amount0_out for intent {intent.intent_id}: {amount0_out!r}"
                if not isinstance(amount1_out, int) or isinstance(amount1_out, bool) or amount1_out <= 0:
                    return False, f"Invalid amount1_out for intent {intent.intent_id}: {amount1_out!r}"
                pool.reserve0 = int(pool.reserve0) - int(amount0_out)
                pool.reserve1 = int(pool.reserve1) - int(amount1_out)
                pools_mut[pool_id] = pool
                continue

            intent_kind: object = intent.kind
            if intent_kind not in (IntentKind.SWAP_EXACT_IN, IntentKind.SWAP_EXACT_OUT):
                return False, f"Tau gate does not support intent kind {intent.kind} (intent {intent.intent_id})"

            asset_in = intent.get_field("asset_in")
            asset_out = intent.get_field("asset_out")
            if asset_in not in (pool.asset0, pool.asset1) or asset_out not in (pool.asset0, pool.asset1):
                return False, f"Swap assets not in pool for intent {intent.intent_id}"
            if asset_in == asset_out:
                return False, f"Swap asset_in == asset_out for intent {intent.intent_id}"

            if getattr(fill, "reason", None) == "COW_NETTED":
                # Netting does not touch pool reserves; do not run swap specs.
                continue

            amount_in = getattr(fill, "amount_in_filled", None)
            amount_out = getattr(fill, "amount_out_filled", None)
            if type(amount_in) is not int or amount_in <= 0:
                return False, f"Invalid amount_in_filled for intent {intent.intent_id}: {amount_in!r}"
            if type(amount_out) is not int or amount_out <= 0:
                return False, f"Invalid amount_out_filled for intent {intent.intent_id}: {amount_out!r}"
            protocol_fee_raw = getattr(fill, "protocol_fee_paid", None)
            if protocol_fee_raw is None:
                protocol_fee = 0
            elif type(protocol_fee_raw) is not int or protocol_fee_raw < 0:
                return False, f"Invalid protocol_fee_paid for intent {intent.intent_id}: {protocol_fee_raw!r}"
            else:
                protocol_fee = protocol_fee_raw
            if protocol_fee > amount_in:
                return False, f"protocol_fee_paid exceeds amount_in_filled for intent {intent.intent_id}"

            fee_total = 0
            if protocol_fee > 0:
                fee_total_raw = getattr(fill, "fee_paid", None)
                if type(fee_total_raw) is not int or fee_total_raw < 0:
                    return False, f"Invalid fee_paid for protocol-fee intent {intent.intent_id}: {fee_total_raw!r}"
                if protocol_fee > fee_total_raw:
                    return False, f"protocol_fee_paid exceeds fee_paid for intent {intent.intent_id}"
                fee_total = fee_total_raw
                if config.swap_profile == "proof_gate_range_guard":
                    return False, (
                        "Tau swap_profile=proof_gate_range_guard does not support "
                        f"protocol-fee reserve transitions (intent {intent.intent_id})"
                    )

            # Build reserves in/out from current pool snapshot.
            if asset_in == pool.asset0:
                reserve_in = pool.reserve0
                reserve_out = pool.reserve1
            else:
                reserve_in = pool.reserve1
                reserve_out = pool.reserve0

            if intent.kind == IntentKind.SWAP_EXACT_IN:
                min_amount_out = intent.get_field("min_amount_out", 0)
                if type(min_amount_out) is not int or min_amount_out < 0:
                    return False, f"Invalid min_amount_out for intent {intent.intent_id}: {min_amount_out!r}"
                new_reserve_in = reserve_in + amount_in - protocol_fee
                new_reserve_out = reserve_out - amount_out

                if protocol_fee > 0:
                    _append_swap_segment(
                        pool_id=pool_id,
                        spec_ref=SWAP_EXACT_IN_PROTOCOL_FEE_APPLY_V1,
                        step=build_swap_exact_in_protocol_fee_apply_v1_step(
                            reserve_in=reserve_in,
                            reserve_out=reserve_out,
                            amount_in=amount_in,
                            fee_bps=pool.fee_bps,
                            min_amount_out=min_amount_out,
                            amount_out=amount_out,
                            new_reserve_in=new_reserve_in,
                            new_reserve_out=new_reserve_out,
                            fee_total=fee_total,
                            protocol_fee=protocol_fee,
                        ),
                        intent_id=intent.intent_id,
                    )
                elif config.swap_profile == "proof_gate_range_guard":
                    _append_swap_segment(
                        pool_id=pool_id,
                        spec_ref=SWAP_EXACT_IN_PROOF_GATE_V1,
                        step=build_swap_exact_in_proof_gate_v1_step(
                            reserve_in=reserve_in,
                            reserve_out=reserve_out,
                            amount_in=amount_in,
                            fee_bps=pool.fee_bps,
                            min_amount_out=min_amount_out,
                            amount_out=amount_out,
                            new_reserve_in=new_reserve_in,
                            new_reserve_out=new_reserve_out,
                        ),
                        intent_id=intent.intent_id,
                    )
                    _append_swap_segment(
                        pool_id=pool_id,
                        spec_ref=SWAP_BV32_SAFE_RANGE_GUARD_V1,
                        step=build_swap_bv32_safe_range_guard_v1_step(
                            reserve_in=reserve_in,
                            reserve_out=reserve_out,
                            delta_primary=amount_in,
                            delta_secondary=amount_out,
                            new_reserve_in=new_reserve_in,
                            new_reserve_out=new_reserve_out,
                        ),
                        intent_id=intent.intent_id,
                    )
                else:
                    # v4 is sound but intentionally bounded (safe-range guard <= 0xFFFF).
                    use_v4 = all(
                        isinstance(v, int) and not isinstance(v, bool) and 0 <= v <= 0xFFFF
                        for v in (reserve_in, reserve_out, amount_in, min_amount_out, amount_out, new_reserve_in, new_reserve_out)
                    )
                    _append_swap_segment(
                        pool_id=pool_id,
                        spec_ref=SWAP_EXACT_IN_V4 if use_v4 else SWAP_EXACT_IN_V1,
                        step=(
                            build_swap_exact_in_v4_step(
                                reserve_in=reserve_in,
                                reserve_out=reserve_out,
                                amount_in=amount_in,
                                fee_bps=pool.fee_bps,
                                min_amount_out=min_amount_out,
                                amount_out=amount_out,
                                new_reserve_in=new_reserve_in,
                                new_reserve_out=new_reserve_out,
                            )
                            if use_v4
                            else build_swap_exact_in_v1_step(
                                reserve_in=reserve_in,
                                reserve_out=reserve_out,
                                amount_in=amount_in,
                                fee_bps=pool.fee_bps,
                                min_amount_out=min_amount_out,
                                amount_out=amount_out,
                                new_reserve_in=new_reserve_in,
                                new_reserve_out=new_reserve_out,
                            )
                        ),
                        intent_id=intent.intent_id,
                    )
            else:
                max_amount_in = intent.get_field("max_amount_in", 0)
                if type(max_amount_in) is not int or max_amount_in < 0:
                    return False, f"Invalid max_amount_in for intent {intent.intent_id}: {max_amount_in!r}"
                new_reserve_in = reserve_in + amount_in - protocol_fee
                new_reserve_out = reserve_out - amount_out

                if protocol_fee > 0:
                    _append_swap_segment(
                        pool_id=pool_id,
                        spec_ref=SWAP_EXACT_OUT_PROTOCOL_FEE_APPLY_V1,
                        step=build_swap_exact_out_protocol_fee_apply_v1_step(
                            reserve_in=reserve_in,
                            reserve_out=reserve_out,
                            amount_out=amount_out,
                            fee_bps=pool.fee_bps,
                            max_amount_in=max_amount_in,
                            amount_in=amount_in,
                            new_reserve_in=new_reserve_in,
                            new_reserve_out=new_reserve_out,
                            fee_total=fee_total,
                            protocol_fee=protocol_fee,
                        ),
                        intent_id=intent.intent_id,
                    )
                elif config.swap_profile == "proof_gate_range_guard":
                    _append_swap_segment(
                        pool_id=pool_id,
                        spec_ref=SWAP_EXACT_OUT_PROOF_GATE_V1,
                        step=build_swap_exact_out_proof_gate_v1_step(
                            reserve_in=reserve_in,
                            reserve_out=reserve_out,
                            amount_out=amount_out,
                            fee_bps=pool.fee_bps,
                            max_amount_in=max_amount_in,
                            amount_in=amount_in,
                            new_reserve_in=new_reserve_in,
                            new_reserve_out=new_reserve_out,
                        ),
                        intent_id=intent.intent_id,
                    )
                    _append_swap_segment(
                        pool_id=pool_id,
                        spec_ref=SWAP_BV32_SAFE_RANGE_GUARD_V1,
                        step=build_swap_bv32_safe_range_guard_v1_step(
                            reserve_in=reserve_in,
                            reserve_out=reserve_out,
                            delta_primary=amount_out,
                            delta_secondary=amount_in,
                            new_reserve_in=new_reserve_in,
                            new_reserve_out=new_reserve_out,
                        ),
                        intent_id=intent.intent_id,
                    )
                else:
                    use_v4 = all(
                        isinstance(v, int) and not isinstance(v, bool) and 0 <= v <= 0xFFFF
                        for v in (reserve_in, reserve_out, amount_out, max_amount_in, amount_in, new_reserve_in, new_reserve_out)
                    )
                    _append_swap_segment(
                        pool_id=pool_id,
                        spec_ref=SWAP_EXACT_OUT_V4 if use_v4 else SWAP_EXACT_OUT_V1,
                        step=(
                            build_swap_exact_out_v4_step(
                                reserve_in=reserve_in,
                                reserve_out=reserve_out,
                                amount_out=amount_out,
                                fee_bps=pool.fee_bps,
                                max_amount_in=max_amount_in,
                                amount_in=amount_in,
                                new_reserve_in=new_reserve_in,
                                new_reserve_out=new_reserve_out,
                            )
                            if use_v4
                            else build_swap_exact_out_v1_step(
                                reserve_in=reserve_in,
                                reserve_out=reserve_out,
                                amount_out=amount_out,
                                fee_bps=pool.fee_bps,
                                max_amount_in=max_amount_in,
                                amount_in=amount_in,
                                new_reserve_in=new_reserve_in,
                                new_reserve_out=new_reserve_out,
                            )
                        ),
                        intent_id=intent.intent_id,
                    )

            # Apply to pool snapshot for subsequent steps.
            if asset_in == pool.asset0:
                pool.reserve0 = new_reserve_in
                pool.reserve1 = new_reserve_out
            else:
                pool.reserve1 = new_reserve_in
                pool.reserve0 = new_reserve_out
            pools_mut[pool_id] = pool

        settlement_gate: Optional[Tuple[TauSpecRef, Dict[str, int], str]] = None
        if config.settlement_profile != "off":
            if config.settlement_price_history is None:
                return False, f"Tau settlement_profile={config.settlement_profile} requires settlement_price_history=(price_pp, price_prev, price_curr)"
            included_intent_ids = [intent_id for intent_id, _action in settlement.included_intents]
            if len(included_intent_ids) != 4:
                return False, f"Tau settlement_profile={config.settlement_profile} requires exactly 4 included intents, got {len(included_intent_ids)}"
            a, b, c, d = (_intent_id_to_u64(intent_id) for intent_id in included_intent_ids)
            price_pp, price_prev, price_curr = config.settlement_price_history
            if config.settlement_profile == "aligned_price_rails_v1":
                settlement_gate = (
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
                )
            else:
                flags = config.settlement_module_flags
                if flags is None:
                    return False, "Tau settlement_profile=aligned_compact_bundle_v5 requires settlement_module_flags"
                settlement_gate = (
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
                )

        # No Tau work => pass (do not require tau binary).
        if not segments_in_order and settlement_gate is None:
            return True, None

        if config.tau_bin:
            tau_bin = config.tau_bin
            if not config.allow_path_lookup:
                if not os.path.isabs(tau_bin):
                    return False, "tau_bin must be an absolute path when allow_path_lookup=False"
                if not (os.path.isfile(tau_bin) and os.access(tau_bin, os.X_OK)):
                    return False, f"tau_bin is not an executable file: {tau_bin}"
        elif config.allow_path_lookup:
            tau_bin = find_tau_bin()
        else:
            return False, "tau_bin not configured (set TauGateConfig.tau_bin)"

        if not tau_bin:
            return False, "tau binary not found (fail-closed)"

        for seg in segments_in_order:
            outputs = run_tau_spec_steps(
                tau_bin=tau_bin,
                spec_path=seg.spec_ref.path,
                steps=seg.steps,
                timeout_s=config.timeout_s,
            )
            ok, err = _require_gate_ok(outputs, gate_output=seg.spec_ref.gate_output, intent_ids=seg.intent_ids)
            if not ok:
                return False, err

        if settlement_gate is not None:
            spec_ref, step, label = settlement_gate
            outputs = run_tau_spec_steps(
                tau_bin=tau_bin,
                spec_path=spec_ref.path,
                steps=[step],
                timeout_s=config.timeout_s,
            )
            ok, err = _require_single_gate_ok(outputs, spec_ref=spec_ref, label=label)
            if not ok:
                return False, err

        return True, None
    except Exception as exc:
        # Fail-closed: convert crashes into deterministic rejection.
        return False, f"{type(exc).__name__}: {exc}"
