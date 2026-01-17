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
from dataclasses import dataclass, replace
from typing import Dict, List, Optional, Tuple

from ..core.liquidity import create_pool
from ..state.intents import Intent, IntentKind
from ..state.pools import PoolState
from .tau_runner import find_tau_bin, run_tau_spec_steps
from .tau_witness import (
    SWAP_EXACT_IN_V1,
    SWAP_EXACT_OUT_V1,
    SWAP_EXACT_IN_V4,
    SWAP_EXACT_OUT_V4,
    TauSpecRef,
    build_swap_exact_in_v1_step,
    build_swap_exact_out_v1_step,
    build_swap_exact_in_v4_step,
    build_swap_exact_out_v4_step,
)


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


def validate_settlement_swaps(
    *,
    intents: List[Intent],
    settlement_fills: List,  # Fill objects (typed in src/core/settlement.py)
    pre_pools: Dict[str, PoolState],
    config: TauGateConfig = TauGateConfig(),
) -> Tuple[bool, Optional[str]]:
    """
    Validate swap fills in a settlement using Tau specs (fail-closed).

    Currently gates swap intent transitions via:
    - preferred: `swap_exact_in_v4.tau` / `swap_exact_out_v4.tau` (includes sound k-guard under safe-range)
    - fallback: `swap_exact_in_v1.tau` / `swap_exact_out_v1.tau` (structural only)
    """
    if not config.enabled:
        return True, None

    try:
        intents_by_id = {i.intent_id: i for i in intents}

        pools_mut: Dict[str, PoolState] = {}

        def _get_pool_mut(pid: str) -> Optional[PoolState]:
            pool = pools_mut.get(pid)
            if pool is not None:
                return pool
            pre = pre_pools.get(pid)
            if pre is None:
                return None
            pool = replace(pre)
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
        # Canonical fill iteration order: use the settlement fill list order.
        #
        # This must match the settlement maker's execution order; otherwise a sequential
        # gate can validate a different reserve path than the one assumed by the fills.
        for fill in settlement_fills:
            # Only validate filled intents; rejects are fine.
            if getattr(fill, "action", None) is None or getattr(fill.action, "value", "") != "FILL":
                continue

            intent_id = getattr(fill, "intent_id", None)
            if not isinstance(intent_id, str) or not intent_id:
                return False, "Invalid fill: missing intent_id"
            if intent_id in seen_filled_intent_ids:
                return False, f"Duplicate filled intent_id in settlement: {intent_id}"
            seen_filled_intent_ids.add(intent_id)

            intent = intents_by_id.get(intent_id)
            if intent is None:
                return False, f"Unknown intent_id in fill list: {intent_id}"

            if intent.kind == IntentKind.CREATE_POOL:
                # Reconstruct pool state deterministically.
                asset0 = intent.get_field("asset0")
                asset1 = intent.get_field("asset1")
                fee_bps = intent.get_field("fee_bps")
                amount0 = intent.get_field("amount0")
                amount1 = intent.get_field("amount1")
                created_at = intent.get_field("created_at", 0)
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
                )
                if pool_id in pools_mut or pool_id in pre_pools:
                    return False, f"CREATE_POOL conflicts with existing pool: {pool_id}"
                pools_mut[pool_id] = pool_state
                continue

            # For now, if enabled, fail-closed on non-swap intents that might mutate pool reserves.
            if intent.kind not in (IntentKind.SWAP_EXACT_IN, IntentKind.SWAP_EXACT_OUT):
                return False, f"Tau gate does not support intent kind {intent.kind} (intent {intent.intent_id})"

            pool_id = intent.get_field("pool_id")
            if not isinstance(pool_id, str) or not pool_id:
                return False, f"Missing pool_id for intent {intent.intent_id}"
            pool = _get_pool_mut(pool_id)
            if pool is None:
                return False, f"Pool not found for intent {intent.intent_id}: {pool_id}"

            asset_in = intent.get_field("asset_in")
            asset_out = intent.get_field("asset_out")
            if asset_in not in (pool.asset0, pool.asset1) or asset_out not in (pool.asset0, pool.asset1):
                return False, f"Swap assets not in pool for intent {intent.intent_id}"
            if asset_in == asset_out:
                return False, f"Swap asset_in == asset_out for intent {intent.intent_id}"

            amount_in = getattr(fill, "amount_in_filled", None)
            amount_out = getattr(fill, "amount_out_filled", None)
            if not isinstance(amount_in, int) or isinstance(amount_in, bool) or amount_in <= 0:
                return False, f"Invalid amount_in_filled for intent {intent.intent_id}: {amount_in!r}"
            if not isinstance(amount_out, int) or isinstance(amount_out, bool) or amount_out <= 0:
                return False, f"Invalid amount_out_filled for intent {intent.intent_id}: {amount_out!r}"

            # Build reserves in/out from current pool snapshot.
            if asset_in == pool.asset0:
                reserve_in = pool.reserve0
                reserve_out = pool.reserve1
            else:
                reserve_in = pool.reserve1
                reserve_out = pool.reserve0

            if intent.kind == IntentKind.SWAP_EXACT_IN:
                min_amount_out = intent.get_field("min_amount_out", 0)
                if not isinstance(min_amount_out, int) or isinstance(min_amount_out, bool) or min_amount_out < 0:
                    return False, f"Invalid min_amount_out for intent {intent.intent_id}: {min_amount_out!r}"
                new_reserve_in = reserve_in + amount_in
                new_reserve_out = reserve_out - amount_out

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
                if not isinstance(max_amount_in, int) or isinstance(max_amount_in, bool) or max_amount_in < 0:
                    return False, f"Invalid max_amount_in for intent {intent.intent_id}: {max_amount_in!r}"
                new_reserve_in = reserve_in + amount_in
                new_reserve_out = reserve_out - amount_out

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
                pool.reserve0 = pool.reserve0 + amount_in
                pool.reserve1 = pool.reserve1 - amount_out
            else:
                pool.reserve1 = pool.reserve1 + amount_in
                pool.reserve0 = pool.reserve0 - amount_out
            pools_mut[pool_id] = pool

        # No swap steps => pass (do not require tau binary).
        if not segments_in_order:
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

        return True, None
    except Exception as exc:
        # Fail-closed: convert crashes into deterministic rejection.
        return False, f"{type(exc).__name__}: {exc}"
