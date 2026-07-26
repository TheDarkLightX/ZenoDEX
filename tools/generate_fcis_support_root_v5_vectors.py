#!/usr/bin/env python3
"""Generate source-bound Python golden vectors for FCIS support-root v5."""

# ruff: noqa: E402

from __future__ import annotations

import argparse
import ast
import hashlib
import json
import sys
from pathlib import Path

REPOSITORY_ROOT = Path(__file__).resolve().parents[1]
if str(REPOSITORY_ROOT) not in sys.path:
    sys.path.insert(0, str(REPOSITORY_ROOT))

from src.core.fcis_state_read_trace_v5 import FCISStateReadTraceV5
from src.core.fcis_support_profile_v5 import (
    FCIS_SUPPORT_PROFILE_ID_V5,
    FCIS_SUPPORT_PROFILE_VERSION_V5,
    FCISSupportRootEvidenceV5,
    FCISSupportSetV5,
    compute_fcis_support_root_v5,
)
from src.core.fcis_traced_reads_v5 import read_step_execution_context_v5
from src.core.fees import FeeAccumulatorState
from src.core.liquidity import create_pool
from src.core.settlement import FillAction, Settlement
from src.core.settlement_snapshots import (
    OwnedSettlementV1,
    canonical_owned_settlement_bytes_v1,
    snapshot_settlement,
)
from src.state import BalanceTable, LPTable
from src.state.fcis_execution_context import admit_fcis_step_execution_context_v1
from src.state.fcis_execution_context_codec import encode_fcis_execution_context_v1
from src.state.fcis_execution_context_values import (
    FCIS_STEP_CONTEXT_SCHEMA_ID_V1,
    FCISFeeSplitPolicySourceV1,
    FCISSettlementExecutionContextSourceV1,
    FCISSettlementModeV1,
    FCISStepExecutionContextSourceV1,
    FCISStepExecutionContextV1,
)
from src.state.intent_snapshots import (
    OwnedIntentV1,
    admit_intent_batch,
    canonical_owned_intent_bytes_v1,
)
from src.state.intents import Intent, IntentKind
from src.state.lp_duration_policy_schema import LPDurationPolicyAdmissionSourceV1
from src.state.nonces import NonceTable
from src.state.owned_collections import OwnedMapV1
from src.state.pools import PoolState
from src.state.snapshot_combinators import AdmitOk
from src.state.state_snapshot_values import (
    POOL_STATUS_MEMBER_VALUES_V1,
    CommittedBalanceTableV1,
    CommittedFeeAccumulatorStateV1,
    CommittedLPTableV1,
    CommittedNonceTableV1,
    CommittedPoolStateV1,
)
from src.state.state_snapshots import (
    snapshot_balance_table,
    snapshot_fee_accumulator,
    snapshot_lp_table,
    snapshot_nonce_table,
    snapshot_pool_map,
)

DEFAULT_OUTPUT = REPOSITORY_ROOT / "docs/specs/fcis_support_root_v5_golden_vectors.json"

SENDER = "0x" + "11" * 48
RECIPIENT = "0x" + "22" * 48
PROTOCOL = "0x" + "33" * 48
ASSET0 = "0x" + "01" * 32
ASSET1 = "0x" + "02" * 32

_SOURCE_ROOT_PATHS = (
    "src/core/fcis_state_read_trace_v5.py",
    "src/core/fcis_step_evaluation_values.py",
    "src/core/fcis_step_evaluator.py",
    "src/core/fcis_support_profile_constants_v5.py",
    "src/core/fcis_support_profile_v5.py",
    "src/core/fcis_traced_reads_v5.py",
    "src/core/nonce_batch_transition.py",
    "src/core/route_settlement.py",
    "src/core/settlement_snapshots.py",
    "src/core/settlement_strong_validator.py",
    "src/integration/fcis_spot_shadow.py",
    "src/state/committed_spot_roots.py",
    "src/state/intent_snapshots.py",
    "src/state/lp_duration_transitions.py",
    "src/state/spot_state_transitions.py",
    "src/state/state_transitions.py",
    "src/state/support_root.py",
    "tools/check_fcis_authority_snapshot_contract.py",
    "tools/generate_fcis_support_root_v5_vectors.py",
)
_EVIDENCE_SOURCE_PATHS = ("docs/specs/FCIS_SUPPORT_ROOT_V5.md",)


def _module_name_v5(relative: str) -> str:
    parts = list(Path(relative).with_suffix("").parts)
    if parts[-1] == "__init__":
        parts.pop()
    return ".".join(parts)


def _module_source_path_v5(module: str, *, repository_root: Path) -> str | None:
    relative = Path(*module.split("."))
    candidates = (
        relative.with_suffix(".py"),
        relative / "__init__.py",
    )
    matches = tuple(
        candidate for candidate in candidates if (repository_root / candidate).is_file()
    )
    if len(matches) > 1:
        raise RuntimeError(f"ambiguous local module source for {module}")
    return matches[0].as_posix() if matches else None


def _import_from_module_v5(relative: str, node: ast.ImportFrom) -> str:
    if node.level == 0:
        return node.module or ""
    current_module = _module_name_v5(relative).split(".")
    if Path(relative).name != "__init__.py":
        current_module.pop()
    keep = len(current_module) - node.level + 1
    if keep < 0:
        raise RuntimeError(f"relative import escapes repository package in {relative}")
    parts = current_module[:keep]
    if node.module:
        parts.extend(node.module.split("."))
    return ".".join(parts)


def _direct_local_import_paths_v5(
    relative: str,
    *,
    repository_root: Path = REPOSITORY_ROOT,
) -> tuple[str, ...]:
    source_path = repository_root / relative
    tree = ast.parse(source_path.read_bytes(), filename=relative)
    dependencies: set[str] = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            for alias in node.names:
                module = alias.name
                if module != "src" and not module.startswith("src."):
                    continue
                dependency = _module_source_path_v5(module, repository_root=repository_root)
                if dependency is None:
                    raise RuntimeError(f"unresolved repository-local import {module} in {relative}")
                dependencies.add(dependency)
            continue
        if not isinstance(node, ast.ImportFrom):
            continue
        base = _import_from_module_v5(relative, node)
        if base != "src" and not base.startswith("src."):
            continue
        base_dependency = _module_source_path_v5(base, repository_root=repository_root)
        if base_dependency is None:
            raise RuntimeError(f"unresolved repository-local import {base} in {relative}")
        dependencies.add(base_dependency)
        for alias in node.names:
            if alias.name == "*":
                continue
            submodule = f"{base}.{alias.name}"
            dependency = _module_source_path_v5(submodule, repository_root=repository_root)
            if dependency is not None:
                dependencies.add(dependency)
            elif node.module is None:
                raise RuntimeError(f"unresolved repository-local import {submodule} in {relative}")
    return tuple(sorted(dependencies))


def _source_dependency_closure_v5(
    roots: tuple[str, ...],
    *,
    repository_root: Path = REPOSITORY_ROOT,
) -> tuple[str, ...]:
    if roots != tuple(sorted(set(roots))):
        raise RuntimeError("source dependency roots must be sorted and duplicate-free")
    pending = list(roots)
    closure: set[str] = set()
    while pending:
        relative = pending.pop(0)
        if relative in closure:
            continue
        if not (repository_root / relative).is_file():
            raise RuntimeError(f"missing source dependency root: {relative}")
        closure.add(relative)
        for dependency in _direct_local_import_paths_v5(
            relative,
            repository_root=repository_root,
        ):
            if dependency not in closure and dependency not in pending:
                pending.append(dependency)
        pending.sort()
    return tuple(sorted(closure))


_SOURCE_PATHS = tuple(
    sorted(set(_source_dependency_closure_v5(_SOURCE_ROOT_PATHS)) | set(_EVIDENCE_SOURCE_PATHS))
)
_TOOLCHAIN_PATHS = (
    "pyproject.toml",
    "requirements-core.lock.txt",
    "requirements-dev.lock.txt",
)


def _sha256_file(relative: str) -> str:
    return hashlib.sha256((REPOSITORY_ROOT / relative).read_bytes()).hexdigest()


def _intent_id(index: int) -> str:
    return "0x" + f"{index:064x}"


def _exact_context(
    *,
    fee_policy: bool,
    protocol_fee_share_bps: int = 0,
) -> FCISStepExecutionContextV1:
    source = FCISStepExecutionContextSourceV1(
        settlement=FCISSettlementExecutionContextSourceV1(
            now=700,
            min_lp_position_age_seconds=0,
            mode=FCISSettlementModeV1.STRONG_REPLAY,
            allow_cow_netting=False,
            allow_snapshot_bound_quote_bindings=False,
            protocol_fee_share_bps=protocol_fee_share_bps,
            protocol_fee_recipient_pubkey=(PROTOCOL if protocol_fee_share_bps > 0 else None),
        ),
        require_all_nonces=True,
        reject_settlements_with_rejected_intents=True,
        fee_split_policy=(FCISFeeSplitPolicySourceV1(3_333, 3_333, 3_334) if fee_policy else None),
        lp_duration_policy=LPDurationPolicyAdmissionSourceV1(
            base_age_seconds=0,
            max_age_seconds=3_600,
            churn_window_seconds=600,
            decay_seconds=900,
            multiplier=2,
            max_churn_tier=5,
        ),
        snapshot_version=4,
    )
    admitted = admit_fcis_step_execution_context_v1(source)
    if type(admitted) is not AdmitOk or type(admitted.value) is not FCISStepExecutionContextV1:
        raise RuntimeError("golden-vector context admission failed")
    return admitted.value


def _swap_intent(pool_id: str, *, index: int) -> OwnedIntentV1:
    return admit_intent_batch(
        (
            Intent(
                module="TauSwap",
                version="0.1",
                kind=IntentKind.SWAP_EXACT_IN,
                intent_id=_intent_id(index),
                sender_pubkey=SENDER,
                deadline=10_000,
                fields={
                    "pool_id": pool_id,
                    "asset_in": ASSET0,
                    "asset_out": ASSET1,
                    "recipient": RECIPIENT,
                    "amount_in": 100,
                    "min_amount_out": 1,
                    "nonce": 1,
                },
            ),
        )
    )[0]


def _remove_intent(pool_id: str, *, index: int) -> OwnedIntentV1:
    return admit_intent_batch(
        (
            Intent(
                module="TauSwap",
                version="0.1",
                kind=IntentKind.REMOVE_LIQUIDITY,
                intent_id=_intent_id(index),
                sender_pubkey=SENDER,
                deadline=10_000,
                fields={
                    "pool_id": pool_id,
                    "recipient": RECIPIENT,
                    "lp_amount": 100,
                    "amount0_min": 0,
                    "amount1_min": 0,
                    "nonce": 6,
                },
            ),
        )
    )[0]


def _rejected_settlement(
    vector_id: str,
    intents: tuple[OwnedIntentV1, ...],
) -> OwnedSettlementV1:
    return snapshot_settlement(
        Settlement(
            module="TauSwap",
            version="0.1",
            batch_ref=vector_id,
            included_intents=tuple((intent.intent_id, FillAction.REJECT) for intent in intents),
            fills=(),
            balance_deltas=(),
            reserve_deltas=(),
            lp_deltas=(),
            events=None,
        )
    )


def _pair_entries(
    entries: tuple[tuple[tuple[str, str], int], ...],
) -> list[list[object]]:
    return [[left, right, value] for (left, right), value in entries]


def _pool_projection(pool: CommittedPoolStateV1) -> dict[str, object]:
    return {
        "pool_id": pool.pool_id,
        "asset0": pool.asset0,
        "asset1": pool.asset1,
        "reserve0": pool.reserve0,
        "reserve1": pool.reserve1,
        "fee_bps": pool.fee_bps,
        "lp_supply": pool.lp_supply,
        "status": {
            "schema_revision": pool.status.schema_revision,
            "enum_tag_ordinal": pool.status.enum_tag_ordinal,
            "member_ordinal": pool.status.member_ordinal,
            "member": POOL_STATUS_MEMBER_VALUES_V1[pool.status.member_ordinal],
        },
        "created_at": pool.created_at,
        "curve_tag": pool.curve_tag,
        "curve_params": pool.curve_params,
    }


def _state_projection(
    *,
    balances: CommittedBalanceTableV1,
    pools: OwnedMapV1[str, CommittedPoolStateV1],
    lp_balances: CommittedLPTableV1,
    nonces: CommittedNonceTableV1,
    fee_accumulator: CommittedFeeAccumulatorStateV1,
) -> dict[str, object]:
    return {
        "balances": _pair_entries(balances.entries),
        "pools": [_pool_projection(pool) for _pool_id, pool in pools.entries],
        "lp_balances": _pair_entries(lp_balances.balance_entries),
        "lp_last_mint": _pair_entries(lp_balances.last_mint_entries),
        "lp_last_remove": _pair_entries(lp_balances.last_remove_entries),
        "lp_churn_tier": _pair_entries(lp_balances.churn_tier_entries),
        "lp_last_churn_update": _pair_entries(lp_balances.last_churn_update_entries),
        "nonces": [[pubkey, nonce] for pubkey, nonce in nonces.entries],
        "fee_accumulator_dust": fee_accumulator.dust,
    }


def _support_projection(support: FCISSupportSetV5) -> dict[str, object]:
    return {
        "balance_keys": [list(key) for key in support.balance_keys],
        "pool_ids": list(support.pool_ids),
        "lp_keys": [list(key) for key in support.lp_keys],
        "nonce_keys": list(support.nonce_keys),
        "include_fee_accumulator": support.include_fee_accumulator,
        "context_paths": list(support.context_paths),
    }


def _trace_projection(trace: FCISStateReadTraceV5) -> dict[str, object]:
    return {
        "balance_keys": [list(key) for key in trace.balance_keys],
        "pool_ids": list(trace.pool_ids),
        "lp_keys": [list(key) for key in trace.lp_keys],
        "nonce_keys": list(trace.nonce_keys),
        "reads_fee_accumulator": trace.reads_fee_accumulator,
    }


def _build_vector(
    *,
    vector_id: str,
    description: str,
    intents: tuple[OwnedIntentV1, ...],
    context: FCISStepExecutionContextV1,
    balances: BalanceTable,
    pools_source: dict[str, PoolState],
    lp_balances: LPTable,
    nonces: NonceTable,
    fee_accumulator: FeeAccumulatorState,
    trace: FCISStateReadTraceV5,
) -> dict[str, object]:
    settlement = _rejected_settlement(vector_id, intents)
    exact_balances = snapshot_balance_table(balances)
    exact_pools = snapshot_pool_map(pools_source)
    exact_lp = snapshot_lp_table(lp_balances)
    exact_nonces = snapshot_nonce_table(nonces)
    exact_fee = snapshot_fee_accumulator(fee_accumulator)
    context_read_trace = read_step_execution_context_v5(context)[1]
    evidence = compute_fcis_support_root_v5(
        settlement=settlement,
        intents=intents,
        context=context,
        balances=exact_balances,
        pools=exact_pools,
        lp_balances=exact_lp,
        nonces=exact_nonces,
        fee_accumulator=exact_fee,
        state_read_trace=trace,
        context_read_trace=context_read_trace,
    )
    if type(evidence) is not FCISSupportRootEvidenceV5:
        raise RuntimeError("golden-vector support-root computation failed")
    settlement_bytes = canonical_owned_settlement_bytes_v1(settlement)
    intent_bytes = tuple(canonical_owned_intent_bytes_v1(intent) for intent in intents)
    context_bytes = encode_fcis_execution_context_v1(
        FCIS_STEP_CONTEXT_SCHEMA_ID_V1,
        context,
    )
    return {
        "id": vector_id,
        "description": description,
        "semantic_inputs": {
            "settlement": json.loads(settlement_bytes),
            "intents": [json.loads(value) for value in intent_bytes],
            "execution_context": json.loads(context_bytes),
            "pre_state_projection": _state_projection(
                balances=exact_balances,
                pools=exact_pools,
                lp_balances=exact_lp,
                nonces=exact_nonces,
                fee_accumulator=exact_fee,
            ),
            "observed_state_read_trace": _trace_projection(trace),
            "observed_context_read_trace": list(context_read_trace.paths),
        },
        "canonical_input_bytes": {
            "settlement_hex": settlement_bytes.hex(),
            "intent_hex": [value.hex() for value in intent_bytes],
            "execution_context_hex": context_bytes.hex(),
        },
        "expected": {
            "declared_support": _support_projection(evidence.support),
            "support_set_preimage_hex": evidence.support_set_preimage.hex(),
            "support_set_commitment": evidence.support_set_commitment,
            "command_root": evidence.command_root,
            "execution_context_hash": evidence.execution_context_hash,
            "root_preimage_hex": evidence.root_preimage.hex(),
            "support_root": evidence.root,
        },
    }


def build_vectors_document() -> dict[str, object]:
    pool_id, pool, _owner_lp = create_pool(
        asset0=ASSET0,
        asset1=ASSET1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=SENDER,
        created_at=0,
    )
    absent_swap = _swap_intent(pool_id, index=1)
    present_swap = _swap_intent(pool_id, index=2)
    remove = _remove_intent(pool_id, index=3)

    absent_vector = _build_vector(
        vector_id="swap-absent-cells-no-fee",
        description="Declared balance, pool, and nonce keys are explicitly absent.",
        intents=(absent_swap,),
        context=_exact_context(fee_policy=False),
        balances=BalanceTable(),
        pools_source={},
        lp_balances=LPTable(),
        nonces=NonceTable(),
        fee_accumulator=FeeAccumulatorState(),
        trace=FCISStateReadTraceV5(),
    )

    present_balances = BalanceTable()
    present_balances.set(SENDER, ASSET0, 123_456)
    present_balances.set(RECIPIENT, ASSET1, 77)
    present_balances.set(PROTOCOL, ASSET0, 9)
    present_nonces = NonceTable()
    present_nonces.set_last(SENDER, 0)
    present_trace = FCISStateReadTraceV5(
        balance_keys=tuple(
            sorted(
                (
                    (SENDER, ASSET0),
                    (RECIPIENT, ASSET1),
                    (PROTOCOL, ASSET0),
                )
            )
        ),
        pool_ids=(pool_id,),
        nonce_keys=(SENDER,),
        reads_fee_accumulator=True,
    )
    present_vector = _build_vector(
        vector_id="swap-present-zero-nonce-with-fee",
        description="Present values include an explicit zero nonce and fee accumulator.",
        intents=(present_swap,),
        context=_exact_context(fee_policy=True, protocol_fee_share_bps=1_000),
        balances=present_balances,
        pools_source={pool_id: pool},
        lp_balances=LPTable(),
        nonces=present_nonces,
        fee_accumulator=FeeAccumulatorState(7),
        trace=present_trace,
    )

    remove_balances = BalanceTable()
    remove_balances.set(RECIPIENT, ASSET0, 10)
    remove_balances.set(RECIPIENT, ASSET1, 20)
    remove_lp = LPTable()
    remove_lp.set(SENDER, pool_id, 50_000)
    remove_lp.set_last_mint_timestamp(SENDER, pool_id, 100)
    remove_lp.set_last_remove_timestamp(SENDER, pool_id, 200)
    remove_lp.set_churn_tier(SENDER, pool_id, 2)
    remove_lp.set_last_churn_update_timestamp(SENDER, pool_id, 300)
    remove_nonces = NonceTable()
    remove_nonces.set_last(SENDER, 5)
    remove_trace = FCISStateReadTraceV5(
        balance_keys=tuple(sorted(((RECIPIENT, ASSET0), (RECIPIENT, ASSET1)))),
        pool_ids=(pool_id,),
        lp_keys=((SENDER, pool_id),),
        nonce_keys=(SENDER,),
    )
    remove_vector = _build_vector(
        vector_id="remove-liquidity-complete-lp-aggregate",
        description="Every LP balance and duration-risk component is present.",
        intents=(remove,),
        context=_exact_context(fee_policy=False),
        balances=remove_balances,
        pools_source={pool_id: pool},
        lp_balances=remove_lp,
        nonces=remove_nonces,
        fee_accumulator=FeeAccumulatorState(),
        trace=remove_trace,
    )

    vectors = (absent_vector, present_vector, remove_vector)
    source_sha256 = {relative: _sha256_file(relative) for relative in _SOURCE_PATHS}
    source_manifest = json.dumps(
        source_sha256,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    return {
        "schema": "zenodex/fcis/support-root-golden-vectors/v1",
        "support_profile_id": FCIS_SUPPORT_PROFILE_ID_V5,
        "support_profile_version": FCIS_SUPPORT_PROFILE_VERSION_V5,
        "status": "python-reference-unmounted",
        "rust_parity_status": "open",
        "algorithm_id": "zenodex/fcis/support-root/sha256/v5",
        "schema_id": "zenodex/fcis/support-root-golden-vectors/v1",
        "generator_id": "zenodex/fcis/support-root-vector-generator/v1",
        "canonical_codec_id": "zenodex/canonical/minimal-uvarint/v1",
        "hash": "sha256",
        "uvarint": "minimal-unsigned-leb128-max-256-bits",
        "source_sha256": source_sha256,
        "source_manifest_sha256": hashlib.sha256(source_manifest).hexdigest(),
        "toolchain_input_sha256": {
            relative: _sha256_file(relative) for relative in _TOOLCHAIN_PATHS
        },
        "vector_count": len(vectors),
        "vectors": list(vectors),
        "nonclaims": [
            "These vectors do not authorize the M5 production mount.",
            "Rust, proof-guest, and Tau parity remain open.",
            "The observed traces are codec fixtures, not claims about mounted execution.",
        ],
    }


def render_vectors_document() -> bytes:
    return (
        json.dumps(
            build_vectors_document(),
            sort_keys=True,
            indent=2,
            ensure_ascii=False,
        )
        + "\n"
    ).encode("utf-8")


def _parse_args(argv: list[str] | None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    action = parser.add_mutually_exclusive_group()
    action.add_argument("--check", action="store_true", help="fail if output is stale")
    action.add_argument("--write", action="store_true", help="write the generated output")
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv)
    rendered = render_vectors_document()
    output = args.output
    if args.check:
        if not output.is_file() or output.read_bytes() != rendered:
            print(f"stale FCIS support-root v5 vectors: {output}", file=sys.stderr)
            return 1
        print(f"FCIS support-root v5 vectors are current: {output}")
        return 0
    if args.write:
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_bytes(rendered)
        print(f"wrote FCIS support-root v5 vectors: {output}")
        return 0
    sys.stdout.buffer.write(rendered)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
