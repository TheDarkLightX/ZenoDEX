#!/usr/bin/env python3
"""
Structural blast-radius report for ZenoDEX batches.

Posture:
- exact on intent parsing, support-root scope, and conflict components when a
  valid DEX snapshot is provided
- conservative on LP asset scope when snapshot context is missing
- heuristic on runtime module hints and blast-radius classification

This tool is intentionally explicit about what is exact versus heuristic. It is
meant to narrow containment work, not to claim an exact economic impact model.
"""

from __future__ import annotations

import argparse
import ast
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, Mapping, Optional

import yaml

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.core.intent_access import (  # noqa: E402
    IntentAccess,
    access_for_intent,
    partition_independent_intents,
)
from src.core.quote_receipts import verify_route_quote_receipt  # noqa: E402
from src.integration.dex_snapshot import state_from_snapshot  # noqa: E402
from src.integration.operations import (  # noqa: E402
    SignedIntentEnvelope,
    parse_signed_intents,
)
from src.state.intents import Intent, IntentKind  # noqa: E402
from src.state.pools import PoolState, compute_pool_id  # noqa: E402
from src.state.state_root import compute_state_root  # noqa: E402
from src.state.support_root import (  # noqa: E402
    compute_support_state_root,
    derive_batch_state_support,
)

CLAIMS_REGISTRY_PATH = REPO_ROOT / "docs" / "claims_registry.yaml"
SYSTEM_SPEC_PATH = REPO_ROOT / "src" / "kernels" / "dex" / "zenodex_system_compose_v2.yaml"

_K_BAL = "BAL"
_K_POL = "POL"
_K_LPB = "LPB"

_CORE_MODULE_HINTS_BY_KIND: dict[IntentKind, tuple[str, ...]] = {
    IntentKind.SWAP_EXACT_IN: (
        "src.core.batch_clearing",
        "src.core.amm_dispatch",
        "src.core.settlement_strong_validator",
    ),
    IntentKind.SWAP_EXACT_OUT: (
        "src.core.batch_clearing",
        "src.core.amm_dispatch",
        "src.core.settlement_strong_validator",
    ),
    IntentKind.CREATE_POOL: (
        "src.core.batch_clearing",
        "src.core.liquidity",
        "src.core.settlement_strong_validator",
    ),
    IntentKind.ADD_LIQUIDITY: (
        "src.core.batch_clearing",
        "src.core.liquidity",
        "src.core.settlement_strong_validator",
    ),
    IntentKind.REMOVE_LIQUIDITY: (
        "src.core.batch_clearing",
        "src.core.liquidity",
        "src.core.settlement_strong_validator",
    ),
}

_STATE_MODULE_HINTS_BY_KIND: dict[IntentKind, tuple[str, ...]] = {
    IntentKind.SWAP_EXACT_IN: ("src.state.pools",),
    IntentKind.SWAP_EXACT_OUT: ("src.state.pools",),
    IntentKind.CREATE_POOL: ("src.state.pools", "src.state.lp"),
    IntentKind.ADD_LIQUIDITY: ("src.state.pools", "src.state.lp"),
    IntentKind.REMOVE_LIQUIDITY: ("src.state.pools", "src.state.lp"),
}

_SHELL_MODULE_HINTS = (
    "src.integration.dex_engine",
    "src.integration.validation",
)

_COMPOSE_ALIAS_HINTS_BY_KIND: dict[IntentKind, tuple[str, ...]] = {
    IntentKind.SWAP_EXACT_IN: ("swap", "lp"),
    IntentKind.SWAP_EXACT_OUT: ("swap", "lp"),
    IntentKind.CREATE_POOL: ("lp", "swap"),
    IntentKind.ADD_LIQUIDITY: ("lp", "swap"),
    IntentKind.REMOVE_LIQUIDITY: ("lp", "swap"),
}


@dataclass(frozen=True)
class ModuleEvidence:
    module: str
    path: str
    imported_by_tests: tuple[str, ...]
    kernel_python_imports: tuple[str, ...]
    esso_imports: tuple[str, ...]
    promoted_claim_ids: tuple[str, ...]


def _json_dump(obj: Mapping[str, Any]) -> str:
    return json.dumps(dict(obj), indent=2, sort_keys=True) + "\n"


def _read_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def _iter_py_files(root: Path) -> list[Path]:
    out: list[Path] = []
    for path in root.rglob("*.py"):
        if "__pycache__" in path.parts:
            continue
        out.append(path)
    out.sort()
    return out


def _parse_ast(path: Path) -> ast.AST:
    return ast.parse(path.read_text(encoding="utf-8"), filename=str(path))


def _imports_from_tree(tree: ast.AST) -> list[str]:
    out: list[str] = []
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            for alias in node.names:
                out.append(str(alias.name))
        elif isinstance(node, ast.ImportFrom):
            if node.module is not None:
                out.append(str(node.module))
    return out


def _module_path_for_name(module: str) -> Path:
    parts = module.split(".")
    return REPO_ROOT.joinpath(*parts).with_suffix(".py")


def _display_path(path: Path) -> str:
    try:
        return str(path.relative_to(REPO_ROOT))
    except ValueError:
        return str(path)


def _test_import_index() -> dict[str, tuple[str, ...]]:
    tests_root = REPO_ROOT / "tests"
    idx: dict[str, set[str]] = {}
    if not tests_root.is_dir():
        return {}
    for path in _iter_py_files(tests_root):
        tree = _parse_ast(path)
        for mod in _imports_from_tree(tree):
            if not mod.startswith("src."):
                continue
            idx.setdefault(mod, set()).add(str(path.relative_to(REPO_ROOT)))
    return {k: tuple(sorted(v)) for k, v in idx.items()}


def _claims_index(path: Path) -> dict[str, tuple[str, ...]]:
    if not path.exists():
        return {}
    raw = yaml.safe_load(path.read_text(encoding="utf-8"))
    if not isinstance(raw, dict):
        return {}
    claims = raw.get("claims")
    if not isinstance(claims, list):
        return {}
    idx: dict[str, set[str]] = {}
    for claim in claims:
        if not isinstance(claim, dict):
            continue
        claim_id = claim.get("id")
        if not isinstance(claim_id, str) or not claim_id:
            continue
        evidence = claim.get("evidence")
        if not isinstance(evidence, dict):
            continue
        files = evidence.get("files")
        if not isinstance(files, list):
            continue
        for file_path in files:
            if not isinstance(file_path, str) or not file_path:
                continue
            idx.setdefault(file_path, set()).add(claim_id)
    return {k: tuple(sorted(v)) for k, v in idx.items()}


def _kernel_imports(imports: Iterable[str]) -> tuple[str, ...]:
    out = {
        mod
        for mod in imports
        if mod == "kernels.python"
        or mod.startswith("kernels.python.")
        or mod == "src.kernels.python"
        or mod.startswith("src.kernels.python.")
    }
    return tuple(sorted(out))


def _esso_imports(imports: Iterable[str]) -> tuple[str, ...]:
    out = {mod for mod in imports if mod == "ESSO" or mod.startswith("ESSO.")}
    return tuple(sorted(out))


def _module_evidence(
    *,
    module: str,
    test_idx: Mapping[str, tuple[str, ...]],
    claim_idx: Mapping[str, tuple[str, ...]],
) -> ModuleEvidence:
    path = _module_path_for_name(module)
    rel = str(path.relative_to(REPO_ROOT))
    if not path.exists():
        return ModuleEvidence(
            module=module,
            path=rel,
            imported_by_tests=(),
            kernel_python_imports=(),
            esso_imports=(),
            promoted_claim_ids=(),
        )
    tree = _parse_ast(path)
    imports = _imports_from_tree(tree)
    return ModuleEvidence(
        module=module,
        path=rel,
        imported_by_tests=test_idx.get(module, ()),
        kernel_python_imports=_kernel_imports(imports),
        esso_imports=_esso_imports(imports),
        promoted_claim_ids=claim_idx.get(rel, ()),
    )


def _canonical_recipient(intent: Intent) -> str:
    if intent.kind == IntentKind.CREATE_POOL:
        return str(intent.sender_pubkey)
    recipient = intent.get_field("recipient", intent.sender_pubkey)
    return str(recipient) if isinstance(recipient, str) and recipient else str(intent.sender_pubkey)


def _created_pool_assets(intents: Iterable[Intent]) -> dict[str, tuple[str, str]]:
    out: dict[str, tuple[str, str]] = {}
    for intent in intents:
        if intent.kind != IntentKind.CREATE_POOL:
            continue
        asset0 = intent.get_field("asset0")
        asset1 = intent.get_field("asset1")
        fee_bps = intent.get_field("fee_bps")
        curve_tag = intent.get_field("curve_tag", "CPMM")
        curve_params = intent.get_field("curve_params", "")
        if not isinstance(asset0, str) or not asset0:
            continue
        if not isinstance(asset1, str) or not asset1:
            continue
        if not isinstance(fee_bps, int) or isinstance(fee_bps, bool):
            continue
        try:
            pool_id = compute_pool_id(asset0, asset1, int(fee_bps), curve_tag=curve_tag, curve_params=curve_params)
        except Exception:
            continue
        out[pool_id] = (asset0, asset1)
    return out


def _intent_pool_ids(intent: Intent) -> tuple[str, ...]:
    if intent.kind == IntentKind.CREATE_POOL:
        created = _created_pool_assets([intent])
        return tuple(sorted(created.keys()))
    pool_id = intent.get_field("pool_id")
    if isinstance(pool_id, str) and pool_id:
        return (pool_id,)
    return ()


def _intent_assets(
    intent: Intent,
    *,
    pools: Mapping[str, PoolState],
    created_pools: Mapping[str, tuple[str, str]],
) -> tuple[str, ...]:
    assets: set[str] = set()
    if intent.kind == IntentKind.CREATE_POOL:
        for key in ("asset0", "asset1"):
            value = intent.get_field(key)
            if isinstance(value, str) and value:
                assets.add(value)
        return tuple(sorted(assets))

    if intent.kind in (IntentKind.SWAP_EXACT_IN, IntentKind.SWAP_EXACT_OUT):
        for key in ("asset_in", "asset_out"):
            value = intent.get_field(key)
            if isinstance(value, str) and value:
                assets.add(value)
        return tuple(sorted(assets))

    pool_id = intent.get_field("pool_id")
    if isinstance(pool_id, str) and pool_id:
        if pool_id in pools:
            assets.add(pools[pool_id].asset0)
            assets.add(pools[pool_id].asset1)
        elif pool_id in created_pools:
            asset0, asset1 = created_pools[pool_id]
            assets.add(asset0)
            assets.add(asset1)
    return tuple(sorted(assets))


def _has_nonce(intent: Intent) -> bool:
    fields = intent.fields or {}
    return isinstance(fields, Mapping) and "nonce" in fields


def _has_quote_receipt_hash(intent: Intent) -> bool:
    fields = intent.fields or {}
    value = fields.get("quote_receipt_hash") if isinstance(fields, Mapping) else None
    return isinstance(value, str) and bool(value)


def _has_quote_receipt_witness(env: SignedIntentEnvelope) -> bool:
    return isinstance(env.quote_receipt, dict) and bool(env.quote_receipt)


def _has_verified_quote_receipt_witness(
    env: SignedIntentEnvelope,
    *,
    pools: Mapping[str, PoolState],
) -> bool:
    if not _has_quote_receipt_witness(env):
        return False
    ok, _err = verify_route_quote_receipt(env.quote_receipt, pools_by_id=dict(pools))
    return bool(ok)


def _quote_receipt_binding_status(
    env: SignedIntentEnvelope,
    *,
    pools: Mapping[str, PoolState],
    snapshot_provided: bool,
) -> str:
    intent = env.intent
    has_hash = _has_quote_receipt_hash(intent)
    has_witness = _has_quote_receipt_witness(env)
    has_snapshot_marker = isinstance(intent.get_field("quote_pool_fingerprint"), str) and bool(intent.get_field("quote_pool_fingerprint"))

    if not has_hash and not has_witness and not has_snapshot_marker:
        return "none"
    if has_witness:
        if snapshot_provided:
            return "attached_verified" if _has_verified_quote_receipt_witness(env, pools=pools) else "attached_invalid"
        return "attached_unverified"
    if has_hash:
        return "hash_only"
    if has_snapshot_marker:
        return "snapshot_only"
    return "none"


def _quote_receipt_group_records(signed_intents: list[SignedIntentEnvelope]) -> list[dict[str, Any]]:
    grouped: dict[str, list[SignedIntentEnvelope]] = {}
    for env in signed_intents:
        quote_hash = env.intent.get_field("quote_receipt_hash")
        if not isinstance(quote_hash, str) or not quote_hash:
            continue
        grouped.setdefault(quote_hash, []).append(env)

    records: list[dict[str, Any]] = []
    for quote_hash in sorted(grouped):
        envs = grouped[quote_hash]
        first_receipt = next((env.quote_receipt for env in envs if isinstance(env.quote_receipt, dict) and env.quote_receipt), None)
        body = first_receipt.get("body") if isinstance(first_receipt, Mapping) else None
        legs = body.get("legs") if isinstance(body, Mapping) else None
        expected_leg_indices = list(range(len(legs))) if isinstance(legs, list) else None

        observed_leg_indices: list[int] = []
        missing_leg_index_intent_ids: list[str] = []
        for env in envs:
            leg_index = env.intent.get_field("quote_receipt_leg_index")
            if not isinstance(leg_index, int) or isinstance(leg_index, bool) or leg_index < 0:
                missing_leg_index_intent_ids.append(env.intent.intent_id)
                continue
            observed_leg_indices.append(int(leg_index))

        duplicate_leg_indices = sorted(
            {
                leg_index
                for leg_index in observed_leg_indices
                if observed_leg_indices.count(leg_index) > 1
            }
        )

        if missing_leg_index_intent_ids:
            status = "missing_leg_index"
        elif duplicate_leg_indices:
            status = "duplicate_leg"
        elif expected_leg_indices is not None and (
            set(observed_leg_indices) != set(expected_leg_indices) or len(observed_leg_indices) != len(expected_leg_indices)
        ):
            status = "incomplete"
        elif expected_leg_indices is not None:
            status = "complete"
        else:
            status = "unverified"

        records.append(
            {
                "quote_receipt_hash": quote_hash,
                "intent_ids": [env.intent.intent_id for env in envs],
                "intent_count": len(envs),
                "attached_witness_count": sum(1 for env in envs if _has_quote_receipt_witness(env)),
                "observed_leg_indices": sorted(observed_leg_indices),
                "expected_leg_indices": expected_leg_indices,
                "missing_leg_index_intent_ids": missing_leg_index_intent_ids,
                "duplicate_leg_indices": duplicate_leg_indices,
                "status": status,
            }
        )
    return records


def _system_spec_aliases(path: Path) -> tuple[str, ...]:
    if not path.exists():
        return ()
    raw = yaml.safe_load(path.read_text(encoding="utf-8"))
    if not isinstance(raw, dict):
        return ()
    modules = raw.get("modules")
    if not isinstance(modules, list):
        return ()
    aliases: list[str] = []
    for mod in modules:
        if isinstance(mod, dict) and isinstance(mod.get("alias"), str) and mod["alias"]:
            aliases.append(str(mod["alias"]))
    return tuple(sorted(set(aliases)))


def _intent_accesses(
    intents: list[Intent],
    *,
    pools: Mapping[str, PoolState],
) -> list[IntentAccess]:
    created = _created_pool_assets(intents)
    return [access_for_intent(intent, pools=pools, created_pools=created) for intent in intents]


def _serialize_balance_keys(keys: Iterable[tuple[str, str, str]]) -> list[dict[str, str]]:
    out: list[dict[str, str]] = []
    for tag, a, b in sorted(keys):
        if tag != _K_BAL:
            continue
        out.append({"pubkey": a, "asset": b})
    return out


def _serialize_lp_keys(keys: Iterable[tuple[str, str, str]]) -> list[dict[str, str]]:
    out: list[dict[str, str]] = []
    for tag, a, b in sorted(keys):
        if tag != _K_LPB:
            continue
        out.append({"pubkey": a, "pool_id": b})
    return out


def _serialize_pool_ids(keys: Iterable[tuple[str, str, str]]) -> list[str]:
    return sorted({a for tag, a, _ in keys if tag == _K_POL})


def _component_scope(
    intents: list[Intent],
    *,
    accesses: Mapping[str, IntentAccess],
    pools: Mapping[str, PoolState],
    created_pools: Mapping[str, tuple[str, str]],
) -> dict[str, Any]:
    reads: set[tuple[str, str, str]] = set()
    writes: set[tuple[str, str, str]] = set()
    senders = sorted({str(intent.sender_pubkey) for intent in intents})
    recipients = sorted({_canonical_recipient(intent) for intent in intents})
    assets = sorted({asset for intent in intents for asset in _intent_assets(intent, pools=pools, created_pools=created_pools)})
    pool_ids = sorted({pid for intent in intents for pid in _intent_pool_ids(intent)})
    kinds = sorted({intent.kind.value for intent in intents})
    quote_bound_ids = sorted(intent.intent_id for intent in intents if _has_quote_receipt_hash(intent))
    nonce_ids = sorted(intent.intent_id for intent in intents if _has_nonce(intent))

    for intent in intents:
        access = accesses[intent.intent_id]
        reads |= set(access.reads)
        writes |= set(access.writes)

    return {
        "intent_ids": [intent.intent_id for intent in intents],
        "size": len(intents),
        "senders": senders,
        "recipients": recipients,
        "pool_ids": pool_ids,
        "assets": assets,
        "kinds": kinds,
        "quote_bound_intent_ids": quote_bound_ids,
        "nonce_bound_intent_ids": nonce_ids,
        "read_scope": {
            "balance_keys": _serialize_balance_keys(reads),
            "pool_ids": _serialize_pool_ids(reads),
            "lp_keys": _serialize_lp_keys(reads),
        },
        "write_scope": {
            "balance_keys": _serialize_balance_keys(writes),
            "pool_ids": _serialize_pool_ids(writes),
            "lp_keys": _serialize_lp_keys(writes),
        },
    }


def _structural_class(
    *,
    intent_count: int,
    sender_count: int,
    recipient_count: int,
    pool_count: int,
    asset_count: int,
    component_count: int,
    largest_component: int,
) -> str:
    if intent_count == 0:
        return "none"
    if (
        intent_count == 1
        and sender_count <= 1
        and recipient_count <= 1
        and pool_count <= 1
        and asset_count <= 2
    ):
        return "local"
    if pool_count <= 1 and largest_component <= 2 and sender_count <= 2 and recipient_count <= 2:
        return "contained"
    if pool_count <= 2 and largest_component <= 4 and component_count <= 2:
        return "medium"
    return "wide"


def _module_record(ev: ModuleEvidence) -> dict[str, Any]:
    flags: list[str] = []
    if not Path(REPO_ROOT / ev.path).exists():
        flags.append("module_file_missing")
    if not ev.imported_by_tests:
        flags.append("not_imported_by_tests")
    if not ev.promoted_claim_ids:
        flags.append("no_promoted_claim")
    if not ev.kernel_python_imports and not ev.esso_imports:
        flags.append("no_kernel_or_esso_surface_hint")
    return {
        "module": ev.module,
        "path": ev.path,
        "imported_by_tests": list(ev.imported_by_tests),
        "kernel_python_imports": list(ev.kernel_python_imports),
        "esso_imports": list(ev.esso_imports),
        "promoted_claim_ids": list(ev.promoted_claim_ids),
        "evidence_flags": flags,
    }


def build_blast_radius_report(
    *,
    operations: Mapping[str, Any],
    snapshot: Optional[Mapping[str, Any]] = None,
    claims_registry_path: Path = CLAIMS_REGISTRY_PATH,
    system_spec_path: Path = SYSTEM_SPEC_PATH,
) -> dict[str, Any]:
    signed_intents = parse_signed_intents(dict(operations))
    intents = [env.intent for env in signed_intents]
    state = state_from_snapshot(snapshot) if snapshot is not None else None
    pools = state.pools if state is not None else {}

    created_pools = _created_pool_assets(intents)
    accesses = _intent_accesses(intents, pools=pools)
    access_by_id = {
        intent.intent_id: access
        for intent, access in zip(intents, accesses, strict=True)
    }
    groups = partition_independent_intents(intents, pools=pools)
    support = derive_batch_state_support(intents, pools=pools)

    senders = sorted({str(intent.sender_pubkey) for intent in intents})
    recipients = sorted({_canonical_recipient(intent) for intent in intents})
    pool_ids = sorted({pid for intent in intents for pid in _intent_pool_ids(intent)})
    assets = sorted({asset for intent in intents for asset in _intent_assets(intent, pools=pools, created_pools=created_pools)})
    intent_kinds = sorted({intent.kind.value for intent in intents})

    support_root = None
    full_state_root = None
    state_support_ratio = None
    full_state_counts = None
    if state is not None:
        full_state_root = compute_state_root(
            balances=state.balances,
            pools=state.pools,
            lp_balances=state.lp_balances,
        )
        support_root = compute_support_state_root(
            balances=state.balances,
            pools=state.pools,
            lp_balances=state.lp_balances,
            support=support,
        )
        full_state_counts = {
            "balance_keys": len(state.balances.get_all_balances()),
            "pool_ids": len(state.pools),
            "lp_keys": len(state.lp_balances.get_all_balances()),
            "nonce_keys": len(state.nonces.get_all()),
        }
        support_num = len(support.balance_keys) + len(support.pool_ids) + len(support.lp_keys)
        support_den = max(
            1,
            len(state.balances.get_all_balances()) + len(state.pools) + len(state.lp_balances.get_all_balances()),
        )
        state_support_ratio = round(float(support_num) / float(support_den), 6)

    system_aliases = _system_spec_aliases(system_spec_path)
    compose_alias_hints = sorted(
        {
            alias
            for intent in intents
            for alias in _COMPOSE_ALIAS_HINTS_BY_KIND.get(intent.kind, ())
            if alias in system_aliases
        }
    )

    touched_core_modules = sorted(
        {
            mod
            for intent in intents
            for mod in _CORE_MODULE_HINTS_BY_KIND.get(intent.kind, ())
        }
    )
    touched_state_modules = sorted(
        {
            mod
            for intent in intents
            for mod in _STATE_MODULE_HINTS_BY_KIND.get(intent.kind, ())
        }
    )
    if any(_has_nonce(intent) for intent in intents):
        touched_state_modules.append("src.state.nonces")
    if any(_has_quote_receipt_hash(intent) for intent in intents):
        touched_core_modules.append("src.core.quote_receipts")

    touched_state_modules = sorted(set(touched_state_modules))
    touched_core_modules = sorted(set(touched_core_modules))

    test_idx = _test_import_index()
    claim_idx = _claims_index(claims_registry_path)
    core_module_records = [
        _module_record(_module_evidence(module=mod, test_idx=test_idx, claim_idx=claim_idx))
        for mod in touched_core_modules + touched_state_modules
    ]

    heuristic_flags: list[str] = []
    limitations: list[str] = []
    if snapshot is None:
        heuristic_flags.append("snapshot_missing")
        limitations.append(
            "No snapshot provided: support-root commitment and LP asset scope for existing pools may be conservative only."
        )
    if len(senders) > 1:
        heuristic_flags.append("batch_spans_multiple_senders")
    if len(recipients) > 1:
        heuristic_flags.append("batch_spans_multiple_recipients")
    if len(pool_ids) > 1:
        heuristic_flags.append("batch_spans_multiple_pools")
    if any(_has_nonce(intent) for intent in intents):
        heuristic_flags.append("nonce_surface_hits_integration_shell")
    quote_bound_envs = [env for env in signed_intents if _has_quote_receipt_hash(env.intent)]
    quote_statuses = [
        _quote_receipt_binding_status(
            env,
            pools=pools,
            snapshot_provided=bool(state is not None),
        )
        for env in signed_intents
    ]
    quote_group_records = _quote_receipt_group_records(signed_intents)
    if quote_bound_envs:
        if state is not None and all(_has_verified_quote_receipt_witness(env, pools=pools) for env in quote_bound_envs):
            heuristic_flags.append("quote_receipt_binding_present_runtime_enforcement_full")
        else:
            heuristic_flags.append("quote_receipt_binding_present_runtime_enforcement_partial")
            limitations.append(
                "Quote receipt binding is only classified as full when attached witnesses verify against the provided snapshot; otherwise enforcement is partial or witness-dependent."
            )
    if "attached_invalid" in quote_statuses:
        heuristic_flags.append("quote_receipt_binding_invalid_witness_present")
    if "hash_only" in quote_statuses:
        heuristic_flags.append("quote_receipt_binding_hash_only_present")
    if "snapshot_only" in quote_statuses:
        heuristic_flags.append("quote_receipt_binding_snapshot_only_present")
    if "attached_unverified" in quote_statuses:
        heuristic_flags.append("quote_receipt_binding_attached_witness_unverified")
    if any(record["status"] == "missing_leg_index" for record in quote_group_records):
        heuristic_flags.append("quote_receipt_binding_missing_leg_index_present")
    if any(record["status"] == "duplicate_leg" for record in quote_group_records):
        heuristic_flags.append("quote_receipt_binding_duplicate_leg_present")
    if any(record["status"] == "incomplete" for record in quote_group_records):
        heuristic_flags.append("quote_receipt_binding_incomplete_group_present")
    if len(groups) < len(intents):
        heuristic_flags.append("conflict_components_reduce_parallelism")
    if any(intent.kind == IntentKind.CREATE_POOL for intent in intents):
        heuristic_flags.append("create_pool_surface_not_explicit_in_compose_v2")
    if not system_aliases:
        heuristic_flags.append("system_spec_aliases_unavailable")
        limitations.append("Compose-alias hints were skipped because the system spec could not be loaded.")

    component_records = [
        {
            "component_id": idx,
            **_component_scope(group, accesses=access_by_id, pools=pools, created_pools=created_pools),
        }
        for idx, group in enumerate(groups)
    ]

    report = {
        "schema": "zenodex/blast-radius-report/v1",
        "repo_root": str(REPO_ROOT),
        "inputs": {
            "intent_count": len(intents),
            "snapshot_provided": bool(snapshot is not None),
            "claims_registry_path": _display_path(claims_registry_path),
            "system_spec_path": _display_path(system_spec_path),
        },
        "summary": {
            "intent_count": len(intents),
            "intent_kinds": intent_kinds,
            "sender_count": len(senders),
            "recipient_count": len(recipients),
            "pool_count": len(pool_ids),
            "asset_count": len(assets),
            "conflict_component_count": len(component_records),
            "largest_conflict_component_size": max((c["size"] for c in component_records), default=0),
            "support_counts": {
                "balance_keys": len(support.balance_keys),
                "pool_ids": len(support.pool_ids),
                "lp_keys": len(support.lp_keys),
            },
            "structural_blast_radius_class": _structural_class(
                intent_count=len(intents),
                sender_count=len(senders),
                recipient_count=len(recipients),
                pool_count=len(pool_ids),
                asset_count=len(assets),
                component_count=len(component_records),
                largest_component=max((c["size"] for c in component_records), default=0),
            ),
        },
        "exact_scope": {
            "full_state_root": full_state_root,
            "support_root": support_root,
            "state_support_ratio": state_support_ratio,
            "full_state_counts": full_state_counts,
            "batch_support": {
                "balance_keys": [{"pubkey": pk, "asset": asset} for pk, asset in support.balance_keys],
                "pool_ids": list(support.pool_ids),
                "lp_keys": [{"pubkey": pk, "pool_id": pool_id} for pk, pool_id in support.lp_keys],
            },
            "conflict_components": component_records,
        },
        "heuristic_scope": {
            "state_surfaces": sorted(
                {
                    *(["balances"] if support.balance_keys else []),
                    *(["pools"] if support.pool_ids else []),
                    *(["lp_balances"] if support.lp_keys else []),
                    *(["nonces"] if any(_has_nonce(intent) for intent in intents) else []),
                }
            ),
            "compose_alias_hints": compose_alias_hints,
            "declared_compose_aliases": list(system_aliases),
            "core_module_hints": touched_core_modules,
            "state_module_hints": touched_state_modules,
            "shell_module_hints": list(_SHELL_MODULE_HINTS),
            "heuristic_flags": heuristic_flags,
        },
        "intents": [
            {
                "intent_id": intent.intent_id,
                "kind": intent.kind.value,
                "sender_pubkey": str(intent.sender_pubkey),
                "recipient": _canonical_recipient(intent),
                "pool_ids": list(_intent_pool_ids(intent)),
                "assets": list(_intent_assets(intent, pools=pools, created_pools=created_pools)),
                "has_nonce": _has_nonce(intent),
                "has_quote_receipt_hash": _has_quote_receipt_hash(intent),
                "has_quote_receipt_witness": any(
                    env.intent.intent_id == intent.intent_id and _has_quote_receipt_witness(env)
                    for env in signed_intents
                ),
                "quote_receipt_binding_status": next(
                    (
                        _quote_receipt_binding_status(
                            env,
                            pools=pools,
                            snapshot_provided=bool(state is not None),
                        )
                        for env in signed_intents
                        if env.intent.intent_id == intent.intent_id
                    ),
                    "none",
                ),
            }
            for intent in intents
        ],
        "quote_receipt_groups": quote_group_records,
        "evidence": {
            "functional_core_modules": core_module_records,
        },
        "limitations": limitations,
    }
    return report


def _parse_args(argv: Optional[list[str]] = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Emit a structural blast-radius report for ops['2'] intents.")
    parser.add_argument("--operations", required=True, help="Path to a JSON file containing Tau-style operations.")
    parser.add_argument(
        "--snapshot",
        default="",
        help="Optional path to a DEX snapshot JSON file. Enables exact support-root commitments.",
    )
    parser.add_argument(
        "--claims-registry",
        default=str(CLAIMS_REGISTRY_PATH),
        help="Path to docs/claims_registry.yaml (default: repo-local file).",
    )
    parser.add_argument(
        "--system-spec",
        default=str(SYSTEM_SPEC_PATH),
        help="Path to a system-spec/v1 YAML for compose alias hints.",
    )
    parser.add_argument("--output", default="", help="Optional JSON output path. Defaults to stdout.")
    return parser.parse_args(argv)


def main(argv: Optional[list[str]] = None) -> int:
    args = _parse_args(argv)
    operations_path = Path(str(args.operations))
    if not operations_path.is_absolute():
        operations_path = (Path.cwd() / operations_path).resolve()
    snapshot_path = Path(str(args.snapshot)).resolve() if str(args.snapshot).strip() else None
    claims_registry_path = Path(str(args.claims_registry)).resolve()
    system_spec_path = Path(str(args.system_spec)).resolve()

    operations = _read_json(operations_path)
    snapshot = _read_json(snapshot_path) if snapshot_path is not None else None
    report = build_blast_radius_report(
        operations=operations,
        snapshot=snapshot,
        claims_registry_path=claims_registry_path,
        system_spec_path=system_spec_path,
    )
    payload = _json_dump(report)

    if str(args.output).strip():
        out_path = Path(str(args.output))
        if not out_path.is_absolute():
            out_path = (Path.cwd() / out_path).resolve()
        out_path.write_text(payload, encoding="utf-8")
        print(json.dumps({"ok": True, "out": str(out_path)}, sort_keys=True))
        return 0

    print(payload, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
