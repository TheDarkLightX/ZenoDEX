"""Deterministic ZenoLedger v0 headers, roots, and checkpoints.

This module is intentionally narrow. It commits to ordered transaction bytes,
ingress accountability facts, settlement evidence, and DEX state roots. It does
not define new DEX execution semantics.
"""

from __future__ import annotations

import re
from copy import deepcopy
from typing import Any, Iterable, Mapping, Sequence

from src.core.dex import DexState
from src.integration.dex_engine import DexEngineConfig, apply_ops
from src.integration.dex_snapshot import snapshot_from_state
from src.integration.generic_token_authority_bridge import (
    generic_token_authority_from_obj,
    generic_token_authority_to_obj,
)
from src.integration.risc0_tx_order_body_summary import tx_execution_order_for_body_v1
from src.state.app_root import APP_ROOT_LANE_KINDS, AppRootLeaf, compute_required_app_root
from src.state.canonical import (
    canonical_hex_fixed_allow_0x,
    canonical_json_bytes,
    domain_sep_bytes,
    encode_bytes,
    encode_uvarint,
    hex_to_bytes_fixed,
    sha256_hex,
)

HEADER_SCHEMA_V0 = "zenodex/zeno_ledger/header/v0"
BODY_SCHEMA_V0 = "zenodex/zeno_ledger/body/v0"
CHECKPOINT_SCHEMA_V0 = "zenodex/zeno_ledger/checkpoint/v0"
VALIDATOR_SET_SCHEMA_V0 = "zenodex/zeno_ledger/validator_set/v0"
BATCH_CUTOFF_SCHEMA_V0 = "zenodex/zeno_ledger/batch_cutoff/v0"
INGRESS_RECEIPT_SCHEMA_V0 = "zenodex/zeno_ledger/ingress_receipt/v0"
FORCED_INCLUSION_REQUEST_SCHEMA_V0 = "zenodex/zeno_ledger/forced_inclusion_request/v0"
FORCED_INCLUSION_DECISION_SCHEMA_V0 = "zenodex/zeno_ledger/forced_inclusion_decision/v0"
TX_RECEIPT_SCHEMA_V0 = "zenodex/zeno_ledger/tx_receipt/v0"
PROOF_METADATA_SCHEMA_V0 = "zenodex/zeno_ledger/proof_metadata/v0"

LEDGER_ROOT_VERSION = 1
ROOT_NBYTES = 32
ZERO_ROOT_V0 = "0x" + "00" * ROOT_NBYTES

EMPTY_MERKLE_ROOT_V0 = sha256_hex(
    domain_sep_bytes("zeno_ledger_empty_merkle", version=LEDGER_ROOT_VERSION)
)

INGRESS_RECEIPT_STATUSES_V0 = frozenset(
    {
        "included",
        "pre_admission_rejected",
        "deferred_after_cutoff",
        "forced_inclusion_pending",
        "forced_inclusion_included",
        "forced_inclusion_rejected",
    }
)

FORCED_INCLUSION_DECISIONS_V0 = frozenset(
    {
        "included",
        "pre_admission_rejected",
        "expired_bad_request",
        "expired_missing_body",
    }
)

PROOF_KINDS_V0 = frozenset(
    {
        "deterministic_replay_v0",
        "risc0_zkvm_v0",
        "sp1_zkvm_v0",
        "tee_attestation_v0",
        "recursive_epoch_v0",
    }
)

ZK_PROOF_KINDS_V0 = frozenset({"risc0_zkvm_v0", "sp1_zkvm_v0"})

EVIDENCE_KEYS_V0 = (
    "upba_certificates",
    "price_grid_tables",
    "uniform_batch_hypergraph_roots",
    "oracle_packets",
    "proof_receipts",
    "rejection_receipts",
)

HEADER_ROOT_FIELDS_V0 = (
    "prev_header_hash",
    "sequencer_set_hash",
    "ingress_root",
    "tx_root",
    "pre_state_root",
    "post_state_root",
    "app_hash",
    "evidence_root",
    "body_root",
    "data_availability_root",
    "proof_journal_hash",
    "config_digest",
    "module_versions_digest",
    "signature_set_root",
)

APP_HASH_ROOT_FIELDS_V0 = (
    "post_state_root",
    "evidence_root",
    "config_digest",
    "module_versions_digest",
)

TAU_APP_STATE_SCHEMA_V1 = "zenodex/tau_app_state/v1"
TAU_APP_STATE_VERSION_V1 = 1
TAU_APP_STATE_SCHEMA_V2 = "zenodex/tau_app_state/v2"
TAU_APP_STATE_VERSION_V2 = 2

APP_ROOT_SPOT_LANE_SCHEMA_V0 = "zenodex/zeno_ledger/app_root/spot_lane/v0"
APP_ROOT_TAU_SPOT_LANE_SCHEMA_V0 = "zenodex/zeno_ledger/app_root/tau_spot_lane/v0"
APP_ROOT_SINGLETON_LANE_SCHEMA_V0 = "zenodex/zeno_ledger/app_root/singleton_lane/v0"

APP_ROOT_SPOT_KEYS_V0 = (
    "version",
    "balances",
    "pools",
    "lp_balances",
    "lp_mint_timestamps",
    "lp_duration_risk",
    "nonces",
    "fee_accumulator",
)

APP_ROOT_DEX_LANE_KINDS_V0 = frozenset({"spot", "oracle", "vault", "perps"})
APP_ROOT_REQUIRED_DEX_LANE_KINDS_V0 = APP_ROOT_LANE_KINDS
APP_ROOT_REQUIRED_TAU_APP_LANE_KINDS_V0 = APP_ROOT_LANE_KINDS

_DOMAIN_RE = re.compile(r"^[A-Za-z0-9_.:/-]+$")


def _require_mapping(value: object, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be a JSON object")
    return value


def _require_list(value: object, *, name: str) -> list[Any]:
    if not isinstance(value, list):
        raise TypeError(f"{name} must be a list")
    return value


def _require_str(value: object, *, name: str, allow_empty: bool = False) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a str")
    if not allow_empty and value == "":
        raise ValueError(f"{name} must be non-empty")
    return value


def _require_nonnegative_int(value: object, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise ValueError(f"{name} must be a non-negative int")
    return value


def _require_optional_str(value: object, *, name: str) -> str | None:
    if value is None:
        return None
    return _require_str(value, name=name)


def _require_root(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a str")
    canonical = canonical_hex_fixed_allow_0x(value, nbytes=ROOT_NBYTES, name=name)
    if value != canonical:
        raise ValueError(f"{name} must be canonical lowercase 0x-prefixed hex")
    return canonical


def _require_nonzero_root(value: object, *, name: str) -> str:
    root = _require_root(value, name=name)
    if root == ZERO_ROOT_V0:
        raise ValueError(f"{name} must be non-zero")
    return root


def _validate_domain(domain: str) -> str:
    if not isinstance(domain, str) or not domain:
        raise TypeError("domain must be a non-empty str")
    if not _DOMAIN_RE.fullmatch(domain):
        raise ValueError("domain contains unsupported characters")
    return domain


def canonical_json_bytes_v0(value: object) -> bytes:
    """Canonical JSON bytes used for ZenoLedger v0 commitments."""

    return canonical_json_bytes(value)


def hash_v0(domain: str, value: object | bytes) -> str:
    """Hash a value with ZenoLedger v0 domain separation."""

    domain = _validate_domain(domain)
    prefix = domain_sep_bytes(f"zeno_ledger_{domain}", version=LEDGER_ROOT_VERSION)
    if isinstance(value, (bytes, bytearray)):
        payload = prefix + encode_bytes(bytes(value))
    else:
        payload = prefix + encode_bytes(canonical_json_bytes_v0(value))
    return sha256_hex(payload)


def _root_bytes(root: str, *, name: str) -> bytes:
    _require_root(root, name=name)
    return hex_to_bytes_fixed(root, nbytes=ROOT_NBYTES, name=name)


def merkle_root_v0(domain: str, leaves: Sequence[str]) -> str:
    """Compute an ordered binary Merkle commitment over 32-byte leaf hashes."""

    domain = _validate_domain(domain)
    if not isinstance(leaves, Sequence) or isinstance(leaves, (str, bytes, bytearray)):
        raise TypeError("leaves must be a sequence of root strings")
    if len(leaves) == 0:
        return EMPTY_MERKLE_ROOT_V0

    nodes: list[bytes] = []
    for index, leaf in enumerate(leaves):
        leaf_bytes = _root_bytes(leaf, name=f"leaf[{index}]")
        nodes.append(
            bytes.fromhex(
                hash_v0(
                    f"merkle_leaf_{domain}",
                    domain_sep_bytes(f"zeno_ledger_leaf_index_{domain}", version=LEDGER_ROOT_VERSION)
                    + encode_uvarint(index)
                    + leaf_bytes,
                )[2:]
            )
        )

    level = 0
    while len(nodes) > 1:
        next_nodes: list[bytes] = []
        for pair_index in range(0, len(nodes), 2):
            left = nodes[pair_index]
            right = nodes[pair_index + 1] if pair_index + 1 < len(nodes) else left
            next_nodes.append(
                bytes.fromhex(
                    hash_v0(
                        f"merkle_node_{domain}",
                        domain_sep_bytes(
                            f"zeno_ledger_node_index_{domain}",
                            version=LEDGER_ROOT_VERSION,
                        )
                        + encode_uvarint(level)
                        + encode_uvarint(pair_index // 2)
                        + left
                        + right,
                    )[2:]
                )
            )
        nodes = next_nodes
        level += 1
    return "0x" + nodes[0].hex()


def tx_hash_v0(tx: object) -> str:
    return hash_v0("tx_v0", tx)


def compute_tx_root_v0(transactions: list[object]) -> str:
    _require_list(transactions, name="transactions")
    return merkle_root_v0("tx_root_v0", [tx_hash_v0(tx) for tx in transactions])


def dex_state_root_v0(state: DexState) -> str:
    if not isinstance(state, DexState):
        raise TypeError("state must be a DexState")
    return compute_dex_state_app_root_v0(state)


def _require_positive_int(value: object, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value <= 0:
        raise ValueError(f"{name} must be a positive int")
    return value


def _dex_snapshot_version_for_app_root_v0(snapshot: Mapping[str, Any]) -> int:
    return _require_positive_int(snapshot.get("version"), name="dex_snapshot.version")


def _spot_lane_payload_from_snapshot_v0(snapshot: Mapping[str, Any]) -> dict[str, Any]:
    missing = [key for key in APP_ROOT_SPOT_KEYS_V0 if key not in snapshot]
    if missing:
        raise ValueError(f"dex_snapshot missing spot app-root field(s): {', '.join(missing)}")
    version = _dex_snapshot_version_for_app_root_v0(snapshot)
    for key in (
        "balances",
        "pools",
        "lp_balances",
        "lp_mint_timestamps",
        "lp_duration_risk",
        "nonces",
    ):
        _require_list(snapshot.get(key), name=f"dex_snapshot.{key}")
    _require_mapping(snapshot.get("fee_accumulator"), name="dex_snapshot.fee_accumulator")
    return {
        "schema": APP_ROOT_SPOT_LANE_SCHEMA_V0,
        "snapshot_version": version,
        "state": {
            key: snapshot[key]
            for key in APP_ROOT_SPOT_KEYS_V0
            if key != "version"
        },
    }


def _snapshot_singleton_lane_payload_v0(
    *,
    lane_kind: str,
    snapshot_version: int,
    state: object,
) -> dict[str, Any]:
    return {
        "schema": APP_ROOT_SINGLETON_LANE_SCHEMA_V0,
        "lane_kind": lane_kind,
        "snapshot_version": snapshot_version,
        "state": state,
    }


def _wrapper_singleton_lane_payload_v0(
    *,
    lane_kind: str,
    app_state_version: int,
    state: object,
    source_key: str,
) -> dict[str, Any]:
    return {
        "schema": APP_ROOT_SINGLETON_LANE_SCHEMA_V0,
        "lane_kind": lane_kind,
        "app_state_version": app_state_version,
        "source_key": source_key,
        "state": state,
    }


def app_root_lanes_from_dex_snapshot_v0(snapshot: Mapping[str, Any]) -> tuple[AppRootLeaf, ...]:
    """Return the DexState lanes committed by the app-root JMT bridge.

    Review note, grade A-: the old spot ``state_root`` commitment excluded
    oracle, vault, and perps state. These leaves make each lane explicit and
    include ``None`` lane state where a module is empty.

    Review note, grade B+ -> A-: this path previously returned only the four
    DexState lanes while the app-root evidence builder labeled the root as a
    full multi-lane keystone. That failed review because wrapper-only lanes
    could be silently omitted. The fix commits explicit empty
    ``proof_mining``, ``zusd``, and ``clob`` leaves for Dex snapshots, so a
    full-root claim binds absence instead of relying on a partial tree.
    """

    obj = _require_mapping(snapshot, name="dex_snapshot")
    version = _dex_snapshot_version_for_app_root_v0(obj)
    for key in ("oracle", "vault", "perps"):
        if key not in obj:
            raise ValueError(f"dex_snapshot missing {key} app-root field")
    return (
        AppRootLeaf.from_json(
            lane_kind="spot",
            lane_id="global",
            payload=_spot_lane_payload_from_snapshot_v0(obj),
        ),
        AppRootLeaf.from_json(
            lane_kind="oracle",
            lane_id="global",
            payload=_snapshot_singleton_lane_payload_v0(
                lane_kind="oracle",
                snapshot_version=version,
                state=obj.get("oracle"),
            ),
        ),
        AppRootLeaf.from_json(
            lane_kind="vault",
            lane_id="protocol",
            payload=_snapshot_singleton_lane_payload_v0(
                lane_kind="vault",
                snapshot_version=version,
                state=obj.get("vault"),
            ),
        ),
        AppRootLeaf.from_json(
            lane_kind="perps",
            lane_id="global",
            payload=_snapshot_singleton_lane_payload_v0(
                lane_kind="perps",
                snapshot_version=version,
                state=obj.get("perps"),
            ),
        ),
        AppRootLeaf.from_json(
            lane_kind="proof_mining",
            lane_id="global",
            payload=_snapshot_singleton_lane_payload_v0(
                lane_kind="proof_mining",
                snapshot_version=version,
                state=None,
            ),
        ),
        AppRootLeaf.from_json(
            lane_kind="zusd",
            lane_id="system",
            payload=_snapshot_singleton_lane_payload_v0(
                lane_kind="zusd",
                snapshot_version=version,
                state=None,
            ),
        ),
        AppRootLeaf.from_json(
            lane_kind="clob",
            lane_id="global",
            payload=_snapshot_singleton_lane_payload_v0(
                lane_kind="clob",
                snapshot_version=version,
                state=None,
            ),
        ),
        AppRootLeaf.from_json(
            lane_kind="cross_shard",
            lane_id="global",
            payload=_snapshot_singleton_lane_payload_v0(
                lane_kind="cross_shard",
                snapshot_version=version,
                state=obj.get("cross_shard"),
            ),
        ),
        AppRootLeaf.from_json(
            lane_kind="governance",
            lane_id="global",
            payload=_snapshot_singleton_lane_payload_v0(
                lane_kind="governance",
                snapshot_version=version,
                state=obj.get("governance"),
            ),
        ),
    )


def app_root_lanes_from_dex_state_v0(state: DexState) -> tuple[AppRootLeaf, ...]:
    if not isinstance(state, DexState):
        raise TypeError("state must be a DexState")
    return app_root_lanes_from_dex_snapshot_v0(snapshot_from_state(state).data)


def compute_dex_snapshot_app_root_v0(
    snapshot: Mapping[str, Any],
    *,
    required_lane_kinds: Iterable[str] = APP_ROOT_REQUIRED_DEX_LANE_KINDS_V0,
) -> str:
    return compute_required_app_root(
        app_root_lanes_from_dex_snapshot_v0(snapshot),
        required_lane_kinds=required_lane_kinds,
    )


def compute_dex_state_app_root_v0(
    state: DexState,
    *,
    required_lane_kinds: Iterable[str] = APP_ROOT_REQUIRED_DEX_LANE_KINDS_V0,
) -> str:
    return compute_required_app_root(
        app_root_lanes_from_dex_state_v0(state),
        required_lane_kinds=required_lane_kinds,
    )


def _tau_app_state_version_for_app_root_v0(app_state: Mapping[str, Any]) -> int:
    schema = app_state.get("schema")
    if schema == TAU_APP_STATE_SCHEMA_V1:
        version = _require_positive_int(
            app_state.get("version", TAU_APP_STATE_VERSION_V1),
            name="app_state.version",
        )
        if version != TAU_APP_STATE_VERSION_V1:
            raise ValueError(f"unsupported app_state version: {version}")
        return version
    if schema == TAU_APP_STATE_SCHEMA_V2:
        version = _require_positive_int(
            app_state.get("version"),
            name="app_state.version",
        )
        if version != TAU_APP_STATE_VERSION_V2:
            raise ValueError(f"unsupported app_state version: {version}")
        return version
    raise ValueError("app_state schema mismatch")


def _clob_lane_source_and_state_v0(app_state: Mapping[str, Any]) -> tuple[str, object]:
    has_clob = "clob" in app_state
    has_orderbook = "orderbook" in app_state
    if has_clob and has_orderbook:
        raise ValueError("app_state must not carry both clob and orderbook lanes")
    if has_clob:
        return "clob", app_state.get("clob")
    if has_orderbook:
        return "orderbook", app_state.get("orderbook")
    return "missing", None


def app_root_lanes_from_tau_app_state_v0(app_state: Mapping[str, Any]) -> tuple[AppRootLeaf, ...]:
    """Return all live Tau app-state lanes for the JMT app-root bridge.

    This is a bridge helper, not a header-v1 migration by itself. It is meant to
    give release gates a precise root target while keeping ZenoLedger v0 header
    validation stable.
    """

    obj = _require_mapping(app_state, name="app_state")
    allowed_keys = {
        "schema",
        "version",
        "dex_state",
        "proof_mining",
        "zusd_monetary",
        "clob",
        "orderbook",
        "cross_shard",
        "governance",
    }
    version = _tau_app_state_version_for_app_root_v0(obj)
    if version == TAU_APP_STATE_VERSION_V2:
        allowed_keys.add("generic_token_authority")
    extra = sorted(set(obj) - allowed_keys)
    if extra:
        raise ValueError(f"unsupported app_state app-root field(s): {', '.join(extra)}")
    dex_snapshot = _require_mapping(obj.get("dex_state"), name="app_state.dex_state")
    generic_authority_obj: dict[str, Any] | None = None
    if version == TAU_APP_STATE_VERSION_V2:
        generic_authority_obj = generic_token_authority_to_obj(
            generic_token_authority_from_obj(obj.get("generic_token_authority"))
        )
    clob_source_key, clob_state = _clob_lane_source_and_state_v0(obj)
    leaves: list[AppRootLeaf] = []
    for leaf in app_root_lanes_from_dex_snapshot_v0(dex_snapshot):
        if leaf.lane_kind not in APP_ROOT_DEX_LANE_KINDS_V0:
            continue
        if leaf.lane_kind == "spot" and generic_authority_obj is not None:
            leaves.append(
                AppRootLeaf.from_json(
                    lane_kind="spot",
                    lane_id="global",
                    payload={
                        "schema": APP_ROOT_TAU_SPOT_LANE_SCHEMA_V0,
                        "app_state_version": version,
                        "dex_spot": _spot_lane_payload_from_snapshot_v0(dex_snapshot),
                        "generic_token_authority": generic_authority_obj,
                    },
                )
            )
        else:
            leaves.append(leaf)
    leaves.extend(
        (
            AppRootLeaf.from_json(
                lane_kind="proof_mining",
                lane_id="global",
                payload=_wrapper_singleton_lane_payload_v0(
                    lane_kind="proof_mining",
                    app_state_version=version,
                    source_key="proof_mining" if "proof_mining" in obj else "missing",
                    state=obj.get("proof_mining"),
                ),
            ),
            AppRootLeaf.from_json(
                lane_kind="zusd",
                lane_id="system",
                payload=_wrapper_singleton_lane_payload_v0(
                    lane_kind="zusd",
                    app_state_version=version,
                    source_key="zusd_monetary" if "zusd_monetary" in obj else "missing",
                    state=obj.get("zusd_monetary"),
                ),
            ),
            AppRootLeaf.from_json(
                lane_kind="clob",
                lane_id="global",
                payload=_wrapper_singleton_lane_payload_v0(
                    lane_kind="clob",
                    app_state_version=version,
                    source_key=clob_source_key,
                    state=clob_state,
                ),
            ),
            AppRootLeaf.from_json(
                lane_kind="cross_shard",
                lane_id="global",
                payload=_wrapper_singleton_lane_payload_v0(
                    lane_kind="cross_shard",
                    app_state_version=version,
                    source_key="cross_shard" if "cross_shard" in obj else "missing",
                    state=obj.get("cross_shard"),
                ),
            ),
            AppRootLeaf.from_json(
                lane_kind="governance",
                lane_id="global",
                payload=_wrapper_singleton_lane_payload_v0(
                    lane_kind="governance",
                    app_state_version=version,
                    source_key="governance" if "governance" in obj else "missing",
                    state=obj.get("governance"),
                ),
            ),
        )
    )
    return tuple(leaves)


def compute_tau_app_state_app_root_v0(
    app_state: Mapping[str, Any],
    *,
    required_lane_kinds: Iterable[str] = APP_ROOT_REQUIRED_TAU_APP_LANE_KINDS_V0,
) -> str:
    return compute_required_app_root(
        app_root_lanes_from_tau_app_state_v0(app_state),
        required_lane_kinds=required_lane_kinds,
    )


def _stable_error_code_v0(error: str | None) -> str:
    raw = "unknown_error" if not error else str(error).strip().lower()
    out = re.sub(r"[^a-z0-9_]+", "_", raw).strip("_")
    return out[:160] or "unknown_error"


def stable_error_code_v0(error: str | None) -> str:
    return _stable_error_code_v0(error)


def build_tx_receipt_v0(
    *,
    tx_hash: str,
    height: int,
    index: int,
    accepted: bool,
    error_code: str | None,
    state_changed: bool,
) -> dict[str, Any]:
    _require_root(tx_hash, name="tx_hash")
    _require_nonnegative_int(height, name="height")
    _require_nonnegative_int(index, name="index")
    if not isinstance(accepted, bool):
        raise TypeError("accepted must be a bool")
    if not isinstance(state_changed, bool):
        raise TypeError("state_changed must be a bool")
    if accepted and error_code is not None:
        raise ValueError("accepted receipt must not carry error_code")
    if not accepted:
        _require_str(error_code, name="error_code")
    body = {
        "schema": TX_RECEIPT_SCHEMA_V0,
        "tx_hash": tx_hash,
        "height": height,
        "index": index,
        "accepted": accepted,
        "error_code": error_code,
        "state_changed": state_changed,
    }
    return {**body, "receipt_hash": hash_v0("tx_receipt_v0", body)}


def build_proof_metadata_v0(
    *,
    chain_id: str,
    height: int,
    proof_kind: str,
    program_id: str,
    verifier_id: str,
    proof_commitment: str,
    public_input_hash: str,
    journal_hash: str,
    pre_state_root: str,
    post_state_root: str,
    tx_root: str,
    evidence_root: str,
    body_root: str,
    conflict_schedule_hash: str,
    feature_suite_hash: str,
    dependency_lock_hash: str,
    toolchain_lock_hash: str,
    tee_measurement_hash: str = ZERO_ROOT_V0,
    child_receipts_root: str = ZERO_ROOT_V0,
) -> dict[str, Any]:
    """Build proof metadata that can be bound into `header.proof_journal_hash`.

    This object is backend-neutral. It does not verify Risc0/SP1/TEE cryptography;
    it records the public binding contract that those verifiers must satisfy.
    """

    metadata = {
        "schema": PROOF_METADATA_SCHEMA_V0,
        "chain_id": chain_id,
        "height": height,
        "proof_kind": proof_kind,
        "program_id": program_id,
        "verifier_id": verifier_id,
        "proof_commitment": proof_commitment,
        "public_input_hash": public_input_hash,
        "journal_hash": journal_hash,
        "pre_state_root": pre_state_root,
        "post_state_root": post_state_root,
        "tx_root": tx_root,
        "evidence_root": evidence_root,
        "body_root": body_root,
        "conflict_schedule_hash": conflict_schedule_hash,
        "feature_suite_hash": feature_suite_hash,
        "dependency_lock_hash": dependency_lock_hash,
        "toolchain_lock_hash": toolchain_lock_hash,
        "tee_measurement_hash": tee_measurement_hash,
        "child_receipts_root": child_receipts_root,
    }
    validate_proof_metadata_v0(metadata)
    return metadata


def validate_proof_metadata_v0(metadata: dict[str, Any]) -> None:
    obj = _require_mapping(metadata, name="proof_metadata")
    expected = {
        "schema",
        "chain_id",
        "height",
        "proof_kind",
        "program_id",
        "verifier_id",
        "proof_commitment",
        "public_input_hash",
        "journal_hash",
        "pre_state_root",
        "post_state_root",
        "tx_root",
        "evidence_root",
        "body_root",
        "conflict_schedule_hash",
        "feature_suite_hash",
        "dependency_lock_hash",
        "toolchain_lock_hash",
        "tee_measurement_hash",
        "child_receipts_root",
    }
    if set(obj.keys()) != expected:
        raise ValueError("proof_metadata keys mismatch")
    if obj.get("schema") != PROOF_METADATA_SCHEMA_V0:
        raise ValueError("proof_metadata schema mismatch")

    _require_str(obj.get("chain_id"), name="proof_metadata.chain_id")
    _require_nonnegative_int(obj.get("height"), name="proof_metadata.height")
    proof_kind = _require_str(obj.get("proof_kind"), name="proof_metadata.proof_kind")
    if proof_kind not in PROOF_KINDS_V0:
        raise ValueError("proof_metadata proof_kind is not allowed")
    _require_str(obj.get("program_id"), name="proof_metadata.program_id")
    _require_str(obj.get("verifier_id"), name="proof_metadata.verifier_id")
    for key in (
        "proof_commitment",
        "public_input_hash",
        "journal_hash",
        "pre_state_root",
        "post_state_root",
        "tx_root",
        "evidence_root",
        "body_root",
        "conflict_schedule_hash",
        "feature_suite_hash",
        "dependency_lock_hash",
        "toolchain_lock_hash",
    ):
        _require_nonzero_root(obj.get(key), name=f"proof_metadata.{key}")
    for key in (
        "tee_measurement_hash",
        "child_receipts_root",
    ):
        _require_root(obj.get(key), name=f"proof_metadata.{key}")

    tee_measurement_hash = obj["tee_measurement_hash"]
    child_receipts_root = obj["child_receipts_root"]
    if proof_kind == "tee_attestation_v0":
        _require_nonzero_root(tee_measurement_hash, name="proof_metadata.tee_measurement_hash")
    elif tee_measurement_hash != ZERO_ROOT_V0:
        raise ValueError("proof_metadata tee_measurement_hash must be zero for non-TEE proof")

    if proof_kind == "recursive_epoch_v0":
        _require_nonzero_root(child_receipts_root, name="proof_metadata.child_receipts_root")
    elif child_receipts_root != ZERO_ROOT_V0:
        raise ValueError("proof_metadata child_receipts_root must be zero for non-recursive proof")

    if proof_kind in ZK_PROOF_KINDS_V0 and obj["program_id"] == obj["verifier_id"]:
        raise ValueError("proof_metadata zk program_id and verifier_id must be distinct")


def proof_metadata_hash_v0(metadata: dict[str, Any]) -> str:
    validate_proof_metadata_v0(metadata)
    return hash_v0("proof_metadata_v0", metadata)


def _extract_tx_operations_v0(tx: object, *, index: int) -> Mapping[str, Any]:
    obj = _require_mapping(tx, name=f"transactions[{index}]")
    operations = obj.get("operations")
    if operations is None:
        raise ValueError(f"transactions[{index}].operations is required")
    return _require_mapping(operations, name=f"transactions[{index}].operations")


def _extract_tx_block_timestamp_v0(tx: object, *, index: int, default: int | None) -> int:
    obj = _require_mapping(tx, name=f"transactions[{index}]")
    value = obj.get("block_timestamp", default)
    if value is None:
        raise ValueError(f"transactions[{index}].block_timestamp is required")
    return _require_nonnegative_int(value, name=f"transactions[{index}].block_timestamp")


def _extract_tx_sender_v0(tx: object, *, index: int) -> str | None:
    obj = _require_mapping(tx, name=f"transactions[{index}]")
    value = obj.get("tx_sender_pubkey")
    if value is None:
        return None
    return _require_str(value, name=f"transactions[{index}].tx_sender_pubkey")


def apply_body_transactions_v0(
    *,
    state: DexState,
    body: dict[str, Any],
    config: DexEngineConfig,
    default_block_timestamp: int | None = None,
) -> tuple[DexState, dict[str, Any], list[dict[str, Any]]]:
    """
    Execute `body.transactions` through `apply_ops`.

    Rejected transactions leave state unchanged and are committed into
    `body.evidence.rejection_receipts` in the returned body.
    """

    if not isinstance(config, DexEngineConfig):
        raise TypeError("config must be a DexEngineConfig")
    validate_body_v0(body)
    working_state = state
    executed_body = deepcopy(body)
    receipts: list[dict[str, Any]] = []
    executed_body["evidence"]["rejection_receipts"] = []
    rejection_receipts = executed_body["evidence"]["rejection_receipts"]
    height = _require_nonnegative_int(executed_body["height"], name="body.height")

    transactions = executed_body["transactions"]
    execution_order = tx_execution_order_for_body_v1(executed_body)
    if len(execution_order) != len(transactions):
        raise ValueError("tx execution order length mismatch")
    receipts_by_index: list[dict[str, Any] | None] = [None] * len(transactions)

    for index in execution_order:
        tx = transactions[index]
        tx_hash = tx_hash_v0(tx)
        try:
            operations = dict(_extract_tx_operations_v0(tx, index=index))
            block_timestamp = _extract_tx_block_timestamp_v0(
                tx,
                index=index,
                default=default_block_timestamp,
            )
            tx_sender = _extract_tx_sender_v0(tx, index=index)
            result = apply_ops(
                config=config,
                state=working_state,
                operations=operations,
                block_timestamp=block_timestamp,
                tx_sender_pubkey=tx_sender,
            )
            if result.ok:
                if result.state is None:
                    raise ValueError("accepted transaction returned no state")
                state_changed = result.state is not working_state
                working_state = result.state
                receipt = build_tx_receipt_v0(
                    tx_hash=tx_hash,
                    height=height,
                    index=index,
                    accepted=True,
                    error_code=None,
                    state_changed=state_changed,
                )
            else:
                receipt = build_tx_receipt_v0(
                    tx_hash=tx_hash,
                    height=height,
                    index=index,
                    accepted=False,
                    error_code=_stable_error_code_v0(result.error),
                    state_changed=False,
                )
                rejection_receipts.append(receipt)
        except (TypeError, ValueError) as exc:
            receipt = build_tx_receipt_v0(
                tx_hash=tx_hash,
                height=height,
                index=index,
                accepted=False,
                error_code=_stable_error_code_v0(str(exc)),
                state_changed=False,
            )
            rejection_receipts.append(receipt)
        receipts_by_index[index] = receipt

    for index, indexed_receipt in enumerate(receipts_by_index):
        if indexed_receipt is None:
            raise ValueError(f"transactions[{index}] was not executed")
        receipts.append(indexed_receipt)

    validate_body_v0(executed_body)
    return working_state, executed_body, receipts


def _validate_batch_cutoff(batch_cutoff: object) -> None:
    obj = _require_mapping(batch_cutoff, name="batch_cutoff")
    if obj.get("schema") != BATCH_CUTOFF_SCHEMA_V0:
        raise ValueError("batch_cutoff schema mismatch")
    _require_str(obj.get("chain_id"), name="batch_cutoff.chain_id")
    _require_nonnegative_int(obj.get("height"), name="batch_cutoff.height")
    _require_nonnegative_int(obj.get("cutoff_time_ms"), name="batch_cutoff.cutoff_time_ms")
    _require_nonnegative_int(obj.get("cutoff_sequence"), name="batch_cutoff.cutoff_sequence")
    _require_str(obj.get("sequencer_id"), name="batch_cutoff.sequencer_id")
    _require_str(obj.get("policy_id"), name="batch_cutoff.policy_id")
    _require_root(obj.get("policy_digest"), name="batch_cutoff.policy_digest")


def _validate_ingress_receipt(receipt: object, *, index: int) -> None:
    obj = _require_mapping(receipt, name=f"ingress_receipts[{index}]")
    if obj.get("schema") != INGRESS_RECEIPT_SCHEMA_V0:
        raise ValueError(f"ingress_receipts[{index}] schema mismatch")
    _require_str(obj.get("chain_id"), name=f"ingress_receipts[{index}].chain_id")
    _require_root(obj.get("tx_hash"), name=f"ingress_receipts[{index}].tx_hash")
    _require_nonnegative_int(
        obj.get("received_time_ms"),
        name=f"ingress_receipts[{index}].received_time_ms",
    )
    _require_nonnegative_int(
        obj.get("received_sequence"),
        name=f"ingress_receipts[{index}].received_sequence",
    )
    _require_str(obj.get("sequencer_id"), name=f"ingress_receipts[{index}].sequencer_id")
    status = _require_str(obj.get("status"), name=f"ingress_receipts[{index}].status")
    if status not in INGRESS_RECEIPT_STATUSES_V0:
        raise ValueError(f"ingress_receipts[{index}] status is not allowed")
    _require_nonnegative_int(obj.get("height"), name=f"ingress_receipts[{index}].height")
    _require_nonnegative_int(obj.get("index"), name=f"ingress_receipts[{index}].index")
    _require_optional_str(obj.get("reject_code"), name=f"ingress_receipts[{index}].reject_code")
    _require_root(obj.get("receipt_hash"), name=f"ingress_receipts[{index}].receipt_hash")


def _validate_forced_inclusion_request(request: object, *, index: int) -> None:
    obj = _require_mapping(request, name=f"forced_inclusion_requests[{index}]")
    if obj.get("schema") != FORCED_INCLUSION_REQUEST_SCHEMA_V0:
        raise ValueError(f"forced_inclusion_requests[{index}] schema mismatch")
    _require_str(obj.get("chain_id"), name=f"forced_inclusion_requests[{index}].chain_id")
    _require_root(obj.get("tx_hash"), name=f"forced_inclusion_requests[{index}].tx_hash")
    _require_root(obj.get("tx_body_hash"), name=f"forced_inclusion_requests[{index}].tx_body_hash")
    _require_str(obj.get("submitter_id"), name=f"forced_inclusion_requests[{index}].submitter_id")
    _require_nonnegative_int(
        obj.get("first_seen_time_ms"),
        name=f"forced_inclusion_requests[{index}].first_seen_time_ms",
    )
    _require_nonnegative_int(
        obj.get("first_seen_sequence"),
        name=f"forced_inclusion_requests[{index}].first_seen_sequence",
    )
    _require_nonnegative_int(
        obj.get("deadline_height"),
        name=f"forced_inclusion_requests[{index}].deadline_height",
    )
    _require_root(obj.get("request_hash"), name=f"forced_inclusion_requests[{index}].request_hash")


def _validate_forced_inclusion_decision(decision: object, *, index: int) -> None:
    obj = _require_mapping(decision, name=f"forced_inclusion_decisions[{index}]")
    if obj.get("schema") != FORCED_INCLUSION_DECISION_SCHEMA_V0:
        raise ValueError(f"forced_inclusion_decisions[{index}] schema mismatch")
    _require_str(obj.get("chain_id"), name=f"forced_inclusion_decisions[{index}].chain_id")
    _require_nonnegative_int(obj.get("height"), name=f"forced_inclusion_decisions[{index}].height")
    _require_root(obj.get("request_hash"), name=f"forced_inclusion_decisions[{index}].request_hash")
    decision_value = _require_str(
        obj.get("decision"),
        name=f"forced_inclusion_decisions[{index}].decision",
    )
    if decision_value not in FORCED_INCLUSION_DECISIONS_V0:
        raise ValueError(f"forced_inclusion_decisions[{index}] decision is not allowed")
    _require_root(obj.get("tx_hash"), name=f"forced_inclusion_decisions[{index}].tx_hash")
    _require_nonnegative_int(obj.get("index"), name=f"forced_inclusion_decisions[{index}].index")
    _require_optional_str(
        obj.get("reject_code"),
        name=f"forced_inclusion_decisions[{index}].reject_code",
    )


def validate_ingress_v0(ingress: dict[str, Any]) -> None:
    obj = _require_mapping(ingress, name="ingress")
    expected = {
        "batch_cutoff",
        "ingress_receipts",
        "forced_inclusion_requests",
        "forced_inclusion_decisions",
    }
    if set(obj.keys()) != expected:
        raise ValueError("ingress keys mismatch")
    _validate_batch_cutoff(obj["batch_cutoff"])
    for index, receipt in enumerate(_require_list(obj["ingress_receipts"], name="ingress_receipts")):
        _validate_ingress_receipt(receipt, index=index)
    for index, request in enumerate(
        _require_list(obj["forced_inclusion_requests"], name="forced_inclusion_requests")
    ):
        _validate_forced_inclusion_request(request, index=index)
    for index, decision in enumerate(
        _require_list(obj["forced_inclusion_decisions"], name="forced_inclusion_decisions")
    ):
        _validate_forced_inclusion_decision(decision, index=index)


def _validate_ingress_body_context_v0(ingress: object, *, chain_id: str, height: int) -> None:
    obj = _require_mapping(ingress, name="ingress")
    batch_cutoff = _require_mapping(obj.get("batch_cutoff"), name="ingress.batch_cutoff")
    if batch_cutoff.get("chain_id") != chain_id:
        raise ValueError("batch_cutoff/body chain_id mismatch")
    if batch_cutoff.get("height") != height:
        raise ValueError("batch_cutoff/body height mismatch")

    for index, raw_receipt in enumerate(_require_list(obj.get("ingress_receipts"), name="ingress.ingress_receipts")):
        receipt = _require_mapping(raw_receipt, name=f"ingress.ingress_receipts[{index}]")
        if receipt.get("chain_id") != chain_id:
            raise ValueError(f"ingress_receipts[{index}]/body chain_id mismatch")
        if receipt.get("height") != height:
            raise ValueError(f"ingress_receipts[{index}]/body height mismatch")

    for index, raw_request in enumerate(
        _require_list(obj.get("forced_inclusion_requests"), name="ingress.forced_inclusion_requests")
    ):
        request = _require_mapping(raw_request, name=f"ingress.forced_inclusion_requests[{index}]")
        if request.get("chain_id") != chain_id:
            raise ValueError(f"forced_inclusion_requests[{index}]/body chain_id mismatch")

    for index, raw_decision in enumerate(
        _require_list(obj.get("forced_inclusion_decisions"), name="ingress.forced_inclusion_decisions")
    ):
        decision = _require_mapping(raw_decision, name=f"ingress.forced_inclusion_decisions[{index}]")
        if decision.get("chain_id") != chain_id:
            raise ValueError(f"forced_inclusion_decisions[{index}]/body chain_id mismatch")


def compute_ingress_root_v0(ingress: dict[str, Any]) -> str:
    validate_ingress_v0(ingress)
    leaves: list[str] = [hash_v0("batch_cutoff_v0", ingress["batch_cutoff"])]
    leaves.extend(hash_v0("ingress_receipt_v0", item) for item in ingress["ingress_receipts"])
    leaves.extend(
        hash_v0("forced_inclusion_request_v0", item)
        for item in ingress["forced_inclusion_requests"]
    )
    leaves.extend(
        hash_v0("forced_inclusion_decision_v0", item)
        for item in ingress["forced_inclusion_decisions"]
    )
    return merkle_root_v0("ingress_root_v0", leaves)


def _validate_evidence(evidence: object) -> Mapping[str, Any]:
    obj = _require_mapping(evidence, name="evidence")
    if set(obj.keys()) != set(EVIDENCE_KEYS_V0):
        raise ValueError("evidence keys mismatch")
    for key in EVIDENCE_KEYS_V0:
        _require_list(obj[key], name=f"evidence.{key}")
    return obj


def compute_evidence_root_v0(evidence: dict[str, Any]) -> str:
    obj = _validate_evidence(evidence)
    leaves: list[str] = []
    for key in EVIDENCE_KEYS_V0:
        leaves.extend(hash_v0(f"evidence_{key}_v0", item) for item in obj[key])
    return merkle_root_v0("evidence_root_v0", leaves)


def validate_body_v0(body: dict[str, Any]) -> None:
    obj = _require_mapping(body, name="body")
    expected = {"schema", "chain_id", "height", "ingress", "transactions", "settlement_envelopes", "evidence"}
    if set(obj.keys()) != expected:
        raise ValueError("body keys mismatch")
    if obj.get("schema") != BODY_SCHEMA_V0:
        raise ValueError("body schema mismatch")
    chain_id = _require_str(obj.get("chain_id"), name="body.chain_id")
    height = _require_nonnegative_int(obj.get("height"), name="body.height")
    validate_ingress_v0(obj["ingress"])
    _validate_ingress_body_context_v0(obj["ingress"], chain_id=chain_id, height=height)
    _require_list(obj.get("transactions"), name="body.transactions")
    _require_list(obj.get("settlement_envelopes"), name="body.settlement_envelopes")
    _validate_evidence(obj.get("evidence"))


def canonical_body_root_v0(body: dict[str, Any]) -> str:
    validate_body_v0(body)
    return hash_v0("body_v0", body)


def compute_app_hash_v0(fields: Mapping[str, Any]) -> str:
    obj = _require_mapping(fields, name="app_hash_fields")
    expected = {"chain_id", "height", *APP_HASH_ROOT_FIELDS_V0}
    if set(obj.keys()) != expected:
        raise ValueError("app_hash fields mismatch")
    _require_str(obj.get("chain_id"), name="app_hash.chain_id")
    _require_nonnegative_int(obj.get("height"), name="app_hash.height")
    for key in APP_HASH_ROOT_FIELDS_V0:
        _require_root(obj.get(key), name=f"app_hash.{key}")
    return hash_v0("app_hash_v0", dict(obj))


def validate_header_v0(header: dict[str, Any]) -> None:
    obj = _require_mapping(header, name="header")
    expected = {"schema", "chain_id", "height", "time_ms", *HEADER_ROOT_FIELDS_V0}
    if set(obj.keys()) != expected:
        raise ValueError("header keys mismatch")
    if obj.get("schema") != HEADER_SCHEMA_V0:
        raise ValueError("header schema mismatch")
    _require_str(obj.get("chain_id"), name="header.chain_id")
    _require_nonnegative_int(obj.get("height"), name="header.height")
    _require_nonnegative_int(obj.get("time_ms"), name="header.time_ms")
    for key in HEADER_ROOT_FIELDS_V0:
        _require_root(obj.get(key), name=f"header.{key}")


def validate_validator_set_v0(validator_set: dict[str, Any]) -> None:
    obj = _require_mapping(validator_set, name="validator_set")
    expected = {"schema", "chain_id", "epoch", "validators"}
    if set(obj.keys()) != expected:
        raise ValueError("validator_set keys mismatch")
    if obj.get("schema") != VALIDATOR_SET_SCHEMA_V0:
        raise ValueError("validator_set schema mismatch")
    _require_str(obj.get("chain_id"), name="validator_set.chain_id")
    _require_nonnegative_int(obj.get("epoch"), name="validator_set.epoch")
    validators = _require_list(obj.get("validators"), name="validator_set.validators")
    if not validators:
        raise ValueError("validator_set.validators must be non-empty")
    seen_ids: set[str] = set()
    seen_public_keys: set[str] = set()
    for index, raw_validator in enumerate(validators):
        validator = _require_mapping(raw_validator, name=f"validator_set.validators[{index}]")
        if set(validator.keys()) != {"validator_id", "public_key", "voting_power"}:
            raise ValueError("validator keys mismatch")
        validator_id = _require_str(validator.get("validator_id"), name="validator.validator_id")
        if validator_id in seen_ids:
            raise ValueError("duplicate validator_id")
        seen_ids.add(validator_id)
        public_key = _require_str(validator.get("public_key"), name="validator.public_key")
        if public_key in seen_public_keys:
            raise ValueError("duplicate validator.public_key")
        seen_public_keys.add(public_key)
        voting_power = _require_nonnegative_int(validator.get("voting_power"), name="validator.voting_power")
        if voting_power == 0:
            raise ValueError("validator.voting_power must be positive")


def validator_set_hash_v0(validator_set: dict[str, Any]) -> str:
    validate_validator_set_v0(validator_set)
    validators = [
        {
            "validator_id": str(validator["validator_id"]),
            "public_key": str(validator["public_key"]),
            "voting_power": int(validator["voting_power"]),
        }
        for validator in validator_set["validators"]
    ]
    normalized = {
        "schema": VALIDATOR_SET_SCHEMA_V0,
        "chain_id": validator_set["chain_id"],
        "epoch": int(validator_set["epoch"]),
        "validators": sorted(validators, key=lambda validator: str(validator["validator_id"])),
    }
    return hash_v0("validator_set_v0", normalized)


def scheduled_validator_id_for_height_v0(
    validator_set: dict[str, Any],
    *,
    height: int,
) -> str:
    validate_validator_set_v0(validator_set)
    height_v = _require_nonnegative_int(height, name="height")
    validators = sorted(
        (
            (
                str(validator["validator_id"]),
                int(validator["voting_power"]),
            )
            for validator in validator_set["validators"]
        ),
        key=lambda item: item[0],
    )
    total_power = sum(power for _, power in validators)
    slot = height_v % total_power
    cumulative = 0
    for validator_id, power in validators:
        cumulative += power
        if slot < cumulative:
            return validator_id
    raise AssertionError("unreachable validator schedule state")


def validate_header_validator_set_hash_v0(
    header: dict[str, Any],
    validator_set: dict[str, Any],
) -> None:
    validate_header_v0(header)
    validate_validator_set_v0(validator_set)
    if header["chain_id"] != validator_set["chain_id"]:
        raise ValueError("header/validator_set chain_id mismatch")
    expected_hash = validator_set_hash_v0(validator_set)
    if header["sequencer_set_hash"] != expected_hash:
        raise ValueError("header sequencer_set_hash mismatch")


def validate_body_validator_schedule_v0(
    body: dict[str, Any],
    validator_set: dict[str, Any],
) -> None:
    validate_body_v0(body)
    validate_validator_set_v0(validator_set)
    if body["chain_id"] != validator_set["chain_id"]:
        raise ValueError("body/validator_set chain_id mismatch")
    batch_cutoff = _require_mapping(body["ingress"].get("batch_cutoff"), name="body.ingress.batch_cutoff")
    sequencer_id = _require_str(batch_cutoff.get("sequencer_id"), name="body.ingress.batch_cutoff.sequencer_id")
    expected = scheduled_validator_id_for_height_v0(validator_set, height=int(body["height"]))
    if sequencer_id != expected:
        raise ValueError("body sequencer_id does not match validator schedule")


def detect_header_equivocations_v0(headers: object) -> list[dict[str, Any]]:
    if not isinstance(headers, Sequence) or isinstance(headers, (str, bytes, bytearray)):
        raise TypeError("headers must be a sequence")
    by_height: dict[tuple[str, int], set[str]] = {}
    for header in headers:
        validate_header_v0(header)
        key = (str(header["chain_id"]), int(header["height"]))
        by_height.setdefault(key, set()).add(canonical_header_hash_v0(header))
    conflicts: list[dict[str, Any]] = []
    for (chain_id, height), hashes in sorted(by_height.items()):
        if len(hashes) > 1:
            conflicts.append(
                {
                    "chain_id": chain_id,
                    "height": height,
                    "header_hashes": sorted(hashes),
                }
            )
    return conflicts


def validate_header_chain_linkage_v0(
    headers: object,
    *,
    expected_prev_header_hash: str | None = None,
) -> None:
    """Fail closed unless an ordered header segment links by parent hash."""

    if not isinstance(headers, Sequence) or isinstance(headers, (str, bytes, bytearray)):
        raise TypeError("headers must be a sequence")
    if not headers:
        raise ValueError("headers must be non-empty")
    if expected_prev_header_hash is not None:
        _require_root(expected_prev_header_hash, name="expected_prev_header_hash")

    normalized: list[dict[str, Any]] = []
    for index, header in enumerate(headers):
        if not isinstance(header, dict):
            raise TypeError(f"headers[{index}] must be a dict")
        validate_header_v0(header)
        normalized.append(header)

    chain_ids = {str(header["chain_id"]) for header in normalized}
    if len(chain_ids) != 1:
        raise ValueError("headers must share one chain_id")

    by_height: dict[int, dict[str, Any]] = {}
    for header in normalized:
        height = int(header["height"])
        if height in by_height:
            raise ValueError("headers must contain unique heights")
        by_height[height] = header
    sorted_headers = [by_height[height] for height in sorted(by_height)]

    first = sorted_headers[0]
    if expected_prev_header_hash is not None and first["prev_header_hash"] != expected_prev_header_hash:
        raise ValueError("first header prev_header_hash mismatch")

    previous = first
    for current in sorted_headers[1:]:
        if int(current["height"]) != int(previous["height"]) + 1:
            raise ValueError("headers must have consecutive heights")
        expected_prev = canonical_header_hash_v0(previous)
        if current["prev_header_hash"] != expected_prev:
            raise ValueError("header prev_header_hash does not match previous header hash")
        previous = current


def canonical_header_chain_tip_v0(headers: Sequence[dict[str, Any]]) -> str:
    validate_header_chain_linkage_v0(headers)
    tip = max(headers, key=lambda header: int(header["height"]))
    return canonical_header_hash_v0(tip)


def evaluate_header_fork_choice_v0(
    headers: object,
    *,
    expected_prev_header_hash: str = ZERO_ROOT_V0,
) -> dict[str, Any]:
    """Select a deterministic canonical branch from an anchored header set."""

    if not isinstance(headers, Sequence) or isinstance(headers, (str, bytes, bytearray)):
        raise TypeError("headers must be a sequence")
    if not headers:
        raise ValueError("headers must be non-empty")
    _require_root(expected_prev_header_hash, name="expected_prev_header_hash")

    hash_to_header: dict[str, dict[str, Any]] = {}
    for index, header in enumerate(headers):
        if not isinstance(header, dict):
            raise TypeError(f"headers[{index}] must be a dict")
        validate_header_v0(header)
        header_hash = canonical_header_hash_v0(header)
        hash_to_header.setdefault(header_hash, header)

    chain_ids = {str(header["chain_id"]) for header in hash_to_header.values()}
    if len(chain_ids) != 1:
        raise ValueError("headers must share one chain_id")
    chain_id = next(iter(chain_ids))

    anchored_chains: list[list[dict[str, Any]]] = []
    orphan_header_hashes: set[str] = set()
    for tip_hash in sorted(hash_to_header):
        chain_hashes_from_tip: list[str] = []
        seen_hashes: set[str] = set()
        current_hash = tip_hash
        anchored = False
        while True:
            if current_hash in seen_hashes:
                raise ValueError("header parent cycle")
            seen_hashes.add(current_hash)
            current = hash_to_header[current_hash]
            chain_hashes_from_tip.append(current_hash)
            parent_hash = str(current["prev_header_hash"])
            if parent_hash == expected_prev_header_hash:
                anchored = True
                break
            parent = hash_to_header.get(parent_hash)
            if parent is None:
                break
            if int(parent["height"]) + 1 != int(current["height"]):
                raise ValueError("header parent height mismatch")
            current_hash = parent_hash

        if anchored:
            chain_headers = [
                hash_to_header[header_hash]
                for header_hash in reversed(chain_hashes_from_tip)
            ]
            validate_header_chain_linkage_v0(
                chain_headers,
                expected_prev_header_hash=expected_prev_header_hash,
            )
            anchored_chains.append(chain_headers)
        else:
            orphan_header_hashes.add(tip_hash)

    if not anchored_chains:
        raise ValueError("no anchored header chain")

    def _score(chain: list[dict[str, Any]]) -> tuple[int, int]:
        return int(chain[-1]["height"]), len(chain)

    best_score = max(_score(chain) for chain in anchored_chains)
    best_candidates = [chain for chain in anchored_chains if _score(chain) == best_score]
    selected = min(best_candidates, key=lambda chain: canonical_header_hash_v0(chain[-1]))
    selected_hashes = [canonical_header_hash_v0(header) for header in selected]

    return {
        "schema": "zenodex/zeno_ledger/header_fork_choice_report/v0",
        "chain_id": chain_id,
        "expected_prev_header_hash": expected_prev_header_hash,
        "canonical_tip_hash": selected_hashes[-1],
        "canonical_tip_height": int(selected[-1]["height"]),
        "canonical_chain_hashes": selected_hashes,
        "anchored_chain_count": len(anchored_chains),
        "orphan_header_hashes": sorted(orphan_header_hashes),
        "tie_breaker": "max_tip_height_then_chain_length_then_lowest_tip_hash",
    }


def select_canonical_header_chain_v0(
    headers: Sequence[dict[str, Any]],
    *,
    expected_prev_header_hash: str = ZERO_ROOT_V0,
) -> list[dict[str, Any]]:
    report = evaluate_header_fork_choice_v0(
        headers,
        expected_prev_header_hash=expected_prev_header_hash,
    )
    by_hash = {canonical_header_hash_v0(header): header for header in headers}
    return [by_hash[header_hash] for header_hash in report["canonical_chain_hashes"]]


def canonical_header_hash_v0(header: dict[str, Any]) -> str:
    validate_header_v0(header)
    return hash_v0("header_v0", header)


def build_header_v0(
    *,
    chain_id: str,
    height: int,
    time_ms: int,
    prev_header_hash: str,
    sequencer_set_hash: str,
    ingress_root: str,
    tx_root: str,
    pre_state_root: str,
    post_state_root: str,
    app_hash: str,
    evidence_root: str,
    body_root: str,
    data_availability_root: str,
    proof_journal_hash: str,
    config_digest: str,
    module_versions_digest: str,
    signature_set_root: str,
) -> dict[str, Any]:
    header = {
        "schema": HEADER_SCHEMA_V0,
        "chain_id": chain_id,
        "height": height,
        "time_ms": time_ms,
        "prev_header_hash": prev_header_hash,
        "sequencer_set_hash": sequencer_set_hash,
        "ingress_root": ingress_root,
        "tx_root": tx_root,
        "pre_state_root": pre_state_root,
        "post_state_root": post_state_root,
        "app_hash": app_hash,
        "evidence_root": evidence_root,
        "body_root": body_root,
        "data_availability_root": data_availability_root,
        "proof_journal_hash": proof_journal_hash,
        "config_digest": config_digest,
        "module_versions_digest": module_versions_digest,
        "signature_set_root": signature_set_root,
    }
    validate_header_v0(header)
    return header


def expected_header_roots_from_body_v0(body: dict[str, Any]) -> dict[str, str]:
    """Return the body-derived header root fields for a ZenoLedger v0 body."""

    validate_body_v0(body)
    return {
        "ingress_root": compute_ingress_root_v0(body["ingress"]),
        "tx_root": compute_tx_root_v0(body["transactions"]),
        "evidence_root": compute_evidence_root_v0(body["evidence"]),
        "body_root": canonical_body_root_v0(body),
    }


def validate_header_body_roots_v0(header: dict[str, Any], body: dict[str, Any]) -> None:
    """Fail closed unless a header commits to the supplied body."""

    validate_header_v0(header)
    validate_body_v0(body)
    if header["chain_id"] != body["chain_id"]:
        raise ValueError("header/body chain_id mismatch")
    if header["height"] != body["height"]:
        raise ValueError("header/body height mismatch")

    expected_roots = expected_header_roots_from_body_v0(body)
    for key, expected in expected_roots.items():
        if header[key] != expected:
            raise ValueError(f"header {key} mismatch")

    expected_app_hash = compute_app_hash_v0(
        {
            "chain_id": header["chain_id"],
            "height": header["height"],
            "post_state_root": header["post_state_root"],
            "evidence_root": header["evidence_root"],
            "config_digest": header["config_digest"],
            "module_versions_digest": header["module_versions_digest"],
        }
    )
    if header["app_hash"] != expected_app_hash:
        raise ValueError("header app_hash mismatch")


def validate_proof_metadata_header_binding_v0(
    metadata: dict[str, Any],
    header: dict[str, Any],
) -> None:
    """Fail closed unless proof metadata is exactly bound to a header."""

    validate_proof_metadata_v0(metadata)
    validate_header_v0(header)
    if metadata["chain_id"] != header["chain_id"]:
        raise ValueError("proof_metadata/header chain_id mismatch")
    if metadata["height"] != header["height"]:
        raise ValueError("proof_metadata/header height mismatch")
    for key in (
        "pre_state_root",
        "post_state_root",
        "tx_root",
        "evidence_root",
        "body_root",
    ):
        if metadata[key] != header[key]:
            raise ValueError(f"proof_metadata/header {key} mismatch")
    if proof_metadata_hash_v0(metadata) != header["proof_journal_hash"]:
        raise ValueError("proof_metadata/header proof_journal_hash mismatch")


def validate_checkpoint_v0(checkpoint: dict[str, Any]) -> None:
    obj = _require_mapping(checkpoint, name="checkpoint")
    expected = {
        "schema",
        "chain_id",
        "height",
        "header_hash",
        "app_hash",
        "post_state_root",
        "ingress_root",
        "evidence_root",
        "body_root",
        "config_digest",
        "proof_journal_hash",
        "sequencer_set_hash",
        "signature_set_root",
        "signature_set",
    }
    if set(obj.keys()) != expected:
        raise ValueError("checkpoint keys mismatch")
    if obj.get("schema") != CHECKPOINT_SCHEMA_V0:
        raise ValueError("checkpoint schema mismatch")
    _require_str(obj.get("chain_id"), name="checkpoint.chain_id")
    _require_nonnegative_int(obj.get("height"), name="checkpoint.height")
    for key in (
        "header_hash",
        "app_hash",
        "post_state_root",
        "ingress_root",
        "evidence_root",
        "body_root",
        "config_digest",
        "proof_journal_hash",
        "sequencer_set_hash",
        "signature_set_root",
    ):
        _require_root(obj.get(key), name=f"checkpoint.{key}")
    _require_list(obj.get("signature_set"), name="checkpoint.signature_set")


def build_checkpoint_v0(header: dict[str, Any], *, signature_set: list[object] | None = None) -> dict[str, Any]:
    validate_header_v0(header)
    checkpoint = {
        "schema": CHECKPOINT_SCHEMA_V0,
        "chain_id": header["chain_id"],
        "height": header["height"],
        "header_hash": canonical_header_hash_v0(header),
        "app_hash": header["app_hash"],
        "post_state_root": header["post_state_root"],
        "ingress_root": header["ingress_root"],
        "evidence_root": header["evidence_root"],
        "body_root": header["body_root"],
        "config_digest": header["config_digest"],
        "proof_journal_hash": header["proof_journal_hash"],
        "sequencer_set_hash": header["sequencer_set_hash"],
        "signature_set_root": header["signature_set_root"],
        "signature_set": [] if signature_set is None else signature_set,
    }
    validate_checkpoint_v0(checkpoint)
    return checkpoint


def validate_checkpoint_header_binding_v0(
    checkpoint: dict[str, Any],
    header: dict[str, Any],
) -> None:
    """Fail closed unless a checkpoint is exactly derived from `header`."""

    validate_checkpoint_v0(checkpoint)
    validate_header_v0(header)
    expected = build_checkpoint_v0(
        header,
        signature_set=checkpoint["signature_set"],
    )
    if checkpoint != expected:
        raise ValueError("checkpoint/header binding mismatch")
