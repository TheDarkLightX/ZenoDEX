#!/usr/bin/env python3
"""Independently replay the Spot V1 to ZRPF V3 adapter hash fixture.

This checker deliberately reimplements the canonical byte layouts. It does not
invoke Rust, parse Rust source, or consume a Rust-produced fixture at runtime.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from typing import Final


ADAPTER_IMAGE_ID_WORDS: Final = (1, 2, 3, 4, 5, 6, 7, 8)
SOURCE_IMAGE_ID_WORDS: Final = (
    1_106_212_114,
    3_876_807_999,
    30_284_647,
    3_707_445_917,
    3_791_588_337,
    1_758_404_023,
    1_845_828_211,
    57_936_497,
)
SOURCE_PROGRAM_SHA256: Final = bytes.fromhex(
    "d1fd8915a3c1650b42527e6b878f203679cd447b506916c6a9a56008ed0951a8"
)
SOURCE_LOCAL_TREE_ROOT: Final = bytes.fromhex(
    "7a3bed2a1d8fff3ad2e93f2d406df435a9990d1a9c0462ff3323fb028327564e"
)
SOURCE_PROOF_TYPE: Final = b"risc0.zenodex_recursive_spot_leaf.v1"
SOURCE_PROFILE: Final = b"recursive_spot_leaf_v1"
ADAPTER_PROFILE: Final = b"zrpf_v1_leaf_adapter_compatibility_v1"

APPLICATION_ID_DOMAIN: Final = b"zenodex.zrpf.application_id.v3"
DOMAIN_ID_DOMAIN: Final = b"zenodex.zrpf.chain_or_domain_id.v3"
PROFILE_ID_DOMAIN: Final = b"zenodex.zrpf.profile_id.v3"
COUNT_UNIT_ID_DOMAIN: Final = b"zenodex.zrpf.count_unit_id.v3"
SOURCE_PROTOCOL_ID_DOMAIN: Final = b"zenodex.zrpf.source_protocol_id.v3"
SOURCE_LANE_ID_DOMAIN: Final = b"zenodex.zrpf.source_lane_id.v3"
SOURCE_MANIFEST_DOMAIN: Final = b"zenodex.zrpf.v1_source_manifest.v1"
SOURCE_BINDING_DOMAIN: Final = b"zenodex.zrpf.source_binding.v3"
ADAPTER_MANIFEST_DOMAIN: Final = b"zenodex.zrpf.v1_adapter_manifest.v1"
ADAPTER_MANIFEST_CLASS: Final = b"unreleased_compatibility_manifest"
TASK_ID_DOMAIN: Final = b"zenodex.zrpf.v1_adapter_task_id.v1"
NODE_STATEMENT_DOMAIN: Final = b"zenodex.zrpf.v1_adapter_node_statement.v1"
PROVENANCE_ROOT_DOMAIN: Final = b"zenodex.zrpf.v1_adapter_provenance_root.v1"
TASK_SET_ROOT_DOMAIN: Final = b"zenodex.zrpf.v1_adapter_task_set_root.v1"
SEMANTIC_SOURCE_SET_ROOT_DOMAIN: Final = (
    b"zenodex.zrpf.v1_adapter_semantic_source_set_root.v1"
)
PARTITION_ENTRY_DOMAIN: Final = b"zenodex.zrpf.v1_adapter_partition_entry.v1"
PARTITION_PLAN_ROOT_DOMAIN: Final = b"zenodex.zrpf.v1_adapter_partition_plan_root.v1"
CONFLICT_SCHEDULE_DOMAIN: Final = b"zenodex.zrpf.v1_adapter_conflict_schedule.v1"
DA_PAYLOAD_ROOT_DOMAIN: Final = b"zenodex.zrpf.v1_adapter_da_payload_root.v1"
UNSUPPORTED_FIELD_DOMAIN: Final = b"zenodex.zrpf.v1_adapter_unsupported_field.v1"
PRE_STATE_VECTOR_DOMAIN: Final = b"zenodex.risc0.recursive.pre_state_vector_root.v1"
POST_STATE_VECTOR_DOMAIN: Final = b"zenodex.risc0.recursive.post_state_vector_root.v1"

EMPTY_CHILD_DOMAINS: Final = (
    b"zenodex.zrpf.child_tasks_root.v3",
    b"zenodex.zrpf.child_claims_root.v3",
    b"zenodex.zrpf.child_journals_root.v3",
    b"zenodex.zrpf.child_programs_root.v3",
    b"zenodex.zrpf.child_profiles_root.v3",
    b"zenodex.zrpf.child_verifiers_root.v3",
    b"zenodex.zrpf.immediate_verifier_set_root.v3",
    b"zenodex.zrpf.child_statements_root.v3",
    b"zenodex.zrpf.child_manifests_root.v3",
    b"zenodex.zrpf.child_effects_root.v3",
    b"zenodex.zrpf.child_provenance_roots.v3",
    b"zenodex.zrpf.child_data_availability_roots.v3",
)

EXPECTED_VECTOR: Final[dict[str, str | int]] = {
    "source_journal_length": 605,
    "source_journal_sha256": (
        "96f78b062f04c8d77e02335815b98ac220f81112cbf7793c22ad588dc0618103"
    ),
    "source_journal_hash": (
        "4f54fc68cec1a5d1ddae5cb47c344395ac7b13f951502164f06e01ab5736b0cf"
    ),
    "source_claim_hash": (
        "6302f3ba6a7164350c6a94837c458d96a69c4ecf09006deba67b35b142aaecd8"
    ),
    "source_verifier_id": (
        "e0a68fa82f2c45a252cd76b3b68dc4968b14f63eecf8a294dd79113c8d3aa536"
    ),
    "source_effect_hash": (
        "15804b0177a987a5bf3b636e066733ea69ca1646cbed1e3b15418ada142528a8"
    ),
    "source_scope_hash": (
        "f48bf7cd090b358a872061e882d52c3aa7f29eb4fc02ac382d4c8d4e3cf9a803"
    ),
    "source_manifest_root": (
        "a0f0fd801f63d4f5055bfd312588b716b612f6a7f85dd65bc6034d67c3a6f955"
    ),
    "source_binding_hash": (
        "99af2b45e51e5f0a95f0d655bb844305ddcb57f41206f43bfb588da8d92d4705"
    ),
    "task_id": "c7ddf09572c68cac733fd9457d53f45e9ae4f2a47860dfe017ae6b70bece91dc",
    "count_unit_id": (
        "fc3f8bdba6c5e7647d5419a61af0ebd31582850020d88ea5aa8b987de8913a5f"
    ),
    "adapter_manifest_root": (
        "872531a2c9b92643a1bcacfef28c25c9007e8d96a170d40b073ea62d77018501"
    ),
    "commitments_hash": (
        "33532707000fa8b33f194cca95f3070415b7df1769a252460562e501072e56be"
    ),
    "node_statement_hash": (
        "7bdbc7a88ccfa6d8544ea489f5cb113ef627acd90b77e3766d99fc0e753cc4a1"
    ),
    "v3_verifier_id": (
        "f9b1970f3d68f47db33575c3aed176db8edcb973b03719d808f58197a2ae1660"
    ),
    "journal_hash": (
        "1c54cfb1bb753dc898b6375563a0f8c8e223e0f9cc72f6154af6380b69a8ca53"
    ),
    "v3_postcard_length": 1_547,
    "v3_postcard_sha256": (
        "64ab9d838fd84fc3fec1643dba0c2c551746df35f96b1dd40b21753e77d6a1a3"
    ),
}


def _u16(value: int) -> bytes:
    return value.to_bytes(2, "big")


def _u32(value: int) -> bytes:
    return value.to_bytes(4, "big")


def _u64(value: int) -> bytes:
    return value.to_bytes(8, "big")


def _domain_prefix(domain: bytes) -> bytes:
    if len(domain) > 0xFFFF:
        raise ValueError("hash domain exceeds u16")
    return _u16(len(domain)) + domain


def _hash_fixed(domain: bytes, *fields: bytes) -> bytes:
    return hashlib.sha256(_domain_prefix(domain) + b"".join(fields)).digest()


def _hash_framed(domain: bytes, *fields: bytes) -> bytes:
    encoded_fields = b"".join(_u32(len(field)) + field for field in fields)
    return hashlib.sha256(_domain_prefix(domain) + encoded_fields).digest()


def _v1_string(value: bytes) -> bytes:
    return _u32(len(value)) + value


def _v1_image_words(words: tuple[int, ...]) -> bytes:
    return b"".join(_u32(word) for word in words)


def _risc0_program_id(words: tuple[int, ...]) -> bytes:
    return b"".join(word.to_bytes(4, "little") for word in words)


def _postcard_uvarint(value: int) -> bytes:
    if value < 0:
        raise ValueError("Postcard unsigned integer cannot be negative")
    encoded = bytearray()
    while value >= 0x80:
        encoded.append((value & 0x7F) | 0x80)
        value >>= 7
    encoded.append(value)
    return bytes(encoded)


def _postcard_string(value: bytes) -> bytes:
    return _postcard_uvarint(len(value)) + value


def _v1_root_list(domain: bytes, roots: tuple[bytes, ...] = ()) -> bytes:
    return hashlib.sha256(domain + _u32(len(roots)) + b"".join(roots)).digest()


def _v3_list_root(domain: bytes, roots: tuple[bytes, ...] = ()) -> bytes:
    return _hash_fixed(domain, _u32(len(roots)), *roots)


@dataclass(frozen=True)
class SpotSummary:
    statement_hash: bytes
    summary_version: int = 1
    lane_id: bytes = b"spot-lane-1"
    lane_kind: bytes = b"spot"
    chain_id: bytes = b"zenodex-test"
    epoch_id: int = 17
    proof_profile: bytes = SOURCE_PROFILE
    image_id_words: tuple[int, ...] = SOURCE_IMAGE_ID_WORDS
    pre_state_root: bytes = bytes([2]) * 32
    post_state_root: bytes = bytes([3]) * 32
    transaction_root: bytes = bytes([4]) * 32
    evidence_root: bytes = bytes([5]) * 32
    receipt_root: bytes = bytes([6]) * 32
    accepted_receipts_root: bytes = _v1_root_list(
        b"zenodex.risc0.recursive.receipt_ids_root.v1"
    )
    rejected_receipts_root: bytes = _v1_root_list(
        b"zenodex.risc0.recursive.receipt_ids_root.v1"
    )
    asset_delta_root: bytes = bytes([7]) * 32
    cross_lane_outbox_root: bytes = _v1_root_list(
        b"zenodex.risc0.recursive.cross_shard_messages_root.v1"
    )
    cross_lane_inbox_root: bytes = _v1_root_list(
        b"zenodex.risc0.recursive.cross_shard_messages_root.v1"
    )
    write_set_root: bytes = bytes([8]) * 32
    public_policy_hash: bytes = bytes([9]) * 32
    feature_suite_hash: bytes = bytes([10]) * 32
    dependency_lock_hash: bytes = bytes([11]) * 32
    toolchain_lock_hash: bytes = bytes([12]) * 32

    def roots_in_wire_order(self) -> tuple[bytes, ...]:
        return (
            self.statement_hash,
            self.pre_state_root,
            self.post_state_root,
            self.transaction_root,
            self.evidence_root,
            self.receipt_root,
            self.accepted_receipts_root,
            self.rejected_receipts_root,
            self.asset_delta_root,
            self.cross_lane_outbox_root,
            self.cross_lane_inbox_root,
            self.write_set_root,
            self.public_policy_hash,
            self.feature_suite_hash,
            self.dependency_lock_hash,
            self.toolchain_lock_hash,
        )


@dataclass(frozen=True)
class MaterializedVector:
    values: dict[str, str | int]
    source_journal: bytes
    v3_postcard: bytes


def _encode_v1_summary_postcard(summary: SpotSummary) -> bytes:
    return b"".join(
        (
            _postcard_uvarint(summary.summary_version),
            _postcard_string(summary.lane_id),
            _postcard_string(summary.lane_kind),
            _postcard_string(summary.chain_id),
            _postcard_uvarint(summary.epoch_id),
            _postcard_string(summary.proof_profile),
            *(_postcard_uvarint(word) for word in summary.image_id_words),
            *summary.roots_in_wire_order(),
        )
    )


def _source_effect_hash(summary: SpotSummary) -> bytes:
    return hashlib.sha256(
        b"zenodex.risc0.recursive.effect_summary_hash.v1"
        + _u32(summary.summary_version)
        + _v1_string(summary.lane_id)
        + _v1_string(summary.lane_kind)
        + _v1_string(summary.chain_id)
        + _u64(summary.epoch_id)
        + _v1_string(summary.proof_profile)
        + _v1_image_words(summary.image_id_words)
        + b"".join(summary.roots_in_wire_order())
    ).digest()


def _lane_state_vector_root(domain: bytes, lane_id: bytes, state_root: bytes) -> bytes:
    return hashlib.sha256(domain + _u32(1) + _v1_string(lane_id) + state_root).digest()


def _profile_id(profile: bytes) -> bytes:
    return _hash_framed(PROFILE_ID_DOMAIN, profile)


def _scope_fields(summary: SpotSummary) -> tuple[bytes, ...]:
    return (
        _hash_framed(APPLICATION_ID_DOMAIN, b"zenodex"),
        _hash_framed(DOMAIN_ID_DOMAIN, summary.chain_id),
        _u64(summary.epoch_id),
        _u64(summary.epoch_id),
        summary.public_policy_hash,
        summary.feature_suite_hash,
        summary.dependency_lock_hash,
        summary.toolchain_lock_hash,
    )


def _source_binding_fields(
    summary: SpotSummary,
    source_journal: bytes,
    source_scope_hash: bytes,
) -> tuple[tuple[bytes, ...], dict[str, bytes]]:
    source_program_id = _risc0_program_id(summary.image_id_words)
    source_profile_id = _profile_id(summary.proof_profile)
    source_journal_hash = hashlib.sha256(
        b"zenodex.risc0.recursive.child_journal_hash.v1"
        + _u32(len(source_journal))
        + source_journal
    ).digest()
    source_claim_hash = hashlib.sha256(
        b"zenodex.risc0.recursive.child_verification_claim_hash.v1"
        + _v1_image_words(summary.image_id_words)
        + _u32(len(source_journal))
        + source_journal
    ).digest()
    source_verifier_id = hashlib.sha256(
        b"zenodex.risc0.recursive.child_verifier_id.v1"
        + _v1_image_words(summary.image_id_words)
        + _v1_string(summary.proof_profile)
    ).digest()
    source_manifest_root = _hash_fixed(
        SOURCE_MANIFEST_DOMAIN,
        source_program_id,
        SOURCE_PROGRAM_SHA256,
        SOURCE_LOCAL_TREE_ROOT,
        source_profile_id,
        summary.dependency_lock_hash,
        summary.toolchain_lock_hash,
    )
    source_effect_hash = _source_effect_hash(summary)
    source_protocol_id = _hash_framed(SOURCE_PROTOCOL_ID_DOMAIN, SOURCE_PROOF_TYPE)
    source_lane_id_hash = _hash_framed(SOURCE_LANE_ID_DOMAIN, summary.lane_id)
    fields = (
        source_protocol_id,
        source_program_id,
        source_profile_id,
        source_verifier_id,
        source_manifest_root,
        source_claim_hash,
        source_journal_hash,
        summary.statement_hash,
        source_effect_hash,
        source_scope_hash,
        source_lane_id_hash,
    )
    named = {
        "source_journal_hash": source_journal_hash,
        "source_claim_hash": source_claim_hash,
        "source_verifier_id": source_verifier_id,
        "source_effect_hash": source_effect_hash,
        "source_manifest_root": source_manifest_root,
    }
    return fields, named


def _commitment_fields(
    summary: SpotSummary,
    source_journal: bytes,
    source_binding_fields: tuple[bytes, ...],
    source_binding_hash: bytes,
    task_id: bytes,
    partition_start: int,
    partition_end: int,
) -> tuple[bytes, ...]:
    source_claim_hash = source_binding_fields[5]
    source_journal_hash = source_binding_fields[6]
    source_effect_hash = source_binding_fields[8]
    partition_entry = _hash_fixed(
        PARTITION_ENTRY_DOMAIN,
        task_id,
        _u64(partition_start),
        _u64(partition_end),
    )
    def unsupported(label: bytes) -> bytes:
        return _hash_framed(UNSUPPORTED_FIELD_DOMAIN, label, source_binding_hash)
    return (
        _lane_state_vector_root(
            PRE_STATE_VECTOR_DOMAIN, summary.lane_id, summary.pre_state_root
        ),
        _lane_state_vector_root(
            POST_STATE_VECTOR_DOMAIN, summary.lane_id, summary.post_state_root
        ),
        source_claim_hash,
        summary.transaction_root,
        summary.evidence_root,
        _v3_list_root(PROVENANCE_ROOT_DOMAIN, (source_binding_hash,)),
        summary.receipt_root,
        summary.accepted_receipts_root,
        summary.rejected_receipts_root,
        source_effect_hash,
        summary.write_set_root,
        summary.asset_delta_root,
        summary.cross_lane_outbox_root,
        summary.cross_lane_inbox_root,
        _v1_root_list(b"zenodex.risc0.recursive.message_ids_root.v1"),
        _hash_fixed(
            CONFLICT_SCHEDULE_DOMAIN,
            task_id,
            _u64(partition_start),
            _u64(partition_end),
            summary.write_set_root,
            summary.statement_hash,
        ),
        _hash_fixed(
            DA_PAYLOAD_ROOT_DOMAIN,
            source_journal_hash,
            _u32(len(source_journal)),
        ),
        unsupported(b"data_availability_certificate"),
        unsupported(b"carry_queue_pre"),
        unsupported(b"carry_queue_post"),
        _v3_list_root(TASK_SET_ROOT_DOMAIN, (task_id,)),
        _v3_list_root(SEMANTIC_SOURCE_SET_ROOT_DOMAIN, (source_binding_hash,)),
        _v3_list_root(PARTITION_PLAN_ROOT_DOMAIN, (partition_entry,)),
    )


def _encode_v3_leaf_postcard(
    *,
    task_id: bytes,
    count_unit_id: bytes,
    scope_fields: tuple[bytes, ...],
    adapter_profile_id: bytes,
    adapter_program_id: bytes,
    v3_verifier_id: bytes,
    node_statement_hash: bytes,
    adapter_manifest_root: bytes,
    commitments: tuple[bytes, ...],
    empty_child_roots: tuple[bytes, ...],
    partition_start: int,
    partition_end: int,
) -> bytes:
    return b"".join(
        (
            _postcard_uvarint(3),
            task_id,
            _postcard_uvarint(0),  # NodeKindV3::Leaf
            bytes((0,)),  # NodeLevelV3::LEAF
            _postcard_uvarint(partition_start),
            _postcard_uvarint(partition_end),
            bytes((0,)),  # immediate child count
            _postcard_uvarint(1),  # leaf count
            _postcard_uvarint(1),  # one source transition receipt
            count_unit_id,
            _postcard_uvarint(1),  # subtree node count
            scope_fields[0],
            scope_fields[1],
            _postcard_uvarint(17),
            _postcard_uvarint(17),
            *scope_fields[4:],
            adapter_profile_id,
            adapter_program_id,
            v3_verifier_id,
            node_statement_hash,
            adapter_manifest_root,
            *commitments,
            *empty_child_roots,
        )
    )


def _materialize(statement_hash: bytes = bytes([1]) * 32) -> MaterializedVector:
    if len(statement_hash) != 32:
        raise ValueError("statement_hash must contain exactly 32 bytes")
    summary = SpotSummary(statement_hash=statement_hash)
    source_journal = _encode_v1_summary_postcard(summary)
    scope_fields = _scope_fields(summary)
    source_scope_hash = _hash_fixed(b"zenodex.zrpf.node_scope_hash.v3", *scope_fields)
    source_binding_fields, source_named = _source_binding_fields(
        summary, source_journal, source_scope_hash
    )
    source_binding_hash = _hash_fixed(SOURCE_BINDING_DOMAIN, *source_binding_fields)
    task_id = _hash_fixed(
        TASK_ID_DOMAIN,
        source_scope_hash,
        source_named["source_claim_hash"],
        summary.statement_hash,
        source_binding_fields[10],
        source_binding_fields[2],
    )
    partition_start = 4
    partition_end = 5
    commitments = _commitment_fields(
        summary,
        source_journal,
        source_binding_fields,
        source_binding_hash,
        task_id,
        partition_start,
        partition_end,
    )
    commitments_hash = _hash_fixed(
        b"zenodex.zrpf.node_commitments_hash.v3", *commitments
    )
    adapter_program_id = _risc0_program_id(ADAPTER_IMAGE_ID_WORDS)
    adapter_profile_id = _profile_id(ADAPTER_PROFILE)
    count_unit_id = _hash_framed(COUNT_UNIT_ID_DOMAIN, b"source_transition_receipt")
    adapter_manifest_root = _hash_framed(
        ADAPTER_MANIFEST_DOMAIN,
        adapter_program_id,
        adapter_profile_id,
        ADAPTER_MANIFEST_CLASS,
    )
    node_statement_hash = _hash_fixed(
        NODE_STATEMENT_DOMAIN,
        adapter_program_id,
        adapter_profile_id,
        adapter_manifest_root,
        source_binding_hash,
        source_scope_hash,
        task_id,
        _u64(partition_start),
        _u64(partition_end),
        _u64(1),
        count_unit_id,
        commitments_hash,
    )
    v3_verifier_id = _hash_fixed(
        b"zenodex.zrpf.verifier_id.v3",
        adapter_program_id,
        adapter_profile_id,
        _u16(3),
    )
    empty_child_roots = tuple(_v3_list_root(domain) for domain in EMPTY_CHILD_DOMAINS)

    canonical_journal_fields = (
        _u16(3),
        task_id,
        bytes((0, 0)),
        _u64(partition_start),
        _u64(partition_end),
        bytes((0,)),
        _u64(1),
        _u64(1),
        count_unit_id,
        _u64(1),
        *scope_fields,
        adapter_profile_id,
        adapter_program_id,
        v3_verifier_id,
        node_statement_hash,
        adapter_manifest_root,
        *commitments,
        *empty_child_roots,
    )
    journal_hash = _hash_fixed(
        b"zenodex.zrpf.node_journal_hash.v3", *canonical_journal_fields
    )
    v3_postcard = _encode_v3_leaf_postcard(
        task_id=task_id,
        count_unit_id=count_unit_id,
        scope_fields=scope_fields,
        adapter_profile_id=adapter_profile_id,
        adapter_program_id=adapter_program_id,
        v3_verifier_id=v3_verifier_id,
        node_statement_hash=node_statement_hash,
        adapter_manifest_root=adapter_manifest_root,
        commitments=commitments,
        empty_child_roots=empty_child_roots,
        partition_start=partition_start,
        partition_end=partition_end,
    )

    values: dict[str, str | int] = {
        "source_journal_length": len(source_journal),
        "source_journal_sha256": hashlib.sha256(source_journal).hexdigest(),
        **{name: value.hex() for name, value in source_named.items()},
        "source_scope_hash": source_scope_hash.hex(),
        "source_binding_hash": source_binding_hash.hex(),
        "task_id": task_id.hex(),
        "count_unit_id": count_unit_id.hex(),
        "adapter_manifest_root": adapter_manifest_root.hex(),
        "commitments_hash": commitments_hash.hex(),
        "node_statement_hash": node_statement_hash.hex(),
        "v3_verifier_id": v3_verifier_id.hex(),
        "journal_hash": journal_hash.hex(),
        "v3_postcard_length": len(v3_postcard),
        "v3_postcard_sha256": hashlib.sha256(v3_postcard).hexdigest(),
    }
    return MaterializedVector(values, source_journal, v3_postcard)


def reference_vector(statement_hash: bytes = bytes([1]) * 32) -> dict[str, str | int]:
    """Return the independently reconstructed vector for one fixed Spot summary."""

    return _materialize(statement_hash).values


def check(statement_hash: bytes = bytes([1]) * 32) -> dict[str, object]:
    """Compare the reconstructed vector with the pinned normative values."""

    actual = reference_vector(statement_hash)
    checks = {name: actual[name] == expected for name, expected in EXPECTED_VECTOR.items()}
    return {
        "ok": all(checks.values()),
        "checks": checks,
        "vector": actual,
    }


def main() -> int:
    report = check()
    print(json.dumps(report, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
