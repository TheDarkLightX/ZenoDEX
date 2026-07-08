"""Adapter-neutral Tau export packets for ZenoLedger checkpoints."""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from typing import Any, Mapping, Sequence

from src.core.cross_shard_ledger_posting import (
    CrossShardLedgerPostingBuildResult,
    CrossShardLedgerPostingSummaryV1,
)
from src.integration.tau_state_proof_binding import validate_tau_state_proof_binding
from src.integration.zeno_ledger_profile import validate_checkpoint_admission_v0
from src.integration.zeno_ledger_v0 import (
    ROOT_NBYTES,
    canonical_body_root_v0,
    hash_v0,
    validate_checkpoint_header_binding_v0,
    validate_header_body_roots_v0,
)
from src.state.canonical import canonical_hex_fixed_allow_0x

CrossShardPostingSummaryExportV0 = dict[str, Any]
TauExportPacketV0 = dict[str, Any]
TauExportAcceptanceReceiptV0 = dict[str, Any]

TAU_EXPORT_PACKET_SCHEMA_V0 = "zenodex/zeno_ledger/tau_export_packet/v0"
TAU_EXPORT_PACKET_KIND_V0 = "zenoledger_checkpoint_for_tau"
TAU_EXPORT_ADAPTER_CONTRACT_V0 = "zenoledger_tau_adapter_v0"
TAU_EXPORT_ACCEPTANCE_RECEIPT_SCHEMA_V0 = (
    "zenodex/zeno_ledger/tau_export_acceptance_receipt/v0"
)
TAU_EXPORT_ACCEPTANCE_STATUS_ASSIGNED_V0 = "tau_state_hash_assigned"
CROSS_SHARD_POSTING_SUMMARY_EXPORT_SCHEMA_V0 = (
    "zenodex/zeno_ledger/cross_shard_posting_summary_export/v0"
)
CROSS_SHARD_POSTING_SUMMARY_SET_SCHEMA_V0 = (
    "zenodex/zeno_ledger/cross_shard_posting_summary_set/v0"
)
CROSS_SHARD_TERMINAL_ADMISSION_SET_SCHEMA_V0 = (
    "zenodex/zeno_ledger/cross_shard_terminal_admission_set/v0"
)
CROSS_SHARD_POSTING_SUMMARY_OPTIONAL_V0 = "optional"
CROSS_SHARD_POSTING_SUMMARY_REQUIRED_V0 = "required"
CROSS_SHARD_POSTING_SUMMARY_FORBIDDEN_V0 = "forbidden"
CROSS_SHARD_POSTING_SUMMARY_BODY_EVIDENCE_V0 = "body_evidence"
CROSS_SHARD_POSTING_REQUIREMENT_SOURCE_OPERATOR_V0 = "operator"
CROSS_SHARD_POSTING_REQUIREMENT_SOURCE_BODY_EVIDENCE_V0 = "body_evidence"
CROSS_SHARD_POSTING_REQUIREMENT_EVIDENCE_SCHEMA_V0 = (
    "zenodex/zeno_ledger/cross_shard_posting_requirement_evidence/v0"
)
CROSS_SHARD_POSTING_SUMMARY_REQUIREMENTS_V0 = frozenset(
    {
        CROSS_SHARD_POSTING_SUMMARY_OPTIONAL_V0,
        CROSS_SHARD_POSTING_SUMMARY_REQUIRED_V0,
        CROSS_SHARD_POSTING_SUMMARY_FORBIDDEN_V0,
    }
)
CROSS_SHARD_POSTING_SUMMARY_REQUESTS_V0 = frozenset(
    {
        *CROSS_SHARD_POSTING_SUMMARY_REQUIREMENTS_V0,
        CROSS_SHARD_POSTING_SUMMARY_BODY_EVIDENCE_V0,
    }
)
CROSS_SHARD_POSTING_REQUIREMENT_SOURCES_V0 = frozenset(
    {
        CROSS_SHARD_POSTING_REQUIREMENT_SOURCE_OPERATOR_V0,
        CROSS_SHARD_POSTING_REQUIREMENT_SOURCE_BODY_EVIDENCE_V0,
    }
)

_POSTING_SUMMARY_EXPORT_KEYS_V0 = frozenset(
    {
        "schema",
        "status",
        "sharded_settlement_certificate_hash",
        "posting_count",
        "total_committed_debit_atoms",
        "total_committed_credit_atoms",
        "postings",
        "posting_summary_hash",
    }
)
_POSTING_ROW_KEYS_V0 = frozenset(
    {
        "asset_id",
        "committed_debit_atoms",
        "committed_credit_atoms",
    }
)
_PACKET_POSTING_SUMMARY_KEYS_V0 = frozenset(
    {
        "status",
        "posting_summary_hash",
        "summary",
    }
)
_PACKET_POSTING_SUMMARY_SET_KEYS_V0 = frozenset(
    {
        "status",
        "posting_summary_hashes",
        "posting_summary_set_hash",
        "summaries",
    }
)
_POSTING_REQUIREMENT_EVIDENCE_KEYS_V0 = frozenset(
    {
        "schema",
        "requirement",
        "cross_shard_transfer_count",
        "applied_cross_shard_transfer_count",
        "posting_summary_hash",
        "posting_summary_hashes",
        "posting_summary_set_hash",
        "terminal_admission_hash",
        "terminal_admission_hashes",
        "terminal_admission_set_hash",
    }
)
_TAU_EXPORT_ACCEPTANCE_RECEIPT_KEYS_V0 = frozenset(
    {
        "schema",
        "status",
        "adapter_contract",
        "tau_network_id",
        "tau_adapter_ref",
        "chain_id",
        "height",
        "packet_hash",
        "packet_app_hash",
        "post_state_root",
        "tau_state_hash",
        "state_hash_key",
        "state_proof_type",
        "tau_state_app_hash",
        "shared_pool_frontier_signature_certificate_count",
        "shared_pool_frontier_signature_certificates_root",
        "authorizes_settlement",
        "receipt_hash",
    }
)
FRONTIER_SIGNATURE_CERTIFICATES_ROOT_DOMAIN_V1 = (
    "zenodex.mev.shared_pool_frontier_signature_certificates_root.v1"
)
FRONTIER_SIGNATURE_CERTIFICATES_MAX_V1 = 16
FRONTIER_SIGNATURE_CERTIFICATES_EMPTY_ROOT_V1 = "0x" + hashlib.sha256(
    len(FRONTIER_SIGNATURE_CERTIFICATES_ROOT_DOMAIN_V1.encode("utf-8")).to_bytes(
        4,
        "big",
    )
    + FRONTIER_SIGNATURE_CERTIFICATES_ROOT_DOMAIN_V1.encode("utf-8")
    + (0).to_bytes(4, "big")
).hexdigest()


@dataclass(frozen=True)
class CrossShardPostingSummaryBodyEvidenceV0:
    requirement: str
    expected_posting_summary_hash: str | None
    expected_posting_summary_hashes: tuple[str, ...]
    expected_posting_summary_set_hash: str | None
    expected_terminal_admission_hash: str | None
    expected_terminal_admission_hashes: tuple[str, ...]
    expected_terminal_admission_set_hash: str | None


def build_cross_shard_posting_summary_export_v0(
    *,
    posting_result: CrossShardLedgerPostingBuildResult,
) -> CrossShardPostingSummaryExportV0:
    if not isinstance(posting_result, CrossShardLedgerPostingBuildResult):
        raise TypeError("posting_result must be CrossShardLedgerPostingBuildResult")
    if not posting_result.ok:
        raise ValueError("cross-shard posting result must be accepted")
    postings = [posting.to_payload() for posting in posting_result.postings]
    packet_body = {
        "schema": CROSS_SHARD_POSTING_SUMMARY_EXPORT_SCHEMA_V0,
        "status": "verified_committed_only",
        "sharded_settlement_certificate_hash": posting_result.sharded_settlement_certificate_hash,
        "posting_count": len(postings),
        "total_committed_debit_atoms": int(posting_result.total_committed_debit_atoms),
        "total_committed_credit_atoms": int(posting_result.total_committed_credit_atoms),
        "postings": postings,
    }
    return {
        **packet_body,
        "posting_summary_hash": hash_v0(
            "cross_shard_posting_summary_export_v0",
            packet_body,
        ),
    }


def canonical_cross_shard_posting_summary_hashes_v0(
    posting_summary_hashes: Sequence[str],
) -> tuple[str, ...]:
    hashes = tuple(
        _require_hash(
            value,
            name=f"cross_shard_posting_summary_hashes[{index}]",
        )
        for index, value in enumerate(posting_summary_hashes)
    )
    if len(hashes) == 0:
        raise ValueError("cross-shard posting summary hashes must be non-empty")
    if len(set(hashes)) != len(hashes):
        raise ValueError("cross-shard posting summary hashes must be unique")
    return tuple(sorted(hashes))


def cross_shard_posting_summary_set_hash_v0(
    posting_summary_hashes: Sequence[str],
) -> str:
    canonical_hashes = canonical_cross_shard_posting_summary_hashes_v0(
        posting_summary_hashes
    )
    return hash_v0(
        "cross_shard_posting_summary_set_v0",
        {
            "schema": CROSS_SHARD_POSTING_SUMMARY_SET_SCHEMA_V0,
            "posting_summary_hashes": list(canonical_hashes),
        },
    )


def canonical_cross_shard_terminal_admission_hashes_v0(
    terminal_admission_hashes: Sequence[str],
) -> tuple[str, ...]:
    hashes = tuple(
        _require_hash(
            value,
            name=f"cross_shard_terminal_admission_hashes[{index}]",
        )
        for index, value in enumerate(terminal_admission_hashes)
    )
    if len(hashes) == 0:
        raise ValueError("cross-shard terminal admission hashes must be non-empty")
    if len(set(hashes)) != len(hashes):
        raise ValueError("cross-shard terminal admission hashes must be unique")
    return tuple(sorted(hashes))


def cross_shard_terminal_admission_set_hash_v0(
    terminal_admission_hashes: Sequence[str],
) -> str:
    canonical_hashes = canonical_cross_shard_terminal_admission_hashes_v0(
        terminal_admission_hashes
    )
    return hash_v0(
        "cross_shard_terminal_admission_set_v0",
        {
            "schema": CROSS_SHARD_TERMINAL_ADMISSION_SET_SCHEMA_V0,
            "terminal_admission_hashes": list(canonical_hashes),
        },
    )


def build_tau_export_packet_v0(
    *,
    checkpoint: Mapping[str, Any],
    header: Mapping[str, Any],
    body: Mapping[str, Any],
    profile: Mapping[str, Any],
    tau_network_id: str,
    tau_adapter_ref: str,
    cross_shard_posting_summary: Mapping[str, Any] | None = None,
    cross_shard_posting_summaries: Sequence[Mapping[str, Any]] | None = None,
    cross_shard_posting_summary_requirement: str = CROSS_SHARD_POSTING_SUMMARY_OPTIONAL_V0,
) -> TauExportPacketV0:
    """Build a deterministic Tau-facing export packet.

    The packet is a handoff contract. It binds ZenoLedger roots to a named Tau
    network and adapter reference without assuming Tau has accepted any plugin.
    """

    checkpoint_obj = dict(checkpoint)
    header_obj = dict(header)
    body_obj = dict(body)
    profile_obj = dict(profile)
    validate_header_body_roots_v0(header_obj, body_obj)
    validate_checkpoint_header_binding_v0(checkpoint_obj, header_obj)
    validate_checkpoint_admission_v0(checkpoint=checkpoint_obj, profile=profile_obj)

    if not isinstance(tau_network_id, str) or tau_network_id == "":
        raise ValueError("tau_network_id must be a non-empty string")
    if not isinstance(tau_adapter_ref, str) or tau_adapter_ref == "":
        raise ValueError("tau_adapter_ref must be a non-empty string")
    posting_request = _require_posting_summary_request(
        cross_shard_posting_summary_requirement
    )
    posting_evidence, posting_requirement_source = _resolve_posting_requirement(
        body_obj=body_obj,
        posting_request=posting_request,
    )
    posting_requirement = posting_evidence.requirement
    posting_summaries = _normalize_packet_posting_summaries(
        cross_shard_posting_summary=cross_shard_posting_summary,
        cross_shard_posting_summaries=cross_shard_posting_summaries,
    )
    if (
        posting_requirement == CROSS_SHARD_POSTING_SUMMARY_REQUIRED_V0
        and len(posting_summaries) == 0
    ):
        raise ValueError("cross-shard posting summary is required")
    if (
        posting_requirement == CROSS_SHARD_POSTING_SUMMARY_FORBIDDEN_V0
        and len(posting_summaries) != 0
    ):
        raise ValueError("cross-shard posting summary is forbidden")
    _validate_expected_posting_summary_hashes(
        posting_summaries=posting_summaries,
        expected_evidence=posting_evidence,
    )

    packet_body = {
        "schema": TAU_EXPORT_PACKET_SCHEMA_V0,
        "packet_kind": TAU_EXPORT_PACKET_KIND_V0,
        "adapter_contract": TAU_EXPORT_ADAPTER_CONTRACT_V0,
        "tau_network_id": tau_network_id,
        "tau_adapter_ref": tau_adapter_ref,
        "profile_id": profile_obj["profile_id"],
        "deployment_mode": profile_obj["deployment_mode"],
        "chain_id": checkpoint_obj["chain_id"],
        "height": checkpoint_obj["height"],
        "header_hash": checkpoint_obj["header_hash"],
        "app_hash": checkpoint_obj["app_hash"],
        "post_state_root": checkpoint_obj["post_state_root"],
        "body_root": checkpoint_obj["body_root"],
        "evidence_root": checkpoint_obj["evidence_root"],
        "config_digest": checkpoint_obj["config_digest"],
        "proof_journal_hash": checkpoint_obj["proof_journal_hash"],
        "body_payload_root": canonical_body_root_v0(body_obj),
        "tau_admission": {
            "status": "handoff_only",
            "requires_tau_adapter_verification": True,
            "requires_tau_plugin_acceptance": True,
            "requires_tau_state_hash_assignment": True,
        },
        "tau_state_proof_hint": {
            "proof_type": "zenoledger.checkpoint.v0",
            "committed_app_hash": checkpoint_obj["app_hash"],
            "committed_body_root": checkpoint_obj["body_root"],
            "committed_header_hash": checkpoint_obj["header_hash"],
            "tau_state_hash_status": "unassigned",
        },
    }
    if (
        posting_requirement != CROSS_SHARD_POSTING_SUMMARY_OPTIONAL_V0
        or len(posting_summaries) != 0
        or posting_requirement_source
        == CROSS_SHARD_POSTING_REQUIREMENT_SOURCE_BODY_EVIDENCE_V0
    ):
        packet_body["tau_admission"] = {
            **packet_body["tau_admission"],
            "cross_shard_posting_summary_requirement": posting_requirement,
            "cross_shard_posting_summary_requirement_source": posting_requirement_source,
        }
        if posting_evidence.expected_posting_summary_hash is not None:
            packet_body["tau_admission"] = {
                **packet_body["tau_admission"],
                "cross_shard_posting_summary_expected_hash": (
                    posting_evidence.expected_posting_summary_hash
                ),
            }
        if posting_evidence.expected_posting_summary_set_hash is not None:
            packet_body["tau_admission"] = {
                **packet_body["tau_admission"],
                "cross_shard_posting_summary_expected_hashes": list(
                    posting_evidence.expected_posting_summary_hashes
                ),
                "cross_shard_posting_summary_expected_set_hash": (
                    posting_evidence.expected_posting_summary_set_hash
                ),
            }
        if posting_evidence.expected_terminal_admission_hash is not None:
            packet_body["tau_admission"] = {
                **packet_body["tau_admission"],
                "cross_shard_terminal_admission_expected_hash": (
                    posting_evidence.expected_terminal_admission_hash
                ),
            }
        if posting_evidence.expected_terminal_admission_set_hash is not None:
            packet_body["tau_admission"] = {
                **packet_body["tau_admission"],
                "cross_shard_terminal_admission_expected_hashes": list(
                    posting_evidence.expected_terminal_admission_hashes
                ),
                "cross_shard_terminal_admission_expected_set_hash": (
                    posting_evidence.expected_terminal_admission_set_hash
                ),
            }
    if (
        len(posting_summaries) == 1
        and posting_evidence.expected_posting_summary_set_hash is None
    ):
        posting_summary = posting_summaries[0]
        posting_hash = posting_summary["posting_summary_hash"]
        packet_body["cross_shard_posting_summary"] = {
            "status": "bound",
            "posting_summary_hash": posting_hash,
            "summary": posting_summary,
        }
        packet_body["tau_admission"] = {
            **packet_body["tau_admission"],
            "requires_cross_shard_posting_summary_verification": True,
        }
        packet_body["tau_state_proof_hint"] = {
            **packet_body["tau_state_proof_hint"],
            "cross_shard_posting_summary_hash": posting_hash,
        }
    elif len(posting_summaries) != 0:
        posting_hashes = tuple(
            str(posting_summary["posting_summary_hash"])
            for posting_summary in posting_summaries
        )
        posting_set_hash = cross_shard_posting_summary_set_hash_v0(posting_hashes)
        packet_body["cross_shard_posting_summary_set"] = {
            "status": "bound",
            "posting_summary_hashes": list(posting_hashes),
            "posting_summary_set_hash": posting_set_hash,
            "summaries": list(posting_summaries),
        }
        packet_body["tau_admission"] = {
            **packet_body["tau_admission"],
            "requires_cross_shard_posting_summary_verification": True,
        }
        packet_body["tau_state_proof_hint"] = {
            **packet_body["tau_state_proof_hint"],
            "cross_shard_posting_summary_hashes": list(posting_hashes),
            "cross_shard_posting_summary_set_hash": posting_set_hash,
        }
    return {**packet_body, "packet_hash": hash_v0("tau_export_packet_v0", packet_body)}


def validate_cross_shard_posting_summary_export_v0(
    posting_summary: Mapping[str, Any],
) -> CrossShardPostingSummaryExportV0:
    obj = _require_mapping(posting_summary, name="cross_shard_posting_summary")
    _reject_unknown_keys(
        obj,
        allowed=_POSTING_SUMMARY_EXPORT_KEYS_V0,
        name="cross_shard_posting_summary",
    )
    if obj.get("schema") != CROSS_SHARD_POSTING_SUMMARY_EXPORT_SCHEMA_V0:
        raise ValueError("cross-shard posting summary schema mismatch")
    if obj.get("status") != "verified_committed_only":
        raise ValueError("cross-shard posting summary status mismatch")
    postings = _parse_postings(obj.get("postings"))
    posting_result = CrossShardLedgerPostingBuildResult(
        ok=True,
        error=None,
        sharded_settlement_certificate_hash=_require_hash(
            obj.get("sharded_settlement_certificate_hash"),
            name="cross_shard_posting_summary.sharded_settlement_certificate_hash",
        ),
        postings=postings,
        total_committed_debit_atoms=_require_non_negative_int(
            obj.get("total_committed_debit_atoms"),
            name="cross_shard_posting_summary.total_committed_debit_atoms",
        ),
        total_committed_credit_atoms=_require_non_negative_int(
            obj.get("total_committed_credit_atoms"),
            name="cross_shard_posting_summary.total_committed_credit_atoms",
        ),
    )
    if obj.get("posting_count") != len(postings):
        raise ValueError("cross-shard posting summary posting_count mismatch")
    expected = build_cross_shard_posting_summary_export_v0(
        posting_result=posting_result
    )
    if dict(obj) != expected:
        raise ValueError("cross-shard posting summary export binding mismatch")
    return expected


def cross_shard_posting_summary_export_to_build_result_v0(
    posting_summary: Mapping[str, Any],
) -> CrossShardLedgerPostingBuildResult:
    validated = validate_cross_shard_posting_summary_export_v0(posting_summary)
    return CrossShardLedgerPostingBuildResult(
        ok=True,
        error=None,
        sharded_settlement_certificate_hash=_require_hash(
            validated["sharded_settlement_certificate_hash"],
            name="cross_shard_posting_summary.sharded_settlement_certificate_hash",
        ),
        postings=_parse_postings(validated["postings"]),
        total_committed_debit_atoms=_require_non_negative_int(
            validated["total_committed_debit_atoms"],
            name="cross_shard_posting_summary.total_committed_debit_atoms",
        ),
        total_committed_credit_atoms=_require_non_negative_int(
            validated["total_committed_credit_atoms"],
            name="cross_shard_posting_summary.total_committed_credit_atoms",
        ),
    )


def infer_cross_shard_posting_summary_requirement_v0(
    body: Mapping[str, Any],
) -> str:
    """Infer the posting-summary policy from committed body evidence."""

    return infer_cross_shard_posting_summary_body_evidence_detail_v0(
        body
    ).requirement


def infer_cross_shard_posting_summary_body_evidence_v0(
    body: Mapping[str, Any],
) -> tuple[str, str | None]:
    """Infer the posting-summary policy and expected summary hash."""

    detail = infer_cross_shard_posting_summary_body_evidence_detail_v0(body)
    return detail.requirement, detail.expected_posting_summary_hash


def infer_cross_shard_posting_summary_body_evidence_detail_v0(
    body: Mapping[str, Any],
) -> CrossShardPostingSummaryBodyEvidenceV0:
    """Infer posting-summary policy, legacy hash, and canonical set hash."""

    obj = _require_mapping(body, name="body")
    evidence = _require_mapping(obj.get("evidence"), name="body.evidence")
    proof_receipts = evidence.get("proof_receipts")
    if not isinstance(proof_receipts, list):
        raise TypeError("body.evidence.proof_receipts must be a list")

    requirements: set[str] = set()
    posting_hashes: set[str] = set()
    posting_hash_sets: set[tuple[str, ...]] = set()
    posting_set_hashes: set[str] = set()
    terminal_hashes: set[str] = set()
    terminal_hash_sets: set[tuple[str, ...]] = set()
    terminal_set_hashes: set[str] = set()
    for index, receipt in enumerate(proof_receipts):
        if not isinstance(receipt, Mapping):
            continue
        if receipt.get("schema") != CROSS_SHARD_POSTING_REQUIREMENT_EVIDENCE_SCHEMA_V0:
            continue
        parsed = _parse_posting_requirement_evidence(
            receipt,
            index=index,
        )
        requirements.add(parsed.requirement)
        if parsed.expected_posting_summary_hash is not None:
            posting_hashes.add(parsed.expected_posting_summary_hash)
        if parsed.expected_posting_summary_set_hash is not None:
            posting_hash_sets.add(parsed.expected_posting_summary_hashes)
            posting_set_hashes.add(parsed.expected_posting_summary_set_hash)
        if parsed.expected_terminal_admission_hash is not None:
            terminal_hashes.add(parsed.expected_terminal_admission_hash)
        if parsed.expected_terminal_admission_set_hash is not None:
            terminal_hash_sets.add(parsed.expected_terminal_admission_hashes)
            terminal_set_hashes.add(parsed.expected_terminal_admission_set_hash)

    if len(requirements) == 0:
        return CrossShardPostingSummaryBodyEvidenceV0(
            requirement=CROSS_SHARD_POSTING_SUMMARY_OPTIONAL_V0,
            expected_posting_summary_hash=None,
            expected_posting_summary_hashes=(),
            expected_posting_summary_set_hash=None,
            expected_terminal_admission_hash=None,
            expected_terminal_admission_hashes=(),
            expected_terminal_admission_set_hash=None,
        )
    if len(requirements) > 1:
        raise ValueError("conflicting cross-shard posting summary requirements")
    requirement = next(iter(requirements))
    if posting_hashes and posting_set_hashes:
        raise ValueError("conflicting cross-shard posting summary hash forms")
    if terminal_hashes and terminal_set_hashes:
        raise ValueError("conflicting cross-shard terminal admission hash forms")
    if len(posting_hashes) > 1:
        raise ValueError("conflicting cross-shard posting summary hashes")
    if len(terminal_hashes) > 1:
        raise ValueError("conflicting cross-shard terminal admission hashes")
    if len(posting_set_hashes) > 1 or len(posting_hash_sets) > 1:
        raise ValueError("conflicting cross-shard posting summary set hashes")
    if len(terminal_set_hashes) > 1 or len(terminal_hash_sets) > 1:
        raise ValueError("conflicting cross-shard terminal admission set hashes")
    if posting_set_hashes:
        if not terminal_set_hashes:
            raise ValueError(
                "required cross-shard posting set evidence needs "
                "terminal_admission_hashes and terminal_admission_set_hash"
            )
        return CrossShardPostingSummaryBodyEvidenceV0(
            requirement=requirement,
            expected_posting_summary_hash=None,
            expected_posting_summary_hashes=next(iter(posting_hash_sets)),
            expected_posting_summary_set_hash=next(iter(posting_set_hashes)),
            expected_terminal_admission_hash=None,
            expected_terminal_admission_hashes=next(iter(terminal_hash_sets)),
            expected_terminal_admission_set_hash=next(iter(terminal_set_hashes)),
        )
    posting_hash = next(iter(posting_hashes)) if posting_hashes else None
    terminal_hash = next(iter(terminal_hashes)) if terminal_hashes else None
    if requirement == CROSS_SHARD_POSTING_SUMMARY_REQUIRED_V0 and posting_hash is None:
        raise ValueError(
            "required cross-shard posting evidence needs posting_summary_hash "
            "or posting_summary_set_hash"
        )
    if (
        requirement == CROSS_SHARD_POSTING_SUMMARY_REQUIRED_V0
        and terminal_hash is None
    ):
        raise ValueError(
            "required cross-shard posting evidence needs terminal_admission_hash "
            "or terminal_admission_set_hash"
        )
    return CrossShardPostingSummaryBodyEvidenceV0(
        requirement=requirement,
        expected_posting_summary_hash=posting_hash,
        expected_posting_summary_hashes=()
        if posting_hash is None
        else (posting_hash,),
        expected_posting_summary_set_hash=None,
        expected_terminal_admission_hash=terminal_hash,
        expected_terminal_admission_hashes=()
        if terminal_hash is None
        else (terminal_hash,),
        expected_terminal_admission_set_hash=None,
    )


def validate_tau_export_packet_v0(
    *,
    packet: Mapping[str, Any],
    checkpoint: Mapping[str, Any],
    header: Mapping[str, Any],
    body: Mapping[str, Any],
    profile: Mapping[str, Any],
) -> None:
    if not isinstance(packet, Mapping):
        raise TypeError("packet must be a JSON object")
    tau_network_id = packet.get("tau_network_id")
    tau_adapter_ref = packet.get("tau_adapter_ref")
    if not isinstance(tau_network_id, str) or tau_network_id == "":
        raise ValueError("packet tau_network_id must be a non-empty string")
    if not isinstance(tau_adapter_ref, str) or tau_adapter_ref == "":
        raise ValueError("packet tau_adapter_ref must be a non-empty string")
    posting_summary = _parse_packet_posting_summary(
        packet.get("cross_shard_posting_summary")
    )
    posting_summary_set = _parse_packet_posting_summary_set(
        packet.get("cross_shard_posting_summary_set")
    )
    if posting_summary is not None and posting_summary_set:
        raise ValueError("packet cannot mix posting summary and posting summary set")
    tau_admission = _require_mapping(
        packet.get("tau_admission"),
        name="packet.tau_admission",
    )
    posting_requirement_source = _require_posting_requirement_source(
        tau_admission.get(
            "cross_shard_posting_summary_requirement_source",
            CROSS_SHARD_POSTING_REQUIREMENT_SOURCE_OPERATOR_V0,
        )
    )
    posting_requirement = _require_posting_summary_requirement(
        tau_admission.get(
            "cross_shard_posting_summary_requirement",
            CROSS_SHARD_POSTING_SUMMARY_OPTIONAL_V0,
        )
    )
    posting_request = (
        CROSS_SHARD_POSTING_SUMMARY_BODY_EVIDENCE_V0
        if posting_requirement_source
        == CROSS_SHARD_POSTING_REQUIREMENT_SOURCE_BODY_EVIDENCE_V0
        else posting_requirement
    )
    expected = build_tau_export_packet_v0(
        checkpoint=checkpoint,
        header=header,
        body=body,
        profile=profile,
        tau_network_id=tau_network_id,
        tau_adapter_ref=tau_adapter_ref,
        cross_shard_posting_summary=posting_summary,
        cross_shard_posting_summaries=posting_summary_set,
        cross_shard_posting_summary_requirement=posting_request,
    )
    if dict(packet) != expected:
        raise ValueError("Tau export packet binding mismatch")


def build_tau_export_acceptance_receipt_v0(
    *,
    packet: Mapping[str, Any],
    checkpoint: Mapping[str, Any],
    header: Mapping[str, Any],
    body: Mapping[str, Any],
    profile: Mapping[str, Any],
    state_proof: Mapping[str, Any],
    tau_state: Mapping[str, Any] | None = None,
) -> TauExportAcceptanceReceiptV0:
    """Build a receipt that binds a Tau state proof to a Tau export packet.

    This receipt upgrades packet evidence from handoff-only to state-hash
    assigned, while preserving the boundary that this receipt does not
    authorize settlement.
    """

    packet_obj = _require_mapping(packet, name="packet")
    validate_tau_export_packet_v0(
        packet=packet_obj,
        checkpoint=checkpoint,
        header=header,
        body=body,
        profile=profile,
    )
    _require_handoff_only_tau_admission(packet_obj)

    proof_obj = _require_mapping(state_proof, name="state_proof")
    state_hash = _require_tau_state_root(proof_obj.get("state_hash"), name="state_proof.state_hash")
    packet_app_hash = _require_hash(packet_obj.get("app_hash"), name="packet.app_hash")
    ok, error = validate_tau_state_proof_binding(
        state_proof=proof_obj,
        committed_state_hash=state_hash,
        committed_app_hash=packet_app_hash,
        tau_state=tau_state,
    )
    if not ok:
        raise ValueError(f"Tau state proof binding mismatch: {error}")
    tau_state_app_hash = _extract_tau_state_app_hash(
        state_proof=proof_obj,
        tau_state=tau_state,
    )
    if tau_state_app_hash != packet_app_hash:
        raise ValueError("Tau state app_hash does not match packet app_hash")

    frontier_binding = _extract_state_proof_frontier_signature_binding_v0(
        proof_obj
    )
    packet_hash = _require_hash(packet_obj.get("packet_hash"), name="packet.packet_hash")
    receipt_body = {
        "schema": TAU_EXPORT_ACCEPTANCE_RECEIPT_SCHEMA_V0,
        "status": TAU_EXPORT_ACCEPTANCE_STATUS_ASSIGNED_V0,
        "adapter_contract": TAU_EXPORT_ADAPTER_CONTRACT_V0,
        "tau_network_id": _require_str(
            packet_obj.get("tau_network_id"),
            name="packet.tau_network_id",
        ),
        "tau_adapter_ref": _require_str(
            packet_obj.get("tau_adapter_ref"),
            name="packet.tau_adapter_ref",
        ),
        "chain_id": _require_str(packet_obj.get("chain_id"), name="packet.chain_id"),
        "height": _require_non_negative_int(packet_obj.get("height"), name="packet.height"),
        "packet_hash": packet_hash,
        "packet_app_hash": packet_app_hash,
        "post_state_root": _require_hash(
            packet_obj.get("post_state_root"),
            name="packet.post_state_root",
        ),
        "tau_state_hash": state_hash,
        "state_hash_key": f"state_proof:{state_hash[2:]}",
        "state_proof_type": _require_str(
            proof_obj.get("proof_type"),
            name="state_proof.proof_type",
        ),
        "tau_state_app_hash": tau_state_app_hash,
        "shared_pool_frontier_signature_certificate_count": (
            frontier_binding.certificate_count
        ),
        "shared_pool_frontier_signature_certificates_root": (
            frontier_binding.certificates_root
        ),
        "authorizes_settlement": False,
    }
    return {
        **receipt_body,
        "receipt_hash": hash_v0(
            "tau_export_acceptance_receipt_v0",
            receipt_body,
        ),
    }


def validate_tau_export_acceptance_receipt_v0(
    *,
    receipt: Mapping[str, Any],
    packet: Mapping[str, Any],
    checkpoint: Mapping[str, Any],
    header: Mapping[str, Any],
    body: Mapping[str, Any],
    profile: Mapping[str, Any],
    state_proof: Mapping[str, Any],
    tau_state: Mapping[str, Any] | None = None,
) -> None:
    obj = _require_mapping(receipt, name="receipt")
    _reject_unknown_keys(
        obj,
        allowed=_TAU_EXPORT_ACCEPTANCE_RECEIPT_KEYS_V0,
        name="receipt",
    )
    expected = build_tau_export_acceptance_receipt_v0(
        packet=packet,
        checkpoint=checkpoint,
        header=header,
        body=body,
        profile=profile,
        state_proof=state_proof,
        tau_state=tau_state,
    )
    if dict(obj) != expected:
        raise ValueError("Tau export acceptance receipt binding mismatch")


def _parse_packet_posting_summary(value: object) -> Mapping[str, Any] | None:
    if value is None:
        return None
    obj = _require_mapping(value, name="packet.cross_shard_posting_summary")
    _reject_unknown_keys(
        obj,
        allowed=_PACKET_POSTING_SUMMARY_KEYS_V0,
        name="packet.cross_shard_posting_summary",
    )
    if obj.get("status") != "bound":
        raise ValueError("packet cross-shard posting summary status mismatch")
    summary = validate_cross_shard_posting_summary_export_v0(
        _require_mapping(obj.get("summary"), name="packet.cross_shard_posting_summary.summary")
    )
    if obj.get("posting_summary_hash") != summary["posting_summary_hash"]:
        raise ValueError("packet cross-shard posting summary hash mismatch")
    return summary


def _parse_packet_posting_summary_set(
    value: object,
) -> tuple[Mapping[str, Any], ...]:
    if value is None:
        return ()
    obj = _require_mapping(value, name="packet.cross_shard_posting_summary_set")
    _reject_unknown_keys(
        obj,
        allowed=_PACKET_POSTING_SUMMARY_SET_KEYS_V0,
        name="packet.cross_shard_posting_summary_set",
    )
    if obj.get("status") != "bound":
        raise ValueError("packet cross-shard posting summary set status mismatch")
    summaries_raw = obj.get("summaries")
    if not isinstance(summaries_raw, list):
        raise TypeError("packet cross-shard posting summary set summaries must be a list")
    summaries = tuple(
        validate_cross_shard_posting_summary_export_v0(
            _require_mapping(
                summary,
                name=f"packet.cross_shard_posting_summary_set.summaries[{index}]",
            )
        )
        for index, summary in enumerate(summaries_raw)
    )
    if len(summaries) == 0:
        raise ValueError("packet cross-shard posting summary set must be non-empty")
    posting_hashes = tuple(
        str(summary["posting_summary_hash"])
        for summary in summaries
    )
    _require_canonical_posting_summary_hash_list_v0(
        obj.get("posting_summary_hashes"),
        name="packet.cross_shard_posting_summary_set.posting_summary_hashes",
    )
    if list(posting_hashes) != obj.get("posting_summary_hashes"):
        raise ValueError("packet cross-shard posting summary set hashes mismatch")
    expected_set_hash = cross_shard_posting_summary_set_hash_v0(posting_hashes)
    if obj.get("posting_summary_set_hash") != expected_set_hash:
        raise ValueError("packet cross-shard posting summary set hash mismatch")
    return summaries


def _require_handoff_only_tau_admission(packet: Mapping[str, Any]) -> None:
    tau_admission = _require_mapping(
        packet.get("tau_admission"),
        name="packet.tau_admission",
    )
    if tau_admission.get("status") != "handoff_only":
        raise ValueError("packet tau_admission status must be handoff_only")
    for field in (
        "requires_tau_adapter_verification",
        "requires_tau_plugin_acceptance",
        "requires_tau_state_hash_assignment",
    ):
        if tau_admission.get(field) is not True:
            raise ValueError(f"packet tau_admission {field} must be true")
    hint = _require_mapping(
        packet.get("tau_state_proof_hint"),
        name="packet.tau_state_proof_hint",
    )
    if hint.get("tau_state_hash_status") != "unassigned":
        raise ValueError("packet tau_state_hash_status must be unassigned")
    if "state_hash_key" in hint:
        raise ValueError("handoff packet must not include state_hash_key")


@dataclass(frozen=True)
class _FrontierSignatureBindingV0:
    certificate_count: int
    certificates_root: str


def _extract_state_proof_frontier_signature_binding_v0(
    state_proof: Mapping[str, Any],
) -> _FrontierSignatureBindingV0:
    meta_raw = state_proof.get("meta")
    if meta_raw is None:
        return _FrontierSignatureBindingV0(
            certificate_count=0,
            certificates_root=FRONTIER_SIGNATURE_CERTIFICATES_EMPTY_ROOT_V1,
        )
    meta = _require_mapping(meta_raw, name="state_proof.meta")
    count_raw = meta.get("shared_pool_frontier_signature_certificate_count")
    root_raw = meta.get("shared_pool_frontier_signature_certificates_root")
    if count_raw is None and root_raw is None:
        return _FrontierSignatureBindingV0(
            certificate_count=0,
            certificates_root=FRONTIER_SIGNATURE_CERTIFICATES_EMPTY_ROOT_V1,
        )
    if count_raw is None:
        raise ValueError(
            "state_proof.meta.shared_pool_frontier_signature_certificate_count "
            "missing"
        )
    if root_raw is None:
        raise ValueError(
            "state_proof.meta.shared_pool_frontier_signature_certificates_root "
            "missing"
        )
    count = _require_non_negative_int(
        count_raw,
        name="state_proof.meta.shared_pool_frontier_signature_certificate_count",
    )
    if count > FRONTIER_SIGNATURE_CERTIFICATES_MAX_V1:
        raise ValueError(
            "state_proof.meta.shared_pool_frontier_signature_certificate_count "
            "exceeds max"
        )
    root = _require_tau_state_root(
        root_raw,
        name="state_proof.meta.shared_pool_frontier_signature_certificates_root",
    )
    if count == 0 and root != FRONTIER_SIGNATURE_CERTIFICATES_EMPTY_ROOT_V1:
        raise ValueError(
            "state_proof.meta.shared_pool_frontier_signature_certificates_root "
            "must be empty root when count is zero"
        )
    return _FrontierSignatureBindingV0(
        certificate_count=count,
        certificates_root=root,
    )


def _extract_tau_state_app_hash(
    *,
    state_proof: Mapping[str, Any],
    tau_state: Mapping[str, Any] | None,
) -> str:
    raw = None if tau_state is None else tau_state.get("app_hash")
    if raw is None:
        raw = state_proof.get("app_hash")
    return _require_tau_state_root(raw, name="tau_state.app_hash")


def _normalize_packet_posting_summaries(
    *,
    cross_shard_posting_summary: Mapping[str, Any] | None,
    cross_shard_posting_summaries: Sequence[Mapping[str, Any]] | None,
) -> tuple[Mapping[str, Any], ...]:
    if cross_shard_posting_summary is not None and cross_shard_posting_summaries:
        raise ValueError(
            "use either cross_shard_posting_summary or "
            "cross_shard_posting_summaries"
        )
    if cross_shard_posting_summary is not None:
        summaries = (
            validate_cross_shard_posting_summary_export_v0(
                cross_shard_posting_summary
            ),
        )
    else:
        summaries = tuple(
            validate_cross_shard_posting_summary_export_v0(summary)
            for summary in (cross_shard_posting_summaries or ())
        )
    posting_hashes = tuple(
        str(summary["posting_summary_hash"])
        for summary in summaries
    )
    if len(set(posting_hashes)) != len(posting_hashes):
        raise ValueError("duplicate cross-shard posting summary hash")
    return tuple(
        summary
        for _, summary in sorted(
            zip(posting_hashes, summaries, strict=True),
            key=lambda item: item[0],
        )
    )


def _parse_postings(value: object) -> tuple[CrossShardLedgerPostingSummaryV1, ...]:
    if not isinstance(value, list):
        raise TypeError("cross_shard_posting_summary.postings must be a list")
    return tuple(_parse_posting(row, index=index) for index, row in enumerate(value))


def _parse_posting(value: object, *, index: int) -> CrossShardLedgerPostingSummaryV1:
    obj = _require_mapping(value, name=f"cross_shard_posting_summary.postings[{index}]")
    _reject_unknown_keys(
        obj,
        allowed=_POSTING_ROW_KEYS_V0,
        name=f"cross_shard_posting_summary.postings[{index}]",
    )
    return CrossShardLedgerPostingSummaryV1(
        asset_id=_require_str(
            obj.get("asset_id"),
            name=f"cross_shard_posting_summary.postings[{index}].asset_id",
        ),
        committed_debit_atoms=_require_positive_int(
            obj.get("committed_debit_atoms"),
            name=f"cross_shard_posting_summary.postings[{index}].committed_debit_atoms",
        ),
        committed_credit_atoms=_require_positive_int(
            obj.get("committed_credit_atoms"),
            name=f"cross_shard_posting_summary.postings[{index}].committed_credit_atoms",
        ),
    )


def _parse_posting_requirement_evidence(
    value: Mapping[str, Any],
    *,
    index: int,
) -> CrossShardPostingSummaryBodyEvidenceV0:
    obj = _require_mapping(
        value,
        name=f"body.evidence.proof_receipts[{index}]",
    )
    _reject_unknown_keys(
        obj,
        allowed=_POSTING_REQUIREMENT_EVIDENCE_KEYS_V0,
        name=f"body.evidence.proof_receipts[{index}]",
    )
    if obj.get("schema") != CROSS_SHARD_POSTING_REQUIREMENT_EVIDENCE_SCHEMA_V0:
        raise ValueError("cross-shard posting requirement evidence schema mismatch")
    requirement = _require_posting_summary_requirement(obj.get("requirement"))
    posting_hash = obj.get("posting_summary_hash")
    posting_hashes = obj.get("posting_summary_hashes")
    posting_set_hash = obj.get("posting_summary_set_hash")
    terminal_hash = obj.get("terminal_admission_hash")
    terminal_hashes = obj.get("terminal_admission_hashes")
    terminal_set_hash = obj.get("terminal_admission_set_hash")
    if posting_hash is not None and (
        posting_hashes is not None or posting_set_hash is not None
    ):
        raise ValueError(
            "cross-shard posting evidence cannot mix single hash and hash set"
        )
    if terminal_hash is not None and (
        terminal_hashes is not None or terminal_set_hash is not None
    ):
        raise ValueError(
            "cross-shard posting evidence cannot mix single terminal hash and "
            "terminal hash set"
        )
    expected_hash = _parse_requirement_posting_hash(
        posting_hash,
        requirement=requirement,
        index=index,
    )
    expected_hashes: tuple[str, ...] = ()
    expected_set_hash: str | None = None
    expected_terminal_hash = _parse_requirement_terminal_admission_hash(
        terminal_hash,
        requirement=requirement,
        index=index,
    )
    expected_terminal_hashes: tuple[str, ...] = ()
    expected_terminal_set_hash: str | None = None
    if posting_hashes is not None or posting_set_hash is not None:
        if requirement != CROSS_SHARD_POSTING_SUMMARY_REQUIRED_V0:
            raise ValueError(
                "non-required cross-shard posting evidence cannot include "
                "posting summary hashes"
            )
        if posting_hashes is None or posting_set_hash is None:
            raise ValueError(
                "required cross-shard posting set evidence needs "
                "posting_summary_hashes and posting_summary_set_hash"
            )
        expected_hashes = _require_canonical_posting_summary_hash_list_v0(
            posting_hashes,
            name=f"body.evidence.proof_receipts[{index}].posting_summary_hashes",
        )
        expected_set_hash = _require_hash(
            posting_set_hash,
            name=f"body.evidence.proof_receipts[{index}].posting_summary_set_hash",
        )
        if cross_shard_posting_summary_set_hash_v0(expected_hashes) != expected_set_hash:
            raise ValueError("cross-shard posting summary set hash mismatch")
    if terminal_hashes is not None or terminal_set_hash is not None:
        if requirement != CROSS_SHARD_POSTING_SUMMARY_REQUIRED_V0:
            raise ValueError(
                "non-required cross-shard posting evidence cannot include "
                "terminal admission hashes"
            )
        if terminal_hashes is None or terminal_set_hash is None:
            raise ValueError(
                "required cross-shard posting set evidence needs "
                "terminal_admission_hashes and terminal_admission_set_hash"
            )
        expected_terminal_hashes = _require_canonical_terminal_admission_hash_list_v0(
            terminal_hashes,
            name=f"body.evidence.proof_receipts[{index}].terminal_admission_hashes",
        )
        expected_terminal_set_hash = _require_hash(
            terminal_set_hash,
            name=f"body.evidence.proof_receipts[{index}].terminal_admission_set_hash",
        )
        if (
            cross_shard_terminal_admission_set_hash_v0(expected_terminal_hashes)
            != expected_terminal_set_hash
        ):
            raise ValueError("cross-shard terminal admission set hash mismatch")
    if (expected_set_hash is None) != (expected_terminal_set_hash is None):
        raise ValueError(
            "cross-shard posting set evidence must include matching terminal "
            "admission set evidence"
        )
    if expected_set_hash is not None and len(expected_hashes) != len(
        expected_terminal_hashes
    ):
        raise ValueError(
            "cross-shard posting set evidence terminal admission count mismatch"
        )
    transfer_count = _require_non_negative_int(
        obj.get("cross_shard_transfer_count"),
        name=(
            f"body.evidence.proof_receipts[{index}]."
            "cross_shard_transfer_count"
        ),
    )
    applied_count = _require_non_negative_int(
        obj.get("applied_cross_shard_transfer_count"),
        name=(
            f"body.evidence.proof_receipts[{index}]."
            "applied_cross_shard_transfer_count"
        ),
    )
    if applied_count > transfer_count:
        raise ValueError("applied cross-shard transfer count exceeds transfer count")
    if (
        requirement == CROSS_SHARD_POSTING_SUMMARY_REQUIRED_V0
        and applied_count == 0
    ):
        raise ValueError("required cross-shard posting evidence needs applied transfers")
    if (
        requirement == CROSS_SHARD_POSTING_SUMMARY_FORBIDDEN_V0
        and applied_count != 0
    ):
        raise ValueError("forbidden cross-shard posting evidence has applied transfers")
    if (
        requirement == CROSS_SHARD_POSTING_SUMMARY_OPTIONAL_V0
        and applied_count != 0
    ):
        raise ValueError("optional cross-shard posting evidence has applied transfers")
    if expected_hash is not None:
        expected_hashes = (expected_hash,)
    if expected_terminal_hash is not None:
        expected_terminal_hashes = (expected_terminal_hash,)
    if (
        requirement == CROSS_SHARD_POSTING_SUMMARY_REQUIRED_V0
        and applied_count > 0
        and not expected_terminal_hashes
    ):
        raise ValueError(
            "required cross-shard posting evidence needs terminal_admission_hash "
            "or terminal_admission_set_hash"
        )
    return CrossShardPostingSummaryBodyEvidenceV0(
        requirement=requirement,
        expected_posting_summary_hash=expected_hash,
        expected_posting_summary_hashes=expected_hashes,
        expected_posting_summary_set_hash=expected_set_hash,
        expected_terminal_admission_hash=expected_terminal_hash,
        expected_terminal_admission_hashes=expected_terminal_hashes,
        expected_terminal_admission_set_hash=expected_terminal_set_hash,
    )


def _resolve_posting_requirement(
    *,
    body_obj: Mapping[str, Any],
    posting_request: str,
) -> tuple[CrossShardPostingSummaryBodyEvidenceV0, str]:
    body_evidence = (
        infer_cross_shard_posting_summary_body_evidence_detail_v0(body_obj)
    )
    if posting_request == CROSS_SHARD_POSTING_SUMMARY_BODY_EVIDENCE_V0:
        return (
            body_evidence,
            CROSS_SHARD_POSTING_REQUIREMENT_SOURCE_BODY_EVIDENCE_V0,
        )
    if body_evidence.requirement == CROSS_SHARD_POSTING_SUMMARY_OPTIONAL_V0:
        return (
            CrossShardPostingSummaryBodyEvidenceV0(
                requirement=posting_request,
                expected_posting_summary_hash=None,
                expected_posting_summary_hashes=(),
                expected_posting_summary_set_hash=None,
                expected_terminal_admission_hash=None,
                expected_terminal_admission_hashes=(),
                expected_terminal_admission_set_hash=None,
            ),
            CROSS_SHARD_POSTING_REQUIREMENT_SOURCE_OPERATOR_V0,
        )
    if (
        posting_request != CROSS_SHARD_POSTING_SUMMARY_OPTIONAL_V0
        and posting_request != body_evidence.requirement
    ):
        raise ValueError(
            "cross-shard posting summary requirement conflicts with body evidence"
        )
    return (
        body_evidence,
        CROSS_SHARD_POSTING_REQUIREMENT_SOURCE_BODY_EVIDENCE_V0,
    )


def _parse_requirement_posting_hash(
    value: object,
    *,
    requirement: str,
    index: int,
) -> str | None:
    name = f"body.evidence.proof_receipts[{index}].posting_summary_hash"
    if requirement == CROSS_SHARD_POSTING_SUMMARY_REQUIRED_V0:
        if value is None:
            return None
        return _require_hash(value, name=name)
    if value is not None:
        raise ValueError("non-required cross-shard posting evidence cannot include posting_summary_hash")
    return None


def _parse_requirement_terminal_admission_hash(
    value: object,
    *,
    requirement: str,
    index: int,
) -> str | None:
    name = f"body.evidence.proof_receipts[{index}].terminal_admission_hash"
    if requirement == CROSS_SHARD_POSTING_SUMMARY_REQUIRED_V0:
        if value is None:
            return None
        return _require_hash(value, name=name)
    if value is not None:
        raise ValueError(
            "non-required cross-shard posting evidence cannot include "
            "terminal_admission_hash"
        )
    return None


def _require_canonical_posting_summary_hash_list_v0(
    value: object,
    *,
    name: str,
) -> tuple[str, ...]:
    if not isinstance(value, list):
        raise TypeError(f"{name} must be a list")
    hashes = tuple(
        _require_hash(item, name=f"{name}[{index}]")
        for index, item in enumerate(value)
    )
    if len(hashes) == 0:
        raise ValueError(f"{name} must be non-empty")
    if tuple(sorted(hashes)) != hashes:
        raise ValueError(f"{name} must be sorted")
    if len(set(hashes)) != len(hashes):
        raise ValueError(f"{name} must be unique")
    return hashes


def _require_canonical_terminal_admission_hash_list_v0(
    value: object,
    *,
    name: str,
) -> tuple[str, ...]:
    if not isinstance(value, list):
        raise TypeError(f"{name} must be a list")
    hashes = tuple(
        _require_hash(item, name=f"{name}[{index}]")
        for index, item in enumerate(value)
    )
    if len(hashes) == 0:
        raise ValueError(f"{name} must be non-empty")
    if tuple(sorted(hashes)) != hashes:
        raise ValueError(f"{name} must be sorted")
    if len(set(hashes)) != len(hashes):
        raise ValueError(f"{name} must be unique")
    return hashes


def _validate_expected_posting_summary_hashes(
    *,
    posting_summaries: Sequence[Mapping[str, Any]],
    expected_evidence: CrossShardPostingSummaryBodyEvidenceV0,
) -> None:
    expected_hashes = expected_evidence.expected_posting_summary_hashes
    if not expected_hashes:
        return
    if len(posting_summaries) == 0:
        raise ValueError("cross-shard posting summary is required")
    posting_hashes = tuple(
        str(posting_summary["posting_summary_hash"])
        for posting_summary in posting_summaries
    )
    if posting_hashes != expected_hashes:
        if expected_evidence.expected_posting_summary_set_hash is None:
            raise ValueError(
                "cross-shard posting summary hash conflicts with body evidence"
            )
        raise ValueError(
            "cross-shard posting summary set conflicts with body evidence"
        )
    if expected_evidence.expected_posting_summary_set_hash is None:
        return
    if (
        cross_shard_posting_summary_set_hash_v0(posting_hashes)
        != expected_evidence.expected_posting_summary_set_hash
    ):
        raise ValueError("cross-shard posting summary set hash conflicts with body evidence")


def _require_posting_summary_requirement(value: object) -> str:
    requirement = _require_str(
        value,
        name="cross_shard_posting_summary_requirement",
    )
    if requirement not in CROSS_SHARD_POSTING_SUMMARY_REQUIREMENTS_V0:
        raise ValueError("cross_shard_posting_summary_requirement is not allowed")
    return requirement


def _require_posting_summary_request(value: object) -> str:
    requirement = _require_str(
        value,
        name="cross_shard_posting_summary_requirement",
    )
    if requirement not in CROSS_SHARD_POSTING_SUMMARY_REQUESTS_V0:
        raise ValueError("cross_shard_posting_summary_requirement is not allowed")
    return requirement


def _require_posting_requirement_source(value: object) -> str:
    source = _require_str(
        value,
        name="cross_shard_posting_summary_requirement_source",
    )
    if source not in CROSS_SHARD_POSTING_REQUIREMENT_SOURCES_V0:
        raise ValueError("cross_shard_posting_summary_requirement_source is not allowed")
    return source


def _reject_unknown_keys(
    value: Mapping[str, Any],
    *,
    allowed: frozenset[str],
    name: str,
) -> None:
    extra = sorted(set(value.keys()) - set(allowed))
    if extra:
        raise ValueError(f"{name} contains unknown keys: {extra}")


def _require_mapping(value: object, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be a JSON object")
    return value


def _require_str(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a str")
    if value == "":
        raise ValueError(f"{name} must be non-empty")
    if "\x00" in value:
        raise ValueError(f"{name} must not contain NUL")
    return value


def _require_hash(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a str")
    canonical = canonical_hex_fixed_allow_0x(
        value,
        nbytes=ROOT_NBYTES,
        name=name,
    )
    if value != canonical:
        raise ValueError(f"{name} must be canonical lowercase 0x-prefixed hex")
    return canonical


def _require_tau_state_root(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a str")
    return canonical_hex_fixed_allow_0x(
        value,
        nbytes=ROOT_NBYTES,
        name=name,
    )


def _require_positive_int(value: object, *, name: str) -> int:
    out = _require_int(value, name=name)
    if out <= 0:
        raise ValueError(f"{name} must be positive")
    return out


def _require_non_negative_int(value: object, *, name: str) -> int:
    out = _require_int(value, name=name)
    if out < 0:
        raise ValueError(f"{name} must be non-negative")
    return out


def _require_int(value: object, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    return int(value)
