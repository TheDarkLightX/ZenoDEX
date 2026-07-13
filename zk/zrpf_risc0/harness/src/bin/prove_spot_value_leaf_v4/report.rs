use risc0_zkvm::Digest;
use serde_json::{json, Value};
use zenodex_zrpf_protocol_v3::encode_node_journal_v3;
use zenodex_zrpf_risc0_value_node_shared::PINNED_V1_ADAPTER_IMAGE_ID_A;
use zenodex_zrpf_risc0_verifier::historical_spot_value_leaf_v4::ExactSpotValueLeafReceiptV4;

use super::artifact_io::sha256_hex;
use super::source::VerifiedSource;
use super::{
    PreparedLeaf, VerifiedAdapter, ASSIGNED_LEAF_ORDINAL, EXPECTED_V4_GUEST_ELF_BYTES,
    EXPECTED_V4_GUEST_ELF_SHA256, EXPECTED_V4_IMAGE_ID,
};

const REPORT_SCHEMA: &str = "zenodex/zrpf_spot_value_leaf_v4_local_report/v2";

pub(super) struct ReportInput<'a> {
    pub(super) source: &'a VerifiedSource,
    pub(super) adapter: &'a VerifiedAdapter,
    pub(super) prepared: &'a PreparedLeaf,
    pub(super) verified: &'a ExactSpotValueLeafReceiptV4,
    pub(super) receipt_bytes: &'a [u8],
    pub(super) receipt_written: bool,
    pub(super) guest_artifact_loaded_and_matched: bool,
    pub(super) status: &'a str,
}

pub(super) fn print_report(input: ReportInput<'_>) -> Result<(), String> {
    println!("{}", report_value(input)?);
    Ok(())
}

pub(super) fn guest_artifact_report(loaded_and_matched: bool) -> Value {
    let observed_elf_bytes = loaded_and_matched.then_some(EXPECTED_V4_GUEST_ELF_BYTES);
    let observed_elf_sha256 = loaded_and_matched.then_some(EXPECTED_V4_GUEST_ELF_SHA256);
    json!({
        "expected_elf_bytes": EXPECTED_V4_GUEST_ELF_BYTES,
        "expected_elf_sha256": EXPECTED_V4_GUEST_ELF_SHA256,
        "loaded_and_matched": loaded_and_matched,
        "observed_elf_bytes": observed_elf_bytes,
        "observed_elf_sha256": observed_elf_sha256,
        "source_to_elf_provenance_verified": false,
    })
}

fn report_value(input: ReportInput<'_>) -> Result<Value, String> {
    let journal = input.verified.journal();
    let structural_bytes = encode_node_journal_v3(journal.structural())
        .map_err(|error| format!("structural journal encode: {error}"))?;
    let journal_hash = journal
        .canonical_hash()
        .map_err(|error| format!("V4 journal hash: {error}"))?;
    Ok(json!({
        "adapter_image_id": Digest::from(PINNED_V1_ADAPTER_IMAGE_ID_A).to_string(),
        "adapter_journal_sha256": sha256_hex(&input.adapter.receipt.receipt().journal.bytes),
        "adapter_receipt_sha256": input.adapter.receipt_sha256,
        "application_statement_hash": hex::encode(journal.application_statement_hash().as_bytes()),
        "asset_flow_count": journal.semantic_subtree().asset_flows().len(),
        "assigned_leaf_ordinal": ASSIGNED_LEAF_ORDINAL,
        "authority_use_count": journal.semantic_subtree().authority_uses().len(),
        "claim_binding": hex::encode(input.verified.claim_binding().as_bytes()),
        "exact_expected_journal_verified": true,
        "guest_artifact": guest_artifact_report(input.guest_artifact_loaded_and_matched),
        "host_reconstructed_input_bytes": input.prepared.input_bytes.len(),
        "host_reconstructed_input_sha256": sha256_hex(&input.prepared.input_bytes),
        "journal_hash": hex::encode(journal_hash.as_bytes()),
        "journal_sha256": sha256_hex(&input.verified.authenticated().receipt().journal.bytes),
        "nonclaims": [
            "the retained source and adapter receipts were not regenerated",
            "the compiler-visible guest path is temporary and not release-governed",
            "the public policy and empty mint-grant set are local witness inputs without governance authority",
            "the retained source has zero asset rows and unchanged raw state",
            "this residual leaf does not prove closed-epoch conservation or semantic finality",
            "verify-only replay does not load, hash, or recompute the guest ELF and does not establish ELF-to-image provenance",
            "the host-reconstructed input hash is not a receipt-proven private-input commitment",
            "no data-availability, schedule, carry, ledger-admission, settlement, release, privacy, sandbox, reproducible-build, or production authority"
        ],
        "ok": true,
        "outer_image_governance_verified": false,
        "production_authority": false,
        "receipt_bytes": input.receipt_bytes.len(),
        "receipt_sha256": sha256_hex(input.receipt_bytes),
        "receipt_written_create_new": input.receipt_written,
        "release_authority": false,
        "receipt_proves_private_input_hash": false,
        "represented_row_count": journal.semantic_subtree().represented_row_count(),
        "schema": REPORT_SCHEMA,
        "settlement_authority": false,
        "source_receipt_sha256": input.source.receipt_sha256,
        "source_state_unchanged": input.source.summary.pre_state_root == input.source.summary.post_state_root,
        "status": input.status,
        "structural_journal_sha256": sha256_hex(&structural_bytes),
        "value_subtree_root": hex::encode(journal.semantic_subtree().value_subtree_root().as_bytes()),
        "v4_image_id": Digest::from(EXPECTED_V4_IMAGE_ID).to_string(),
        "zero_knowledge_privacy": false,
    }))
}
