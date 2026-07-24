use std::{env, path::PathBuf};

use risc0_zkvm::{
    compute_image_id, default_prover, Digest, ExecutorEnv, InnerReceipt, ProverOpts, Receipt,
};
use zenodex_zrpf_protocol_v3::{
    decode_exact_settlement_admission_journal_v1, derive_sparse_merkle_root_v1,
    encode_full_blob_da_certificate_v1, ApplicationIdV3, CommitmentV3, DomainIdV3,
    FullBlobDataAvailabilityCertificateInputV1, FullBlobDataAvailabilityCertificateV1, NodeLevelV3,
    SparseMerkleCellTransitionWitnessInputV1, SparseMerkleCellTransitionWitnessV1,
    SparseMerkleSiblingPathV1, ValueHashV2, SPARSE_MERKLE_TREE_DEPTH_V1,
    SPARSE_MERKLE_WITNESS_VERSION_V1,
};
use zenodex_zrpf_risc0_semantic_shared::{
    derive_spot_settlement_projection_v1, propose_spot_settlement_state_projection_v2,
    OrdinarySpotSettlementGuestInputV2, OrdinarySpotSettlementReplayDataV2,
    SpotSettlementAuthorizationInputV1,
};
use zenodex_zrpf_risc0_shared::derive_risc0_verified_claim_binding_v1;
use zenodex_zrpf_risc0_spot_settlement_root_policy_v6::PINNED_SOURCE_OPENED_SPOT_SETTLEMENT_IMAGE_ID_V6;
use zenodex_zrpf_risc0_spot_settlement_v6_shared::{
    compose_source_opened_spot_settlement_output_after_l2_verification_v3,
    encode_source_opened_spot_settlement_guest_input_v3,
    encode_source_opened_spot_settlement_replay_v3,
    source_opened_spot_settlement_replay_schema_id_v3,
    validate_singleton_source_opened_spot_relation_v6, SourceOpenedSpotSettlementGuestInputV3,
};
use zenodex_zrpf_risc0_spot_v6_methods::{
    ZENODEX_ZRPF_RISC0_SOURCE_OPENED_SPOT_SETTLEMENT_V6_ELF,
    ZENODEX_ZRPF_RISC0_SOURCE_OPENED_SPOT_SETTLEMENT_V6_ID,
    ZENODEX_ZRPF_RISC0_SPOT_VALUE_AGGREGATE_L2_V6_ELF,
    ZENODEX_ZRPF_RISC0_SPOT_VALUE_AGGREGATE_L2_V6_ID,
};
use zenodex_zrpf_risc0_spot_value_aggregate_root_policy_v6::pinned_source_opened_spot_value_aggregate_l2_root_identity_v6;
use zenodex_zrpf_risc0_verifier::{
    ExpectedValueAggregateReceiptIdentityV5, VerifiedSourceOpenedSpotSettlementAdmissionV6,
    VerifiedValueAggregateReceiptV5,
};

#[path = "prove_spot_value_leaf_v4/artifact_io.rs"]
mod artifact_io;

use artifact_io::{
    canonical_receipt_bytes, persist_receipt, read_bounded_regular_file, require_succinct,
    sha256_hex,
};

struct Options {
    receipt_out: PathBuf,
    journal_out: PathBuf,
    mutation_out: PathBuf,
    guest_input_out: PathBuf,
    replay_out: PathBuf,
    da_certificate_out: PathBuf,
    source_envelope: PathBuf,
    l2_receipt: PathBuf,
}

fn main() {
    if let Err(error) = run() {
        eprintln!("{error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    if env::var_os("RISC0_DEV_MODE").is_some() {
        return Err("ambient RISC0_DEV_MODE is forbidden".to_owned());
    }
    let options = parse_options(env::args().skip(1))?;
    validate_method(
        "V6 L2",
        ZENODEX_ZRPF_RISC0_SPOT_VALUE_AGGREGATE_L2_V6_ELF,
        ZENODEX_ZRPF_RISC0_SPOT_VALUE_AGGREGATE_L2_V6_ID,
    )?;
    if ZENODEX_ZRPF_RISC0_SOURCE_OPENED_SPOT_SETTLEMENT_V6_ID
        != PINNED_SOURCE_OPENED_SPOT_SETTLEMENT_IMAGE_ID_V6
    {
        return Err("generated settlement image differs from governed policy".to_owned());
    }
    validate_method(
        "V6 settlement",
        ZENODEX_ZRPF_RISC0_SOURCE_OPENED_SPOT_SETTLEMENT_V6_ELF,
        ZENODEX_ZRPF_RISC0_SOURCE_OPENED_SPOT_SETTLEMENT_V6_ID,
    )?;
    let source_bytes = read_bounded_regular_file(&options.source_envelope, "V6 source envelope")?;
    let source = zenodex_zrpf_risc0_spot_value_leaf_v6_shared::decode_exact_source_opened_spot_value_leaf_input_v6(&source_bytes)
        .map_err(|error| format!("V6 source envelope rejected: {error}"))?;
    let l2_bytes = read_bounded_regular_file(&options.l2_receipt, "V6 L2 receipt")?;
    let root = pinned_source_opened_spot_value_aggregate_l2_root_identity_v6()
        .map_err(|error| format!("derive V6 L2 root policy: {error}"))?;
    if root.expected_image_id() != ZENODEX_ZRPF_RISC0_SPOT_VALUE_AGGREGATE_L2_V6_ID {
        return Err("generated V6 L2 image differs from governed root policy".to_owned());
    }
    let l2_identity = ExpectedValueAggregateReceiptIdentityV5::new(
        NodeLevelV3::new(2).map_err(|error| format!("derive V6 L2 level: {error}"))?,
        root.expected_profile_id(),
        root.expected_manifest_root(),
    )
    .map_err(|error| format!("construct V6 L2 identity: {error}"))?;
    let l2 = VerifiedValueAggregateReceiptV5::verify_canonical_succinct_bytes(
        &l2_bytes,
        ZENODEX_ZRPF_RISC0_SPOT_VALUE_AGGREGATE_L2_V6_ID,
        l2_identity,
    )
    .map_err(|error| format!("V6 L2 receipt verification failed: {error}"))?;
    let statement = validate_singleton_source_opened_spot_relation_v6(l2.proposal(), &source)
        .map_err(|error| format!("V6 source/L2 relation rejected: {error}"))?;
    let authorization = SpotSettlementAuthorizationInputV1 {
        authorization_subject_id: statement.authorization_subject_id(),
        authorization_scope_id: statement.authorization_scope_id(),
        authorization_nonce: statement.authorization_nonce(),
        authorization_grant_id: statement.authorization_grant_id(),
    };
    let witness = settlement_witness(l2.proposal(), authorization)?;
    let replay =
        OrdinarySpotSettlementReplayDataV2::recompose(l2.proposal(), authorization, &witness)
            .map_err(|error| format!("V6 settlement replay rejected: {error}"))?;
    let replay_bytes = encode_source_opened_spot_settlement_replay_v3(&replay, &source)
        .map_err(|error| format!("V6 settlement replay encoding failed: {error}"))?;
    let da = da_certificate(l2.proposal(), &replay_bytes)?;
    let da_bytes = encode_full_blob_da_certificate_v1(&da)
        .map_err(|error| format!("V6 DA certificate encoding failed: {error}"))?;
    let base = OrdinarySpotSettlementGuestInputV2::new(
        l2.receipt().journal.bytes.clone(),
        authorization,
        witness,
        da,
    )
    .map_err(|error| format!("V6 settlement base input rejected: {error}"))?;
    let input = SourceOpenedSpotSettlementGuestInputV3::new(base, source)
        .map_err(|error| format!("V6 settlement source input rejected: {error}"))?;
    let guest_input = encode_source_opened_spot_settlement_guest_input_v3(&input)
        .map_err(|error| format!("V6 settlement input encoding failed: {error}"))?;
    let l2_claim = derive_risc0_verified_claim_binding_v1(
        ZENODEX_ZRPF_RISC0_SPOT_VALUE_AGGREGATE_L2_V6_ID,
        &l2.receipt().journal.bytes,
    )
    .map_err(|error| format!("derive V6 L2 claim binding: {error}"))?;
    let expected_journal =
        compose_source_opened_spot_settlement_output_after_l2_verification_v3(&input, l2_claim)
            .map_err(|error| format!("V6 settlement recomposition rejected: {error}"))?;
    let input_length = u32::try_from(guest_input.len())
        .map_err(|_| "V6 settlement input exceeds u32".to_owned())?;
    let executor_env = ExecutorEnv::builder()
        .write_slice(&[input_length])
        .write_slice(&guest_input)
        .add_assumption(l2.receipt().clone())
        .build()
        .map_err(|error| format!("V6 settlement executor environment rejected: {error}"))?;
    let receipt = default_prover()
        .prove_with_opts(
            executor_env,
            ZENODEX_ZRPF_RISC0_SOURCE_OPENED_SPOT_SETTLEMENT_V6_ELF,
            &ProverOpts::succinct(),
        )
        .map_err(|error| format!("V6 settlement proving failed: {error}"))?
        .receipt;
    require_succinct(&receipt, "V6 settlement")?;
    let expected_admission = decode_exact_settlement_admission_journal_v1(&expected_journal)
        .map_err(|error| format!("expected V6 admission journal decode failed: {error}"))?;
    let receipt_bytes = canonical_receipt_bytes(&receipt)?;
    let verified =
        VerifiedSourceOpenedSpotSettlementAdmissionV6::verify(&receipt_bytes, &guest_input)
            .map_err(|error| format!("sealed V6 settlement verification failed: {error}"))?;
    if verified.verified_receipt().journal() != &expected_admission {
        return Err("verified V6 admission differs from host recomposition".to_owned());
    }
    let verified_receipt = verified.verified_receipt().receipt();
    let admission =
        decode_exact_settlement_admission_journal_v1(&verified_receipt.journal.bytes)
            .map_err(|error| format!("V6 admission journal strict decode failed: {error}"))?;
    let mutation_bytes = exact_seal_mutation_reject(&receipt)?;
    persist_receipt(&options.journal_out, &verified_receipt.journal.bytes)?;
    persist_receipt(&options.guest_input_out, &guest_input)?;
    persist_receipt(&options.replay_out, &replay_bytes)?;
    persist_receipt(&options.da_certificate_out, &da_bytes)?;
    persist_receipt(&options.receipt_out, &receipt_bytes)?;
    persist_receipt(&options.mutation_out, &mutation_bytes)?;
    println!(
        "{}",
        serde_json::to_string(&serde_json::json!({
            "action_count": admission.action_count(),
            "admission_journal_bytes": verified_receipt.journal.bytes.len(),
            "admission_journal_sha256": sha256_hex(&verified_receipt.journal.bytes),
            "consumed_object_count": admission.consumed_object_count(),
            "data_availability_certificate_bytes": da_bytes.len(),
            "data_availability_certificate_sha256": sha256_hex(&da_bytes),
            "image_id": Digest::from(ZENODEX_ZRPF_RISC0_SOURCE_OPENED_SPOT_SETTLEMENT_V6_ID).to_string(),
            "l2_receipt_sha256": sha256_hex(&l2_bytes),
            "mutation_receipt_sha256": sha256_hex(&mutation_bytes),
            "mutation_rejected": true,
            "ok": true,
            "receipt_bytes": receipt_bytes.len(),
            "receipt_sha256": sha256_hex(&receipt_bytes),
            "replay_bytes": replay_bytes.len(),
            "replay_sha256": sha256_hex(&replay_bytes),
            "schema": "zenodex/zrpf_source_opened_spot_settlement_v6_proof_report/v1",
            "source_envelope_sha256": sha256_hex(&source_bytes),
            "status": "source_opened_spot_settlement_v6_succinct_receipt_verified",
            "settlement_claim_binding": hex::encode(verified.verified_receipt().settlement_claim_binding().as_bytes()),
            "settlement_program_manifest_root": hex::encode(verified.verified_receipt().verified_program_manifest_root().as_bytes()),
            "settlement_program_id": hex::encode(verified.verified_receipt().verified_program_id().as_bytes()),
            "succinct_receipt_profile_id": verified.verified_receipt().receipt_profile().profile_id(),
            "guest_input_bytes": guest_input.len(),
            "guest_input_sha256": sha256_hex(&guest_input),
            "nonclaims": [
                "the accepted source receipt does not establish an end-user signature scheme",
                "this local receipt grants no release, governance, Tau-finality, or production authority"
            ],
        }))
        .map_err(|error| format!("V6 settlement report encode: {error}"))?
    );
    Ok(())
}

fn settlement_witness(
    proposal: &zenodex_zrpf_protocol_v3::ProposedValueAggregateV5,
    authorization: SpotSettlementAuthorizationInputV1,
) -> Result<SparseMerkleCellTransitionWitnessV1, String> {
    let projection = derive_spot_settlement_projection_v1(proposal, authorization)
        .map_err(|error| format!("derive settlement projection: {error}"))?;
    let cell_key = projection.cell_key();
    let pre_value_hash = ValueHashV2::new(
        proposal
            .semantic_subtree()
            .raw_subtree_pre_state_root()
            .into_bytes(),
    );
    let post_value_hash = ValueHashV2::new(
        proposal
            .semantic_subtree()
            .raw_subtree_post_state_root()
            .into_bytes(),
    );
    let siblings = SparseMerkleSiblingPathV1::new(
        [CommitmentV3::new([90; 32]).map_err(|error| format!("sibling commitment: {error}"))?;
            SPARSE_MERKLE_TREE_DEPTH_V1],
    );
    let pre_root = derive_sparse_merkle_root_v1(cell_key, pre_value_hash, &siblings)
        .map_err(|error| format!("derive settlement pre-root: {error}"))?;
    let post_root = derive_sparse_merkle_root_v1(cell_key, post_value_hash, &siblings)
        .map_err(|error| format!("derive settlement post-root: {error}"))?;
    let proposed =
        propose_spot_settlement_state_projection_v2(proposal, authorization, pre_root, post_root)
            .map_err(|error| format!("derive settlement state projection: {error}"))?;
    SparseMerkleCellTransitionWitnessV1::new(SparseMerkleCellTransitionWitnessInputV1 {
        witness_version: SPARSE_MERKLE_WITNESS_VERSION_V1,
        economic_action_id: proposed.economic_action_id(),
        cell_key,
        pre_value_hash,
        post_value_hash,
        sibling_commitments: siblings,
        claimed_pre_root: pre_root,
        claimed_post_root: post_root,
    })
    .map_err(|error| format!("construct settlement witness: {error}"))
}

fn da_certificate(
    proposal: &zenodex_zrpf_protocol_v3::ProposedValueAggregateV5,
    blob: &[u8],
) -> Result<FullBlobDataAvailabilityCertificateV1, String> {
    let retention = proposal
        .scope()
        .epoch_start()
        .checked_add(10)
        .ok_or_else(|| "DA retention epoch overflow".to_owned())?;
    FullBlobDataAvailabilityCertificateV1::derive(FullBlobDataAvailabilityCertificateInputV1 {
        application_id: ApplicationIdV3::new(proposal.scope().application_id().into_bytes())
            .map_err(|error| format!("DA application ID: {error}"))?,
        chain_or_domain_id: DomainIdV3::new(proposal.scope().chain_or_domain_id().into_bytes())
            .map_err(|error| format!("DA domain ID: {error}"))?,
        epoch_id: proposal.scope().epoch_start(),
        data_schema_id: source_opened_spot_settlement_replay_schema_id_v3()
            .map_err(|error| format!("DA schema ID: {error}"))?,
        blob,
        retention_through_epoch: retention,
        storage_policy_hash: proposal.scope().public_policy_hash(),
    })
    .map_err(|error| format!("derive full-blob DA certificate: {error}"))
}

fn exact_seal_mutation_reject(receipt: &Receipt) -> Result<Vec<u8>, String> {
    let mut candidate = receipt.clone();
    let InnerReceipt::Succinct(inner) = &mut candidate.inner else {
        return Err("V6 settlement receipt is not Succinct".to_owned());
    };
    let word = inner
        .seal
        .get_mut(1)
        .ok_or_else(|| "V6 settlement Succinct seal lacks word 1".to_owned())?;
    *word ^= 1;
    if candidate
        .verify(ZENODEX_ZRPF_RISC0_SOURCE_OPENED_SPOT_SETTLEMENT_V6_ID)
        .is_ok()
    {
        return Err("mutated V6 settlement receipt was accepted".to_owned());
    }
    canonical_receipt_bytes(&candidate)
}

fn parse_options(args: impl IntoIterator<Item = String>) -> Result<Options, String> {
    let args = args.into_iter().collect::<Vec<_>>();
    if args.len() != 16
        || args[0] != "--receipt-out"
        || args[2] != "--journal-out"
        || args[4] != "--mutation-out"
        || args[6] != "--guest-input-out"
        || args[8] != "--replay-out"
        || args[10] != "--da-certificate-out"
        || args[12] != "--source-envelope"
        || args[14] != "--l2-receipt"
        || [1, 3, 5, 7, 9, 11, 13, 15]
            .iter()
            .any(|index| args[*index].is_empty() || args[*index].starts_with("--"))
    {
        return Err("usage: prove_source_opened_spot_settlement_v6 --receipt-out <settlement.receipt.json> --journal-out <admission.bin> --mutation-out <mutated.receipt.json> --guest-input-out <settlement.input.bin> --replay-out <replay.bin> --da-certificate-out <da.bin> --source-envelope <v6.input.bin> --l2-receipt <l2.receipt.json>".to_owned());
    }
    Ok(Options {
        receipt_out: PathBuf::from(&args[1]),
        journal_out: PathBuf::from(&args[3]),
        mutation_out: PathBuf::from(&args[5]),
        guest_input_out: PathBuf::from(&args[7]),
        replay_out: PathBuf::from(&args[9]),
        da_certificate_out: PathBuf::from(&args[11]),
        source_envelope: PathBuf::from(&args[13]),
        l2_receipt: PathBuf::from(&args[15]),
    })
}

fn validate_method(name: &str, elf: &[u8], image_id: [u32; 8]) -> Result<(), String> {
    if elf.is_empty() || image_id.iter().all(|word| *word == 0) {
        return Err(format!("{name} method is a placeholder"));
    }
    let computed = compute_image_id(elf).map_err(|error| format!("compute {name}: {error}"))?;
    if computed != Digest::from(image_id) {
        return Err(format!("{name} image ID mismatch"));
    }
    Ok(())
}
