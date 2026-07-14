//! Exact authority-neutral mutation verification for the bounded Spot V6/V7 chain.
//!
//! Every positive receipt crosses its governed cryptographic verifier before
//! this process creates any new mutation. The three generated mutations and
//! the two prover-retained mutations must each differ from their positive
//! receipt only at Succinct seal word 1, bit 0. Acceptance produces a
//! content-bound report and three mutation artifacts. It grants no proof,
//! release, settlement, or production authority.

use std::{
    env,
    fs::OpenOptions,
    io::{Read, Write},
    os::unix::fs::{MetadataExt, OpenOptionsExt},
    path::{Path, PathBuf},
};

use risc0_zkvm::{compute_image_id, Digest, InnerReceipt, Receipt};
use serde::Serialize;
use sha2::{Digest as _, Sha256};
use zenodex_zrpf_protocol_v3::NodeLevelV3;
use zenodex_zrpf_risc0_shared::program_id_from_risc0_words_v3;
use zenodex_zrpf_risc0_spot_settlement_root_policy_v6::pinned_source_opened_spot_settlement_identity_v6;
use zenodex_zrpf_risc0_spot_settlement_v6_shared::decode_exact_source_opened_spot_settlement_guest_envelope_v3;
use zenodex_zrpf_risc0_spot_settlement_v7_methods::ZENODEX_ZRPF_RISC0_SPOT_SETTLEMENT_V7_ID;
use zenodex_zrpf_risc0_spot_settlement_v7_verifier::{
    verify_spot_settlement_v7_canonical_succinct_bytes, VerifiedSpotSettlementV7ErrorV1,
    VerifiedSpotSettlementV7ReceiptV1,
};
use zenodex_zrpf_risc0_spot_v6_methods::{
    ZENODEX_ZRPF_RISC0_SPOT_VALUE_AGGREGATE_L1_V6_ID, ZENODEX_ZRPF_RISC0_SPOT_VALUE_LEAF_V6_ID,
};
use zenodex_zrpf_risc0_spot_value_aggregate_l1_policy_v6::{
    pinned_source_opened_spot_value_leaf_identity_v6,
    source_opened_spot_value_aggregate_l1_manifest_root_v6,
    source_opened_spot_value_aggregate_l1_profile_id_v6,
};
use zenodex_zrpf_risc0_spot_value_aggregate_l2_policy_v6::{
    pinned_source_opened_spot_value_aggregate_l1_identity_v6,
    PINNED_SOURCE_OPENED_SPOT_VALUE_AGGREGATE_L1_IMAGE_ID_V6,
};
use zenodex_zrpf_risc0_spot_value_aggregate_root_policy_v6::pinned_source_opened_spot_value_aggregate_l2_root_identity_v6;
use zenodex_zrpf_risc0_spot_value_leaf_v6_shared::{
    decode_exact_source_opened_spot_value_leaf_input_v6,
    recompose_source_opened_spot_value_leaf_statement_v6,
};
use zenodex_zrpf_risc0_value_aggregate_shared::{
    recompose_expected_source_opened_spot_value_aggregate_level_one_v6,
    recompose_expected_value_aggregate_level_two_v5, ValueAggregateLevelOneInputV5,
    ValueAggregateLevelTwoInputV5, ValueAggregateRecompositionPolicyV5,
};
use zenodex_zrpf_risc0_verifier::{
    ExpectedValueAggregateReceiptIdentityV5, VerifiedNodeReceiptErrorV3,
    VerifiedSourceOpenedSpotSettlementAdmissionV6,
    VerifiedSourceOpenedSpotSettlementReceiptErrorV6,
    VerifiedSourceOpenedSpotValueLeafReceiptErrorV6, VerifiedSourceOpenedSpotValueLeafReceiptV6,
    VerifiedValueAggregateReceiptErrorV5, VerifiedValueAggregateReceiptV5,
    ZRPF_RISC0_SUCCINCT_RECEIPT_PROFILE_ID_V1,
};

const REPORT_SCHEMA: &str = "zenodex/zrpf_remote_mutation_verification/v1";
const REPORT_STATUS: &str = "five_positive_receipts_verified_and_five_exact_mutations_rejected";
const REPORT_DOMAIN: &[u8] = b"zenodex/zrpf_remote_mutation_verification_report_id/v1\0";
const ZERO_SHA256: &str = "0000000000000000000000000000000000000000000000000000000000000000";
const MUTATION_WORD_INDEX: usize = 1;
const XOR_MASK: u32 = 1;
const MAX_RECEIPT_BYTES: usize = 16 * 1_024 * 1_024;
const MAX_GUEST_INPUT_BYTES: usize = 16 * 1_024 * 1_024;
const MAX_PROGRAM_BYTES: usize = 64 * 1_024 * 1_024;
const EXPECTED_STAGE_IDS: [&str; 5] = [
    "v6_leaf",
    "v6_l1",
    "v6_l2",
    "v6_settlement",
    "v7_settlement",
];
const EXPECTED_REJECT_BOUNDARIES: [&str; 5] = [
    "VerifiedSourceOpenedSpotValueLeafReceiptV6",
    "VerifiedValueAggregateReceiptV5",
    "VerifiedValueAggregateReceiptV5",
    "VerifiedSourceOpenedSpotSettlementAdmissionV6",
    "VerifiedSpotSettlementV7ReceiptV1",
];
const RECEIPT_VERIFICATION_REJECT_CODE: &str = "receipt_verification_failed";

#[derive(Debug)]
struct Options {
    leaf_source_envelope: PathBuf,
    settlement_guest_input: PathBuf,
    v7_guest_input: PathBuf,
    leaf_program: PathBuf,
    level_one_program: PathBuf,
    level_two_program: PathBuf,
    settlement_program: PathBuf,
    v7_program: PathBuf,
    leaf_receipt: PathBuf,
    level_one_receipt: PathBuf,
    level_two_receipt: PathBuf,
    settlement_receipt: PathBuf,
    v7_receipt: PathBuf,
    settlement_mutation: PathBuf,
    v7_mutation: PathBuf,
    leaf_mutation_out: PathBuf,
    level_one_mutation_out: PathBuf,
    level_two_mutation_out: PathBuf,
}

#[derive(Clone, Debug, Serialize)]
struct AuthorityV1 {
    proof_authority: bool,
    release_authority: bool,
    settlement_authority: bool,
    production_authority: bool,
}

#[derive(Clone, Debug, Serialize)]
struct ProgramFactsV1 {
    program_bytes: usize,
    program_sha256: String,
    expected_image_id: String,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
struct MutationFactsV1 {
    word_count: usize,
    word_index: usize,
    original_word: u32,
    mutated_word: u32,
    xor_mask: u32,
}

#[derive(Clone, Debug, Serialize)]
struct StageFactsV1 {
    stage_id: &'static str,
    program: ProgramFactsV1,
    receipt_profile_id: String,
    positive_receipt_bytes: usize,
    positive_receipt_sha256: String,
    positive_journal_sha256: String,
    mutation_receipt_bytes: usize,
    mutation_receipt_sha256: String,
    mutation: MutationFactsV1,
    reject_boundary: &'static str,
    reject_code: &'static str,
}

#[derive(Clone, Debug, Serialize)]
struct ReportV1 {
    schema: &'static str,
    status: &'static str,
    report_id: String,
    receipt_profile_id: String,
    positive_receipts_verified: u8,
    exact_seal_mutations_rejected: u8,
    settlement_l2_claim_bound: bool,
    stages: [StageFactsV1; 5],
    authority: AuthorityV1,
    non_claims: [&'static str; 4],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct CliError(&'static str);

impl std::fmt::Display for CliError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(self.0)
    }
}

fn main() {
    if let Err(error) = run() {
        eprintln!("{}", error.0);
        std::process::exit(1);
    }
}

fn run() -> Result<(), CliError> {
    if env::var_os("RISC0_DEV_MODE").is_some() {
        return Err(CliError("ambient_risc0_dev_mode_forbidden"));
    }
    let options = parse_options(env::args().skip(1))?;
    let inputs = Inputs::read(&options)?;
    let programs = verify_programs(&inputs)?;
    let chain = VerifiedChain::verify(&inputs)?;
    let mutations = VerifiedMutations::derive_and_reject(&inputs, &chain)?;

    mutations.persist(&options)?;
    let report = finalized_report(report_stages(programs, &inputs, &chain, &mutations))?;
    write_report(&report)
}

struct VerifiedChain {
    leaf: VerifiedSourceOpenedSpotValueLeafReceiptV6,
    level_one: VerifiedValueAggregateReceiptV5,
    level_one_identity: ExpectedValueAggregateReceiptIdentityV5,
    level_two: VerifiedValueAggregateReceiptV5,
    level_two_image_id: [u32; 8],
    level_two_identity: ExpectedValueAggregateReceiptIdentityV5,
    settlement: VerifiedSourceOpenedSpotSettlementAdmissionV6,
    v7: VerifiedSpotSettlementV7ReceiptV1,
}

impl VerifiedChain {
    fn verify(inputs: &Inputs) -> Result<Self, CliError> {
        let leaf = verify_leaf(inputs)?;
        let (level_one, level_one_identity) = verify_level_one(inputs, &leaf)?;
        let (level_two, level_two_image_id, level_two_identity) =
            verify_level_two(inputs, &level_one)?;
        require_settlement_l2_claim(
            &inputs.settlement_guest_input,
            &level_two.receipt().journal.bytes,
        )?;
        let settlement = VerifiedSourceOpenedSpotSettlementAdmissionV6::verify(
            &inputs.settlement_receipt,
            &inputs.settlement_guest_input,
        )
        .map_err(|_| CliError("settlement_positive_receipt_rejected"))?;
        let v7 = verify_spot_settlement_v7_canonical_succinct_bytes(
            &inputs.v7_receipt,
            &inputs.v7_guest_input,
            &inputs.settlement_receipt,
        )
        .map_err(|_| CliError("v7_positive_receipt_rejected"))?;
        require_common_profile(
            leaf.receipt_profile().profile_id(),
            level_one.receipt_profile().profile_id(),
            level_two.receipt_profile().profile_id(),
            settlement.verified_receipt().receipt_profile().profile_id(),
            v7.receipt_profile().profile_id(),
        )?;
        Ok(Self {
            leaf,
            level_one,
            level_one_identity,
            level_two,
            level_two_image_id,
            level_two_identity,
            settlement,
            v7,
        })
    }
}

fn require_settlement_l2_claim(
    exact_settlement_guest_input: &[u8],
    verified_l2_journal: &[u8],
) -> Result<(), CliError> {
    let envelope =
        decode_exact_source_opened_spot_settlement_guest_envelope_v3(exact_settlement_guest_input)
            .map_err(|_| CliError("settlement_guest_envelope_rejected"))?;
    require_exact_settlement_l2_claim(envelope.proposal_bytes(), verified_l2_journal)
}

fn require_exact_settlement_l2_claim(
    settlement_proposal: &[u8],
    verified_l2_journal: &[u8],
) -> Result<(), CliError> {
    if settlement_proposal != verified_l2_journal {
        return Err(CliError("settlement_l2_claim_mismatch"));
    }
    Ok(())
}

fn verify_leaf(inputs: &Inputs) -> Result<VerifiedSourceOpenedSpotValueLeafReceiptV6, CliError> {
    let envelope = decode_exact_source_opened_spot_value_leaf_input_v6(&inputs.leaf_envelope)
        .map_err(|_| CliError("leaf_source_envelope_rejected"))?;
    let expected = recompose_source_opened_spot_value_leaf_statement_v6(&envelope)
        .map_err(|_| CliError("leaf_recomposition_rejected"))?;
    VerifiedSourceOpenedSpotValueLeafReceiptV6::verify_governed_exact_succinct_bytes(
        &inputs.leaf_receipt,
        &expected,
    )
    .map_err(|_| CliError("leaf_positive_receipt_rejected"))
}

fn verify_level_one(
    inputs: &Inputs,
    leaf: &VerifiedSourceOpenedSpotValueLeafReceiptV6,
) -> Result<
    (
        VerifiedValueAggregateReceiptV5,
        ExpectedValueAggregateReceiptIdentityV5,
    ),
    CliError,
> {
    let input = ValueAggregateLevelOneInputV5::new(vec![leaf.receipt().journal.bytes.clone()])
        .map_err(|_| CliError("level_one_input_rejected"))?;
    let child_identity = pinned_source_opened_spot_value_leaf_identity_v6()
        .map_err(|_| CliError("level_one_policy_rejected"))?;
    let policy = ValueAggregateRecompositionPolicyV5::new(
        leaf.statement()
            .structural_adapter_journal()
            .scope()
            .clone(),
        vec![child_identity],
    )
    .map_err(|_| CliError("level_one_policy_rejected"))?;
    let expected =
        recompose_expected_source_opened_spot_value_aggregate_level_one_v6(&input, &policy)
            .map_err(|_| CliError("level_one_recomposition_rejected"))?;
    let identity = expected_level_one_identity()?;
    let verified = VerifiedValueAggregateReceiptV5::verify_exact_succinct_bytes(
        &inputs.level_one_receipt,
        PINNED_SOURCE_OPENED_SPOT_VALUE_AGGREGATE_L1_IMAGE_ID_V6,
        identity,
        &expected,
    )
    .map_err(|_| CliError("level_one_positive_receipt_rejected"))?;
    Ok((verified, identity))
}

fn verify_level_two(
    inputs: &Inputs,
    level_one: &VerifiedValueAggregateReceiptV5,
) -> Result<
    (
        VerifiedValueAggregateReceiptV5,
        [u32; 8],
        ExpectedValueAggregateReceiptIdentityV5,
    ),
    CliError,
> {
    let input = ValueAggregateLevelTwoInputV5::new(vec![level_one.receipt().journal.bytes.clone()])
        .map_err(|_| CliError("level_two_input_rejected"))?;
    let child_identity = pinned_source_opened_spot_value_aggregate_l1_identity_v6()
        .map_err(|_| CliError("level_two_policy_rejected"))?;
    let policy = ValueAggregateRecompositionPolicyV5::new(
        level_one.proposal().scope().clone(),
        vec![child_identity],
    )
    .map_err(|_| CliError("level_two_policy_rejected"))?;
    let expected = recompose_expected_value_aggregate_level_two_v5(&input, &policy)
        .map_err(|_| CliError("level_two_recomposition_rejected"))?;
    let root = pinned_source_opened_spot_value_aggregate_l2_root_identity_v6()
        .map_err(|_| CliError("level_two_identity_rejected"))?;
    let identity = ExpectedValueAggregateReceiptIdentityV5::new(
        NodeLevelV3::new(2).map_err(|_| CliError("level_two_identity_rejected"))?,
        root.expected_profile_id(),
        root.expected_manifest_root(),
    )
    .map_err(|_| CliError("level_two_identity_rejected"))?;
    let image_id = root.expected_image_id();
    let verified = VerifiedValueAggregateReceiptV5::verify_exact_succinct_bytes(
        &inputs.level_two_receipt,
        image_id,
        identity,
        &expected,
    )
    .map_err(|_| CliError("level_two_positive_receipt_rejected"))?;
    Ok((verified, image_id, identity))
}

struct VerifiedMutations {
    leaf_bytes: Vec<u8>,
    leaf_facts: MutationFactsV1,
    level_one_bytes: Vec<u8>,
    level_one_facts: MutationFactsV1,
    level_two_bytes: Vec<u8>,
    level_two_facts: MutationFactsV1,
    settlement_facts: MutationFactsV1,
    v7_facts: MutationFactsV1,
}

impl VerifiedMutations {
    fn derive_and_reject(inputs: &Inputs, chain: &VerifiedChain) -> Result<Self, CliError> {
        let (leaf_bytes, leaf_facts) = exact_seal_word_one_xor_one(chain.leaf.receipt())?;
        let (level_one_bytes, level_one_facts) =
            exact_seal_word_one_xor_one(chain.level_one.receipt())?;
        let (level_two_bytes, level_two_facts) =
            exact_seal_word_one_xor_one(chain.level_two.receipt())?;
        let settlement_facts =
            require_exact_mutation_bytes(&inputs.settlement_receipt, &inputs.settlement_mutation)?;
        let v7_facts = require_exact_mutation_bytes(&inputs.v7_receipt, &inputs.v7_mutation)?;

        require_leaf_mutation_rejected(&leaf_bytes, chain.leaf.statement())?;
        require_aggregate_mutation_rejected(
            VerifiedValueAggregateReceiptV5::verify_exact_succinct_bytes(
                &level_one_bytes,
                PINNED_SOURCE_OPENED_SPOT_VALUE_AGGREGATE_L1_IMAGE_ID_V6,
                chain.level_one_identity,
                chain.level_one.proposal(),
            ),
            "level_one_mutation_rejected_at_unexpected_boundary",
        )?;
        require_aggregate_mutation_rejected(
            VerifiedValueAggregateReceiptV5::verify_exact_succinct_bytes(
                &level_two_bytes,
                chain.level_two_image_id,
                chain.level_two_identity,
                chain.level_two.proposal(),
            ),
            "level_two_mutation_rejected_at_unexpected_boundary",
        )?;
        require_settlement_mutation_rejected(
            &inputs.settlement_mutation,
            &inputs.settlement_guest_input,
        )?;
        require_v7_mutation_rejected(
            &inputs.v7_mutation,
            &inputs.v7_guest_input,
            &inputs.settlement_receipt,
        )?;
        Ok(Self {
            leaf_bytes,
            leaf_facts,
            level_one_bytes,
            level_one_facts,
            level_two_bytes,
            level_two_facts,
            settlement_facts,
            v7_facts,
        })
    }

    fn persist(&self, options: &Options) -> Result<(), CliError> {
        persist_new(
            &options.leaf_mutation_out,
            &self.leaf_bytes,
            "leaf_mutation_output",
        )?;
        persist_new(
            &options.level_one_mutation_out,
            &self.level_one_bytes,
            "level_one_mutation_output",
        )?;
        persist_new(
            &options.level_two_mutation_out,
            &self.level_two_bytes,
            "level_two_mutation_output",
        )
    }
}

struct Inputs {
    leaf_envelope: Vec<u8>,
    settlement_guest_input: Vec<u8>,
    v7_guest_input: Vec<u8>,
    leaf_program: Vec<u8>,
    level_one_program: Vec<u8>,
    level_two_program: Vec<u8>,
    settlement_program: Vec<u8>,
    v7_program: Vec<u8>,
    leaf_receipt: Vec<u8>,
    level_one_receipt: Vec<u8>,
    level_two_receipt: Vec<u8>,
    settlement_receipt: Vec<u8>,
    v7_receipt: Vec<u8>,
    settlement_mutation: Vec<u8>,
    v7_mutation: Vec<u8>,
}

impl Inputs {
    fn read(options: &Options) -> Result<Self, CliError> {
        Ok(Self {
            leaf_envelope: read_stable(&options.leaf_source_envelope, MAX_GUEST_INPUT_BYTES)?,
            settlement_guest_input: read_stable(
                &options.settlement_guest_input,
                MAX_GUEST_INPUT_BYTES,
            )?,
            v7_guest_input: read_stable(&options.v7_guest_input, MAX_GUEST_INPUT_BYTES)?,
            leaf_program: read_stable(&options.leaf_program, MAX_PROGRAM_BYTES)?,
            level_one_program: read_stable(&options.level_one_program, MAX_PROGRAM_BYTES)?,
            level_two_program: read_stable(&options.level_two_program, MAX_PROGRAM_BYTES)?,
            settlement_program: read_stable(&options.settlement_program, MAX_PROGRAM_BYTES)?,
            v7_program: read_stable(&options.v7_program, MAX_PROGRAM_BYTES)?,
            leaf_receipt: read_stable(&options.leaf_receipt, MAX_RECEIPT_BYTES)?,
            level_one_receipt: read_stable(&options.level_one_receipt, MAX_RECEIPT_BYTES)?,
            level_two_receipt: read_stable(&options.level_two_receipt, MAX_RECEIPT_BYTES)?,
            settlement_receipt: read_stable(&options.settlement_receipt, MAX_RECEIPT_BYTES)?,
            v7_receipt: read_stable(&options.v7_receipt, MAX_RECEIPT_BYTES)?,
            settlement_mutation: read_stable(&options.settlement_mutation, MAX_RECEIPT_BYTES)?,
            v7_mutation: read_stable(&options.v7_mutation, MAX_RECEIPT_BYTES)?,
        })
    }
}

struct Programs {
    leaf: ProgramFactsV1,
    level_one: ProgramFactsV1,
    level_two: ProgramFactsV1,
    settlement: ProgramFactsV1,
    v7: ProgramFactsV1,
}

fn report_stages(
    programs: Programs,
    inputs: &Inputs,
    chain: &VerifiedChain,
    mutations: &VerifiedMutations,
) -> [StageFactsV1; 5] {
    [
        stage_facts(
            "v6_leaf",
            programs.leaf,
            chain.leaf.receipt_profile().profile_id(),
            chain.leaf.receipt(),
            &inputs.leaf_receipt,
            &mutations.leaf_bytes,
            mutations.leaf_facts,
            "VerifiedSourceOpenedSpotValueLeafReceiptV6",
        ),
        stage_facts(
            "v6_l1",
            programs.level_one,
            chain.level_one.receipt_profile().profile_id(),
            chain.level_one.receipt(),
            &inputs.level_one_receipt,
            &mutations.level_one_bytes,
            mutations.level_one_facts,
            "VerifiedValueAggregateReceiptV5",
        ),
        stage_facts(
            "v6_l2",
            programs.level_two,
            chain.level_two.receipt_profile().profile_id(),
            chain.level_two.receipt(),
            &inputs.level_two_receipt,
            &mutations.level_two_bytes,
            mutations.level_two_facts,
            "VerifiedValueAggregateReceiptV5",
        ),
        stage_facts(
            "v6_settlement",
            programs.settlement,
            chain
                .settlement
                .verified_receipt()
                .receipt_profile()
                .profile_id(),
            chain.settlement.verified_receipt().receipt(),
            &inputs.settlement_receipt,
            &inputs.settlement_mutation,
            mutations.settlement_facts,
            "VerifiedSourceOpenedSpotSettlementAdmissionV6",
        ),
        stage_facts(
            "v7_settlement",
            programs.v7,
            chain.v7.receipt_profile().profile_id(),
            chain.v7.receipt(),
            &inputs.v7_receipt,
            &inputs.v7_mutation,
            mutations.v7_facts,
            "VerifiedSpotSettlementV7ReceiptV1",
        ),
    ]
}

fn verify_programs(inputs: &Inputs) -> Result<Programs, CliError> {
    let settlement_identity = pinned_source_opened_spot_settlement_identity_v6()
        .map_err(|_| CliError("settlement_program_identity_rejected"))?;
    let l2_identity = pinned_source_opened_spot_value_aggregate_l2_root_identity_v6()
        .map_err(|_| CliError("level_two_program_identity_rejected"))?;
    Ok(Programs {
        leaf: verify_program(
            &inputs.leaf_program,
            ZENODEX_ZRPF_RISC0_SPOT_VALUE_LEAF_V6_ID,
        )?,
        level_one: verify_program(
            &inputs.level_one_program,
            ZENODEX_ZRPF_RISC0_SPOT_VALUE_AGGREGATE_L1_V6_ID,
        )?,
        level_two: verify_program(&inputs.level_two_program, l2_identity.expected_image_id())?,
        settlement: verify_program(
            &inputs.settlement_program,
            settlement_identity.expected_image_id(),
        )?,
        v7: verify_program(&inputs.v7_program, ZENODEX_ZRPF_RISC0_SPOT_SETTLEMENT_V7_ID)?,
    })
}

fn verify_program(bytes: &[u8], expected_image: [u32; 8]) -> Result<ProgramFactsV1, CliError> {
    if expected_image.iter().all(|word| *word == 0) {
        return Err(CliError("expected_program_image_unmaterialized"));
    }
    let computed = compute_image_id(bytes).map_err(|_| CliError("program_image_compute_failed"))?;
    if computed != Digest::from(expected_image) {
        return Err(CliError("program_image_mismatch"));
    }
    Ok(ProgramFactsV1 {
        program_bytes: bytes.len(),
        program_sha256: sha256_hex(bytes),
        expected_image_id: computed.to_string(),
    })
}

fn expected_level_one_identity() -> Result<ExpectedValueAggregateReceiptIdentityV5, CliError> {
    let program_id =
        program_id_from_risc0_words_v3(PINNED_SOURCE_OPENED_SPOT_VALUE_AGGREGATE_L1_IMAGE_ID_V6)
            .map_err(|_| CliError("level_one_identity_rejected"))?;
    ExpectedValueAggregateReceiptIdentityV5::new(
        NodeLevelV3::new(1).map_err(|_| CliError("level_one_identity_rejected"))?,
        source_opened_spot_value_aggregate_l1_profile_id_v6()
            .map_err(|_| CliError("level_one_identity_rejected"))?,
        source_opened_spot_value_aggregate_l1_manifest_root_v6(program_id)
            .map_err(|_| CliError("level_one_identity_rejected"))?,
    )
    .map_err(|_| CliError("level_one_identity_rejected"))
}

fn exact_seal_word_one_xor_one(receipt: &Receipt) -> Result<(Vec<u8>, MutationFactsV1), CliError> {
    let source_bytes = canonical_receipt_bytes(receipt)?;
    let mut candidate = receipt.clone();
    let InnerReceipt::Succinct(inner) = &mut candidate.inner else {
        return Err(CliError("positive_receipt_is_not_succinct"));
    };
    let original_word = *inner
        .seal
        .get(MUTATION_WORD_INDEX)
        .ok_or(CliError("succinct_seal_word_one_missing"))?;
    inner.seal[MUTATION_WORD_INDEX] = original_word ^ XOR_MASK;
    let candidate_bytes = canonical_receipt_bytes(&candidate)?;
    let facts = require_exact_mutation_bytes(&source_bytes, &candidate_bytes)?;
    Ok((candidate_bytes, facts))
}

fn require_exact_mutation_bytes(
    source_bytes: &[u8],
    candidate_bytes: &[u8],
) -> Result<MutationFactsV1, CliError> {
    let source = decode_canonical_receipt(source_bytes)?;
    let candidate = decode_canonical_receipt(candidate_bytes)?;
    let (InnerReceipt::Succinct(source_inner), InnerReceipt::Succinct(candidate_inner)) =
        (&source.inner, &candidate.inner)
    else {
        return Err(CliError("mutation_receipt_is_not_succinct"));
    };
    let facts = require_exact_word_relation(&source_inner.seal, &candidate_inner.seal)?;
    let mut restored = candidate;
    let InnerReceipt::Succinct(restored_inner) = &mut restored.inner else {
        return Err(CliError("mutation_receipt_is_not_succinct"));
    };
    restored_inner.seal[MUTATION_WORD_INDEX] = facts.original_word;
    let restored_bytes = canonical_receipt_bytes(&restored)?;
    if restored_bytes != source_bytes {
        return Err(CliError("mutation_changes_non_seal_receipt_bytes"));
    }
    Ok(facts)
}

fn require_exact_word_relation(
    source: &[u32],
    candidate: &[u32],
) -> Result<MutationFactsV1, CliError> {
    if source.len() <= MUTATION_WORD_INDEX || source.len() != candidate.len() {
        return Err(CliError("mutation_seal_shape_mismatch"));
    }
    let differences = source
        .iter()
        .copied()
        .zip(candidate.iter().copied())
        .enumerate()
        .filter(|(_, (original, mutated))| original != mutated)
        .collect::<Vec<_>>();
    let [(word_index, (original_word, mutated_word))] = differences.as_slice() else {
        return Err(CliError("mutation_must_change_exactly_one_seal_word"));
    };
    if *word_index != MUTATION_WORD_INDEX || *mutated_word != original_word ^ XOR_MASK {
        return Err(CliError("mutation_must_xor_seal_word_one_bit_zero"));
    }
    Ok(MutationFactsV1 {
        word_count: source.len(),
        word_index: MUTATION_WORD_INDEX,
        original_word: *original_word,
        mutated_word: *mutated_word,
        xor_mask: XOR_MASK,
    })
}

fn require_leaf_mutation_rejected(
    bytes: &[u8],
    expected: &zenodex_zrpf_risc0_spot_value_leaf_v6_shared::SourceOpenedSpotValueLeafStatementV6,
) -> Result<(), CliError> {
    match VerifiedSourceOpenedSpotValueLeafReceiptV6::verify_governed_exact_succinct_bytes(
        bytes, expected,
    ) {
        Err(VerifiedSourceOpenedSpotValueLeafReceiptErrorV6::ReceiptArtifact(
            VerifiedNodeReceiptErrorV3::ReceiptVerificationFailed,
        )) => Ok(()),
        Err(_) => Err(CliError("leaf_mutation_rejected_at_unexpected_boundary")),
        Ok(_) => Err(CliError("leaf_mutation_accepted")),
    }
}

fn require_aggregate_mutation_rejected(
    result: Result<VerifiedValueAggregateReceiptV5, VerifiedValueAggregateReceiptErrorV5>,
    unexpected_code: &'static str,
) -> Result<(), CliError> {
    match result {
        Err(VerifiedValueAggregateReceiptErrorV5::ReceiptArtifact(
            VerifiedNodeReceiptErrorV3::ReceiptVerificationFailed,
        )) => Ok(()),
        Err(_) => Err(CliError(unexpected_code)),
        Ok(_) => Err(CliError("aggregate_mutation_accepted")),
    }
}

fn require_settlement_mutation_rejected(bytes: &[u8], guest_input: &[u8]) -> Result<(), CliError> {
    match VerifiedSourceOpenedSpotSettlementAdmissionV6::verify(bytes, guest_input) {
        Err(VerifiedSourceOpenedSpotSettlementReceiptErrorV6::ReceiptArtifact(
            VerifiedNodeReceiptErrorV3::ReceiptVerificationFailed,
        )) => Ok(()),
        Err(_) => Err(CliError(
            "settlement_mutation_rejected_at_unexpected_boundary",
        )),
        Ok(_) => Err(CliError("settlement_mutation_accepted")),
    }
}

fn require_v7_mutation_rejected(
    bytes: &[u8],
    guest_input: &[u8],
    child: &[u8],
) -> Result<(), CliError> {
    match verify_spot_settlement_v7_canonical_succinct_bytes(bytes, guest_input, child) {
        Err(VerifiedSpotSettlementV7ErrorV1::ReceiptVerificationFailed) => Ok(()),
        Err(_) => Err(CliError("v7_mutation_rejected_at_unexpected_boundary")),
        Ok(_) => Err(CliError("v7_mutation_accepted")),
    }
}

fn require_common_profile(
    leaf: &str,
    level_one: &str,
    level_two: &str,
    settlement: &str,
    v7: &str,
) -> Result<(), CliError> {
    if [leaf, level_one, level_two, settlement, v7]
        .iter()
        .any(|profile| *profile != ZRPF_RISC0_SUCCINCT_RECEIPT_PROFILE_ID_V1)
    {
        return Err(CliError("receipt_profile_mismatch"));
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn stage_facts(
    stage_id: &'static str,
    program: ProgramFactsV1,
    profile: &str,
    receipt: &Receipt,
    receipt_bytes: &[u8],
    mutation_bytes: &[u8],
    mutation: MutationFactsV1,
    reject_boundary: &'static str,
) -> StageFactsV1 {
    StageFactsV1 {
        stage_id,
        program,
        receipt_profile_id: profile.to_owned(),
        positive_receipt_bytes: receipt_bytes.len(),
        positive_receipt_sha256: sha256_hex(receipt_bytes),
        positive_journal_sha256: sha256_hex(&receipt.journal.bytes),
        mutation_receipt_bytes: mutation_bytes.len(),
        mutation_receipt_sha256: sha256_hex(mutation_bytes),
        mutation,
        reject_boundary,
        reject_code: RECEIPT_VERIFICATION_REJECT_CODE,
    }
}

fn finalized_report(stages: [StageFactsV1; 5]) -> Result<ReportV1, CliError> {
    for ((stage, expected_id), expected_boundary) in stages
        .iter()
        .zip(EXPECTED_STAGE_IDS)
        .zip(EXPECTED_REJECT_BOUNDARIES)
    {
        if stage.stage_id != expected_id {
            return Err(CliError("report_stage_order_rejected"));
        }
        validate_stage_facts(stage, expected_boundary)?;
    }
    let mut report = ReportV1 {
        schema: REPORT_SCHEMA,
        status: REPORT_STATUS,
        report_id: ZERO_SHA256.to_owned(),
        receipt_profile_id: ZRPF_RISC0_SUCCINCT_RECEIPT_PROFILE_ID_V1.to_owned(),
        positive_receipts_verified: 5,
        exact_seal_mutations_rejected: 5,
        settlement_l2_claim_bound: true,
        stages,
        authority: AuthorityV1 {
            proof_authority: false,
            release_authority: false,
            settlement_authority: false,
            production_authority: false,
        },
        non_claims: [
            "report_is_an_unkeyed_authority_neutral_process_observation",
            "report_does_not_establish_source_to_binary_or_release_provenance",
            "report_does_not_establish_data_availability_finality_or_ledger_admission",
            "report_does_not_grant_proof_release_settlement_or_production_authority",
        ],
    };
    report.report_id = derive_report_id(&report)?;
    Ok(report)
}

fn validate_stage_facts(stage: &StageFactsV1, expected_boundary: &str) -> Result<(), CliError> {
    if stage.receipt_profile_id != ZRPF_RISC0_SUCCINCT_RECEIPT_PROFILE_ID_V1 {
        return Err(CliError("report_stage_profile_rejected"));
    }
    if stage.program.program_bytes == 0
        || !is_lower_hex_sha256(&stage.program.program_sha256)
        || !is_lower_hex_sha256(&stage.program.expected_image_id)
    {
        return Err(CliError("report_stage_program_rejected"));
    }
    if stage.positive_receipt_bytes == 0
        || stage.mutation_receipt_bytes == 0
        || !is_lower_hex_sha256(&stage.positive_receipt_sha256)
        || !is_lower_hex_sha256(&stage.positive_journal_sha256)
        || !is_lower_hex_sha256(&stage.mutation_receipt_sha256)
    {
        return Err(CliError("report_stage_receipt_rejected"));
    }
    if stage.mutation.word_count <= MUTATION_WORD_INDEX
        || stage.mutation.word_index != MUTATION_WORD_INDEX
        || stage.mutation.xor_mask != XOR_MASK
        || stage.mutation.mutated_word != stage.mutation.original_word ^ XOR_MASK
    {
        return Err(CliError("report_stage_mutation_rejected"));
    }
    if stage.reject_boundary != expected_boundary
        || stage.reject_code != RECEIPT_VERIFICATION_REJECT_CODE
    {
        return Err(CliError("report_stage_reject_boundary_rejected"));
    }
    Ok(())
}

fn is_lower_hex_sha256(value: &str) -> bool {
    value.len() == 64
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

fn derive_report_id(report: &ReportV1) -> Result<String, CliError> {
    let mut committed = report.clone();
    committed.report_id = ZERO_SHA256.to_owned();
    let canonical = serde_json::to_vec(&committed).map_err(|_| CliError("report_encode_failed"))?;
    let mut hasher = Sha256::new();
    hasher.update(REPORT_DOMAIN);
    hasher.update(canonical);
    Ok(hex_bytes(&hasher.finalize()))
}

fn write_report(report: &ReportV1) -> Result<(), CliError> {
    let bytes = serde_json::to_vec(report).map_err(|_| CliError("report_encode_failed"))?;
    let mut output = std::io::stdout().lock();
    output
        .write_all(&bytes)
        .and_then(|()| output.write_all(b"\n"))
        .map_err(|_| CliError("report_write_failed"))
}

fn canonical_receipt_bytes(receipt: &Receipt) -> Result<Vec<u8>, CliError> {
    serde_json::to_vec(receipt).map_err(|_| CliError("receipt_encode_failed"))
}

fn decode_canonical_receipt(bytes: &[u8]) -> Result<Receipt, CliError> {
    let receipt: Receipt =
        serde_json::from_slice(bytes).map_err(|_| CliError("receipt_decode_failed"))?;
    if canonical_receipt_bytes(&receipt)? != bytes {
        return Err(CliError("receipt_is_not_canonical"));
    }
    Ok(receipt)
}

fn read_stable(path: &Path, maximum: usize) -> Result<Vec<u8>, CliError> {
    let maximum_u64 = u64::try_from(maximum).map_err(|_| CliError("input_maximum_out_of_range"))?;
    let read_limit = maximum_u64
        .checked_add(1)
        .ok_or(CliError("input_maximum_out_of_range"))?;
    let mut file = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC)
        .open(path)
        .map_err(|_| CliError("input_open_failed"))?;
    let opened = file
        .metadata()
        .map_err(|_| CliError("input_metadata_failed"))?;
    if !opened.file_type().is_file()
        || opened.nlink() != 1
        || opened.len() == 0
        || opened.len() > maximum_u64
    {
        return Err(CliError("input_file_rejected"));
    }
    let path_facts = path
        .symlink_metadata()
        .map_err(|_| CliError("input_metadata_failed"))?;
    if metadata_identity(&path_facts) != metadata_identity(&opened) {
        return Err(CliError("input_path_changed_before_read"));
    }
    let mut bytes = Vec::new();
    Read::by_ref(&mut file)
        .take(read_limit)
        .read_to_end(&mut bytes)
        .map_err(|_| CliError("input_read_failed"))?;
    let after = file
        .metadata()
        .map_err(|_| CliError("input_metadata_failed"))?;
    let after_path = path
        .symlink_metadata()
        .map_err(|_| CliError("input_metadata_failed"))?;
    let bytes_len = u64::try_from(bytes.len()).map_err(|_| CliError("input_size_out_of_range"))?;
    if metadata_identity(&opened) != metadata_identity(&after)
        || metadata_identity(&after) != metadata_identity(&after_path)
        || bytes_len != opened.len()
    {
        return Err(CliError("input_changed_during_read"));
    }
    Ok(bytes)
}

fn metadata_identity(metadata: &std::fs::Metadata) -> (u64, u64, u32, u64, i64, i64, i64, i64) {
    (
        metadata.dev(),
        metadata.ino(),
        metadata.mode(),
        metadata.len(),
        metadata.mtime(),
        metadata.mtime_nsec(),
        metadata.ctime(),
        metadata.ctime_nsec(),
    )
}

fn persist_new(path: &Path, bytes: &[u8], code: &'static str) -> Result<(), CliError> {
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)
        .map_err(|_| CliError(code))?;
    file.write_all(bytes)
        .and_then(|()| file.sync_all())
        .map_err(|_| CliError(code))?;
    drop(file);
    if read_stable(path, MAX_RECEIPT_BYTES)? != bytes {
        return Err(CliError(code));
    }
    Ok(())
}

fn parse_options(args: impl IntoIterator<Item = String>) -> Result<Options, CliError> {
    let values = args.into_iter().collect::<Vec<_>>();
    const FLAGS: [&str; 18] = [
        "--leaf-source-envelope",
        "--settlement-guest-input",
        "--v7-guest-input",
        "--leaf-program",
        "--level-one-program",
        "--level-two-program",
        "--settlement-program",
        "--v7-program",
        "--leaf-receipt",
        "--level-one-receipt",
        "--level-two-receipt",
        "--settlement-receipt",
        "--v7-receipt",
        "--settlement-mutation",
        "--v7-mutation",
        "--leaf-mutation-out",
        "--level-one-mutation-out",
        "--level-two-mutation-out",
    ];
    if values.len() != FLAGS.len() * 2
        || FLAGS
            .iter()
            .enumerate()
            .any(|(index, flag)| values[index * 2] != *flag || values[index * 2 + 1].is_empty())
    {
        return Err(CliError("arguments_rejected"));
    }
    let path = |index: usize| PathBuf::from(&values[index * 2 + 1]);
    Ok(Options {
        leaf_source_envelope: path(0),
        settlement_guest_input: path(1),
        v7_guest_input: path(2),
        leaf_program: path(3),
        level_one_program: path(4),
        level_two_program: path(5),
        settlement_program: path(6),
        v7_program: path(7),
        leaf_receipt: path(8),
        level_one_receipt: path(9),
        level_two_receipt: path(10),
        settlement_receipt: path(11),
        v7_receipt: path(12),
        settlement_mutation: path(13),
        v7_mutation: path(14),
        leaf_mutation_out: path(15),
        level_one_mutation_out: path(16),
        level_two_mutation_out: path(17),
    })
}

fn sha256_hex(bytes: &[u8]) -> String {
    hex_bytes(&Sha256::digest(bytes))
}

fn hex_bytes(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut output = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        output.push(char::from(HEX[usize::from(byte >> 4)]));
        output.push(char::from(HEX[usize::from(byte & 0x0f)]));
    }
    output
}

#[cfg(test)]
mod tests {
    use super::*;

    const ORIGINAL_WORDS: [u32; 5] = [
        0x1357_9bdf,
        0x2468_ace0,
        0x1020_3040,
        0x55aa_c33c,
        0x89ab_cdef,
    ];
    const WRONG_STAGE_IDS: [&str; 5] = [
        "wrong_leaf",
        "wrong_l1",
        "wrong_l2",
        "wrong_settlement",
        "wrong_v7",
    ];
    const WRONG_BOUNDARIES: [&str; 5] = [
        "WrongLeafBoundary",
        "WrongL1Boundary",
        "WrongL2Boundary",
        "WrongSettlementBoundary",
        "WrongV7Boundary",
    ];
    const WRONG_REJECT_CODES: [&str; 5] = [
        "wrong_leaf_code",
        "wrong_l1_code",
        "wrong_l2_code",
        "wrong_settlement_code",
        "wrong_v7_code",
    ];
    const POSITION_MARKERS: [u8; 5] = [1, 2, 3, 4, 5];
    const POSITION_ROTATIONS: [u32; 5] = [0, 1, 2, 3, 4];
    const WRONG_XOR_MASKS: [u32; 5] = [3, 5, 7, 9, 11];
    const STAGE_SCALAR_NAMES: [&str; 17] = [
        "stage_id",
        "program_bytes",
        "program_sha256",
        "expected_image_id",
        "receipt_profile_id",
        "positive_receipt_bytes",
        "positive_receipt_sha256",
        "positive_journal_sha256",
        "mutation_receipt_bytes",
        "mutation_receipt_sha256",
        "word_count",
        "word_index",
        "original_word",
        "mutated_word",
        "xor_mask",
        "reject_boundary",
        "reject_code",
    ];

    fn fixture_digest(domain: u8, marker: u8) -> String {
        let value =
            (u128::from(domain) << 88) | (u128::from(marker) << 48) | 0x1357_9bdf_2468_ace0_u128;
        format!("{value:064x}")
    }

    fn stage(stage_id: &'static str, marker: u8) -> StageFactsV1 {
        let position = usize::from(marker - 1);
        let original_word = ORIGINAL_WORDS[position];
        StageFactsV1 {
            stage_id,
            program: ProgramFactsV1 {
                program_bytes: 586 + usize::from(marker) * 17,
                program_sha256: fixture_digest(0x11, marker),
                expected_image_id: fixture_digest(0x22, marker),
            },
            receipt_profile_id: ZRPF_RISC0_SUCCINCT_RECEIPT_PROFILE_ID_V1.to_owned(),
            positive_receipt_bytes: 701 + usize::from(marker) * 19,
            positive_receipt_sha256: fixture_digest(0x33, marker),
            positive_journal_sha256: fixture_digest(0x44, marker),
            mutation_receipt_bytes: 809 + usize::from(marker) * 23,
            mutation_receipt_sha256: fixture_digest(0x55, marker),
            mutation: MutationFactsV1 {
                word_count: 11 + usize::from(marker) * 2,
                word_index: 1,
                original_word,
                mutated_word: original_word ^ XOR_MASK,
                xor_mask: 1,
            },
            reject_boundary: EXPECTED_REJECT_BOUNDARIES[position],
            reject_code: RECEIPT_VERIFICATION_REJECT_CODE,
        }
    }

    fn stages() -> [StageFactsV1; 5] {
        [
            stage("v6_leaf", 1),
            stage("v6_l1", 2),
            stage("v6_l2", 3),
            stage("v6_settlement", 4),
            stage("v7_settlement", 5),
        ]
    }

    #[test]
    fn position_distinct_non_palindromic_words_distinguish_the_only_allowed_mutation() {
        let source = [0x1357_9bdf, 0x2468_ace0, 0x1020_3040, 0x55aa_c33c];
        let mut candidate = source;
        candidate[MUTATION_WORD_INDEX] ^= XOR_MASK;
        let facts = require_exact_word_relation(&source, &candidate).unwrap();
        assert_eq!(facts.word_index, MUTATION_WORD_INDEX);
        assert_eq!(facts.original_word, 0x2468_ace0);
        assert_eq!(facts.mutated_word, 0x2468_ace1);
    }

    #[test]
    fn every_other_position_or_bit_is_distinguished() {
        let source = [0x1357_9bdf, 0x2468_ace0, 0x1020_3040, 0x55aa_c33c];
        for index in 0..source.len() {
            for bit in 0..32 {
                let mut candidate = source;
                candidate[index] ^= 1_u32 << bit;
                let accepted = require_exact_word_relation(&source, &candidate).is_ok();
                assert_eq!(accepted, index == MUTATION_WORD_INDEX && bit == 0);
            }
        }
    }

    #[test]
    fn settlement_l2_link_distinguishes_position_specific_proposals() {
        let verified_l2 = [0x13, 0x57, 0x9b, 0xdf, 0x24, 0x68, 0xac, 0xe0, 0x5a];
        let foreign_l2 = [0x13, 0x57, 0x9b, 0xdf, 0x24, 0x68, 0xad, 0xe0, 0xa5];
        assert_eq!(
            require_exact_settlement_l2_claim(&verified_l2, &verified_l2),
            Ok(())
        );
        assert_eq!(
            require_exact_settlement_l2_claim(&foreign_l2, &verified_l2),
            Err(CliError("settlement_l2_claim_mismatch"))
        );
        assert_eq!(
            require_exact_settlement_l2_claim(&verified_l2, &foreign_l2),
            Err(CliError("settlement_l2_claim_mismatch"))
        );
        assert_eq!(
            require_settlement_l2_claim(&verified_l2, &verified_l2),
            Err(CliError("settlement_guest_envelope_rejected"))
        );
    }

    fn mutate_stage_scalar(
        changed: &mut [StageFactsV1; 5],
        position: usize,
        scalar: usize,
    ) -> Option<CliError> {
        let stage = &mut changed[position];
        match scalar {
            0 => {
                stage.stage_id = WRONG_STAGE_IDS[position];
                assert_eq!(stage.stage_id, WRONG_STAGE_IDS[position]);
                Some(CliError("report_stage_order_rejected"))
            }
            1 => {
                stage.program.program_bytes += 1_009 + position * 17;
                assert_eq!(
                    stage.program.program_bytes,
                    586 + (position + 1) * 17 + 1_009 + position * 17
                );
                None
            }
            2 => {
                stage.program.program_sha256 = fixture_digest(0x66, POSITION_MARKERS[position]);
                assert_eq!(
                    stage.program.program_sha256,
                    fixture_digest(0x66, POSITION_MARKERS[position])
                );
                None
            }
            3 => {
                stage.program.expected_image_id = fixture_digest(0x77, POSITION_MARKERS[position]);
                assert_eq!(
                    stage.program.expected_image_id,
                    fixture_digest(0x77, POSITION_MARKERS[position])
                );
                None
            }
            4 => {
                stage.receipt_profile_id = format!("wrong-profile-{}", position + 1);
                assert_eq!(
                    stage.receipt_profile_id,
                    format!("wrong-profile-{}", position + 1)
                );
                Some(CliError("report_stage_profile_rejected"))
            }
            5 => {
                stage.positive_receipt_bytes += 2_003 + position * 19;
                assert_eq!(
                    stage.positive_receipt_bytes,
                    701 + (position + 1) * 19 + 2_003 + position * 19
                );
                None
            }
            6 => {
                stage.positive_receipt_sha256 = fixture_digest(0x88, POSITION_MARKERS[position]);
                assert_eq!(
                    stage.positive_receipt_sha256,
                    fixture_digest(0x88, POSITION_MARKERS[position])
                );
                None
            }
            7 => {
                stage.positive_journal_sha256 = fixture_digest(0x99, POSITION_MARKERS[position]);
                assert_eq!(
                    stage.positive_journal_sha256,
                    fixture_digest(0x99, POSITION_MARKERS[position])
                );
                None
            }
            8 => {
                stage.mutation_receipt_bytes += 3_001 + position * 23;
                assert_eq!(
                    stage.mutation_receipt_bytes,
                    809 + (position + 1) * 23 + 3_001 + position * 23
                );
                None
            }
            9 => {
                stage.mutation_receipt_sha256 = fixture_digest(0xaa, POSITION_MARKERS[position]);
                assert_eq!(
                    stage.mutation_receipt_sha256,
                    fixture_digest(0xaa, POSITION_MARKERS[position])
                );
                None
            }
            10 => {
                stage.mutation.word_count += 101 + position * 2;
                assert_eq!(
                    stage.mutation.word_count,
                    11 + (position + 1) * 2 + 101 + position * 2
                );
                None
            }
            11 => {
                stage.mutation.word_index = position + 2;
                assert_eq!(stage.mutation.word_index, position + 2);
                Some(CliError("report_stage_mutation_rejected"))
            }
            12 => {
                stage.mutation.original_word ^=
                    0x0102_0408_u32.rotate_left(POSITION_ROTATIONS[position]);
                assert_ne!(stage.mutation.original_word, ORIGINAL_WORDS[position]);
                Some(CliError("report_stage_mutation_rejected"))
            }
            13 => {
                stage.mutation.mutated_word ^=
                    0x1020_4080_u32.rotate_left(POSITION_ROTATIONS[position]);
                assert_ne!(
                    stage.mutation.mutated_word,
                    ORIGINAL_WORDS[position] ^ XOR_MASK
                );
                Some(CliError("report_stage_mutation_rejected"))
            }
            14 => {
                stage.mutation.xor_mask = WRONG_XOR_MASKS[position];
                assert_eq!(stage.mutation.xor_mask, WRONG_XOR_MASKS[position]);
                Some(CliError("report_stage_mutation_rejected"))
            }
            15 => {
                stage.reject_boundary = WRONG_BOUNDARIES[position];
                assert_eq!(stage.reject_boundary, WRONG_BOUNDARIES[position]);
                Some(CliError("report_stage_reject_boundary_rejected"))
            }
            16 => {
                stage.reject_code = WRONG_REJECT_CODES[position];
                assert_eq!(stage.reject_code, WRONG_REJECT_CODES[position]);
                Some(CliError("report_stage_reject_boundary_rejected"))
            }
            _ => unreachable!(),
        }
    }

    #[test]
    fn report_id_or_finalizer_distinguishes_every_stage_scalar_at_every_position() {
        let baseline = finalized_report(stages()).unwrap().report_id;
        for position in 0..EXPECTED_STAGE_IDS.len() {
            for (scalar, scalar_name) in STAGE_SCALAR_NAMES.iter().enumerate() {
                let mut changed = stages();
                let expected_reject = mutate_stage_scalar(&mut changed, position, scalar);
                let result = finalized_report(changed);
                if let Some(expected) = expected_reject {
                    assert_eq!(
                        result.unwrap_err(),
                        expected,
                        "position={position} scalar={scalar_name}"
                    );
                } else {
                    assert_ne!(
                        result.unwrap().report_id,
                        baseline,
                        "position={position} scalar={scalar_name}"
                    );
                }
            }
        }
    }

    #[test]
    fn report_id_commits_fixed_construction_invariants_and_excludes_only_itself() {
        let baseline = finalized_report(stages()).unwrap();
        assert_eq!(baseline.schema, REPORT_SCHEMA);
        assert_eq!(baseline.status, REPORT_STATUS);
        assert_eq!(baseline.positive_receipts_verified, 5);
        assert_eq!(baseline.exact_seal_mutations_rejected, 5);
        assert!(baseline.settlement_l2_claim_bound);
        assert_eq!(
            baseline.receipt_profile_id,
            ZRPF_RISC0_SUCCINCT_RECEIPT_PROFILE_ID_V1
        );
        assert!(!baseline.authority.proof_authority);
        assert!(!baseline.authority.release_authority);
        assert!(!baseline.authority.settlement_authority);
        assert!(!baseline.authority.production_authority);

        for invariant in 0..14 {
            let mut changed = baseline.clone();
            match invariant {
                0 => changed.schema = "wrong-schema",
                1 => changed.status = "wrong-status",
                2 => changed.receipt_profile_id = "wrong-profile".to_owned(),
                3 => changed.positive_receipts_verified = 7,
                4 => changed.exact_seal_mutations_rejected = 9,
                5 => changed.authority.proof_authority = true,
                6 => changed.authority.release_authority = true,
                7 => changed.authority.settlement_authority = true,
                8 => changed.authority.production_authority = true,
                9 => changed.non_claims[0] = "wrong-nonclaim-0",
                10 => changed.non_claims[1] = "wrong-nonclaim-1",
                11 => changed.non_claims[2] = "wrong-nonclaim-2",
                12 => changed.non_claims[3] = "wrong-nonclaim-3",
                13 => changed.settlement_l2_claim_bound = false,
                _ => unreachable!(),
            }
            assert_ne!(derive_report_id(&changed).unwrap(), baseline.report_id);
        }

        let mut self_changed = baseline.clone();
        self_changed.report_id = "f".repeat(64);
        assert_eq!(derive_report_id(&self_changed).unwrap(), baseline.report_id);
    }

    #[test]
    fn report_constructor_rejects_stage_reordering() {
        let mut changed = stages();
        changed.swap(0, 1);
        assert_eq!(
            finalized_report(changed).unwrap_err(),
            CliError("report_stage_order_rejected")
        );
    }
}
