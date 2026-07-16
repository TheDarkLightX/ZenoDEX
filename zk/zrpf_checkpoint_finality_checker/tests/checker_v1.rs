use sha2::{Digest, Sha256};
use std::io::Write;
use std::process::{Command, Output, Stdio};
use zenodex_zrpf_checkpoint_finality_checker_v1::{
    check_request_bytes_v1, decode_checker_response_v1, encode_checker_request_v1,
    CheckpointFinalityCheckerErrorV1, CheckpointFinalityCheckerRequestInputV1,
    CERTIFICATE_LENGTH_OFFSET_V1, EXPECTED_CHECKPOINT_HASH_OFFSET_V1,
    EXPECTED_CHECKPOINT_SEQUENCE_OFFSET_V1, EXPECTED_EPOCH_OFFSET_V1,
    EXPECTED_FINALITY_EVIDENCE_ROOT_OFFSET_V1, EXPECTED_PARENT_CHECKPOINT_HASH_OFFSET_V1,
    EXPECTED_POST_STATE_ROOT_OFFSET_V1, EXPECTED_PROOF_JOURNAL_HASH_OFFSET_V1,
    POLICY_APPLICATION_ID_OFFSET_V1, POLICY_GENESIS_CHECKPOINT_HASH_OFFSET_V1,
    PRIOR_CURSOR_TAG_OFFSET_V1, PRIOR_RECORD_APPLICATION_ID_OFFSET_V1, PRIOR_RECORD_HASH_OFFSET_V1,
    PRIOR_RECORD_SEQUENCE_OFFSET_V1, REQUEST_HEADER_BYTES_V1, REQUEST_VERSION_OFFSET_V1,
    RESPONSE_BYTES_V1,
};
use zenodex_zrpf_protocol_v3::{
    encode_checkpoint_finality_certificate_v2, ApplicationIdV3, CheckpointCursorProposalV2,
    CheckpointFinalityCertificateInputV2, CheckpointFinalityCertificateV2,
    CheckpointFinalityPolicyInputV2, CheckpointFinalityPolicyV2, CommitmentV3, DomainIdV3,
    ProposedPriorApplicationCheckpointRecordInputV2, ProposedPriorApplicationCheckpointRecordV2,
    SuppliedCheckpointFinalityBindingV2, MAX_CHECKPOINT_FINALITY_CERTIFICATE_BYTES_V2,
};

fn application_id(seed: u8) -> ApplicationIdV3 {
    ApplicationIdV3::new([seed; 32]).unwrap_or_else(|error| panic!("fixture rejected: {error}"))
}

fn domain_id(seed: u8) -> DomainIdV3 {
    DomainIdV3::new([seed; 32]).unwrap_or_else(|error| panic!("fixture rejected: {error}"))
}

fn commitment(seed: u8) -> CommitmentV3 {
    CommitmentV3::new([seed; 32]).unwrap_or_else(|error| panic!("fixture rejected: {error}"))
}

fn position_bytes(tag: u8) -> [u8; 32] {
    std::array::from_fn(|index| {
        let position =
            u8::try_from(index).unwrap_or_else(|error| panic!("fixture index rejected: {error}"));
        tag.wrapping_add(17_u8.wrapping_mul(position))
            .wrapping_add(position.wrapping_mul(position))
    })
}

fn policy(genesis_sequence: u64, genesis_hash: CommitmentV3) -> CheckpointFinalityPolicyV2 {
    CheckpointFinalityPolicyV2::new(CheckpointFinalityPolicyInputV2 {
        application_id: application_id(1),
        chain_or_domain_id: domain_id(2),
        finality_network_id: commitment(6),
        finality_protocol_id: commitment(7),
        expected_external_finality_policy_hash: commitment(8),
        expected_finality_verifier_set_root: commitment(9),
        genesis_application_checkpoint_sequence: genesis_sequence,
        genesis_application_checkpoint_hash: genesis_hash,
    })
}

fn certificate(
    policy: &CheckpointFinalityPolicyV2,
    sequence: u64,
    candidate_hash: CommitmentV3,
    parent_hash: CommitmentV3,
) -> CheckpointFinalityCertificateV2 {
    CheckpointFinalityCertificateV2::derive(CheckpointFinalityCertificateInputV2 {
        application_id: application_id(1),
        chain_or_domain_id: domain_id(2),
        epoch_id: 11,
        proof_journal_hash: commitment(3),
        post_state_root: commitment(4),
        application_checkpoint_sequence: sequence,
        application_checkpoint_hash: candidate_hash,
        parent_application_checkpoint_hash: parent_hash,
        finality_network_id: commitment(6),
        finality_protocol_id: commitment(7),
        external_finality_policy_hash: commitment(8),
        finality_verifier_set_root: commitment(9),
        finality_evidence_root: commitment(10),
        finality_policy_root: policy.policy_root().expect("policy root derives"),
    })
    .unwrap_or_else(|error| panic!("fixture rejected: {error}"))
}

fn expected(
    sequence: u64,
    candidate_hash: CommitmentV3,
    parent_hash: CommitmentV3,
) -> SuppliedCheckpointFinalityBindingV2 {
    SuppliedCheckpointFinalityBindingV2 {
        application_id: application_id(1),
        chain_or_domain_id: domain_id(2),
        epoch_id: 11,
        proof_journal_hash: commitment(3),
        post_state_root: commitment(4),
        application_checkpoint_sequence: sequence,
        application_checkpoint_hash: candidate_hash,
        parent_application_checkpoint_hash: parent_hash,
        finality_network_id: commitment(6),
        finality_protocol_id: commitment(7),
        external_finality_policy_hash: commitment(8),
        finality_verifier_set_root: commitment(9),
        finality_evidence_root: commitment(10),
    }
}

fn encoded_request(
    policy: &CheckpointFinalityPolicyV2,
    certificate: &CheckpointFinalityCertificateV2,
    expected: SuppliedCheckpointFinalityBindingV2,
    prior_cursor_proposal: CheckpointCursorProposalV2,
) -> Vec<u8> {
    let certificate_bytes = encode_checkpoint_finality_certificate_v2(certificate)
        .unwrap_or_else(|error| panic!("fixture rejected: {error}"));
    encode_checker_request_v1(CheckpointFinalityCheckerRequestInputV1 {
        policy,
        expected,
        prior_cursor_proposal,
        exact_certificate_bytes: &certificate_bytes,
    })
    .unwrap_or_else(|error| panic!("fixture rejected: {error}"))
}

fn genesis_request() -> (Vec<u8>, CheckpointFinalityCertificateV2) {
    let policy = policy(0, commitment(5));
    let certificate = certificate(&policy, 1, commitment(11), commitment(5));
    let request = encoded_request(
        &policy,
        &certificate,
        expected(1, commitment(11), commitment(5)),
        CheckpointCursorProposalV2::empty(),
    );
    (request, certificate)
}

fn prior_record_request() -> Vec<u8> {
    let policy = policy(41, commitment(5));
    let certificate = certificate(&policy, 43, commitment(12), commitment(11));
    let prior = CheckpointCursorProposalV2::from_prior_record(
        ProposedPriorApplicationCheckpointRecordV2::new(
            ProposedPriorApplicationCheckpointRecordInputV2 {
                application_id: policy.application_id(),
                chain_or_domain_id: policy.chain_or_domain_id(),
                finality_network_id: policy.finality_network_id(),
                finality_protocol_id: policy.finality_protocol_id(),
                external_finality_policy_hash: policy.expected_external_finality_policy_hash(),
                finality_verifier_set_root: policy.expected_finality_verifier_set_root(),
                finality_policy_root: policy.policy_root().expect("policy root derives"),
                application_checkpoint_sequence: 42,
                application_checkpoint_hash: commitment(11),
            },
        ),
    );
    encoded_request(
        &policy,
        &certificate,
        expected(43, commitment(12), commitment(11)),
        prior,
    )
}

fn position_distinct_request() -> Vec<u8> {
    let genesis_sequence = 0x0102_0304_0506_0708_u64;
    let prior_sequence = genesis_sequence + 1;
    let checkpoint_sequence = prior_sequence + 1;
    let epoch_id = 0x1112_1314_1516_1718_u64;
    let application = ApplicationIdV3::new(position_bytes(0x11)).expect("fixture application");
    let domain = DomainIdV3::new(position_bytes(0x22)).expect("fixture domain");
    let proof_journal_hash = CommitmentV3::new(position_bytes(0x33)).expect("fixture journal");
    let post_state_root = CommitmentV3::new(position_bytes(0x44)).expect("fixture state");
    let genesis_hash = CommitmentV3::new(position_bytes(0x55)).expect("fixture genesis");
    let finality_network = CommitmentV3::new(position_bytes(0x66)).expect("fixture network");
    let finality_protocol = CommitmentV3::new(position_bytes(0x77)).expect("fixture protocol");
    let external_policy = CommitmentV3::new(position_bytes(0x88)).expect("fixture policy");
    let verifier_set = CommitmentV3::new(position_bytes(0x99)).expect("fixture verifier set");
    let evidence_root = CommitmentV3::new(position_bytes(0xaa)).expect("fixture evidence");
    let prior_hash = CommitmentV3::new(position_bytes(0xab)).expect("fixture prior");
    let checkpoint_hash = CommitmentV3::new(position_bytes(0xbb)).expect("fixture checkpoint");
    let policy = CheckpointFinalityPolicyV2::new(CheckpointFinalityPolicyInputV2 {
        application_id: application,
        chain_or_domain_id: domain,
        finality_network_id: finality_network,
        finality_protocol_id: finality_protocol,
        expected_external_finality_policy_hash: external_policy,
        expected_finality_verifier_set_root: verifier_set,
        genesis_application_checkpoint_sequence: genesis_sequence,
        genesis_application_checkpoint_hash: genesis_hash,
    });
    let policy_root = policy.policy_root().expect("fixture policy root");
    let certificate =
        CheckpointFinalityCertificateV2::derive(CheckpointFinalityCertificateInputV2 {
            application_id: application,
            chain_or_domain_id: domain,
            epoch_id,
            proof_journal_hash,
            post_state_root,
            application_checkpoint_sequence: checkpoint_sequence,
            application_checkpoint_hash: checkpoint_hash,
            parent_application_checkpoint_hash: prior_hash,
            finality_network_id: finality_network,
            finality_protocol_id: finality_protocol,
            external_finality_policy_hash: external_policy,
            finality_verifier_set_root: verifier_set,
            finality_evidence_root: evidence_root,
            finality_policy_root: policy_root,
        })
        .expect("fixture certificate");
    let prior = CheckpointCursorProposalV2::from_prior_record(
        ProposedPriorApplicationCheckpointRecordV2::new(
            ProposedPriorApplicationCheckpointRecordInputV2 {
                application_id: application,
                chain_or_domain_id: domain,
                finality_network_id: finality_network,
                finality_protocol_id: finality_protocol,
                external_finality_policy_hash: external_policy,
                finality_verifier_set_root: verifier_set,
                finality_policy_root: policy_root,
                application_checkpoint_sequence: prior_sequence,
                application_checkpoint_hash: prior_hash,
            },
        ),
    );
    encoded_request(
        &policy,
        &certificate,
        SuppliedCheckpointFinalityBindingV2 {
            application_id: application,
            chain_or_domain_id: domain,
            epoch_id,
            proof_journal_hash,
            post_state_root,
            application_checkpoint_sequence: checkpoint_sequence,
            application_checkpoint_hash: checkpoint_hash,
            parent_application_checkpoint_hash: prior_hash,
            finality_network_id: finality_network,
            finality_protocol_id: finality_protocol,
            external_finality_policy_hash: external_policy,
            finality_verifier_set_root: verifier_set,
            finality_evidence_root: evidence_root,
        },
        prior,
    )
}

#[test]
fn nonzero_genesis_request_runs_exact_checker_and_emits_fixed_response() {
    let (request, certificate) = genesis_request();
    let first = check_request_bytes_v1(&request)
        .unwrap_or_else(|error| panic!("valid request rejected: {error}"));
    let second = check_request_bytes_v1(&request)
        .unwrap_or_else(|error| panic!("valid request rejected: {error}"));
    assert_eq!(first.len(), RESPONSE_BYTES_V1);
    assert_eq!(first, second);

    let response = decode_checker_response_v1(&first)
        .unwrap_or_else(|error| panic!("valid response rejected: {error}"));
    assert_eq!(response.application_id(), application_id(1));
    assert_eq!(response.chain_or_domain_id(), domain_id(2));
    assert_eq!(response.epoch_id(), 11);
    assert_eq!(response.certificate_root(), certificate.certificate_root());
    assert_eq!(response.prior_application_checkpoint_sequence(), 0);
    assert_eq!(response.prior_application_checkpoint_hash(), commitment(5));
    assert_eq!(response.next_application_checkpoint_sequence(), 1);
    assert_eq!(response.next_application_checkpoint_hash(), commitment(11));
    assert_eq!(
        response.request_sha256(),
        <[u8; 32]>::from(Sha256::digest(&request))
    );
}

#[test]
fn v2_zero_genesis_parent_and_prior_hashes_reject_at_typed_boundaries() {
    let (request, _) = genesis_request();

    let mut zero_genesis = request.clone();
    zero_genesis
        [POLICY_GENESIS_CHECKPOINT_HASH_OFFSET_V1..POLICY_GENESIS_CHECKPOINT_HASH_OFFSET_V1 + 32]
        .fill(0);
    assert_eq!(
        check_request_bytes_v1(&zero_genesis),
        Err(CheckpointFinalityCheckerErrorV1::InvalidTypedField(
            "policy_genesis_application_checkpoint_hash"
        ))
    );

    let mut zero_expected_parent = request.clone();
    zero_expected_parent
        [EXPECTED_PARENT_CHECKPOINT_HASH_OFFSET_V1..EXPECTED_PARENT_CHECKPOINT_HASH_OFFSET_V1 + 32]
        .fill(0);
    assert_eq!(
        check_request_bytes_v1(&zero_expected_parent),
        Err(CheckpointFinalityCheckerErrorV1::InvalidTypedField(
            "expected_parent_application_checkpoint_hash"
        ))
    );

    let mut zero_prior_above_genesis = prior_record_request();
    zero_prior_above_genesis[PRIOR_RECORD_HASH_OFFSET_V1..PRIOR_RECORD_HASH_OFFSET_V1 + 32].fill(0);
    assert_eq!(
        check_request_bytes_v1(&zero_prior_above_genesis),
        Err(CheckpointFinalityCheckerErrorV1::InvalidTypedField(
            "prior_application_checkpoint_hash"
        ))
    );

    let mut zero_certificate_parent = request;
    let certificate_parent_offsets: Vec<_> = zero_certificate_parent[REQUEST_HEADER_BYTES_V1..]
        .windows(32)
        .enumerate()
        .filter_map(|(index, bytes)| (bytes == [5_u8; 32]).then_some(index))
        .collect();
    assert_eq!(
        certificate_parent_offsets.len(),
        1,
        "fixture must contain one exact serialized parent hash"
    );
    let parent_start = REQUEST_HEADER_BYTES_V1 + certificate_parent_offsets[0];
    zero_certificate_parent[parent_start..parent_start + 32].fill(0);
    assert_eq!(
        check_request_bytes_v1(&zero_certificate_parent),
        Err(CheckpointFinalityCheckerErrorV1::CertificateRejected)
    );
}

#[test]
fn v2_zero_prior_hash_in_a_recommitted_response_rejects() {
    let (request, _) = genesis_request();
    let mut response = check_request_bytes_v1(&request).expect("valid request checks");
    response[162..194].fill(0);
    let mut response_commitment = Sha256::new();
    response_commitment.update(b"zenodex.zrpf.checkpoint_finality_checker.response_commitment.v1");
    response_commitment.update(&response[..298]);
    response[298..330].copy_from_slice(&response_commitment.finalize());

    assert_eq!(
        decode_checker_response_v1(&response),
        Err(CheckpointFinalityCheckerErrorV1::InvalidTypedField(
            "response_prior_application_checkpoint_hash"
        ))
    );
}

#[test]
fn python_v2_request_vectors_cover_nonzero_and_zero_hash_boundaries() {
    let policy = policy(41, commitment(5));
    let certificate = certificate(&policy, 42, commitment(11), commitment(5));
    let request = encoded_request(
        &policy,
        &certificate,
        expected(42, commitment(11), commitment(5)),
        CheckpointCursorProposalV2::empty(),
    );
    assert_eq!(request.len(), 1_304);
    assert_eq!(
        Sha256::digest(&request).as_slice(),
        &[
            0x39, 0xbb, 0xe9, 0x6f, 0x57, 0xab, 0xd6, 0x46, 0x37, 0xdf, 0xa9, 0x0d, 0xb8, 0x5b,
            0x2c, 0x72, 0x4e, 0x4d, 0x8d, 0x49, 0xda, 0xe1, 0xa8, 0x8c, 0x7f, 0x8b, 0x7a, 0x58,
            0xa3, 0x67, 0x58, 0x09,
        ]
    );

    let mut zero_genesis = request;
    zero_genesis
        [POLICY_GENESIS_CHECKPOINT_HASH_OFFSET_V1..POLICY_GENESIS_CHECKPOINT_HASH_OFFSET_V1 + 32]
        .fill(0);
    assert_eq!(
        Sha256::digest(&zero_genesis).as_slice(),
        &[
            0x35, 0xbf, 0xe8, 0x0d, 0xd3, 0xec, 0x8d, 0x27, 0x00, 0x5d, 0x57, 0x8e, 0xc8, 0x8e,
            0xb0, 0xa1, 0x8e, 0x20, 0xa7, 0x97, 0x37, 0x73, 0x57, 0x18, 0x0d, 0x82, 0xaf, 0x49,
            0x25, 0x5c, 0xfc, 0xc4,
        ]
    );
    assert!(check_request_bytes_v1(&zero_genesis).is_err());

    let prior_request = prior_record_request();
    assert_eq!(
        Sha256::digest(&prior_request).as_slice(),
        &[
            0x0b, 0x24, 0x44, 0xd3, 0x9e, 0x04, 0x08, 0x6c, 0x2e, 0x4c, 0xad, 0xcc, 0x8a, 0x1b,
            0xc1, 0x17, 0xad, 0x6a, 0x51, 0x9e, 0xf5, 0x16, 0xcc, 0xfe, 0xd5, 0xb7, 0xc9, 0xb5,
            0x02, 0xdd, 0x84, 0xbb,
        ]
    );
    let mut zero_prior_above_genesis = prior_request;
    zero_prior_above_genesis[PRIOR_RECORD_HASH_OFFSET_V1..PRIOR_RECORD_HASH_OFFSET_V1 + 32].fill(0);
    assert_eq!(
        Sha256::digest(&zero_prior_above_genesis).as_slice(),
        &[
            0xdf, 0x6f, 0x34, 0x07, 0x4c, 0xa1, 0x6d, 0x72, 0x2b, 0x30, 0xf5, 0xe0, 0x54, 0x83,
            0xec, 0x54, 0x21, 0x8f, 0xb2, 0x87, 0x0b, 0xed, 0xc4, 0x98, 0xe8, 0xca, 0x0c, 0xd7,
            0x56, 0x19, 0x50, 0x51,
        ]
    );
    assert!(check_request_bytes_v1(&zero_prior_above_genesis).is_err());
}

#[test]
fn python_position_distinct_vector_activates_representation_choices() {
    let request = position_distinct_request();

    assert_eq!(request.len(), 1_320);
    assert_eq!(&request[18..50], &position_bytes(0x11));
    let mut reversed_application = position_bytes(0x11);
    reversed_application.reverse();
    assert_ne!(&request[18..50], &reversed_application);
    assert_eq!(&request[210..218], &0x0102_0304_0506_0708_u64.to_be_bytes());
    assert_eq!(
        &request[EXPECTED_EPOCH_OFFSET_V1..EXPECTED_EPOCH_OFFSET_V1 + 8],
        &0x1112_1314_1516_1718_u64.to_be_bytes()
    );
    assert_eq!(request[PRIOR_CURSOR_TAG_OFFSET_V1], 1);
    assert_eq!(
        &request[PRIOR_RECORD_SEQUENCE_OFFSET_V1..PRIOR_RECORD_SEQUENCE_OFFSET_V1 + 8],
        &0x0102_0304_0506_0709_u64.to_be_bytes()
    );
    assert_eq!(
        Sha256::digest(&request).as_slice(),
        &[
            0x5c, 0x6a, 0x7d, 0x9c, 0x69, 0x03, 0x7d, 0x53, 0xcb, 0x4d, 0x64, 0x7a, 0x59, 0x7a,
            0x99, 0xd9, 0x2d, 0xb0, 0x78, 0x18, 0x6b, 0xa9, 0xa4, 0x3f, 0x54, 0xcc, 0x47, 0x14,
            0xba, 0x27, 0xad, 0x36,
        ]
    );
    check_request_bytes_v1(&request).expect("position-distinct request checks");
}

#[test]
fn scoped_prior_record_runs_exact_successor_rule() {
    let request = prior_record_request();
    let response_bytes = check_request_bytes_v1(&request)
        .unwrap_or_else(|error| panic!("valid request rejected: {error}"));
    let response = decode_checker_response_v1(&response_bytes)
        .unwrap_or_else(|error| panic!("valid response rejected: {error}"));
    assert_eq!(response.prior_application_checkpoint_sequence(), 42);
    assert_eq!(response.prior_application_checkpoint_hash(), commitment(11));
    assert_eq!(response.next_application_checkpoint_sequence(), 43);
    assert_eq!(response.next_application_checkpoint_hash(), commitment(12));
}

#[test]
fn fixed_request_and_response_offsets_match_independent_layout() {
    let (request, certificate) = genesis_request();
    let certificate_bytes = encode_checkpoint_finality_certificate_v2(&certificate)
        .expect("fixture certificate encodes");
    assert_eq!(REQUEST_HEADER_BYTES_V1, 885);
    assert_eq!(&request[0..16], b"ZRPFCFV2REQV1!!!");
    assert_eq!(&request[16..18], &1_u16.to_be_bytes());
    assert_eq!(&request[18..50], &[1; 32]);
    assert_eq!(&request[50..82], &[2; 32]);
    assert_eq!(&request[82..114], &[6; 32]);
    assert_eq!(&request[114..146], &[7; 32]);
    assert_eq!(&request[146..178], &[8; 32]);
    assert_eq!(&request[178..210], &[9; 32]);
    assert_eq!(&request[210..218], &0_u64.to_be_bytes());
    assert_eq!(&request[218..250], &[5; 32]);
    assert_eq!(&request[250..282], &[1; 32]);
    assert_eq!(&request[282..314], &[2; 32]);
    assert_eq!(&request[314..322], &11_u64.to_be_bytes());
    assert_eq!(&request[322..354], &[3; 32]);
    assert_eq!(&request[354..386], &[4; 32]);
    assert_eq!(&request[386..394], &1_u64.to_be_bytes());
    assert_eq!(&request[394..426], &[11; 32]);
    assert_eq!(&request[426..458], &[5; 32]);
    assert_eq!(&request[458..490], &[6; 32]);
    assert_eq!(&request[490..522], &[7; 32]);
    assert_eq!(&request[522..554], &[8; 32]);
    assert_eq!(&request[554..586], &[9; 32]);
    assert_eq!(&request[586..618], &[10; 32]);
    assert_eq!(request[618], 0);
    assert!(request[619..883].iter().all(|byte| *byte == 0));
    assert_eq!(
        &request[883..885],
        &u16::try_from(certificate_bytes.len())
            .expect("certificate length fits")
            .to_be_bytes()
    );
    assert_eq!(&request[885..], certificate_bytes);

    let response = check_request_bytes_v1(&request).expect("valid request checks");
    let genesis_policy = policy(0, commitment(5));
    let policy_root = genesis_policy.policy_root().expect("policy root derives");
    assert_eq!(&response[0..16], b"ZRPFCFV2RESV1!!!");
    assert_eq!(&response[16..18], &1_u16.to_be_bytes());
    assert_eq!(&response[18..50], &[1; 32]);
    assert_eq!(&response[50..82], &[2; 32]);
    assert_eq!(&response[82..90], &11_u64.to_be_bytes());
    assert_eq!(&response[90..122], policy_root.as_bytes());
    assert_eq!(
        &response[122..154],
        certificate.certificate_root().as_bytes()
    );
    assert_eq!(&response[154..162], &0_u64.to_be_bytes());
    assert_eq!(&response[162..194], &[5; 32]);
    assert_eq!(&response[194..202], &1_u64.to_be_bytes());
    assert_eq!(&response[202..234], &[11; 32]);
    assert_eq!(
        &response[234..266],
        Sha256::digest(&certificate_bytes).as_slice()
    );
    assert_eq!(&response[266..298], Sha256::digest(&request).as_slice());
    let mut response_commitment = Sha256::new();
    response_commitment.update(b"zenodex.zrpf.checkpoint_finality_checker.response_commitment.v1");
    response_commitment.update(&response[..298]);
    assert_eq!(
        &response[298..330],
        response_commitment.finalize().as_slice()
    );
}

#[test]
fn every_truncated_prefix_extension_and_framing_substitution_rejects() {
    let (request, _) = genesis_request();
    for length in 0..request.len() {
        assert!(
            check_request_bytes_v1(&request[..length]).is_err(),
            "truncated prefix of length {length} was accepted"
        );
    }

    let mut extended = request.clone();
    extended.push(0);
    assert_eq!(
        check_request_bytes_v1(&extended),
        Err(CheckpointFinalityCheckerErrorV1::RequestSize)
    );

    let mut wrong_magic = request.clone();
    wrong_magic[0] ^= 1;
    assert_eq!(
        check_request_bytes_v1(&wrong_magic),
        Err(CheckpointFinalityCheckerErrorV1::RequestMagic)
    );

    let mut wrong_version = request.clone();
    wrong_version[REQUEST_VERSION_OFFSET_V1..REQUEST_VERSION_OFFSET_V1 + 2]
        .copy_from_slice(&2_u16.to_be_bytes());
    assert_eq!(
        check_request_bytes_v1(&wrong_version),
        Err(CheckpointFinalityCheckerErrorV1::RequestVersion(2))
    );

    let mut wrong_tag = request.clone();
    wrong_tag[PRIOR_CURSOR_TAG_OFFSET_V1] = 2;
    assert_eq!(
        check_request_bytes_v1(&wrong_tag),
        Err(CheckpointFinalityCheckerErrorV1::PriorCursorTag(2))
    );
}

#[test]
fn empty_prior_cursor_and_nonzero_typed_fields_are_canonical() {
    let (request, _) = genesis_request();

    let mut populated_empty = request.clone();
    populated_empty[PRIOR_RECORD_APPLICATION_ID_OFFSET_V1] = 1;
    assert_eq!(
        check_request_bytes_v1(&populated_empty),
        Err(CheckpointFinalityCheckerErrorV1::NonCanonicalEmptyPriorCursor)
    );

    let mut zero_policy_application = request.clone();
    zero_policy_application[POLICY_APPLICATION_ID_OFFSET_V1..POLICY_APPLICATION_ID_OFFSET_V1 + 32]
        .fill(0);
    assert_eq!(
        check_request_bytes_v1(&zero_policy_application),
        Err(CheckpointFinalityCheckerErrorV1::InvalidTypedField(
            "policy_application_id"
        ))
    );

    let mut zero_candidate_hash = request.clone();
    zero_candidate_hash
        [EXPECTED_CHECKPOINT_HASH_OFFSET_V1..EXPECTED_CHECKPOINT_HASH_OFFSET_V1 + 32]
        .fill(0);
    assert_eq!(
        check_request_bytes_v1(&zero_candidate_hash),
        Err(CheckpointFinalityCheckerErrorV1::InvalidTypedField(
            "expected_application_checkpoint_hash"
        ))
    );

    let mut prior = prior_record_request();
    prior[PRIOR_RECORD_APPLICATION_ID_OFFSET_V1..PRIOR_RECORD_APPLICATION_ID_OFFSET_V1 + 32]
        .fill(0);
    assert_eq!(
        check_request_bytes_v1(&prior),
        Err(CheckpointFinalityCheckerErrorV1::InvalidTypedField(
            "prior_application_id"
        ))
    );
}

#[test]
fn structure_preserving_policy_binding_and_cursor_mutations_reject() {
    let (request, _) = genesis_request();
    let mut mutations = Vec::new();

    let mut changed_epoch = request.clone();
    changed_epoch[EXPECTED_EPOCH_OFFSET_V1..EXPECTED_EPOCH_OFFSET_V1 + 8]
        .copy_from_slice(&12_u64.to_be_bytes());
    mutations.push(changed_epoch);

    for offset in [
        EXPECTED_PROOF_JOURNAL_HASH_OFFSET_V1,
        EXPECTED_POST_STATE_ROOT_OFFSET_V1,
        EXPECTED_CHECKPOINT_HASH_OFFSET_V1,
        EXPECTED_PARENT_CHECKPOINT_HASH_OFFSET_V1,
        EXPECTED_FINALITY_EVIDENCE_ROOT_OFFSET_V1,
    ] {
        let mut changed = request.clone();
        changed[offset] ^= 1;
        mutations.push(changed);
    }

    let mut changed_sequence = request;
    changed_sequence
        [EXPECTED_CHECKPOINT_SEQUENCE_OFFSET_V1..EXPECTED_CHECKPOINT_SEQUENCE_OFFSET_V1 + 8]
        .copy_from_slice(&2_u64.to_be_bytes());
    mutations.push(changed_sequence);

    for (index, changed) in mutations.iter().enumerate() {
        assert_eq!(
            check_request_bytes_v1(changed),
            Err(CheckpointFinalityCheckerErrorV1::PolicyRejected),
            "binding mutation {index} reached acceptance"
        );
    }

    let prior = prior_record_request();
    let mut changed_prior_sequence = prior.clone();
    changed_prior_sequence[PRIOR_RECORD_SEQUENCE_OFFSET_V1..PRIOR_RECORD_SEQUENCE_OFFSET_V1 + 8]
        .copy_from_slice(&41_u64.to_be_bytes());
    assert_eq!(
        check_request_bytes_v1(&changed_prior_sequence),
        Err(CheckpointFinalityCheckerErrorV1::PolicyRejected)
    );

    let mut changed_prior_hash = prior;
    changed_prior_hash[PRIOR_RECORD_HASH_OFFSET_V1] ^= 1;
    assert_eq!(
        check_request_bytes_v1(&changed_prior_hash),
        Err(CheckpointFinalityCheckerErrorV1::PolicyRejected)
    );
}

#[test]
fn every_single_bit_certificate_mutation_rejects() {
    let (request, _) = genesis_request();
    let certificate_length = usize::from(u16::from_be_bytes(
        request[CERTIFICATE_LENGTH_OFFSET_V1..REQUEST_HEADER_BYTES_V1]
            .try_into()
            .expect("certificate length has exact width"),
    ));
    assert_eq!(request.len(), REQUEST_HEADER_BYTES_V1 + certificate_length);

    for byte_index in REQUEST_HEADER_BYTES_V1..request.len() {
        for bit in 0..8 {
            let mut mutated = request.clone();
            mutated[byte_index] ^= 1 << bit;
            assert!(
                check_request_bytes_v1(&mutated).is_err(),
                "certificate mutation at byte {byte_index} bit {bit} was accepted"
            );
        }
    }
}

#[test]
fn certificate_bounds_and_response_mutations_fail_closed() {
    let policy = policy(0, commitment(5));
    let expected = expected(1, commitment(11), commitment(5));
    assert_eq!(
        encode_checker_request_v1(CheckpointFinalityCheckerRequestInputV1 {
            policy: &policy,
            expected,
            prior_cursor_proposal: CheckpointCursorProposalV2::empty(),
            exact_certificate_bytes: &[],
        }),
        Err(CheckpointFinalityCheckerErrorV1::CertificateLength)
    );
    let oversized = vec![0_u8; MAX_CHECKPOINT_FINALITY_CERTIFICATE_BYTES_V2 + 1];
    assert_eq!(
        encode_checker_request_v1(CheckpointFinalityCheckerRequestInputV1 {
            policy: &policy,
            expected,
            prior_cursor_proposal: CheckpointCursorProposalV2::empty(),
            exact_certificate_bytes: &oversized,
        }),
        Err(CheckpointFinalityCheckerErrorV1::CertificateLength)
    );

    let (request, _) = genesis_request();
    let response = check_request_bytes_v1(&request).expect("valid request checks");
    for index in [0, 17, 89, 153, 201, 265, RESPONSE_BYTES_V1 - 1] {
        let mut mutated = response;
        mutated[index] ^= 1;
        assert!(
            decode_checker_response_v1(&mutated).is_err(),
            "response mutation at byte {index} was accepted"
        );
    }
    assert_eq!(
        decode_checker_response_v1(&response[..response.len() - 1]),
        Err(CheckpointFinalityCheckerErrorV1::ResponseSize)
    );
}

#[test]
fn binary_emits_only_fixed_success_bytes_and_rejects_bad_input() {
    let (request, _) = genesis_request();
    let expected_response = check_request_bytes_v1(&request).expect("valid request checks");
    let output = run_binary(&request);
    assert!(output.status.success());
    assert_eq!(output.stdout, expected_response);
    assert!(output.stderr.is_empty());

    let mut invalid = request;
    invalid[0] ^= 1;
    let output = run_binary(&invalid);
    assert!(!output.status.success());
    assert!(output.stdout.is_empty());
    assert!(output.stderr.is_empty());
}

fn run_binary(request: &[u8]) -> Output {
    let mut child = Command::new(env!("CARGO_BIN_EXE_zrpf-checkpoint-finality-checker-v1"))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("checker process starts");
    child
        .stdin
        .take()
        .expect("checker stdin exists")
        .write_all(request)
        .expect("request writes");
    child.wait_with_output().expect("checker process exits")
}
