use core::fmt;

use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::{
    check_checkpoint_finality_policy_satisfied_v2, decode_exact_checkpoint_finality_certificate_v2,
    ApplicationIdV3, CheckpointCursorProposalV2, CheckpointFinalityPolicyCheckInputV2,
    CheckpointFinalityPolicyInputV2, CheckpointFinalityPolicyV2, CommitmentV3, DomainIdV3,
    ProposedPriorApplicationCheckpointRecordInputV2, ProposedPriorApplicationCheckpointRecordV2,
    SuppliedCheckpointFinalityBindingV2, MAX_CHECKPOINT_FINALITY_CERTIFICATE_BYTES_V2,
};

pub const CHECKER_PROTOCOL_VERSION_V1: u16 = 1;
pub const REQUEST_MAGIC_V1: [u8; 16] = *b"ZRPFCFV2REQV1!!!";
pub const RESPONSE_MAGIC_V1: [u8; 16] = *b"ZRPFCFV2RESV1!!!";
pub const PRIOR_CURSOR_EMPTY_V1: u8 = 0;
pub const PRIOR_CURSOR_RECORD_V1: u8 = 1;

pub const REQUEST_VERSION_OFFSET_V1: usize = 16;
pub const POLICY_APPLICATION_ID_OFFSET_V1: usize = 18;
pub const POLICY_GENESIS_CHECKPOINT_HASH_OFFSET_V1: usize = 218;
pub const EXPECTED_EPOCH_OFFSET_V1: usize = 314;
pub const EXPECTED_PROOF_JOURNAL_HASH_OFFSET_V1: usize = 322;
pub const EXPECTED_POST_STATE_ROOT_OFFSET_V1: usize = 354;
pub const EXPECTED_CHECKPOINT_SEQUENCE_OFFSET_V1: usize = 386;
pub const EXPECTED_CHECKPOINT_HASH_OFFSET_V1: usize = 394;
pub const EXPECTED_PARENT_CHECKPOINT_HASH_OFFSET_V1: usize = 426;
pub const EXPECTED_FINALITY_EVIDENCE_ROOT_OFFSET_V1: usize = 586;
pub const PRIOR_CURSOR_TAG_OFFSET_V1: usize = 618;
pub const PRIOR_RECORD_APPLICATION_ID_OFFSET_V1: usize = 619;
pub const PRIOR_RECORD_SEQUENCE_OFFSET_V1: usize = 843;
pub const PRIOR_RECORD_HASH_OFFSET_V1: usize = 851;
pub const CERTIFICATE_LENGTH_OFFSET_V1: usize = 883;
pub const REQUEST_HEADER_BYTES_V1: usize = 885;
pub const MAX_CHECKER_REQUEST_BYTES_V1: usize =
    REQUEST_HEADER_BYTES_V1 + MAX_CHECKPOINT_FINALITY_CERTIFICATE_BYTES_V2;

pub const RESPONSE_BODY_BYTES_V1: usize = 298;
pub const RESPONSE_BYTES_V1: usize = RESPONSE_BODY_BYTES_V1 + 32;

const PRIOR_RECORD_BYTES_V1: usize = 264;
const RESPONSE_COMMITMENT_DOMAIN_V1: &[u8] =
    b"zenodex.zrpf.checkpoint_finality_checker.response_commitment.v1";

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CheckpointFinalityCheckerErrorV1 {
    RequestSize,
    RequestMagic,
    RequestVersion(u16),
    InvalidTypedField(&'static str),
    PriorCursorTag(u8),
    NonCanonicalEmptyPriorCursor,
    CertificateLength,
    ArithmeticOverflow,
    CertificateRejected,
    PolicyRejected,
    ResponseSize,
    ResponseMagic,
    ResponseVersion(u16),
    ResponseCommitment,
    ResponseEncoding,
}

impl fmt::Display for CheckpointFinalityCheckerErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::RequestSize => formatter.write_str("checkpoint-finality request size rejected"),
            Self::RequestMagic => formatter.write_str("checkpoint-finality request magic rejected"),
            Self::RequestVersion(version) => write!(
                formatter,
                "checkpoint-finality request version {version} rejected"
            ),
            Self::InvalidTypedField(field) => {
                write!(
                    formatter,
                    "checkpoint-finality typed field rejected: {field}"
                )
            }
            Self::PriorCursorTag(tag) => {
                write!(
                    formatter,
                    "checkpoint-finality prior cursor tag {tag} rejected"
                )
            }
            Self::NonCanonicalEmptyPriorCursor => formatter
                .write_str("checkpoint-finality empty prior cursor contains nonzero record bytes"),
            Self::CertificateLength => {
                formatter.write_str("checkpoint-finality certificate length rejected")
            }
            Self::ArithmeticOverflow => {
                formatter.write_str("checkpoint-finality request arithmetic overflow")
            }
            Self::CertificateRejected => {
                formatter.write_str("checkpoint-finality certificate rejected")
            }
            Self::PolicyRejected => formatter.write_str("checkpoint-finality policy rejected"),
            Self::ResponseSize => formatter.write_str("checkpoint-finality response size rejected"),
            Self::ResponseMagic => {
                formatter.write_str("checkpoint-finality response magic rejected")
            }
            Self::ResponseVersion(version) => write!(
                formatter,
                "checkpoint-finality response version {version} rejected"
            ),
            Self::ResponseCommitment => {
                formatter.write_str("checkpoint-finality response commitment rejected")
            }
            Self::ResponseEncoding => {
                formatter.write_str("checkpoint-finality response encoding rejected")
            }
        }
    }
}

pub struct CheckpointFinalityCheckerRequestInputV1<'a> {
    pub policy: &'a CheckpointFinalityPolicyV2,
    pub expected: SuppliedCheckpointFinalityBindingV2,
    pub prior_cursor_proposal: CheckpointCursorProposalV2,
    pub exact_certificate_bytes: &'a [u8],
}

struct DecodedCheckerRequestV1<'a> {
    policy: CheckpointFinalityPolicyV2,
    expected: SuppliedCheckpointFinalityBindingV2,
    prior_cursor_proposal: CheckpointCursorProposalV2,
    certificate_bytes: &'a [u8],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CheckpointFinalityCheckerResponseV1 {
    application_id: ApplicationIdV3,
    chain_or_domain_id: DomainIdV3,
    epoch_id: u64,
    policy_root: CommitmentV3,
    certificate_root: CommitmentV3,
    prior_application_checkpoint_sequence: u64,
    prior_application_checkpoint_hash: CommitmentV3,
    next_application_checkpoint_sequence: u64,
    next_application_checkpoint_hash: CommitmentV3,
    exact_certificate_sha256: [u8; 32],
    request_sha256: [u8; 32],
}

impl CheckpointFinalityCheckerResponseV1 {
    pub const fn application_id(&self) -> ApplicationIdV3 {
        self.application_id
    }

    pub const fn chain_or_domain_id(&self) -> DomainIdV3 {
        self.chain_or_domain_id
    }

    pub const fn epoch_id(&self) -> u64 {
        self.epoch_id
    }

    pub const fn policy_root(&self) -> CommitmentV3 {
        self.policy_root
    }

    pub const fn certificate_root(&self) -> CommitmentV3 {
        self.certificate_root
    }

    pub const fn prior_application_checkpoint_sequence(&self) -> u64 {
        self.prior_application_checkpoint_sequence
    }

    pub const fn prior_application_checkpoint_hash(&self) -> CommitmentV3 {
        self.prior_application_checkpoint_hash
    }

    pub const fn next_application_checkpoint_sequence(&self) -> u64 {
        self.next_application_checkpoint_sequence
    }

    pub const fn next_application_checkpoint_hash(&self) -> CommitmentV3 {
        self.next_application_checkpoint_hash
    }

    pub const fn exact_certificate_sha256(&self) -> [u8; 32] {
        self.exact_certificate_sha256
    }

    pub const fn request_sha256(&self) -> [u8; 32] {
        self.request_sha256
    }
}

pub fn encode_checker_request_v1(
    input: CheckpointFinalityCheckerRequestInputV1<'_>,
) -> Result<Vec<u8>, CheckpointFinalityCheckerErrorV1> {
    require_certificate_length(input.exact_certificate_bytes.len())?;
    let certificate_length = u16::try_from(input.exact_certificate_bytes.len())
        .map_err(|_| CheckpointFinalityCheckerErrorV1::CertificateLength)?;
    let capacity = REQUEST_HEADER_BYTES_V1
        .checked_add(input.exact_certificate_bytes.len())
        .ok_or(CheckpointFinalityCheckerErrorV1::ArithmeticOverflow)?;
    let mut request = Vec::with_capacity(capacity);
    request.extend_from_slice(&REQUEST_MAGIC_V1);
    request.extend_from_slice(&CHECKER_PROTOCOL_VERSION_V1.to_be_bytes());
    append_policy(&mut request, input.policy);
    append_expected(&mut request, input.expected);
    append_prior_cursor(&mut request, input.prior_cursor_proposal);
    request.extend_from_slice(&certificate_length.to_be_bytes());
    request.extend_from_slice(input.exact_certificate_bytes);
    if request.len() != capacity {
        return Err(CheckpointFinalityCheckerErrorV1::RequestSize);
    }
    Ok(request)
}

pub fn check_request_bytes_v1(
    request: &[u8],
) -> Result<[u8; RESPONSE_BYTES_V1], CheckpointFinalityCheckerErrorV1> {
    let decoded = decode_checker_request_v1(request)?;
    let certificate = decode_exact_checkpoint_finality_certificate_v2(decoded.certificate_bytes)
        .map_err(|_| CheckpointFinalityCheckerErrorV1::CertificateRejected)?;
    let checked =
        check_checkpoint_finality_policy_satisfied_v2(CheckpointFinalityPolicyCheckInputV2 {
            policy: &decoded.policy,
            certificate: &certificate,
            expected: decoded.expected,
            prior_cursor_proposal: decoded.prior_cursor_proposal,
        })
        .map_err(|_| CheckpointFinalityCheckerErrorV1::PolicyRejected)?;
    let (prior_sequence, prior_hash) = match checked.prior_cursor_proposal().prior_record() {
        Some(record) => (
            record.application_checkpoint_sequence(),
            record.application_checkpoint_hash(),
        ),
        None => (
            decoded.policy.genesis_application_checkpoint_sequence(),
            decoded.policy.genesis_application_checkpoint_hash(),
        ),
    };
    let next = checked.derived_next_cursor();
    encode_response_v1(CheckpointFinalityCheckerResponseV1 {
        application_id: decoded.policy.application_id(),
        chain_or_domain_id: decoded.policy.chain_or_domain_id(),
        epoch_id: certificate.epoch_id(),
        policy_root: checked.policy_root(),
        certificate_root: checked.certificate_root(),
        prior_application_checkpoint_sequence: prior_sequence,
        prior_application_checkpoint_hash: prior_hash,
        next_application_checkpoint_sequence: next.application_checkpoint_sequence(),
        next_application_checkpoint_hash: next.application_checkpoint_hash(),
        exact_certificate_sha256: sha256(decoded.certificate_bytes),
        request_sha256: sha256(request),
    })
}

pub fn decode_checker_response_v1(
    response: &[u8],
) -> Result<CheckpointFinalityCheckerResponseV1, CheckpointFinalityCheckerErrorV1> {
    if response.len() != RESPONSE_BYTES_V1 {
        return Err(CheckpointFinalityCheckerErrorV1::ResponseSize);
    }
    let body = response
        .get(..RESPONSE_BODY_BYTES_V1)
        .ok_or(CheckpointFinalityCheckerErrorV1::ResponseSize)?;
    let supplied_commitment = response
        .get(RESPONSE_BODY_BYTES_V1..)
        .ok_or(CheckpointFinalityCheckerErrorV1::ResponseSize)?;
    if supplied_commitment != response_commitment_v1(body) {
        return Err(CheckpointFinalityCheckerErrorV1::ResponseCommitment);
    }
    let mut cursor = ByteCursorV1::new(body);
    if cursor.take_array::<16>()? != RESPONSE_MAGIC_V1 {
        return Err(CheckpointFinalityCheckerErrorV1::ResponseMagic);
    }
    let version = cursor.take_u16()?;
    if version != CHECKER_PROTOCOL_VERSION_V1 {
        return Err(CheckpointFinalityCheckerErrorV1::ResponseVersion(version));
    }
    let decoded = CheckpointFinalityCheckerResponseV1 {
        application_id: take_application_id(&mut cursor, "response_application_id")?,
        chain_or_domain_id: take_domain_id(&mut cursor, "response_chain_or_domain_id")?,
        epoch_id: cursor.take_u64()?,
        policy_root: take_commitment(&mut cursor, "response_policy_root")?,
        certificate_root: take_commitment(&mut cursor, "response_certificate_root")?,
        prior_application_checkpoint_sequence: cursor.take_u64()?,
        prior_application_checkpoint_hash: take_commitment(
            &mut cursor,
            "response_prior_application_checkpoint_hash",
        )?,
        next_application_checkpoint_sequence: cursor.take_u64()?,
        next_application_checkpoint_hash: take_commitment(
            &mut cursor,
            "response_next_application_checkpoint_hash",
        )?,
        exact_certificate_sha256: cursor.take_array::<32>()?,
        request_sha256: cursor.take_array::<32>()?,
    };
    if !cursor.is_finished() {
        return Err(CheckpointFinalityCheckerErrorV1::ResponseSize);
    }
    Ok(decoded)
}

fn append_policy(output: &mut Vec<u8>, policy: &CheckpointFinalityPolicyV2) {
    output.extend_from_slice(policy.application_id().as_bytes());
    output.extend_from_slice(policy.chain_or_domain_id().as_bytes());
    output.extend_from_slice(policy.finality_network_id().as_bytes());
    output.extend_from_slice(policy.finality_protocol_id().as_bytes());
    output.extend_from_slice(policy.expected_external_finality_policy_hash().as_bytes());
    output.extend_from_slice(policy.expected_finality_verifier_set_root().as_bytes());
    output.extend_from_slice(
        &policy
            .genesis_application_checkpoint_sequence()
            .to_be_bytes(),
    );
    output.extend_from_slice(policy.genesis_application_checkpoint_hash().as_bytes());
}

fn append_expected(output: &mut Vec<u8>, expected: SuppliedCheckpointFinalityBindingV2) {
    output.extend_from_slice(expected.application_id.as_bytes());
    output.extend_from_slice(expected.chain_or_domain_id.as_bytes());
    output.extend_from_slice(&expected.epoch_id.to_be_bytes());
    output.extend_from_slice(expected.proof_journal_hash.as_bytes());
    output.extend_from_slice(expected.post_state_root.as_bytes());
    output.extend_from_slice(&expected.application_checkpoint_sequence.to_be_bytes());
    output.extend_from_slice(expected.application_checkpoint_hash.as_bytes());
    output.extend_from_slice(expected.parent_application_checkpoint_hash.as_bytes());
    output.extend_from_slice(expected.finality_network_id.as_bytes());
    output.extend_from_slice(expected.finality_protocol_id.as_bytes());
    output.extend_from_slice(expected.external_finality_policy_hash.as_bytes());
    output.extend_from_slice(expected.finality_verifier_set_root.as_bytes());
    output.extend_from_slice(expected.finality_evidence_root.as_bytes());
}

fn append_prior_cursor(output: &mut Vec<u8>, proposal: CheckpointCursorProposalV2) {
    match proposal.prior_record() {
        None => {
            output.push(PRIOR_CURSOR_EMPTY_V1);
            let new_length = output.len() + PRIOR_RECORD_BYTES_V1;
            output.resize(new_length, 0);
        }
        Some(record) => {
            output.push(PRIOR_CURSOR_RECORD_V1);
            output.extend_from_slice(record.application_id().as_bytes());
            output.extend_from_slice(record.chain_or_domain_id().as_bytes());
            output.extend_from_slice(record.finality_network_id().as_bytes());
            output.extend_from_slice(record.finality_protocol_id().as_bytes());
            output.extend_from_slice(record.external_finality_policy_hash().as_bytes());
            output.extend_from_slice(record.finality_verifier_set_root().as_bytes());
            output.extend_from_slice(record.finality_policy_root().as_bytes());
            output.extend_from_slice(&record.application_checkpoint_sequence().to_be_bytes());
            output.extend_from_slice(record.application_checkpoint_hash().as_bytes());
        }
    }
}

fn decode_checker_request_v1(
    request: &[u8],
) -> Result<DecodedCheckerRequestV1<'_>, CheckpointFinalityCheckerErrorV1> {
    if request.len() < REQUEST_HEADER_BYTES_V1 || request.len() > MAX_CHECKER_REQUEST_BYTES_V1 {
        return Err(CheckpointFinalityCheckerErrorV1::RequestSize);
    }
    let mut cursor = ByteCursorV1::new(request);
    if cursor.take_array::<16>()? != REQUEST_MAGIC_V1 {
        return Err(CheckpointFinalityCheckerErrorV1::RequestMagic);
    }
    let version = cursor.take_u16()?;
    if version != CHECKER_PROTOCOL_VERSION_V1 {
        return Err(CheckpointFinalityCheckerErrorV1::RequestVersion(version));
    }
    let policy = decode_policy(&mut cursor)?;
    let expected = decode_expected(&mut cursor)?;
    let prior_cursor_proposal = decode_prior_cursor(&mut cursor)?;
    let certificate_length = usize::from(cursor.take_u16()?);
    require_certificate_length(certificate_length)?;
    let expected_length = REQUEST_HEADER_BYTES_V1
        .checked_add(certificate_length)
        .ok_or(CheckpointFinalityCheckerErrorV1::ArithmeticOverflow)?;
    if request.len() != expected_length {
        return Err(CheckpointFinalityCheckerErrorV1::RequestSize);
    }
    let certificate_bytes = cursor.take_slice(certificate_length)?;
    if !cursor.is_finished() {
        return Err(CheckpointFinalityCheckerErrorV1::RequestSize);
    }
    Ok(DecodedCheckerRequestV1 {
        policy,
        expected,
        prior_cursor_proposal,
        certificate_bytes,
    })
}

fn decode_policy(
    cursor: &mut ByteCursorV1<'_>,
) -> Result<CheckpointFinalityPolicyV2, CheckpointFinalityCheckerErrorV1> {
    Ok(CheckpointFinalityPolicyV2::new(
        CheckpointFinalityPolicyInputV2 {
            application_id: take_application_id(cursor, "policy_application_id")?,
            chain_or_domain_id: take_domain_id(cursor, "policy_chain_or_domain_id")?,
            finality_network_id: take_commitment(cursor, "policy_finality_network_id")?,
            finality_protocol_id: take_commitment(cursor, "policy_finality_protocol_id")?,
            expected_external_finality_policy_hash: take_commitment(
                cursor,
                "policy_external_finality_policy_hash",
            )?,
            expected_finality_verifier_set_root: take_commitment(
                cursor,
                "policy_finality_verifier_set_root",
            )?,
            genesis_application_checkpoint_sequence: cursor.take_u64()?,
            genesis_application_checkpoint_hash: take_commitment(
                cursor,
                "policy_genesis_application_checkpoint_hash",
            )?,
        },
    ))
}

fn decode_expected(
    cursor: &mut ByteCursorV1<'_>,
) -> Result<SuppliedCheckpointFinalityBindingV2, CheckpointFinalityCheckerErrorV1> {
    Ok(SuppliedCheckpointFinalityBindingV2 {
        application_id: take_application_id(cursor, "expected_application_id")?,
        chain_or_domain_id: take_domain_id(cursor, "expected_chain_or_domain_id")?,
        epoch_id: cursor.take_u64()?,
        proof_journal_hash: take_commitment(cursor, "expected_proof_journal_hash")?,
        post_state_root: take_commitment(cursor, "expected_post_state_root")?,
        application_checkpoint_sequence: cursor.take_u64()?,
        application_checkpoint_hash: take_commitment(
            cursor,
            "expected_application_checkpoint_hash",
        )?,
        parent_application_checkpoint_hash: take_commitment(
            cursor,
            "expected_parent_application_checkpoint_hash",
        )?,
        finality_network_id: take_commitment(cursor, "expected_finality_network_id")?,
        finality_protocol_id: take_commitment(cursor, "expected_finality_protocol_id")?,
        external_finality_policy_hash: take_commitment(
            cursor,
            "expected_external_finality_policy_hash",
        )?,
        finality_verifier_set_root: take_commitment(cursor, "expected_finality_verifier_set_root")?,
        finality_evidence_root: take_commitment(cursor, "expected_finality_evidence_root")?,
    })
}

fn decode_prior_cursor(
    cursor: &mut ByteCursorV1<'_>,
) -> Result<CheckpointCursorProposalV2, CheckpointFinalityCheckerErrorV1> {
    let tag = cursor.take_u8()?;
    let bytes = cursor.take_slice(PRIOR_RECORD_BYTES_V1)?;
    match tag {
        PRIOR_CURSOR_EMPTY_V1 => {
            if bytes.iter().any(|byte| *byte != 0) {
                return Err(CheckpointFinalityCheckerErrorV1::NonCanonicalEmptyPriorCursor);
            }
            Ok(CheckpointCursorProposalV2::empty())
        }
        PRIOR_CURSOR_RECORD_V1 => {
            let mut record = ByteCursorV1::new(bytes);
            let input = ProposedPriorApplicationCheckpointRecordInputV2 {
                application_id: take_application_id(&mut record, "prior_application_id")?,
                chain_or_domain_id: take_domain_id(&mut record, "prior_chain_or_domain_id")?,
                finality_network_id: take_commitment(&mut record, "prior_finality_network_id")?,
                finality_protocol_id: take_commitment(&mut record, "prior_finality_protocol_id")?,
                external_finality_policy_hash: take_commitment(
                    &mut record,
                    "prior_external_finality_policy_hash",
                )?,
                finality_verifier_set_root: take_commitment(
                    &mut record,
                    "prior_finality_verifier_set_root",
                )?,
                finality_policy_root: take_commitment(&mut record, "prior_finality_policy_root")?,
                application_checkpoint_sequence: record.take_u64()?,
                application_checkpoint_hash: take_commitment(
                    &mut record,
                    "prior_application_checkpoint_hash",
                )?,
            };
            if !record.is_finished() {
                return Err(CheckpointFinalityCheckerErrorV1::RequestSize);
            }
            Ok(CheckpointCursorProposalV2::from_prior_record(
                ProposedPriorApplicationCheckpointRecordV2::new(input),
            ))
        }
        _ => Err(CheckpointFinalityCheckerErrorV1::PriorCursorTag(tag)),
    }
}

fn take_application_id(
    cursor: &mut ByteCursorV1<'_>,
    field: &'static str,
) -> Result<ApplicationIdV3, CheckpointFinalityCheckerErrorV1> {
    ApplicationIdV3::new(cursor.take_array::<32>()?)
        .map_err(|_| CheckpointFinalityCheckerErrorV1::InvalidTypedField(field))
}

fn take_domain_id(
    cursor: &mut ByteCursorV1<'_>,
    field: &'static str,
) -> Result<DomainIdV3, CheckpointFinalityCheckerErrorV1> {
    DomainIdV3::new(cursor.take_array::<32>()?)
        .map_err(|_| CheckpointFinalityCheckerErrorV1::InvalidTypedField(field))
}

fn take_commitment(
    cursor: &mut ByteCursorV1<'_>,
    field: &'static str,
) -> Result<CommitmentV3, CheckpointFinalityCheckerErrorV1> {
    CommitmentV3::new(cursor.take_array::<32>()?)
        .map_err(|_| CheckpointFinalityCheckerErrorV1::InvalidTypedField(field))
}

fn require_certificate_length(length: usize) -> Result<(), CheckpointFinalityCheckerErrorV1> {
    if length == 0 || length > MAX_CHECKPOINT_FINALITY_CERTIFICATE_BYTES_V2 {
        return Err(CheckpointFinalityCheckerErrorV1::CertificateLength);
    }
    Ok(())
}

fn encode_response_v1(
    fields: CheckpointFinalityCheckerResponseV1,
) -> Result<[u8; RESPONSE_BYTES_V1], CheckpointFinalityCheckerErrorV1> {
    let mut response = [0_u8; RESPONSE_BYTES_V1];
    let mut cursor = 0;
    append_response(&mut response, &mut cursor, &RESPONSE_MAGIC_V1)?;
    append_response(
        &mut response,
        &mut cursor,
        &CHECKER_PROTOCOL_VERSION_V1.to_be_bytes(),
    )?;
    append_response(&mut response, &mut cursor, fields.application_id.as_bytes())?;
    append_response(
        &mut response,
        &mut cursor,
        fields.chain_or_domain_id.as_bytes(),
    )?;
    append_response(&mut response, &mut cursor, &fields.epoch_id.to_be_bytes())?;
    append_response(&mut response, &mut cursor, fields.policy_root.as_bytes())?;
    append_response(
        &mut response,
        &mut cursor,
        fields.certificate_root.as_bytes(),
    )?;
    append_response(
        &mut response,
        &mut cursor,
        &fields.prior_application_checkpoint_sequence.to_be_bytes(),
    )?;
    append_response(
        &mut response,
        &mut cursor,
        fields.prior_application_checkpoint_hash.as_bytes(),
    )?;
    append_response(
        &mut response,
        &mut cursor,
        &fields.next_application_checkpoint_sequence.to_be_bytes(),
    )?;
    append_response(
        &mut response,
        &mut cursor,
        fields.next_application_checkpoint_hash.as_bytes(),
    )?;
    append_response(&mut response, &mut cursor, &fields.exact_certificate_sha256)?;
    append_response(&mut response, &mut cursor, &fields.request_sha256)?;
    if cursor != RESPONSE_BODY_BYTES_V1 {
        return Err(CheckpointFinalityCheckerErrorV1::ResponseEncoding);
    }
    let body = response
        .get(..RESPONSE_BODY_BYTES_V1)
        .ok_or(CheckpointFinalityCheckerErrorV1::ResponseEncoding)?;
    let commitment = response_commitment_v1(body);
    append_response(&mut response, &mut cursor, &commitment)?;
    if cursor != RESPONSE_BYTES_V1 {
        return Err(CheckpointFinalityCheckerErrorV1::ResponseEncoding);
    }
    Ok(response)
}

fn append_response(
    output: &mut [u8; RESPONSE_BYTES_V1],
    cursor: &mut usize,
    value: &[u8],
) -> Result<(), CheckpointFinalityCheckerErrorV1> {
    let end = cursor
        .checked_add(value.len())
        .ok_or(CheckpointFinalityCheckerErrorV1::ResponseEncoding)?;
    let target = output
        .get_mut(*cursor..end)
        .ok_or(CheckpointFinalityCheckerErrorV1::ResponseEncoding)?;
    target.copy_from_slice(value);
    *cursor = end;
    Ok(())
}

fn sha256(value: &[u8]) -> [u8; 32] {
    Sha256::digest(value).into()
}

fn response_commitment_v1(value: &[u8]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(RESPONSE_COMMITMENT_DOMAIN_V1);
    hasher.update(value);
    hasher.finalize().into()
}

struct ByteCursorV1<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> ByteCursorV1<'a> {
    const fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, offset: 0 }
    }

    fn take_u8(&mut self) -> Result<u8, CheckpointFinalityCheckerErrorV1> {
        Ok(self.take_array::<1>()?[0])
    }

    fn take_u16(&mut self) -> Result<u16, CheckpointFinalityCheckerErrorV1> {
        Ok(u16::from_be_bytes(self.take_array::<2>()?))
    }

    fn take_u64(&mut self) -> Result<u64, CheckpointFinalityCheckerErrorV1> {
        Ok(u64::from_be_bytes(self.take_array::<8>()?))
    }

    fn take_array<const N: usize>(&mut self) -> Result<[u8; N], CheckpointFinalityCheckerErrorV1> {
        self.take_slice(N)?
            .try_into()
            .map_err(|_| CheckpointFinalityCheckerErrorV1::RequestSize)
    }

    fn take_slice(&mut self, length: usize) -> Result<&'a [u8], CheckpointFinalityCheckerErrorV1> {
        let end = self
            .offset
            .checked_add(length)
            .ok_or(CheckpointFinalityCheckerErrorV1::ArithmeticOverflow)?;
        let value = self
            .bytes
            .get(self.offset..end)
            .ok_or(CheckpointFinalityCheckerErrorV1::RequestSize)?;
        self.offset = end;
        Ok(value)
    }

    fn is_finished(&self) -> bool {
        self.offset == self.bytes.len()
    }
}
