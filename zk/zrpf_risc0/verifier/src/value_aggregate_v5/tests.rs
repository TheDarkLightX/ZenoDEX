use std::collections::BTreeSet;

use risc0_zkvm::{FakeReceipt, Receipt, ReceiptClaim};
use zenodex_zrpf_protocol_v3::{CommitmentV3, NodeLevelV3, ProfileIdV3};

use super::{
    derive_certificate_identity_binding_v5, require_exact_proposal_bytes,
    require_expected_aggregate_level, verified_program_id, ExpectedValueAggregateReceiptIdentityV5,
    VerifiedValueAggregateReceiptErrorV5, VerifiedValueAggregateReceiptV5,
};
use crate::{VerifiedNodeReceiptErrorV3, MAX_CANONICAL_RECEIPT_BYTES_V3};

const IMAGE_ID: [u32; 8] = [1, 2, 3, 4, 5, 6, 7, 8];

fn identity() -> ExpectedValueAggregateReceiptIdentityV5 {
    ExpectedValueAggregateReceiptIdentityV5::new(
        NodeLevelV3::new(1).expect("aggregate level"),
        ProfileIdV3::new([9; 32]).expect("nonzero profile"),
        CommitmentV3::new([10; 32]).expect("nonzero manifest"),
    )
    .expect("expected identity")
}

#[test]
fn reject_codes_are_stable_and_unique() {
    let errors = [
        VerifiedValueAggregateReceiptErrorV5::InvalidExpectedAggregateLevel,
        VerifiedValueAggregateReceiptErrorV5::ReceiptArtifact(
            VerifiedNodeReceiptErrorV3::EmptyReceiptBytes,
        ),
        VerifiedValueAggregateReceiptErrorV5::ProposalDecodeFailed,
        VerifiedValueAggregateReceiptErrorV5::AggregateLevelMismatch,
        VerifiedValueAggregateReceiptErrorV5::ProgramIdDerivationFailed,
        VerifiedValueAggregateReceiptErrorV5::ClaimBindingFailed,
        VerifiedValueAggregateReceiptErrorV5::IdentityBindingFailed,
        VerifiedValueAggregateReceiptErrorV5::ExpectedProposalEncodingFailed,
        VerifiedValueAggregateReceiptErrorV5::ProposalBytesMismatch,
    ];
    let codes = errors
        .iter()
        .map(|error| error.code())
        .collect::<BTreeSet<_>>();
    assert_eq!(codes.len(), errors.len());
}

#[test]
fn receipt_boundary_rejects_zero_empty_oversized_noncanonical_and_fake() {
    assert_eq!(
        VerifiedValueAggregateReceiptV5::verify_canonical_succinct_bytes(
            b"{}",
            [0; 8],
            identity(),
        )
        .err(),
        Some(VerifiedValueAggregateReceiptErrorV5::ReceiptArtifact(
            VerifiedNodeReceiptErrorV3::ZeroExpectedImageId,
        ))
    );
    assert_eq!(
        VerifiedValueAggregateReceiptV5::verify_canonical_succinct_bytes(
            &[],
            IMAGE_ID,
            identity(),
        )
        .err(),
        Some(VerifiedValueAggregateReceiptErrorV5::ReceiptArtifact(
            VerifiedNodeReceiptErrorV3::EmptyReceiptBytes,
        ))
    );
    let oversized = vec![0_u8; MAX_CANONICAL_RECEIPT_BYTES_V3 + 1];
    assert_eq!(
        VerifiedValueAggregateReceiptV5::verify_canonical_succinct_bytes(
            &oversized,
            IMAGE_ID,
            identity(),
        )
        .err(),
        Some(VerifiedValueAggregateReceiptErrorV5::ReceiptArtifact(
            VerifiedNodeReceiptErrorV3::ReceiptBytesTooLarge {
                actual: MAX_CANONICAL_RECEIPT_BYTES_V3 + 1,
                maximum: MAX_CANONICAL_RECEIPT_BYTES_V3,
            },
        ))
    );

    let fake = Receipt::try_from(FakeReceipt::new(ReceiptClaim::ok(
        IMAGE_ID,
        b"proof-neutral-v5-proposal".to_vec(),
    )))
    .expect("fake receipt conversion");
    let canonical = serde_json::to_vec(&fake).expect("canonical fake receipt");
    let mut whitespace = vec![b' '];
    whitespace.extend_from_slice(&canonical);
    assert_eq!(
        VerifiedValueAggregateReceiptV5::verify_canonical_succinct_bytes(
            &whitespace,
            IMAGE_ID,
            identity(),
        )
        .err(),
        Some(VerifiedValueAggregateReceiptErrorV5::ReceiptArtifact(
            VerifiedNodeReceiptErrorV3::NonCanonicalReceiptJson,
        ))
    );
    assert_eq!(
        VerifiedValueAggregateReceiptV5::verify_canonical_succinct_bytes(
            &canonical,
            IMAGE_ID,
            identity(),
        )
        .err(),
        Some(VerifiedValueAggregateReceiptErrorV5::ReceiptArtifact(
            VerifiedNodeReceiptErrorV3::NonSuccinctReceipt,
        ))
    );
}

#[test]
fn program_and_governed_identity_are_independent_typed_bindings() {
    let expected = identity();
    let program = verified_program_id(IMAGE_ID).expect("program ID");
    let other_program = verified_program_id([8, 7, 6, 5, 4, 3, 2, 1]).expect("other program ID");

    assert_ne!(program, other_program);
    assert_eq!(expected.aggregate_level().get(), 1);
    assert_eq!(
        expected.proof_profile_id(),
        ProfileIdV3::new([9; 32]).expect("profile")
    );
    assert_eq!(
        expected.program_manifest_root(),
        CommitmentV3::new([10; 32]).expect("manifest")
    );
}

#[test]
fn leaf_level_cannot_be_used_as_an_aggregate_expectation() {
    assert_eq!(
        ExpectedValueAggregateReceiptIdentityV5::new(
            NodeLevelV3::LEAF,
            ProfileIdV3::new([9; 32]).expect("profile"),
            CommitmentV3::new([10; 32]).expect("manifest"),
        ),
        Err(VerifiedValueAggregateReceiptErrorV5::InvalidExpectedAggregateLevel)
    );
}

#[test]
fn authenticated_proposal_level_must_match_the_outer_expectation() {
    assert_eq!(require_expected_aggregate_level(1, identity()), Ok(()));
    assert_eq!(
        require_expected_aggregate_level(2, identity()),
        Err(VerifiedValueAggregateReceiptErrorV5::AggregateLevelMismatch)
    );
}

#[test]
fn certificate_identity_binding_commits_every_outer_identity_field() {
    let expected = identity();
    let claim = CommitmentV3::new([11; 32]).expect("claim");
    let program = verified_program_id(IMAGE_ID).expect("program");
    let baseline =
        derive_certificate_identity_binding_v5(claim, program, expected).expect("baseline binding");
    let other_profile = ExpectedValueAggregateReceiptIdentityV5::new(
        expected.aggregate_level(),
        ProfileIdV3::new([12; 32]).expect("profile"),
        expected.program_manifest_root(),
    )
    .expect("other profile identity");
    let other_manifest = ExpectedValueAggregateReceiptIdentityV5::new(
        expected.aggregate_level(),
        expected.proof_profile_id(),
        CommitmentV3::new([13; 32]).expect("manifest"),
    )
    .expect("other manifest identity");
    let other_level = ExpectedValueAggregateReceiptIdentityV5::new(
        NodeLevelV3::new(2).expect("level two"),
        expected.proof_profile_id(),
        expected.program_manifest_root(),
    )
    .expect("other level identity");

    for changed in [
        derive_certificate_identity_binding_v5(claim, program, other_profile),
        derive_certificate_identity_binding_v5(claim, program, other_manifest),
        derive_certificate_identity_binding_v5(claim, program, other_level),
        derive_certificate_identity_binding_v5(
            CommitmentV3::new([14; 32]).expect("other claim"),
            program,
            expected,
        ),
        derive_certificate_identity_binding_v5(
            claim,
            verified_program_id([8, 7, 6, 5, 4, 3, 2, 1]).expect("other program"),
            expected,
        ),
    ] {
        assert_ne!(baseline, changed.expect("changed binding"));
    }
}

#[test]
fn exact_proposal_bytes_reject_substitution_and_mutation() {
    require_exact_proposal_bytes(b"proposal", b"proposal").expect("exact proposal");
    assert_eq!(
        require_exact_proposal_bytes(b"substituted", b"proposal"),
        Err(VerifiedValueAggregateReceiptErrorV5::ProposalBytesMismatch)
    );
    assert_eq!(
        require_exact_proposal_bytes(b"proposal\0", b"proposal"),
        Err(VerifiedValueAggregateReceiptErrorV5::ProposalBytesMismatch)
    );
}
