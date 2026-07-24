use sha2::{Digest, Sha256};
use std::collections::BTreeSet;
use zenodex_zrpf_protocol_v3::{
    check_checkpoint_finality_policy_satisfied_v1, decode_exact_checkpoint_finality_certificate_v1,
    encode_checkpoint_finality_certificate_v1, ApplicationIdV3,
    CheckpointFinalityCertificateErrorV1, CheckpointFinalityCertificateInputV1,
    CheckpointFinalityCertificateV1, CheckpointFinalityPolicyCheckInputV1,
    CheckpointFinalityPolicyErrorV1, CheckpointFinalityPolicyInputV1, CheckpointFinalityPolicyV1,
    CommitmentV3, DomainIdV3, ExpectedFinalizedCheckpointBindingV1,
    CHECKPOINT_FINALITY_CERTIFICATE_VERSION_V1, MAX_CHECKPOINT_FINALITY_CERTIFICATE_BYTES_V1,
};

const CERTIFICATE_ROOT_DOMAIN_V1: &[u8] = b"zenodex.zrpf.checkpoint_finality.certificate_root.v1";
const POLICY_ROOT_DOMAIN_V1: &[u8] = b"zenodex.zrpf.checkpoint_finality.policy_root.v1";

fn application(byte: u8) -> ApplicationIdV3 {
    ApplicationIdV3::new([byte; 32]).expect("fixture application is nonzero")
}

fn domain(byte: u8) -> DomainIdV3 {
    DomainIdV3::new([byte; 32]).expect("fixture domain is nonzero")
}

fn commitment(byte: u8) -> CommitmentV3 {
    CommitmentV3::new([byte; 32]).expect("fixture commitment is nonzero")
}

fn baseline_policy_input() -> CheckpointFinalityPolicyInputV1 {
    CheckpointFinalityPolicyInputV1 {
        application_id: application(1),
        chain_or_domain_id: domain(2),
        finality_network_id: commitment(6),
        finality_protocol_id: commitment(7),
        expected_external_finality_policy_hash: commitment(8),
        expected_finality_verifier_set_root: commitment(9),
        minimum_checkpoint_height: 40,
    }
}

fn policy_from(input: CheckpointFinalityPolicyInputV1) -> CheckpointFinalityPolicyV1 {
    CheckpointFinalityPolicyV1::new(input)
}

fn baseline_policy() -> CheckpointFinalityPolicyV1 {
    policy_from(baseline_policy_input())
}

fn baseline_certificate_input(
    policy: &CheckpointFinalityPolicyV1,
) -> CheckpointFinalityCertificateInputV1 {
    CheckpointFinalityCertificateInputV1 {
        application_id: application(1),
        chain_or_domain_id: domain(2),
        epoch_id: 11,
        proof_journal_hash: commitment(3),
        post_state_root: commitment(4),
        checkpoint_height: 42,
        checkpoint_hash: commitment(5),
        finality_network_id: commitment(6),
        finality_protocol_id: commitment(7),
        external_finality_policy_hash: commitment(8),
        finality_verifier_set_root: commitment(9),
        finality_evidence_root: commitment(10),
        finality_policy_root: policy.policy_root().expect("policy root derives"),
    }
}

fn certificate_from(
    input: CheckpointFinalityCertificateInputV1,
) -> CheckpointFinalityCertificateV1 {
    CheckpointFinalityCertificateV1::derive(input).expect("fixture certificate derives")
}

fn baseline_certificate(policy: &CheckpointFinalityPolicyV1) -> CheckpointFinalityCertificateV1 {
    certificate_from(baseline_certificate_input(policy))
}

fn expected_binding() -> ExpectedFinalizedCheckpointBindingV1 {
    ExpectedFinalizedCheckpointBindingV1 {
        application_id: application(1),
        chain_or_domain_id: domain(2),
        epoch_id: 11,
        proof_journal_hash: commitment(3),
        post_state_root: commitment(4),
        checkpoint_height: 42,
        checkpoint_hash: commitment(5),
        finality_network_id: commitment(6),
        finality_protocol_id: commitment(7),
        external_finality_policy_hash: commitment(8),
        finality_verifier_set_root: commitment(9),
        finality_evidence_root: commitment(10),
    }
}

fn check(
    policy: &CheckpointFinalityPolicyV1,
    certificate: &CheckpointFinalityCertificateV1,
    expected: ExpectedFinalizedCheckpointBindingV1,
) -> Result<(), CheckpointFinalityPolicyErrorV1> {
    check_with_previous(policy, certificate, expected, Some(41))
}

fn check_with_previous(
    policy: &CheckpointFinalityPolicyV1,
    certificate: &CheckpointFinalityCertificateV1,
    expected: ExpectedFinalizedCheckpointBindingV1,
    previously_accepted_checkpoint_height: Option<u64>,
) -> Result<(), CheckpointFinalityPolicyErrorV1> {
    check_checkpoint_finality_policy_satisfied_v1(CheckpointFinalityPolicyCheckInputV1 {
        policy,
        certificate,
        expected,
        previously_accepted_checkpoint_height,
    })
}

fn domain_hasher(domain: &[u8]) -> Sha256 {
    let mut hasher = Sha256::new();
    hasher.update(
        u16::try_from(domain.len())
            .expect("fixture domain length fits")
            .to_be_bytes(),
    );
    hasher.update(domain);
    hasher
}

fn independent_policy_root(policy: &CheckpointFinalityPolicyV1) -> [u8; 32] {
    let mut hasher = domain_hasher(POLICY_ROOT_DOMAIN_V1);
    hasher.update(policy.policy_version().to_be_bytes());
    hasher.update(policy.application_id().as_bytes());
    hasher.update(policy.chain_or_domain_id().as_bytes());
    hasher.update(policy.finality_network_id().as_bytes());
    hasher.update(policy.finality_protocol_id().as_bytes());
    hasher.update(policy.expected_external_finality_policy_hash().as_bytes());
    hasher.update(policy.expected_finality_verifier_set_root().as_bytes());
    hasher.update(policy.minimum_checkpoint_height().to_be_bytes());
    hasher.finalize().into()
}

fn independent_certificate_root(certificate: &CheckpointFinalityCertificateV1) -> [u8; 32] {
    let mut hasher = domain_hasher(CERTIFICATE_ROOT_DOMAIN_V1);
    hasher.update(certificate.certificate_version().to_be_bytes());
    hasher.update(certificate.application_id().as_bytes());
    hasher.update(certificate.chain_or_domain_id().as_bytes());
    hasher.update(certificate.epoch_id().to_be_bytes());
    hasher.update(certificate.proof_journal_hash().as_bytes());
    hasher.update(certificate.post_state_root().as_bytes());
    hasher.update(certificate.checkpoint_height().to_be_bytes());
    hasher.update(certificate.checkpoint_hash().as_bytes());
    hasher.update(certificate.finality_network_id().as_bytes());
    hasher.update(certificate.finality_protocol_id().as_bytes());
    hasher.update(certificate.external_finality_policy_hash().as_bytes());
    hasher.update(certificate.finality_verifier_set_root().as_bytes());
    hasher.update(certificate.finality_evidence_root().as_bytes());
    hasher.update(certificate.finality_policy_root().as_bytes());
    hasher.finalize().into()
}

#[test]
fn exact_governed_binding_satisfies_policy_and_matches_independent_roots() {
    let policy = baseline_policy();
    let certificate = baseline_certificate(&policy);
    check(&policy, &certificate, expected_binding())
        .expect("exact externally supplied checkpoint binding satisfies policy");
    assert_eq!(
        policy.policy_root().unwrap().into_bytes(),
        independent_policy_root(&policy)
    );
    assert_eq!(
        certificate.certificate_root().into_bytes(),
        independent_certificate_root(&certificate)
    );
}

#[test]
fn exact_codec_round_trips_and_rejects_truncation_trailing_and_oversize() {
    let policy = baseline_policy();
    let certificate = baseline_certificate(&policy);
    let bytes =
        encode_checkpoint_finality_certificate_v1(&certificate).expect("certificate encodes");
    assert!(bytes.len() <= MAX_CHECKPOINT_FINALITY_CERTIFICATE_BYTES_V1);
    assert_eq!(
        decode_exact_checkpoint_finality_certificate_v1(&bytes).expect("certificate decodes"),
        certificate
    );
    for end in 0..bytes.len() {
        assert!(decode_exact_checkpoint_finality_certificate_v1(&bytes[..end]).is_err());
    }
    let mut trailing = bytes;
    trailing.push(0);
    assert_eq!(
        decode_exact_checkpoint_finality_certificate_v1(&trailing),
        Err(CheckpointFinalityCertificateErrorV1::TrailingBytes)
    );
    assert!(matches!(
        decode_exact_checkpoint_finality_certificate_v1(&vec![
            0;
            MAX_CHECKPOINT_FINALITY_CERTIFICATE_BYTES_V1
                + 1
        ]),
        Err(CheckpointFinalityCertificateErrorV1::InputTooLarge { .. })
    ));
}

#[test]
fn wire_rejects_unknown_fields_stale_version_and_forged_root() {
    let policy = baseline_policy();
    let certificate = baseline_certificate(&policy);

    let mut unknown = serde_json::to_value(&certificate).expect("certificate renders");
    unknown["unexpected"] = serde_json::json!(1);
    assert!(serde_json::from_value::<CheckpointFinalityCertificateV1>(unknown).is_err());

    let mut stale_version = serde_json::to_value(&certificate).expect("certificate renders");
    stale_version["certificate_version"] =
        serde_json::json!(CHECKPOINT_FINALITY_CERTIFICATE_VERSION_V1 + 1);
    assert!(serde_json::from_value::<CheckpointFinalityCertificateV1>(stale_version).is_err());

    let mut forged_root = serde_json::to_value(&certificate).expect("certificate renders");
    forged_root["certificate_root"] = serde_json::json!(vec![99; 32]);
    assert!(serde_json::from_value::<CheckpointFinalityCertificateV1>(forged_root).is_err());
}

#[test]
fn certificate_has_no_caller_supplied_finality_or_authority_verdict() {
    let policy = baseline_policy();
    let value = serde_json::to_value(baseline_certificate(&policy)).expect("certificate renders");
    let object = value.as_object().expect("certificate is an object");
    for forbidden in [
        "finalized",
        "verified",
        "finality_verified",
        "settlement_authority",
        "production_authority",
    ] {
        assert!(!object.contains_key(forbidden));
    }
}

#[test]
fn certificate_root_separates_every_bound_field() {
    let policy = baseline_policy();
    let input = baseline_certificate_input(&policy);
    let baseline = certificate_from(input).certificate_root();
    let changed = [
        CheckpointFinalityCertificateInputV1 {
            application_id: application(20),
            ..input
        },
        CheckpointFinalityCertificateInputV1 {
            chain_or_domain_id: domain(20),
            ..input
        },
        CheckpointFinalityCertificateInputV1 {
            epoch_id: 20,
            ..input
        },
        CheckpointFinalityCertificateInputV1 {
            proof_journal_hash: commitment(20),
            ..input
        },
        CheckpointFinalityCertificateInputV1 {
            post_state_root: commitment(20),
            ..input
        },
        CheckpointFinalityCertificateInputV1 {
            checkpoint_height: 20,
            ..input
        },
        CheckpointFinalityCertificateInputV1 {
            checkpoint_hash: commitment(20),
            ..input
        },
        CheckpointFinalityCertificateInputV1 {
            finality_network_id: commitment(20),
            ..input
        },
        CheckpointFinalityCertificateInputV1 {
            finality_protocol_id: commitment(20),
            ..input
        },
        CheckpointFinalityCertificateInputV1 {
            external_finality_policy_hash: commitment(20),
            ..input
        },
        CheckpointFinalityCertificateInputV1 {
            finality_verifier_set_root: commitment(20),
            ..input
        },
        CheckpointFinalityCertificateInputV1 {
            finality_evidence_root: commitment(20),
            ..input
        },
        CheckpointFinalityCertificateInputV1 {
            finality_policy_root: commitment(20),
            ..input
        },
    ];
    for changed_input in changed {
        assert_ne!(certificate_from(changed_input).certificate_root(), baseline);
    }
}

#[test]
fn policy_root_separates_every_governed_field() {
    let input = baseline_policy_input();
    let baseline = policy_from(input).policy_root().unwrap();
    let changed = [
        CheckpointFinalityPolicyInputV1 {
            application_id: application(20),
            ..input
        },
        CheckpointFinalityPolicyInputV1 {
            chain_or_domain_id: domain(20),
            ..input
        },
        CheckpointFinalityPolicyInputV1 {
            finality_network_id: commitment(20),
            ..input
        },
        CheckpointFinalityPolicyInputV1 {
            finality_protocol_id: commitment(20),
            ..input
        },
        CheckpointFinalityPolicyInputV1 {
            expected_external_finality_policy_hash: commitment(20),
            ..input
        },
        CheckpointFinalityPolicyInputV1 {
            expected_finality_verifier_set_root: commitment(20),
            ..input
        },
        CheckpointFinalityPolicyInputV1 {
            minimum_checkpoint_height: 41,
            ..input
        },
    ];
    for changed_input in changed {
        assert_ne!(policy_from(changed_input).policy_root().unwrap(), baseline);
    }
}

#[test]
fn policy_rejects_each_scope_protocol_and_policy_substitution() {
    let policy = baseline_policy();
    let input = baseline_certificate_input(&policy);
    let cases = [
        (
            CheckpointFinalityCertificateInputV1 {
                application_id: application(20),
                ..input
            },
            CheckpointFinalityPolicyErrorV1::ApplicationMismatch,
        ),
        (
            CheckpointFinalityCertificateInputV1 {
                chain_or_domain_id: domain(20),
                ..input
            },
            CheckpointFinalityPolicyErrorV1::DomainMismatch,
        ),
        (
            CheckpointFinalityCertificateInputV1 {
                finality_network_id: commitment(20),
                ..input
            },
            CheckpointFinalityPolicyErrorV1::FinalityNetworkMismatch,
        ),
        (
            CheckpointFinalityCertificateInputV1 {
                finality_protocol_id: commitment(20),
                ..input
            },
            CheckpointFinalityPolicyErrorV1::FinalityProtocolMismatch,
        ),
        (
            CheckpointFinalityCertificateInputV1 {
                external_finality_policy_hash: commitment(20),
                ..input
            },
            CheckpointFinalityPolicyErrorV1::ExternalFinalityPolicyMismatch,
        ),
        (
            CheckpointFinalityCertificateInputV1 {
                finality_verifier_set_root: commitment(20),
                ..input
            },
            CheckpointFinalityPolicyErrorV1::FinalityVerifierSetMismatch,
        ),
        (
            CheckpointFinalityCertificateInputV1 {
                checkpoint_height: 39,
                ..input
            },
            CheckpointFinalityPolicyErrorV1::CheckpointBelowMinimum {
                actual: 39,
                minimum: 40,
            },
        ),
        (
            CheckpointFinalityCertificateInputV1 {
                finality_policy_root: commitment(20),
                ..input
            },
            CheckpointFinalityPolicyErrorV1::FinalityPolicyRootMismatch,
        ),
    ];
    for (changed, error) in cases {
        assert_eq!(
            check(&policy, &certificate_from(changed), expected_binding()),
            Err(error)
        );
    }
}

#[test]
fn policy_rejects_each_authenticated_checkpoint_binding_substitution() {
    let policy = baseline_policy();
    let certificate = baseline_certificate(&policy);
    let expected = expected_binding();
    let cases = [
        (
            ExpectedFinalizedCheckpointBindingV1 {
                application_id: application(20),
                ..expected
            },
            CheckpointFinalityPolicyErrorV1::ExpectedApplicationMismatch,
        ),
        (
            ExpectedFinalizedCheckpointBindingV1 {
                chain_or_domain_id: domain(20),
                ..expected
            },
            CheckpointFinalityPolicyErrorV1::ExpectedDomainMismatch,
        ),
        (
            ExpectedFinalizedCheckpointBindingV1 {
                epoch_id: 12,
                ..expected
            },
            CheckpointFinalityPolicyErrorV1::EpochMismatch {
                actual: 11,
                expected: 12,
            },
        ),
        (
            ExpectedFinalizedCheckpointBindingV1 {
                proof_journal_hash: commitment(20),
                ..expected
            },
            CheckpointFinalityPolicyErrorV1::ProofJournalMismatch,
        ),
        (
            ExpectedFinalizedCheckpointBindingV1 {
                post_state_root: commitment(20),
                ..expected
            },
            CheckpointFinalityPolicyErrorV1::PostStateRootMismatch,
        ),
        (
            ExpectedFinalizedCheckpointBindingV1 {
                checkpoint_height: 43,
                ..expected
            },
            CheckpointFinalityPolicyErrorV1::CheckpointHeightMismatch {
                actual: 42,
                expected: 43,
            },
        ),
        (
            ExpectedFinalizedCheckpointBindingV1 {
                checkpoint_hash: commitment(20),
                ..expected
            },
            CheckpointFinalityPolicyErrorV1::CheckpointHashMismatch,
        ),
        (
            ExpectedFinalizedCheckpointBindingV1 {
                finality_network_id: commitment(20),
                ..expected
            },
            CheckpointFinalityPolicyErrorV1::ExpectedFinalityNetworkMismatch,
        ),
        (
            ExpectedFinalizedCheckpointBindingV1 {
                finality_protocol_id: commitment(20),
                ..expected
            },
            CheckpointFinalityPolicyErrorV1::ExpectedFinalityProtocolMismatch,
        ),
        (
            ExpectedFinalizedCheckpointBindingV1 {
                external_finality_policy_hash: commitment(20),
                ..expected
            },
            CheckpointFinalityPolicyErrorV1::ExpectedExternalFinalityPolicyMismatch,
        ),
        (
            ExpectedFinalizedCheckpointBindingV1 {
                finality_verifier_set_root: commitment(20),
                ..expected
            },
            CheckpointFinalityPolicyErrorV1::ExpectedFinalityVerifierSetMismatch,
        ),
        (
            ExpectedFinalizedCheckpointBindingV1 {
                finality_evidence_root: commitment(20),
                ..expected
            },
            CheckpointFinalityPolicyErrorV1::FinalityEvidenceMismatch,
        ),
    ];
    for (changed, error) in cases {
        assert_eq!(check(&policy, &certificate, changed), Err(error));
    }
}

#[test]
fn policy_requires_strict_checkpoint_height_advance_from_the_admission_cursor() {
    let policy = baseline_policy();
    let certificate = baseline_certificate(&policy);
    let expected = expected_binding();

    check_with_previous(&policy, &certificate, expected, None)
        .expect("an empty admission cursor permits the governed initial checkpoint");
    check_with_previous(&policy, &certificate, expected, Some(41))
        .expect("the next checkpoint strictly advances the admission cursor");
    for previous in [42, 43] {
        assert_eq!(
            check_with_previous(&policy, &certificate, expected, Some(previous)),
            Err(
                CheckpointFinalityPolicyErrorV1::CheckpointNotNewerThanAccepted {
                    actual: 42,
                    previous,
                }
            )
        );
    }
}

#[derive(Clone, Copy)]
enum CertificateMutation {
    Application,
    Domain,
    Epoch,
    ProofJournal,
    PostState,
    CheckpointHeight,
    CheckpointHash,
    FinalityNetwork,
    FinalityProtocol,
    ExternalPolicy,
    VerifierSet,
    Evidence,
    LocalPolicyRoot,
}

fn apply_certificate_mutation(
    input: CheckpointFinalityCertificateInputV1,
    mutation: CertificateMutation,
) -> CheckpointFinalityCertificateInputV1 {
    match mutation {
        CertificateMutation::Application => CheckpointFinalityCertificateInputV1 {
            application_id: application(20),
            ..input
        },
        CertificateMutation::Domain => CheckpointFinalityCertificateInputV1 {
            chain_or_domain_id: domain(20),
            ..input
        },
        CertificateMutation::Epoch => CheckpointFinalityCertificateInputV1 {
            epoch_id: 20,
            ..input
        },
        CertificateMutation::ProofJournal => CheckpointFinalityCertificateInputV1 {
            proof_journal_hash: commitment(20),
            ..input
        },
        CertificateMutation::PostState => CheckpointFinalityCertificateInputV1 {
            post_state_root: commitment(20),
            ..input
        },
        CertificateMutation::CheckpointHeight => CheckpointFinalityCertificateInputV1 {
            checkpoint_height: 43,
            ..input
        },
        CertificateMutation::CheckpointHash => CheckpointFinalityCertificateInputV1 {
            checkpoint_hash: commitment(20),
            ..input
        },
        CertificateMutation::FinalityNetwork => CheckpointFinalityCertificateInputV1 {
            finality_network_id: commitment(20),
            ..input
        },
        CertificateMutation::FinalityProtocol => CheckpointFinalityCertificateInputV1 {
            finality_protocol_id: commitment(20),
            ..input
        },
        CertificateMutation::ExternalPolicy => CheckpointFinalityCertificateInputV1 {
            external_finality_policy_hash: commitment(20),
            ..input
        },
        CertificateMutation::VerifierSet => CheckpointFinalityCertificateInputV1 {
            finality_verifier_set_root: commitment(20),
            ..input
        },
        CertificateMutation::Evidence => CheckpointFinalityCertificateInputV1 {
            finality_evidence_root: commitment(20),
            ..input
        },
        CertificateMutation::LocalPolicyRoot => CheckpointFinalityCertificateInputV1 {
            finality_policy_root: commitment(20),
            ..input
        },
    }
}

#[test]
fn bounded_depth_two_structure_preserving_mutation_atlas_never_accepts() {
    let policy = baseline_policy();
    let input = baseline_certificate_input(&policy);
    let expected = expected_binding();
    let mutations = [
        CertificateMutation::Application,
        CertificateMutation::Domain,
        CertificateMutation::Epoch,
        CertificateMutation::ProofJournal,
        CertificateMutation::PostState,
        CertificateMutation::CheckpointHeight,
        CertificateMutation::CheckpointHash,
        CertificateMutation::FinalityNetwork,
        CertificateMutation::FinalityProtocol,
        CertificateMutation::ExternalPolicy,
        CertificateMutation::VerifierSet,
        CertificateMutation::Evidence,
        CertificateMutation::LocalPolicyRoot,
    ];
    let mut depth_one_outcomes = BTreeSet::new();
    for mutation in mutations {
        let certificate = certificate_from(apply_certificate_mutation(input, mutation));
        let error = check(&policy, &certificate, expected)
            .expect_err("every one-field semantic mutation must reject");
        depth_one_outcomes.insert(format!("{error:?}"));
    }
    assert_eq!(depth_one_outcomes.len(), mutations.len());

    for (first_index, first) in mutations.iter().copied().enumerate() {
        for second in mutations.iter().copied().skip(first_index + 1) {
            let twice =
                apply_certificate_mutation(apply_certificate_mutation(input, first), second);
            let certificate = certificate_from(twice);
            assert!(
                check(&policy, &certificate, expected).is_err(),
                "every bounded depth-two semantic mutation must reject"
            );
        }
    }
}

#[test]
fn every_single_bit_certificate_encoding_mutation_rejects() {
    let policy = baseline_policy();
    let certificate = baseline_certificate(&policy);
    let bytes =
        encode_checkpoint_finality_certificate_v1(&certificate).expect("certificate encodes");
    for index in 0..bytes.len() {
        for bit in 0..8 {
            let mut mutated = bytes.clone();
            mutated[index] ^= 1 << bit;
            assert!(
                decode_exact_checkpoint_finality_certificate_v1(&mutated).is_err(),
                "byte {index}, bit {bit} changed without rejection"
            );
        }
    }
}
