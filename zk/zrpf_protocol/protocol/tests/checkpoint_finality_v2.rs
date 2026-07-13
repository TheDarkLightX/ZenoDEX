use sha2::{Digest, Sha256};
use std::collections::BTreeSet;
use zenodex_zrpf_protocol_v3::{
    check_checkpoint_finality_policy_satisfied_v2, decode_exact_checkpoint_finality_certificate_v2,
    encode_checkpoint_finality_certificate_v2, ApplicationIdV3,
    CheckedCheckpointFinalityTransitionV2, CheckpointCursorProposalV2,
    CheckpointFinalityCertificateErrorV2, CheckpointFinalityCertificateInputV2,
    CheckpointFinalityCertificateV2, CheckpointFinalityPolicyCheckInputV2,
    CheckpointFinalityPolicyErrorV2, CheckpointFinalityPolicyInputV2, CheckpointFinalityPolicyV2,
    CommitmentV3, DomainIdV3, ProposedPriorApplicationCheckpointRecordInputV2,
    ProposedPriorApplicationCheckpointRecordV2, SuppliedCheckpointFinalityBindingV2,
    CHECKPOINT_FINALITY_CERTIFICATE_VERSION_V2, CHECKPOINT_FINALITY_POLICY_VERSION_V2,
    MAX_CHECKPOINT_FINALITY_CERTIFICATE_BYTES_V2,
};

const CERTIFICATE_ROOT_DOMAIN_V2: &[u8] = b"zenodex.zrpf.checkpoint_finality.certificate_root.v2";
const POLICY_ROOT_DOMAIN_V2: &[u8] = b"zenodex.zrpf.checkpoint_finality.policy_root.v2";

fn application(byte: u8) -> ApplicationIdV3 {
    ApplicationIdV3::new([byte; 32]).expect("fixture application is nonzero")
}

fn domain(byte: u8) -> DomainIdV3 {
    DomainIdV3::new([byte; 32]).expect("fixture domain is nonzero")
}

fn commitment(byte: u8) -> CommitmentV3 {
    CommitmentV3::new([byte; 32]).expect("fixture commitment is nonzero")
}

fn baseline_policy_input() -> CheckpointFinalityPolicyInputV2 {
    CheckpointFinalityPolicyInputV2 {
        application_id: application(1),
        chain_or_domain_id: domain(2),
        finality_network_id: commitment(6),
        finality_protocol_id: commitment(7),
        expected_external_finality_policy_hash: commitment(8),
        expected_finality_verifier_set_root: commitment(9),
        genesis_application_checkpoint_sequence: 41,
        genesis_application_checkpoint_hash: commitment(5),
    }
}

fn policy_from(input: CheckpointFinalityPolicyInputV2) -> CheckpointFinalityPolicyV2 {
    CheckpointFinalityPolicyV2::new(input)
}

fn baseline_policy() -> CheckpointFinalityPolicyV2 {
    policy_from(baseline_policy_input())
}

fn baseline_certificate_input(
    policy: &CheckpointFinalityPolicyV2,
) -> CheckpointFinalityCertificateInputV2 {
    CheckpointFinalityCertificateInputV2 {
        application_id: application(1),
        chain_or_domain_id: domain(2),
        epoch_id: 11,
        proof_journal_hash: commitment(3),
        post_state_root: commitment(4),
        application_checkpoint_sequence: 42,
        application_checkpoint_hash: commitment(11),
        parent_application_checkpoint_hash: commitment(5),
        finality_network_id: commitment(6),
        finality_protocol_id: commitment(7),
        external_finality_policy_hash: commitment(8),
        finality_verifier_set_root: commitment(9),
        finality_evidence_root: commitment(10),
        finality_policy_root: policy.policy_root().expect("policy root derives"),
    }
}

fn certificate_from(
    input: CheckpointFinalityCertificateInputV2,
) -> CheckpointFinalityCertificateV2 {
    CheckpointFinalityCertificateV2::derive(input).expect("fixture certificate derives")
}

fn baseline_certificate(policy: &CheckpointFinalityPolicyV2) -> CheckpointFinalityCertificateV2 {
    certificate_from(baseline_certificate_input(policy))
}

fn supplied_binding() -> SuppliedCheckpointFinalityBindingV2 {
    SuppliedCheckpointFinalityBindingV2 {
        application_id: application(1),
        chain_or_domain_id: domain(2),
        epoch_id: 11,
        proof_journal_hash: commitment(3),
        post_state_root: commitment(4),
        application_checkpoint_sequence: 42,
        application_checkpoint_hash: commitment(11),
        parent_application_checkpoint_hash: commitment(5),
        finality_network_id: commitment(6),
        finality_protocol_id: commitment(7),
        external_finality_policy_hash: commitment(8),
        finality_verifier_set_root: commitment(9),
        finality_evidence_root: commitment(10),
    }
}

fn prior_record_input(
    policy: &CheckpointFinalityPolicyV2,
) -> ProposedPriorApplicationCheckpointRecordInputV2 {
    ProposedPriorApplicationCheckpointRecordInputV2 {
        application_id: policy.application_id(),
        chain_or_domain_id: policy.chain_or_domain_id(),
        finality_network_id: policy.finality_network_id(),
        finality_protocol_id: policy.finality_protocol_id(),
        external_finality_policy_hash: policy.expected_external_finality_policy_hash(),
        finality_verifier_set_root: policy.expected_finality_verifier_set_root(),
        finality_policy_root: policy.policy_root().expect("policy root derives"),
        application_checkpoint_sequence: 41,
        application_checkpoint_hash: commitment(5),
    }
}

fn prior_cursor_proposal(policy: &CheckpointFinalityPolicyV2) -> CheckpointCursorProposalV2 {
    CheckpointCursorProposalV2::from_prior_record(ProposedPriorApplicationCheckpointRecordV2::new(
        prior_record_input(policy),
    ))
}

fn check(
    policy: &CheckpointFinalityPolicyV2,
    certificate: &CheckpointFinalityCertificateV2,
    expected: SuppliedCheckpointFinalityBindingV2,
    prior_cursor_proposal: CheckpointCursorProposalV2,
) -> Result<CheckedCheckpointFinalityTransitionV2, CheckpointFinalityPolicyErrorV2> {
    check_checkpoint_finality_policy_satisfied_v2(CheckpointFinalityPolicyCheckInputV2 {
        policy,
        certificate,
        expected,
        prior_cursor_proposal,
    })
}

fn independent_certificate_root(input: CheckpointFinalityCertificateInputV2) -> CommitmentV3 {
    let mut hasher = Sha256::new();
    hasher.update(
        u16::try_from(CERTIFICATE_ROOT_DOMAIN_V2.len())
            .expect("domain length fits")
            .to_be_bytes(),
    );
    hasher.update(CERTIFICATE_ROOT_DOMAIN_V2);
    hasher.update(CHECKPOINT_FINALITY_CERTIFICATE_VERSION_V2.to_be_bytes());
    hasher.update(input.application_id.as_bytes());
    hasher.update(input.chain_or_domain_id.as_bytes());
    hasher.update(input.epoch_id.to_be_bytes());
    hasher.update(input.proof_journal_hash.as_bytes());
    hasher.update(input.post_state_root.as_bytes());
    hasher.update(input.application_checkpoint_sequence.to_be_bytes());
    hasher.update(input.application_checkpoint_hash.as_bytes());
    hasher.update(input.parent_application_checkpoint_hash.as_bytes());
    hasher.update(input.finality_network_id.as_bytes());
    hasher.update(input.finality_protocol_id.as_bytes());
    hasher.update(input.external_finality_policy_hash.as_bytes());
    hasher.update(input.finality_verifier_set_root.as_bytes());
    hasher.update(input.finality_evidence_root.as_bytes());
    hasher.update(input.finality_policy_root.as_bytes());
    CommitmentV3::new(hasher.finalize().into()).expect("fixture root is nonzero")
}

fn independent_policy_root(input: CheckpointFinalityPolicyInputV2) -> CommitmentV3 {
    let mut hasher = Sha256::new();
    hasher.update(
        u16::try_from(POLICY_ROOT_DOMAIN_V2.len())
            .expect("domain length fits")
            .to_be_bytes(),
    );
    hasher.update(POLICY_ROOT_DOMAIN_V2);
    hasher.update(CHECKPOINT_FINALITY_POLICY_VERSION_V2.to_be_bytes());
    hasher.update(input.application_id.as_bytes());
    hasher.update(input.chain_or_domain_id.as_bytes());
    hasher.update(input.finality_network_id.as_bytes());
    hasher.update(input.finality_protocol_id.as_bytes());
    hasher.update(input.expected_external_finality_policy_hash.as_bytes());
    hasher.update(input.expected_finality_verifier_set_root.as_bytes());
    hasher.update(input.genesis_application_checkpoint_sequence.to_be_bytes());
    hasher.update(input.genesis_application_checkpoint_hash.as_bytes());
    CommitmentV3::new(hasher.finalize().into()).expect("fixture root is nonzero")
}

#[test]
fn independent_root_recomputation_matches_protocol() {
    let policy_input = baseline_policy_input();
    let policy = policy_from(policy_input);
    assert_eq!(
        policy.policy_root().expect("policy root derives"),
        independent_policy_root(policy_input)
    );
    let certificate_input = baseline_certificate_input(&policy);
    assert_eq!(
        certificate_from(certificate_input).certificate_root(),
        independent_certificate_root(certificate_input)
    );
}

#[test]
fn exact_codec_round_trip_and_bounds_fail_closed() {
    let policy = baseline_policy();
    let certificate = baseline_certificate(&policy);
    let bytes =
        encode_checkpoint_finality_certificate_v2(&certificate).expect("certificate encodes");
    assert!(bytes.len() <= MAX_CHECKPOINT_FINALITY_CERTIFICATE_BYTES_V2);
    assert_eq!(
        decode_exact_checkpoint_finality_certificate_v2(&bytes).expect("certificate decodes"),
        certificate
    );
    assert_eq!(
        decode_exact_checkpoint_finality_certificate_v2(&[]),
        Err(CheckpointFinalityCertificateErrorV2::EmptyInput)
    );
    assert_eq!(
        decode_exact_checkpoint_finality_certificate_v2(&vec![
            0;
            MAX_CHECKPOINT_FINALITY_CERTIFICATE_BYTES_V2
                + 1
        ]),
        Err(CheckpointFinalityCertificateErrorV2::InputTooLarge {
            actual: MAX_CHECKPOINT_FINALITY_CERTIFICATE_BYTES_V2 + 1,
            maximum: MAX_CHECKPOINT_FINALITY_CERTIFICATE_BYTES_V2,
        })
    );
    for end in 1..bytes.len() {
        assert!(
            decode_exact_checkpoint_finality_certificate_v2(&bytes[..end]).is_err(),
            "truncated prefix {end} accepted"
        );
    }
    let mut trailing = bytes;
    trailing.push(0);
    assert_eq!(
        decode_exact_checkpoint_finality_certificate_v2(&trailing),
        Err(CheckpointFinalityCertificateErrorV2::TrailingBytes)
    );

    let mut noncanonical_version = Vec::with_capacity(trailing.len());
    noncanonical_version.extend_from_slice(&[0x82, 0x00]);
    noncanonical_version.extend_from_slice(&trailing[1..trailing.len() - 1]);
    assert_eq!(
        decode_exact_checkpoint_finality_certificate_v2(&noncanonical_version),
        Err(CheckpointFinalityCertificateErrorV2::NonCanonicalEncoding)
    );
}

#[test]
fn json_boundary_rejects_unknown_fields_stale_versions_and_forged_roots() {
    let policy = baseline_policy();
    let certificate = baseline_certificate(&policy);
    let canonical = serde_json::to_value(&certificate).expect("certificate serializes");

    let mut unknown = canonical.clone();
    unknown
        .as_object_mut()
        .expect("certificate JSON is an object")
        .insert("finalized".to_owned(), serde_json::Value::Bool(true));
    assert!(
        serde_json::from_value::<CheckpointFinalityCertificateV2>(unknown).is_err(),
        "unknown caller verdict field accepted"
    );

    let mut stale = canonical.clone();
    stale
        .as_object_mut()
        .expect("certificate JSON is an object")
        .insert("certificate_version".to_owned(), serde_json::json!(1));
    let stale_error = serde_json::from_value::<CheckpointFinalityCertificateV2>(stale)
        .expect_err("stale version must reject")
        .to_string();
    assert!(stale_error.contains("invalid checkpoint finality V2 certificate version"));

    let mut forged = canonical;
    forged
        .as_object_mut()
        .expect("certificate JSON is an object")
        .insert(
            "certificate_root".to_owned(),
            serde_json::to_value(commitment(99)).expect("commitment serializes"),
        );
    let forged_error = serde_json::from_value::<CheckpointFinalityCertificateV2>(forged)
        .expect_err("forged certificate root must reject")
        .to_string();
    assert!(forged_error.contains("certificate root mismatch"));
}

#[test]
fn certificate_exposes_no_caller_verdict_boolean() {
    let policy = baseline_policy();
    let value =
        serde_json::to_value(baseline_certificate(&policy)).expect("certificate serializes");
    let keys = value
        .as_object()
        .expect("certificate JSON is an object")
        .keys()
        .map(String::as_str)
        .collect::<BTreeSet<_>>();
    for forbidden in [
        "ok",
        "verified",
        "finalized",
        "settlement_authority",
        "production_authority",
    ] {
        assert!(!keys.contains(forbidden));
    }
}

#[test]
fn empty_cursor_uses_exact_governed_genesis_anchor() {
    let policy = baseline_policy();
    let certificate = baseline_certificate(&policy);
    let _checked_transition = check(
        &policy,
        &certificate,
        supplied_binding(),
        CheckpointCursorProposalV2::empty(),
    )
    .expect("first checkpoint exactly succeeds the governed genesis anchor");

    for (sequence, parent, expected_error) in [
        (
            43,
            commitment(5),
            CheckpointFinalityPolicyErrorV2::ApplicationCheckpointIsNotExactSuccessor {
                actual: 43,
                expected: 42,
                prior: 41,
            },
        ),
        (
            41,
            commitment(5),
            CheckpointFinalityPolicyErrorV2::ApplicationCheckpointIsNotExactSuccessor {
                actual: 41,
                expected: 42,
                prior: 41,
            },
        ),
        (
            42,
            commitment(20),
            CheckpointFinalityPolicyErrorV2::ApplicationCheckpointParentDoesNotMatchPrior {
                actual: commitment(20),
                expected: commitment(5),
            },
        ),
    ] {
        let input = CheckpointFinalityCertificateInputV2 {
            application_checkpoint_sequence: sequence,
            parent_application_checkpoint_hash: parent,
            ..baseline_certificate_input(&policy)
        };
        let expected = SuppliedCheckpointFinalityBindingV2 {
            application_checkpoint_sequence: sequence,
            parent_application_checkpoint_hash: parent,
            ..supplied_binding()
        };
        assert_eq!(
            check(
                &policy,
                &certificate_from(input),
                expected,
                CheckpointCursorProposalV2::empty(),
            ),
            Err(expected_error)
        );
    }
}

#[test]
fn proposed_prior_record_requires_exact_next_sequence_and_parent_hash() {
    let policy = baseline_policy();
    let certificate = baseline_certificate(&policy);
    let _checked_transition = check(
        &policy,
        &certificate,
        supplied_binding(),
        prior_cursor_proposal(&policy),
    )
    .expect("candidate exactly succeeds proposed prior record");

    let next_input = CheckpointFinalityCertificateInputV2 {
        application_checkpoint_sequence: 43,
        application_checkpoint_hash: commitment(12),
        parent_application_checkpoint_hash: commitment(11),
        ..baseline_certificate_input(&policy)
    };
    let next_expected = SuppliedCheckpointFinalityBindingV2 {
        application_checkpoint_sequence: 43,
        application_checkpoint_hash: commitment(12),
        parent_application_checkpoint_hash: commitment(11),
        ..supplied_binding()
    };
    let next_cursor = CheckpointCursorProposalV2::from_prior_record(
        ProposedPriorApplicationCheckpointRecordV2::new(
            ProposedPriorApplicationCheckpointRecordInputV2 {
                application_checkpoint_sequence: 42,
                application_checkpoint_hash: commitment(11),
                ..prior_record_input(&policy)
            },
        ),
    );
    let _checked_transition = check(
        &policy,
        &certificate_from(next_input),
        next_expected,
        next_cursor,
    )
    .expect("second candidate exactly succeeds first checked application checkpoint");

    for sequence in [40, 41, 43, 44] {
        let input = CheckpointFinalityCertificateInputV2 {
            application_checkpoint_sequence: sequence,
            ..baseline_certificate_input(&policy)
        };
        let expected = SuppliedCheckpointFinalityBindingV2 {
            application_checkpoint_sequence: sequence,
            ..supplied_binding()
        };
        assert_eq!(
            check(
                &policy,
                &certificate_from(input),
                expected,
                prior_cursor_proposal(&policy),
            ),
            Err(
                CheckpointFinalityPolicyErrorV2::ApplicationCheckpointIsNotExactSuccessor {
                    actual: sequence,
                    expected: 42,
                    prior: 41,
                }
            )
        );
    }

    let wrong_parent_input = CheckpointFinalityCertificateInputV2 {
        parent_application_checkpoint_hash: commitment(20),
        ..baseline_certificate_input(&policy)
    };
    let wrong_parent_expected = SuppliedCheckpointFinalityBindingV2 {
        parent_application_checkpoint_hash: commitment(20),
        ..supplied_binding()
    };
    assert_eq!(
        check(
            &policy,
            &certificate_from(wrong_parent_input),
            wrong_parent_expected,
            prior_cursor_proposal(&policy),
        ),
        Err(
            CheckpointFinalityPolicyErrorV2::ApplicationCheckpointParentDoesNotMatchPrior {
                actual: commitment(20),
                expected: commitment(5),
            }
        )
    );
}

#[test]
fn checked_transition_retains_exact_inputs_and_derives_next_cursor() {
    let policy = baseline_policy();
    let certificate = baseline_certificate(&policy);
    let expected = supplied_binding();
    let prior = prior_cursor_proposal(&policy);
    let checked = check(&policy, &certificate, expected, prior)
        .expect("complete policy and continuity check succeeds");

    assert_eq!(
        checked.policy_root(),
        policy.policy_root().expect("policy root derives")
    );
    assert_eq!(checked.certificate_root(), certificate.certificate_root());
    assert_eq!(checked.supplied_binding(), expected);
    assert_eq!(checked.prior_cursor_proposal(), prior);

    let next = checked.derived_next_cursor();
    assert_eq!(next.application_id(), policy.application_id());
    assert_eq!(next.chain_or_domain_id(), policy.chain_or_domain_id());
    assert_eq!(next.finality_network_id(), policy.finality_network_id());
    assert_eq!(next.finality_protocol_id(), policy.finality_protocol_id());
    assert_eq!(
        next.external_finality_policy_hash(),
        policy.expected_external_finality_policy_hash()
    );
    assert_eq!(
        next.finality_verifier_set_root(),
        policy.expected_finality_verifier_set_root()
    );
    assert_eq!(next.finality_policy_root(), checked.policy_root());
    assert_eq!(
        next.application_checkpoint_sequence(),
        certificate.application_checkpoint_sequence()
    );
    assert_eq!(
        next.application_checkpoint_hash(),
        certificate.application_checkpoint_hash()
    );
}

#[test]
fn next_sequence_overflow_rejects_for_empty_and_proposed_prior_records() {
    let max_policy = policy_from(CheckpointFinalityPolicyInputV2 {
        genesis_application_checkpoint_sequence: u64::MAX,
        ..baseline_policy_input()
    });
    let max_certificate = certificate_from(CheckpointFinalityCertificateInputV2 {
        application_checkpoint_sequence: 0,
        finality_policy_root: max_policy.policy_root().expect("policy root derives"),
        ..baseline_certificate_input(&max_policy)
    });
    let zero_expected = SuppliedCheckpointFinalityBindingV2 {
        application_checkpoint_sequence: 0,
        ..supplied_binding()
    };
    assert_eq!(
        check(
            &max_policy,
            &max_certificate,
            zero_expected,
            CheckpointCursorProposalV2::empty(),
        ),
        Err(
            CheckpointFinalityPolicyErrorV2::NextApplicationCheckpointSequenceOverflow {
                prior: u64::MAX
            }
        )
    );

    let policy = baseline_policy();
    let certificate = certificate_from(CheckpointFinalityCertificateInputV2 {
        application_checkpoint_sequence: 0,
        ..baseline_certificate_input(&policy)
    });
    let max_cursor = CheckpointCursorProposalV2::from_prior_record(
        ProposedPriorApplicationCheckpointRecordV2::new(
            ProposedPriorApplicationCheckpointRecordInputV2 {
                application_checkpoint_sequence: u64::MAX,
                ..prior_record_input(&policy)
            },
        ),
    );
    assert_eq!(
        check(&policy, &certificate, zero_expected, max_cursor),
        Err(
            CheckpointFinalityPolicyErrorV2::NextApplicationCheckpointSequenceOverflow {
                prior: u64::MAX
            }
        )
    );
}

#[test]
fn certificate_policy_scope_substitutions_reject_with_typed_errors() {
    let policy = baseline_policy();
    let input = baseline_certificate_input(&policy);
    let cases = [
        (
            CheckpointFinalityCertificateInputV2 {
                application_id: application(20),
                ..input
            },
            CheckpointFinalityPolicyErrorV2::ApplicationMismatch,
        ),
        (
            CheckpointFinalityCertificateInputV2 {
                chain_or_domain_id: domain(20),
                ..input
            },
            CheckpointFinalityPolicyErrorV2::DomainMismatch,
        ),
        (
            CheckpointFinalityCertificateInputV2 {
                finality_network_id: commitment(20),
                ..input
            },
            CheckpointFinalityPolicyErrorV2::FinalityNetworkMismatch,
        ),
        (
            CheckpointFinalityCertificateInputV2 {
                finality_protocol_id: commitment(20),
                ..input
            },
            CheckpointFinalityPolicyErrorV2::FinalityProtocolMismatch,
        ),
        (
            CheckpointFinalityCertificateInputV2 {
                external_finality_policy_hash: commitment(20),
                ..input
            },
            CheckpointFinalityPolicyErrorV2::ExternalFinalityPolicyMismatch,
        ),
        (
            CheckpointFinalityCertificateInputV2 {
                finality_verifier_set_root: commitment(20),
                ..input
            },
            CheckpointFinalityPolicyErrorV2::FinalityVerifierSetMismatch,
        ),
        (
            CheckpointFinalityCertificateInputV2 {
                finality_policy_root: commitment(20),
                ..input
            },
            CheckpointFinalityPolicyErrorV2::FinalityPolicyRootMismatch,
        ),
    ];
    for (changed, error) in cases {
        assert_eq!(
            check(
                &policy,
                &certificate_from(changed),
                supplied_binding(),
                prior_cursor_proposal(&policy),
            ),
            Err(error)
        );
    }
}

#[test]
fn supplied_binding_substitutions_reject_with_typed_errors() {
    let policy = baseline_policy();
    let certificate = baseline_certificate(&policy);
    let expected = supplied_binding();
    let cases = [
        (
            SuppliedCheckpointFinalityBindingV2 {
                application_id: application(20),
                ..expected
            },
            CheckpointFinalityPolicyErrorV2::SuppliedApplicationMismatch,
        ),
        (
            SuppliedCheckpointFinalityBindingV2 {
                chain_or_domain_id: domain(20),
                ..expected
            },
            CheckpointFinalityPolicyErrorV2::SuppliedDomainMismatch,
        ),
        (
            SuppliedCheckpointFinalityBindingV2 {
                epoch_id: 20,
                ..expected
            },
            CheckpointFinalityPolicyErrorV2::EpochMismatch {
                actual: 11,
                expected: 20,
            },
        ),
        (
            SuppliedCheckpointFinalityBindingV2 {
                proof_journal_hash: commitment(20),
                ..expected
            },
            CheckpointFinalityPolicyErrorV2::ProofJournalMismatch,
        ),
        (
            SuppliedCheckpointFinalityBindingV2 {
                post_state_root: commitment(20),
                ..expected
            },
            CheckpointFinalityPolicyErrorV2::PostStateRootMismatch,
        ),
        (
            SuppliedCheckpointFinalityBindingV2 {
                application_checkpoint_sequence: 43,
                ..expected
            },
            CheckpointFinalityPolicyErrorV2::ApplicationCheckpointSequenceMismatch {
                actual: 42,
                expected: 43,
            },
        ),
        (
            SuppliedCheckpointFinalityBindingV2 {
                application_checkpoint_hash: commitment(20),
                ..expected
            },
            CheckpointFinalityPolicyErrorV2::ApplicationCheckpointHashMismatch,
        ),
        (
            SuppliedCheckpointFinalityBindingV2 {
                parent_application_checkpoint_hash: commitment(20),
                ..expected
            },
            CheckpointFinalityPolicyErrorV2::ParentApplicationCheckpointHashMismatch,
        ),
        (
            SuppliedCheckpointFinalityBindingV2 {
                finality_network_id: commitment(20),
                ..expected
            },
            CheckpointFinalityPolicyErrorV2::SuppliedFinalityNetworkMismatch,
        ),
        (
            SuppliedCheckpointFinalityBindingV2 {
                finality_protocol_id: commitment(20),
                ..expected
            },
            CheckpointFinalityPolicyErrorV2::SuppliedFinalityProtocolMismatch,
        ),
        (
            SuppliedCheckpointFinalityBindingV2 {
                external_finality_policy_hash: commitment(20),
                ..expected
            },
            CheckpointFinalityPolicyErrorV2::SuppliedExternalFinalityPolicyMismatch,
        ),
        (
            SuppliedCheckpointFinalityBindingV2 {
                finality_verifier_set_root: commitment(20),
                ..expected
            },
            CheckpointFinalityPolicyErrorV2::SuppliedFinalityVerifierSetMismatch,
        ),
        (
            SuppliedCheckpointFinalityBindingV2 {
                finality_evidence_root: commitment(20),
                ..expected
            },
            CheckpointFinalityPolicyErrorV2::FinalityEvidenceMismatch,
        ),
    ];
    for (changed, error) in cases {
        assert_eq!(
            check(
                &policy,
                &certificate,
                changed,
                prior_cursor_proposal(&policy)
            ),
            Err(error)
        );
    }
}

#[test]
fn proposed_prior_record_scope_substitutions_reject_with_typed_errors() {
    let policy = baseline_policy();
    let certificate = baseline_certificate(&policy);
    let input = prior_record_input(&policy);
    let cases = [
        (
            ProposedPriorApplicationCheckpointRecordInputV2 {
                application_id: application(20),
                ..input
            },
            CheckpointFinalityPolicyErrorV2::PriorRecordApplicationMismatch,
        ),
        (
            ProposedPriorApplicationCheckpointRecordInputV2 {
                chain_or_domain_id: domain(20),
                ..input
            },
            CheckpointFinalityPolicyErrorV2::PriorRecordDomainMismatch,
        ),
        (
            ProposedPriorApplicationCheckpointRecordInputV2 {
                finality_network_id: commitment(20),
                ..input
            },
            CheckpointFinalityPolicyErrorV2::PriorRecordFinalityNetworkMismatch,
        ),
        (
            ProposedPriorApplicationCheckpointRecordInputV2 {
                finality_protocol_id: commitment(20),
                ..input
            },
            CheckpointFinalityPolicyErrorV2::PriorRecordFinalityProtocolMismatch,
        ),
        (
            ProposedPriorApplicationCheckpointRecordInputV2 {
                external_finality_policy_hash: commitment(20),
                ..input
            },
            CheckpointFinalityPolicyErrorV2::PriorRecordExternalFinalityPolicyMismatch,
        ),
        (
            ProposedPriorApplicationCheckpointRecordInputV2 {
                finality_verifier_set_root: commitment(20),
                ..input
            },
            CheckpointFinalityPolicyErrorV2::PriorRecordFinalityVerifierSetMismatch,
        ),
        (
            ProposedPriorApplicationCheckpointRecordInputV2 {
                finality_policy_root: commitment(20),
                ..input
            },
            CheckpointFinalityPolicyErrorV2::PriorRecordFinalityPolicyRootMismatch,
        ),
    ];
    for (changed, error) in cases {
        let cursor = CheckpointCursorProposalV2::from_prior_record(
            ProposedPriorApplicationCheckpointRecordV2::new(changed),
        );
        assert_eq!(
            check(&policy, &certificate, supplied_binding(), cursor),
            Err(error)
        );
    }
}

#[test]
fn proposed_prior_record_cannot_precede_or_replace_governed_genesis() {
    let policy = baseline_policy();
    let certificate = baseline_certificate(&policy);
    let baseline = prior_record_input(&policy);

    let before_genesis = CheckpointCursorProposalV2::from_prior_record(
        ProposedPriorApplicationCheckpointRecordV2::new(
            ProposedPriorApplicationCheckpointRecordInputV2 {
                application_checkpoint_sequence: 40,
                application_checkpoint_hash: commitment(20),
                ..baseline
            },
        ),
    );
    assert_eq!(
        check(&policy, &certificate, supplied_binding(), before_genesis,),
        Err(CheckpointFinalityPolicyErrorV2::PriorRecordBeforeGenesis {
            actual: 40,
            genesis: 41,
        })
    );

    let replaced_genesis = CheckpointCursorProposalV2::from_prior_record(
        ProposedPriorApplicationCheckpointRecordV2::new(
            ProposedPriorApplicationCheckpointRecordInputV2 {
                application_checkpoint_hash: commitment(20),
                ..baseline
            },
        ),
    );
    assert_eq!(
        check(&policy, &certificate, supplied_binding(), replaced_genesis,),
        Err(
            CheckpointFinalityPolicyErrorV2::PriorRecordGenesisHashMismatch {
                actual: commitment(20),
                expected: commitment(5),
            }
        )
    );

    let exact_genesis = CheckpointCursorProposalV2::from_prior_record(
        ProposedPriorApplicationCheckpointRecordV2::new(baseline),
    );
    let _checked_transition = check(&policy, &certificate, supplied_binding(), exact_genesis)
        .expect("exact governed application genesis record is a valid prior cursor proposal");
}

#[derive(Clone, Copy)]
enum CertificateMutation {
    Application,
    Domain,
    Epoch,
    ProofJournal,
    PostState,
    Height,
    Hash,
    ParentHash,
    Network,
    Protocol,
    ExternalPolicy,
    VerifierSet,
    Evidence,
    LocalPolicy,
}

fn apply_mutation(
    input: CheckpointFinalityCertificateInputV2,
    mutation: CertificateMutation,
) -> CheckpointFinalityCertificateInputV2 {
    match mutation {
        CertificateMutation::Application => CheckpointFinalityCertificateInputV2 {
            application_id: application(20),
            ..input
        },
        CertificateMutation::Domain => CheckpointFinalityCertificateInputV2 {
            chain_or_domain_id: domain(20),
            ..input
        },
        CertificateMutation::Epoch => CheckpointFinalityCertificateInputV2 {
            epoch_id: 20,
            ..input
        },
        CertificateMutation::ProofJournal => CheckpointFinalityCertificateInputV2 {
            proof_journal_hash: commitment(20),
            ..input
        },
        CertificateMutation::PostState => CheckpointFinalityCertificateInputV2 {
            post_state_root: commitment(20),
            ..input
        },
        CertificateMutation::Height => CheckpointFinalityCertificateInputV2 {
            application_checkpoint_sequence: 20,
            ..input
        },
        CertificateMutation::Hash => CheckpointFinalityCertificateInputV2 {
            application_checkpoint_hash: commitment(20),
            ..input
        },
        CertificateMutation::ParentHash => CheckpointFinalityCertificateInputV2 {
            parent_application_checkpoint_hash: commitment(20),
            ..input
        },
        CertificateMutation::Network => CheckpointFinalityCertificateInputV2 {
            finality_network_id: commitment(20),
            ..input
        },
        CertificateMutation::Protocol => CheckpointFinalityCertificateInputV2 {
            finality_protocol_id: commitment(20),
            ..input
        },
        CertificateMutation::ExternalPolicy => CheckpointFinalityCertificateInputV2 {
            external_finality_policy_hash: commitment(20),
            ..input
        },
        CertificateMutation::VerifierSet => CheckpointFinalityCertificateInputV2 {
            finality_verifier_set_root: commitment(20),
            ..input
        },
        CertificateMutation::Evidence => CheckpointFinalityCertificateInputV2 {
            finality_evidence_root: commitment(20),
            ..input
        },
        CertificateMutation::LocalPolicy => CheckpointFinalityCertificateInputV2 {
            finality_policy_root: commitment(20),
            ..input
        },
    }
}

#[test]
fn every_certificate_field_is_root_bound_and_semantic_mutations_reject() {
    let policy = baseline_policy();
    let baseline_input = baseline_certificate_input(&policy);
    let baseline_root = certificate_from(baseline_input).certificate_root();
    let mutations = [
        CertificateMutation::Application,
        CertificateMutation::Domain,
        CertificateMutation::Epoch,
        CertificateMutation::ProofJournal,
        CertificateMutation::PostState,
        CertificateMutation::Height,
        CertificateMutation::Hash,
        CertificateMutation::ParentHash,
        CertificateMutation::Network,
        CertificateMutation::Protocol,
        CertificateMutation::ExternalPolicy,
        CertificateMutation::VerifierSet,
        CertificateMutation::Evidence,
        CertificateMutation::LocalPolicy,
    ];
    let mut roots = BTreeSet::new();
    for mutation in mutations {
        let certificate = certificate_from(apply_mutation(baseline_input, mutation));
        assert_ne!(certificate.certificate_root(), baseline_root);
        assert!(roots.insert(certificate.certificate_root()));
        assert!(check(
            &policy,
            &certificate,
            supplied_binding(),
            prior_cursor_proposal(&policy),
        )
        .is_err());
    }
    assert_eq!(roots.len(), mutations.len());

    for (first_index, first) in mutations.iter().copied().enumerate() {
        for second in mutations.iter().copied().skip(first_index + 1) {
            let twice = apply_mutation(apply_mutation(baseline_input, first), second);
            let certificate = certificate_from(twice);
            assert!(
                check(
                    &policy,
                    &certificate,
                    supplied_binding(),
                    prior_cursor_proposal(&policy),
                )
                .is_err(),
                "every bounded depth-two structure-preserving mutation must reject"
            );
        }
    }
}

#[test]
fn every_policy_field_changes_the_policy_root() {
    let baseline = baseline_policy_input();
    let baseline_root = policy_from(baseline)
        .policy_root()
        .expect("policy root derives");
    let changes = [
        CheckpointFinalityPolicyInputV2 {
            application_id: application(20),
            ..baseline
        },
        CheckpointFinalityPolicyInputV2 {
            chain_or_domain_id: domain(20),
            ..baseline
        },
        CheckpointFinalityPolicyInputV2 {
            finality_network_id: commitment(20),
            ..baseline
        },
        CheckpointFinalityPolicyInputV2 {
            finality_protocol_id: commitment(20),
            ..baseline
        },
        CheckpointFinalityPolicyInputV2 {
            expected_external_finality_policy_hash: commitment(20),
            ..baseline
        },
        CheckpointFinalityPolicyInputV2 {
            expected_finality_verifier_set_root: commitment(20),
            ..baseline
        },
        CheckpointFinalityPolicyInputV2 {
            genesis_application_checkpoint_sequence: 20,
            ..baseline
        },
        CheckpointFinalityPolicyInputV2 {
            genesis_application_checkpoint_hash: commitment(20),
            ..baseline
        },
    ];
    let roots = changes
        .into_iter()
        .map(|input| {
            policy_from(input)
                .policy_root()
                .expect("policy root derives")
        })
        .collect::<BTreeSet<_>>();
    assert_eq!(roots.len(), changes.len());
    assert!(!roots.contains(&baseline_root));
}

#[test]
fn every_single_bit_certificate_encoding_mutation_rejects() {
    let policy = baseline_policy();
    let bytes = encode_checkpoint_finality_certificate_v2(&baseline_certificate(&policy))
        .expect("certificate encodes");
    for index in 0..bytes.len() {
        for bit in 0..8 {
            let mut mutated = bytes.clone();
            mutated[index] ^= 1 << bit;
            assert!(
                decode_exact_checkpoint_finality_certificate_v2(&mutated).is_err(),
                "byte {index}, bit {bit} changed without rejection"
            );
        }
    }
}
