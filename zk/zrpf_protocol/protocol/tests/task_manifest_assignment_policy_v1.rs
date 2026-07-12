use zenodex_zrpf_protocol_v3::{
    decode_exact_proof_assignment_policy_v1, encode_proof_assignment_policy_v1, CommitmentV3,
    ProfileIdV3, ProofAssignmentPolicyErrorV1, ProofAssignmentPolicyInputV1,
    ProofAssignmentPolicyV1, ReceiptCodecIdV1, MAX_PROOF_ASSIGNMENT_POLICY_BYTES_V1,
    MAX_TASK_CYCLES_V1, MAX_TASK_INPUT_BYTES_V1, MAX_TASK_MEMORY_BYTES_V1,
};

fn bytes(seed: u8) -> [u8; 32] {
    [seed; 32]
}

fn commitment(seed: u8) -> CommitmentV3 {
    CommitmentV3::new(bytes(seed)).unwrap()
}

fn policy_input() -> ProofAssignmentPolicyInputV1 {
    ProofAssignmentPolicyInputV1 {
        authorized_program_manifest_root: commitment(1),
        required_proof_profile_id: ProfileIdV3::new(bytes(2)).unwrap(),
        required_receipt_codec_id: ReceiptCodecIdV1::new(bytes(3)).unwrap(),
        required_verifier_policy_root: commitment(4),
        minimum_security_level_bits: 128,
        valid_from_epoch: 10,
        valid_through_epoch: 20,
        max_input_bytes: 1_024,
        max_cycles_or_trace_rows: 2_048,
        max_memory_bytes: 4_096,
    }
}

#[test]
fn assignment_policy_round_trips_through_exact_bounded_codec() {
    let policy = ProofAssignmentPolicyV1::new(policy_input()).unwrap();
    let encoded = encode_proof_assignment_policy_v1(&policy).unwrap();

    assert_eq!(
        decode_exact_proof_assignment_policy_v1(&encoded),
        Ok(policy)
    );
}

#[test]
fn assignment_policy_codec_rejects_truncation_trailing_oversize_stale_and_unknown() {
    let policy = ProofAssignmentPolicyV1::new(policy_input()).unwrap();
    let encoded = encode_proof_assignment_policy_v1(&policy).unwrap();
    assert_eq!(encoded[0], 1);
    for end in 0..encoded.len() {
        assert!(decode_exact_proof_assignment_policy_v1(&encoded[..end]).is_err());
    }

    let mut stale_postcard = encoded.clone();
    stale_postcard[0] = 2;
    assert!(decode_exact_proof_assignment_policy_v1(&stale_postcard).is_err());

    let mut nonminimal_version = vec![0x81, 0x00];
    nonminimal_version.extend_from_slice(&encoded[1..]);
    assert!(matches!(
        decode_exact_proof_assignment_policy_v1(&nonminimal_version),
        Err(ProofAssignmentPolicyErrorV1::PostcardDecode
            | ProofAssignmentPolicyErrorV1::NonCanonicalEncoding)
    ));

    let mut trailing = encoded;
    trailing.push(0);
    assert_eq!(
        decode_exact_proof_assignment_policy_v1(&trailing),
        Err(ProofAssignmentPolicyErrorV1::TrailingBytes)
    );
    assert!(matches!(
        decode_exact_proof_assignment_policy_v1(&vec![0; MAX_PROOF_ASSIGNMENT_POLICY_BYTES_V1 + 1]),
        Err(ProofAssignmentPolicyErrorV1::InputTooLarge { .. })
    ));

    let mut stale = serde_json::to_value(policy).unwrap();
    stale["policy_version"] = serde_json::json!(2);
    assert!(serde_json::from_value::<ProofAssignmentPolicyV1>(stale).is_err());

    let policy = ProofAssignmentPolicyV1::new(policy_input()).unwrap();
    let mut unknown = serde_json::to_value(policy).unwrap();
    unknown["operator_note"] = serde_json::json!(true);
    assert!(serde_json::from_value::<ProofAssignmentPolicyV1>(unknown).is_err());
}

#[test]
fn assignment_policy_constructor_rejects_invalid_security_validity_and_resources() {
    for security_level_bits in [0, 513] {
        let mut input = policy_input();
        input.minimum_security_level_bits = security_level_bits;
        assert_eq!(
            ProofAssignmentPolicyV1::new(input),
            Err(ProofAssignmentPolicyErrorV1::InvalidSecurityLevel)
        );
    }

    let mut reversed = policy_input();
    reversed.valid_from_epoch = 21;
    assert_eq!(
        ProofAssignmentPolicyV1::new(reversed),
        Err(ProofAssignmentPolicyErrorV1::InvalidValidityRange)
    );

    for (field, value, maximum) in [
        ("max_input_bytes", 0, MAX_TASK_INPUT_BYTES_V1),
        (
            "max_cycles_or_trace_rows",
            MAX_TASK_CYCLES_V1 + 1,
            MAX_TASK_CYCLES_V1,
        ),
        (
            "max_memory_bytes",
            MAX_TASK_MEMORY_BYTES_V1 + 1,
            MAX_TASK_MEMORY_BYTES_V1,
        ),
    ] {
        let mut input = policy_input();
        match field {
            "max_input_bytes" => input.max_input_bytes = value,
            "max_cycles_or_trace_rows" => input.max_cycles_or_trace_rows = value,
            "max_memory_bytes" => input.max_memory_bytes = value,
            _ => unreachable!(),
        }
        assert_eq!(
            ProofAssignmentPolicyV1::new(input),
            Err(ProofAssignmentPolicyErrorV1::InvalidResourceCeiling { field, maximum })
        );
    }
}
