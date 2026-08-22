use super::*;

#[test]
fn sequencer_fields_do_not_require_a_second_signature() {
    let fixture = Fixture::new();
    let verifier = RecordingVerifier::accepting();
    let authenticated_intent = fixture.authenticate_intent(&verifier).unwrap();
    bind_authenticated_intent_to_occurrence_v1(&authenticated_intent, &fixture.occurrence).unwrap();
    let mut resequenced = fixture.occurrence.clone();
    resequenced.tx_index = 99;
    resequenced.op_index = 17;
    resequenced.pre_state_root = root(999);
    bind_authenticated_intent_to_occurrence_v1(&authenticated_intent, &resequenced).unwrap();
    assert_eq!(verifier.calls.borrow().len(), 1);
}

#[test]
fn signed_intent_substitution_rejects_during_occurrence_binding() {
    let fixture = Fixture::new();
    let verifier = RecordingVerifier::accepting();
    let authenticated_intent = fixture.authenticate_intent(&verifier).unwrap();
    let mut substituted = fixture.occurrence.clone();
    substituted.grant_root = root(999);
    assert!(matches!(
        bind_authenticated_intent_to_occurrence_v1(&authenticated_intent, &substituted),
        Err(AbiErrorV1::InvalidBinding("grant"))
    ));
}

#[test]
fn body_substitution_rejects_before_signature_verifier() {
    let mut fixture = Fixture::new();
    fixture.envelope.command_body_bytes.push(b' ');
    let verifier = RecordingVerifier::accepting();

    assert!(matches!(
        fixture.authenticate(&verifier),
        Err(AbiErrorV1::InvalidBinding(
            "command authentication body hash"
        ))
    ));
    assert!(verifier.calls.borrow().is_empty());
}

#[test]
fn signer_algorithm_and_disabled_policy_reject_before_verifier() {
    let mut fixture = Fixture::new();
    fixture.envelope.signature_algorithm = "FORGED_V1".to_owned();
    let verifier = RecordingVerifier::accepting();
    assert!(matches!(
        fixture.authenticate(&verifier),
        Err(AbiErrorV1::InvalidBinding(
            "command authentication signature algorithm"
        ))
    ));
    assert!(verifier.calls.borrow().is_empty());

    let mut fixture = Fixture::new();
    fixture.authorization_registry.authorizations[0].enabled = false;
    fixture.policy_registry.bindings[0].policy_root =
        fixture.authorization_registry.registry_root().unwrap();
    fixture.profile = profile(
        &fixture.routes,
        &fixture.policy_registry,
        ProfileStatusV1::ACTIVE,
    );
    fixture.intent.profile_root = fixture.profile.profile_id.clone();
    fixture.occurrence.profile_root = fixture.profile.profile_id.clone();
    let verifier = RecordingVerifier::accepting();
    assert!(matches!(
        fixture.authenticate(&verifier),
        Err(AbiErrorV1::InvalidBinding("command authorization disabled"))
    ));
    assert!(verifier.calls.borrow().is_empty());
}

#[test]
fn height_and_nonce_intervals_use_closed_boundary_semantics() {
    for (height, accepted) in [(9, false), (10, true), (12, true), (13, false)] {
        let mut fixture = Fixture::new();
        fixture.occurrence.height = height;
        let verifier = RecordingVerifier::accepting();
        assert_eq!(fixture.authenticate(&verifier).is_ok(), accepted);
    }
    for (nonce, accepted) in [(7, false), (8, true), (10, true), (11, false)] {
        let mut fixture = Fixture::new();
        fixture.intent.nonce = nonce;
        fixture.occurrence.nonce = nonce;
        let verifier = RecordingVerifier::accepting();
        assert_eq!(fixture.authenticate(&verifier).is_ok(), accepted);
    }
}

#[test]
fn intent_validity_must_fit_inside_authorization_interval() {
    for (valid_from_height, valid_through_height) in [(9, 12), (10, 13)] {
        let mut fixture = Fixture::new();
        fixture.intent.valid_from_height = valid_from_height;
        fixture.intent.valid_through_height = valid_through_height;
        let verifier = RecordingVerifier::accepting();
        assert!(matches!(
            fixture.authenticate_intent(&verifier),
            Err(AbiErrorV1::InvalidBinding(
                "command intent validity exceeds authorization interval"
            ))
        ));
        assert!(verifier.calls.borrow().is_empty());
    }
}

#[test]
fn inactive_profile_and_rejecting_verifier_fail_closed() {
    let mut fixture = Fixture::new();
    fixture.profile.status = ProfileStatusV1::SHADOW;
    let verifier = RecordingVerifier::accepting();
    assert!(matches!(
        fixture.authenticate(&verifier),
        Err(AbiErrorV1::InvalidBinding(
            "command authentication requires active profile"
        ))
    ));
    assert!(verifier.calls.borrow().is_empty());

    let fixture = Fixture::new();
    let verifier = RecordingVerifier {
        result: false,
        calls: RefCell::new(Vec::new()),
    };
    assert!(matches!(
        fixture.authenticate(&verifier),
        Err(AbiErrorV1::InvalidBinding(
            "command authentication signature"
        ))
    ));
    assert_eq!(verifier.calls.borrow().len(), 1);
}

#[test]
fn authorization_registry_rejects_duplicate_and_inverted_intervals() {
    let route = route();
    let authorization = authorization(&route);
    let duplicate = EconomicCommandAuthorizationRegistryV1 {
        schema: ECONOMIC_COMMAND_AUTHENTICATION_SCHEMA_V1.to_owned(),
        authorizations: vec![authorization.clone(), authorization.clone()],
    };
    assert!(matches!(
        duplicate.validate(),
        Err(AbiErrorV1::InvalidOrder("command authorization registry"))
    ));

    let mut inverted = authorization;
    inverted.min_nonce = 11;
    inverted.max_nonce = 10;
    assert!(matches!(
        inverted.validate(),
        Err(AbiErrorV1::InvalidBounds(
            "command authorization nonce interval"
        ))
    ));
}

#[test]
fn authentication_envelope_signature_bytes_use_global_closed_boundary_bva() {
    for (signature_len, accepted) in [
        (0, false),
        (1, true),
        (MAX_COMMAND_SIGNATURE_BYTES_V1, true),
        (MAX_COMMAND_SIGNATURE_BYTES_V1 + 1, false),
    ] {
        let mut fixture = Fixture::new();
        fixture.envelope.signature_bytes = vec![b's'; signature_len];
        assert_eq!(fixture.envelope.validate().is_ok(), accepted);
    }
}
