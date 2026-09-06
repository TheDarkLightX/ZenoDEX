//! Receipt-port checks for the custody-complete asset-transfer successor.
//!
//! The existing custody binding fixture owns the coherent release graph. It is
//! included here because every root-mismatch case must refresh the affected
//! release IDs, registry roots, profile root, occurrence, and module context
//! together before this receipt boundary is exercised.
//! Signature and receipt backends here are synthetic accepting/recording doubles.
//! They establish host-port wiring, not cryptographic receipt or release qualification.

mod custody_release_fixture {
    include!("asset_transfer_custody_release_route_binding.rs");

    use std::cell::RefCell;

    type RecordedModuleReceiptVerifierCall = (Vec<u8>, RootV1, Vec<u8>);

    const COMMAND_SIGNATURE_VERIFIER_ARTIFACT_V1: &[u8] =
        b"custody-receipt-command-signature-verifier-test-artifact-v1";

    fn active_verifier_evidence() -> Vec<CommandSignatureVerifierEvidenceStatusV1> {
        vec![
            CommandSignatureVerifierEvidenceStatusV1::DEPLOYMENT_BOUND,
            CommandSignatureVerifierEvidenceStatusV1::IMPLEMENTATION_REPLAYED,
            CommandSignatureVerifierEvidenceStatusV1::IMPLEMENTED,
            CommandSignatureVerifierEvidenceStatusV1::INDEPENDENTLY_REVIEWED,
            CommandSignatureVerifierEvidenceStatusV1::NO_BYPASS,
            CommandSignatureVerifierEvidenceStatusV1::RELEASE_BACKED,
            CommandSignatureVerifierEvidenceStatusV1::SOURCE_PINNED,
            CommandSignatureVerifierEvidenceStatusV1::SPECIFIED,
            CommandSignatureVerifierEvidenceStatusV1::TESTED,
            CommandSignatureVerifierEvidenceStatusV1::TOOLCHAIN_PINNED,
        ]
    }

    fn signature_verifier_manifest() -> EconomicCommandSignatureVerifierEvidenceManifestV1 {
        let evidence_artifacts = active_verifier_evidence()
            .into_iter()
            .enumerate()
            .map(
                |(index, status)| CommandSignatureVerifierEvidenceArtifactV1 {
                    status,
                    artifact_root: root(700 + u64::try_from(index).unwrap()),
                },
            )
            .collect();
        EconomicCommandSignatureVerifierEvidenceManifestV1 {
            schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
            signature_algorithm: "BLS12_381_G2_BASIC_V1".to_owned(),
            implementation_root: command_signature_verifier_implementation_root_v1(
                COMMAND_SIGNATURE_VERIFIER_ARTIFACT_V1,
            )
            .unwrap(),
            public_key_schema_root: root(687),
            signature_schema_root: root(688),
            message_schema_root: root(689),
            specification_root: root(690),
            source_root: root(691),
            toolchain_root: root(692),
            backend_protocol_root: command_signature_verifier_backend_protocol_root_v1().unwrap(),
            max_public_key_bytes: 160,
            max_signature_bytes: 4_096,
            evidence_artifacts,
        }
    }

    fn signature_verifier_registry() -> EconomicCommandSignatureVerifierRegistryV1 {
        let manifest = signature_verifier_manifest();
        let mut release = EconomicCommandSignatureVerifierReleaseV1 {
            schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
            release_id: root(1),
            semantic_version: "1.0.0-custody-receipt-test".to_owned(),
            signature_algorithm: "BLS12_381_G2_BASIC_V1".to_owned(),
            implementation_root: manifest.implementation_root.clone(),
            public_key_schema_root: manifest.public_key_schema_root.clone(),
            signature_schema_root: manifest.signature_schema_root.clone(),
            message_schema_root: manifest.message_schema_root.clone(),
            specification_root: manifest.specification_root.clone(),
            source_root: manifest.source_root.clone(),
            toolchain_root: manifest.toolchain_root.clone(),
            evidence_manifest_root: manifest.manifest_root().unwrap(),
            max_public_key_bytes: manifest.max_public_key_bytes,
            max_signature_bytes: manifest.max_signature_bytes,
            status: ReleaseStatusV1::ACTIVE_NEW,
            accepts_new_authentications: true,
            evidence_statuses: manifest
                .evidence_artifacts
                .iter()
                .map(|row| row.status)
                .collect(),
        };
        release.release_id = release.derived_release_id().unwrap();
        EconomicCommandSignatureVerifierRegistryV1 {
            schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
            releases: vec![release],
        }
    }

    fn authorization_registry(route: &RouteReleaseV1) -> EconomicCommandAuthorizationRegistryV1 {
        let registry = EconomicCommandAuthorizationRegistryV1 {
            schema: ECONOMIC_COMMAND_AUTHENTICATION_SCHEMA_V1.to_owned(),
            authorizations: vec![EconomicCommandAuthorizationV1 {
                schema: ECONOMIC_COMMAND_AUTHENTICATION_SCHEMA_V1.to_owned(),
                command_kind: ASSET_TRANSFER_COMMAND_KIND_V1.to_owned(),
                subject_id: "alice".to_owned(),
                grant_root: root(7),
                route_release_id: route.route_release_id.clone(),
                signer_key_id: "alice-key-1".to_owned(),
                signer_public_key: "bls12-381-g2:alice-public-key".to_owned(),
                signature_algorithm: "BLS12_381_G2_BASIC_V1".to_owned(),
                valid_from_height: 0,
                valid_through_height: u64::MAX,
                min_nonce: 0,
                max_nonce: u64::MAX,
                enabled: true,
            }],
        };
        registry.validate().unwrap();
        registry
    }

    fn receipt_policy_registry(
        authorization_registry: &EconomicCommandAuthorizationRegistryV1,
        signature_verifier_registry: &EconomicCommandSignatureVerifierRegistryV1,
        asset_policy_registry: &AssetTransferPolicyRegistryV1,
    ) -> EconomicPolicyRegistryV1 {
        let mut bindings = vec![
            EconomicPolicyBindingV1 {
                policy_kind: ECONOMIC_COMMAND_AUTHENTICATION_POLICY_KIND_V1.to_owned(),
                command_kind: ASSET_TRANSFER_COMMAND_KIND_V1.to_owned(),
                policy_root: authorization_registry.registry_root().unwrap(),
            },
            EconomicPolicyBindingV1 {
                policy_kind: ECONOMIC_COMMAND_SIGNATURE_VERIFIER_POLICY_KIND_V1.to_owned(),
                command_kind: ASSET_TRANSFER_COMMAND_KIND_V1.to_owned(),
                policy_root: signature_verifier_registry.registry_root().unwrap(),
            },
            EconomicPolicyBindingV1 {
                policy_kind: ASSET_TRANSFER_ASSET_POLICY_KIND_V1.to_owned(),
                command_kind: ASSET_TRANSFER_COMMAND_KIND_V1.to_owned(),
                policy_root: asset_policy_registry.asset_policy_root().unwrap(),
            },
            EconomicPolicyBindingV1 {
                policy_kind: ASSET_TRANSFER_FEE_POLICY_KIND_V1.to_owned(),
                command_kind: ASSET_TRANSFER_COMMAND_KIND_V1.to_owned(),
                policy_root: asset_policy_registry.fee_policy_root().unwrap(),
            },
        ];
        bindings.sort_by(|left, right| {
            (&left.policy_kind, &left.command_kind).cmp(&(&right.policy_kind, &right.command_kind))
        });
        let registry = EconomicPolicyRegistryV1 {
            schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
            bindings,
        };
        registry.validate().unwrap();
        registry
    }

    struct AcceptingCommandSignatureVerifierV1;

    impl EconomicCommandSignatureVerifierBackendV1 for AcceptingCommandSignatureVerifierV1 {
        fn verify_command_signature(
            &self,
            _signature_algorithm: &str,
            _signer_public_key: &str,
            message_bytes: &[u8],
            signature_bytes: &[u8],
        ) -> Result<bool, AbiErrorV1> {
            Ok(!message_bytes.is_empty() && !signature_bytes.is_empty())
        }
    }

    /// A coherent custody graph plus the separate authentication dependencies
    /// required to mint the existing opaque authenticated-command witness.
    struct ReceiptFixture {
        governance: Governance,
        authorization_registry: EconomicCommandAuthorizationRegistryV1,
        signature_verifier_registry: EconomicCommandSignatureVerifierRegistryV1,
    }

    impl ReceiptFixture {
        fn build(options: &Options) -> Self {
            let mut governance = Governance::build(options);
            let signature_verifier_registry = signature_verifier_registry();
            let authorization_registry = authorization_registry(&governance.routes.routes[0]);
            let policy_registry = receipt_policy_registry(
                &authorization_registry,
                &signature_verifier_registry,
                &governance.asset_policy_registry,
            );
            let module_release_id = governance
                .lanes
                .release_for(LaneIdV1::ASSET_TRANSFER)
                .expect("asset release must exist")
                .release_id
                .clone();
            let custody = governance.module_input.custody.clone();
            let profile = profile_snapshot(
                &governance.lanes,
                &governance.coordinators,
                &governance.routes,
                policy_registry.registry_root().unwrap(),
                governance.profile.status,
                governance.profile.authority_epoch,
            );
            let occurrence = occurrence(&profile, &governance.routes.routes[0]);
            let module_input = module_input(&profile, &module_release_id, &occurrence, custody);

            governance.profile = profile;
            governance.policy_registry = policy_registry;
            governance.occurrence = occurrence;
            governance.module_input = module_input;
            governance.profile.validate().unwrap();
            assert_eq!(
                governance.occurrence.profile_root,
                governance.profile.profile_id
            );
            assert_eq!(
                governance.module_input.context.profile_root,
                governance.profile.profile_id
            );

            Self {
                governance,
                authorization_registry,
                signature_verifier_registry,
            }
        }

        fn authenticated_command(&self) -> AuthenticatedEconomicCommandV1 {
            let occurrence = &self.governance.occurrence;
            let authorization = self
                .authorization_registry
                .authorization_for(occurrence, "alice-key-1")
                .unwrap();
            let intent = EconomicCommandIntentV1 {
                schema: ECONOMIC_COMMAND_AUTHENTICATION_SCHEMA_V1.to_owned(),
                chain_id: occurrence.chain_id.clone(),
                deployment_root: occurrence.deployment_root.clone(),
                profile_root: occurrence.profile_root.clone(),
                command_kind: occurrence.command_kind.clone(),
                command_body_hash: occurrence.command_body_hash.clone(),
                route_release_id: occurrence.route_release_id.clone(),
                subject_id: occurrence.subject_id.clone(),
                grant_root: occurrence.grant_root.clone(),
                nonce: occurrence.nonce,
                consumed_object_ids: occurrence.consumed_object_ids.clone(),
                valid_from_height: 0,
                valid_through_height: u64::MAX,
            };
            let envelope = EconomicCommandAuthenticationEnvelopeV1 {
                command_body_bytes: canonical_economic_command_body_bytes_v1(
                    &self.governance.module_input.command.command_kind,
                    &self.governance.module_input.command,
                )
                .unwrap(),
                signer_key_id: authorization.signer_key_id.clone(),
                signer_public_key: authorization.signer_public_key.clone(),
                signature_algorithm: authorization.signature_algorithm.clone(),
                signature_bytes: b"custody-receipt-test-signature".to_vec(),
            };
            let manifest = signature_verifier_manifest();
            let deployment = bind_economic_command_signature_verifier_deployment_v1(
                &self.signature_verifier_registry.releases[0],
                &manifest,
                COMMAND_SIGNATURE_VERIFIER_ARTIFACT_V1,
                &occurrence.deployment_root,
                &occurrence.profile_root,
                AcceptingCommandSignatureVerifierV1,
            )
            .unwrap();
            let authenticated_intent = authenticate_economic_command_intent_v1(
                &EconomicCommandAuthenticationCandidateV1 {
                    profile: &self.governance.profile,
                    routes: &self.governance.routes,
                    policy_registry: &self.governance.policy_registry,
                    authorization_registry: &self.authorization_registry,
                    signature_verifier_registry: &self.signature_verifier_registry,
                    intent: &intent,
                    envelope: &envelope,
                },
                &deployment,
            )
            .unwrap();
            bind_authenticated_intent_to_occurrence_v1(&authenticated_intent, occurrence).unwrap()
        }

        fn candidate<'a>(
            &'a self,
            authenticated_command: &'a AuthenticatedEconomicCommandV1,
            accepted: &'a AssetTransferLaneModuleAcceptedV1,
            release_route_binding: &'a ReleaseRouteBoundLaneTransitionV1,
            receipt_kind: ReceiptKindV1,
            receipt_bytes: &'a [u8],
        ) -> AssetTransferLaneModuleReceiptCandidateV1<'a> {
            AssetTransferLaneModuleReceiptCandidateV1 {
                profile: &self.governance.profile,
                policy_registry: &self.governance.policy_registry,
                asset_policy_registry: &self.governance.asset_policy_registry,
                lanes: &self.governance.lanes,
                coordinators: &self.governance.coordinators,
                routes: &self.governance.routes,
                authenticated_command,
                module_input: &self.governance.module_input,
                accepted,
                release_route_binding,
                receipt: LaneModuleReceiptEnvelopeV1 {
                    receipt_kind,
                    receipt_bytes,
                },
            }
        }
    }

    #[derive(Default)]
    struct RecordingModuleReceiptVerifier {
        calls: RefCell<Vec<RecordedModuleReceiptVerifierCall>>,
        reject: bool,
    }

    impl LaneModuleSuccinctReceiptVerifierV1 for RecordingModuleReceiptVerifier {
        fn verify_succinct_receipt(
            &self,
            receipt_bytes: &[u8],
            expected_image_id: &RootV1,
            expected_journal_bytes: &[u8],
        ) -> AbiResultV1<()> {
            self.calls.borrow_mut().push((
                receipt_bytes.to_vec(),
                expected_image_id.clone(),
                expected_journal_bytes.to_vec(),
            ));
            if self.reject {
                Err(AbiErrorV1::InvalidBinding(
                    "recording verifier rejected custody receipt",
                ))
            } else {
                Ok(())
            }
        }
    }

    #[test]
    fn matching_successor_roots_with_nonzero_custody_reach_the_port_once_with_exact_bytes() {
        // Given matching module, coordinator, and route bundle roots with seven custody atoms.
        let fixture = ReceiptFixture::build(&Options::matching(custody_rows(7)));
        let accepted = fixture.governance.custody_accepted();
        let rebound = fixture.governance.bind_custody(&accepted).unwrap();
        let authenticated = fixture.authenticated_command();
        let receipt_bytes = b"custody-successor-succinct-receipt";
        let verifier = RecordingModuleReceiptVerifier::default();

        // When the custody successor receipt is verified.
        let verified = verify_asset_transfer_lane_module_custody_receipt_v1(
            fixture.candidate(
                &authenticated,
                &accepted,
                &rebound,
                ReceiptKindV1::SUCCINCT,
                receipt_bytes,
            ),
            &verifier,
        )
        .expect("matching custody successor receipt must reach the recording port");

        // Then the retained oracle receives the selected successor image and custody journal.
        let calls = verifier.calls.borrow();
        assert_eq!(calls.len(), 1);
        assert_eq!(calls[0].0, receipt_bytes);
        assert_eq!(
            calls[0].1,
            fixture
                .governance
                .lanes
                .release_for(LaneIdV1::ASSET_TRANSFER)
                .unwrap()
                .guest_image_id
        );
        assert_eq!(
            calls[0].2,
            canonical_bytes_v1(&accepted.module_journal).unwrap()
        );
        assert_eq!(
            verified.module_journal_root(),
            rebound.module_journal_root()
        );
    }

    #[test]
    fn each_coherent_unknown_or_mixed_semantic_root_rejects_before_recomputation_or_port() {
        let mut module = Options::matching(custody_rows(7));
        module.module.specification_root = unknown_root();
        let mut coordinator = Options::matching(custody_rows(7));
        coordinator.coordinator.specification_root = unknown_root();
        let mut route = Options::matching(custody_rows(7));
        route.route.specification_root = unknown_root();

        for (options, field) in [
            (module, "custody semantics module specification root"),
            (
                coordinator,
                "custody semantics coordinator specification root",
            ),
            (route, "custody semantics route specification root"),
        ] {
            let fixture = ReceiptFixture::build(&options);
            let legacy = fixture.governance.legacy_accepted();
            let legacy_binding = fixture.governance.bind_legacy(&legacy).unwrap();
            let authenticated = fixture.authenticated_command();
            let verifier = RecordingModuleReceiptVerifier::default();

            // The legacy output is an infection witness: custody recomputation would fail if
            // reached, so the semantic error proves the required earlier reject precedence.
            assert_eq!(
                recompute_asset_transfer_lane_module_custody_v1(
                    &fixture.governance.module_input,
                    &legacy,
                )
                .unwrap_err(),
                recomputation_mismatch()
            );
            assert_eq!(
                verify_asset_transfer_lane_module_custody_receipt_v1(
                    fixture.candidate(
                        &authenticated,
                        &legacy,
                        &legacy_binding,
                        ReceiptKindV1::SUCCINCT,
                        b"semantic-root-mismatch",
                    ),
                    &verifier,
                )
                .unwrap_err(),
                AbiErrorV1::InvalidBinding(field)
            );
            assert!(verifier.calls.borrow().is_empty());
        }
    }

    #[test]
    fn binding_and_receipt_boundaries_reject_without_bypassing_the_shared_oracle() {
        let fixture = ReceiptFixture::build(&Options::matching(custody_rows(7)));
        let custody = fixture.governance.custody_accepted();
        let custody_binding = fixture.governance.bind_custody(&custody).unwrap();
        let legacy = fixture.governance.legacy_accepted();
        let legacy_binding = fixture.governance.bind_legacy(&legacy).unwrap();
        let authenticated = fixture.authenticated_command();

        let wrong_binding_verifier = RecordingModuleReceiptVerifier::default();
        assert_eq!(
            verify_asset_transfer_lane_module_custody_receipt_v1(
                fixture.candidate(
                    &authenticated,
                    &custody,
                    &legacy_binding,
                    ReceiptKindV1::SUCCINCT,
                    b"wrong-structural-binding",
                ),
                &wrong_binding_verifier,
            )
            .unwrap_err(),
            AbiErrorV1::InvalidBinding("lane module structural binding")
        );
        assert!(wrong_binding_verifier.calls.borrow().is_empty());

        for (receipt_kind, receipt_bytes, expected_error) in [
            (
                ReceiptKindV1::SUCCINCT,
                &[][..],
                AbiErrorV1::InvalidBounds("lane module receipt bytes"),
            ),
            (
                ReceiptKindV1::COMPOSITE,
                &b"composite"[..],
                AbiErrorV1::InvalidBinding("lane module receipt kind"),
            ),
        ] {
            let verifier = RecordingModuleReceiptVerifier::default();
            assert_eq!(
                verify_asset_transfer_lane_module_custody_receipt_v1(
                    fixture.candidate(
                        &authenticated,
                        &custody,
                        &custody_binding,
                        receipt_kind,
                        receipt_bytes,
                    ),
                    &verifier,
                )
                .unwrap_err(),
                expected_error
            );
            assert!(verifier.calls.borrow().is_empty());
        }

        let rejecting_verifier = RecordingModuleReceiptVerifier {
            reject: true,
            ..Default::default()
        };
        assert_eq!(
            verify_asset_transfer_lane_module_custody_receipt_v1(
                fixture.candidate(
                    &authenticated,
                    &custody,
                    &custody_binding,
                    ReceiptKindV1::SUCCINCT,
                    b"synthetic-reject-propagation",
                ),
                &rejecting_verifier,
            )
            .unwrap_err(),
            AbiErrorV1::InvalidBinding("recording verifier rejected custody receipt")
        );
        assert_eq!(rejecting_verifier.calls.borrow().len(), 1);
    }

    #[test]
    fn zero_one_and_receipt_length_boundaries_preserve_the_successor_controls() {
        for custody_atoms in [0, 1] {
            let fixture = ReceiptFixture::build(&Options::matching(custody_rows(custody_atoms)));
            let accepted = fixture.governance.custody_accepted();
            let binding = fixture.governance.bind_custody(&accepted).unwrap();
            let authenticated = fixture.authenticated_command();
            let verifier = RecordingModuleReceiptVerifier::default();
            verify_asset_transfer_lane_module_custody_receipt_v1(
                fixture.candidate(
                    &authenticated,
                    &accepted,
                    &binding,
                    ReceiptKindV1::SUCCINCT,
                    b"x",
                ),
                &verifier,
            )
            .expect("zero and one custody atom must retain the successor receipt controls");
            assert_eq!(verifier.calls.borrow().len(), 1);
        }

        let fixture = ReceiptFixture::build(&Options::matching(custody_rows(7)));
        let accepted = fixture.governance.custody_accepted();
        let binding = fixture.governance.bind_custody(&accepted).unwrap();
        let authenticated = fixture.authenticated_command();
        let at_limit = vec![0xa5; MAX_LANE_MODULE_RECEIPT_BYTES_V1];
        let at_limit_verifier = RecordingModuleReceiptVerifier::default();
        verify_asset_transfer_lane_module_custody_receipt_v1(
            fixture.candidate(
                &authenticated,
                &accepted,
                &binding,
                ReceiptKindV1::SUCCINCT,
                &at_limit,
            ),
            &at_limit_verifier,
        )
        .expect("receipt at the exact byte ceiling must reach the port");
        assert_eq!(at_limit_verifier.calls.borrow().len(), 1);

        let over_limit = vec![0xa5; MAX_LANE_MODULE_RECEIPT_BYTES_V1 + 1];
        let over_limit_verifier = RecordingModuleReceiptVerifier::default();
        assert_eq!(
            verify_asset_transfer_lane_module_custody_receipt_v1(
                fixture.candidate(
                    &authenticated,
                    &accepted,
                    &binding,
                    ReceiptKindV1::SUCCINCT,
                    &over_limit,
                ),
                &over_limit_verifier,
            )
            .unwrap_err(),
            AbiErrorV1::InvalidBounds("lane module receipt bytes")
        );
        assert!(over_limit_verifier.calls.borrow().is_empty());
    }

    #[test]
    fn active_new_and_accepts_new_objects_boundaries_reject_before_the_receipt_port() {
        let active = ReceiptFixture::build(&Options::matching(custody_rows(7)));
        let active_legacy = active.governance.legacy_accepted();
        let active_binding = active.governance.bind_legacy(&active_legacy).unwrap();
        let active_authenticated = active.authenticated_command();

        let mut drained_lane = Options::matching(custody_rows(7));
        drained_lane.lane_status = (ReleaseStatusV1::DRAIN_ONLY, false);
        let mut drained_route = Options::matching(custody_rows(7));
        drained_route.route_status = (ReleaseStatusV1::DRAIN_ONLY, false);

        for (options, expected_error) in [
            (
                drained_lane,
                AbiErrorV1::InvalidBinding("active route lane release"),
            ),
            (
                drained_route,
                AbiErrorV1::InvalidBinding("active profile route status"),
            ),
        ] {
            let fixture = ReceiptFixture::build(&options);
            let legacy = fixture.governance.legacy_accepted();
            let verifier = RecordingModuleReceiptVerifier::default();
            assert_eq!(
                verify_asset_transfer_lane_module_custody_receipt_v1(
                    fixture.candidate(
                        &active_authenticated,
                        &legacy,
                        &active_binding,
                        ReceiptKindV1::SUCCINCT,
                        b"non-active-successor",
                    ),
                    &verifier,
                )
                .unwrap_err(),
                expected_error
            );
            assert!(verifier.calls.borrow().is_empty());
        }

        // An ACTIVE_NEW/false row cannot acquire a valid registry root. Supply
        // the malformed ordinary Rust value directly, rather than panicking in
        // the fixture builder before the receipt entry gets a chance to reject.
        let mut inconsistent_lanes = active.governance.lanes.clone();
        inconsistent_lanes
            .releases
            .iter_mut()
            .find(|release| release.lane_id == LaneIdV1::ASSET_TRANSFER)
            .unwrap()
            .accepts_new_objects = false;
        let mut inconsistent_routes = active.governance.routes.clone();
        inconsistent_routes.routes[0].accepts_new_objects = false;
        for (lanes, routes, reason) in [
            (
                &inconsistent_lanes,
                &active.governance.routes,
                "lane release status",
            ),
            (
                &active.governance.lanes,
                &inconsistent_routes,
                "route status",
            ),
        ] {
            let verifier = RecordingModuleReceiptVerifier::default();
            let mut candidate = active.candidate(
                &active_authenticated,
                &active_legacy,
                &active_binding,
                ReceiptKindV1::SUCCINCT,
                b"inconsistent-status",
            );
            candidate.lanes = lanes;
            candidate.routes = routes;
            assert_eq!(
                verify_asset_transfer_lane_module_custody_receipt_v1(candidate, &verifier)
                    .unwrap_err(),
                AbiErrorV1::InvalidBinding(reason),
            );
            assert!(verifier.calls.borrow().is_empty());
        }
    }

    #[test]
    fn authenticated_occurrence_profile_and_context_mismatches_reject_before_the_port() {
        let active = ReceiptFixture::build(&Options::matching(custody_rows(7)));
        let accepted = active.governance.custody_accepted();
        let binding = active.governance.bind_custody(&accepted).unwrap();
        let mut other_occurrence = ReceiptFixture::build(&Options::matching(custody_rows(7)));
        other_occurrence.governance.occurrence.nonce += 1;
        let mut foreign_options = Options::matching(custody_rows(7));
        foreign_options.authority_epoch += 1;
        let other_profile = ReceiptFixture::build(&foreign_options);
        for (authenticated, reason) in [
            (
                other_occurrence.authenticated_command(),
                "lane module occurrence",
            ),
            (
                other_profile.authenticated_command(),
                "lane module occurrence profile root",
            ),
        ] {
            let verifier = RecordingModuleReceiptVerifier::default();
            assert_eq!(
                verify_asset_transfer_lane_module_custody_receipt_v1(
                    active.candidate(
                        &authenticated,
                        &accepted,
                        &binding,
                        ReceiptKindV1::SUCCINCT,
                        b"foreign-authenticated-handle"
                    ),
                    &verifier,
                )
                .unwrap_err(),
                AbiErrorV1::InvalidBinding(reason),
            );
            assert!(verifier.calls.borrow().is_empty());
        }

        let mut foreign_context = ReceiptFixture::build(&Options::matching(custody_rows(7)));
        foreign_context.governance.module_input.context.chain_id = "foreign-chain".to_owned();
        let foreign_accepted = foreign_context.governance.custody_accepted();
        let authenticated = active.authenticated_command();
        let verifier = RecordingModuleReceiptVerifier::default();
        assert_eq!(
            verify_asset_transfer_lane_module_custody_receipt_v1(
                foreign_context.candidate(
                    &authenticated,
                    &foreign_accepted,
                    &binding,
                    ReceiptKindV1::SUCCINCT,
                    b"foreign-module-context"
                ),
                &verifier,
            )
            .unwrap_err(),
            AbiErrorV1::InvalidBinding("lane module chain id"),
        );
        assert!(verifier.calls.borrow().is_empty());
    }

    #[test]
    fn exact_journal_release_ceiling_accepts_and_one_more_byte_rejects() {
        let baseline = ReceiptFixture::build(&Options::matching(custody_rows(7)));
        let journal_size =
            canonical_bytes_v1(&baseline.governance.custody_accepted().module_journal)
                .unwrap()
                .len();
        for at_limit in [true, false] {
            let mut options = Options::matching(custody_rows(7));
            options.module_journal_byte_ceiling =
                u64::try_from(journal_size - usize::from(!at_limit)).unwrap();
            let fixture = ReceiptFixture::build(&options);
            let accepted = fixture.governance.custody_accepted();
            assert_eq!(
                canonical_bytes_v1(&accepted.module_journal).unwrap().len(),
                journal_size
            );
            let binding = fixture.governance.bind_custody(&accepted).unwrap();
            let authenticated = fixture.authenticated_command();
            let verifier = RecordingModuleReceiptVerifier::default();
            let result = verify_asset_transfer_lane_module_custody_receipt_v1(
                fixture.candidate(
                    &authenticated,
                    &accepted,
                    &binding,
                    ReceiptKindV1::SUCCINCT,
                    b"journal-size-boundary",
                ),
                &verifier,
            );
            if at_limit {
                result.expect("an exactly fitting journal reaches the recording verifier");
                assert_eq!(verifier.calls.borrow().len(), 1);
            } else {
                assert_eq!(
                    result.unwrap_err(),
                    AbiErrorV1::InvalidBounds("lane module canonical journal bytes")
                );
                assert!(verifier.calls.borrow().is_empty());
            }
        }
    }

    #[test]
    fn legacy_transfer_entry_retains_its_ordinary_recomputation_and_observables() {
        let fixture = ReceiptFixture::build(&Options::matching(custody_rows(7)));
        let legacy = fixture.governance.legacy_accepted();
        let binding = fixture.governance.bind_legacy(&legacy).unwrap();
        let authenticated = fixture.authenticated_command();
        let verifier = RecordingModuleReceiptVerifier::default();
        verify_asset_transfer_lane_module_receipt_v1(
            fixture.candidate(
                &authenticated,
                &legacy,
                &binding,
                ReceiptKindV1::SUCCINCT,
                b"legacy-ordinary-transfer-receipt",
            ),
            &verifier,
        )
        .expect("legacy verifier must retain its ordinary transfer path");
        assert_eq!(verifier.calls.borrow().len(), 1);

        let empty_verifier = RecordingModuleReceiptVerifier::default();
        assert_eq!(
            verify_asset_transfer_lane_module_receipt_v1(
                fixture.candidate(
                    &authenticated,
                    &legacy,
                    &binding,
                    ReceiptKindV1::SUCCINCT,
                    &[],
                ),
                &empty_verifier,
            )
            .unwrap_err(),
            AbiErrorV1::InvalidBounds("lane module receipt bytes")
        );
        assert!(empty_verifier.calls.borrow().is_empty());
    }
}
