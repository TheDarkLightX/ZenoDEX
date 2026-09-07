//! Epoch projection admission tests over the existing custody-complete witness path.
//!
//! The release graph and custody transition come from the ordinary shared fixture. The
//! signature and succinct-receipt backends are accepting test doubles, so these cases test
//! Rust boundary ordering and complete-state binding without making a cryptographic or
//! deployment qualification claim.

mod custody_epoch_fixture {
    include!("asset_transfer_custody_release_route_binding.rs");

    use serde_json::Value;

    const COMMAND_SIGNATURE_VERIFIER_ARTIFACT_V1: &[u8] =
        b"epoch-projection-admission-command-signature-verifier-test-artifact-v1";

    impl Clone for Governance {
        fn clone(&self) -> Self {
            Self {
                profile: self.profile.clone(),
                lanes: self.lanes.clone(),
                coordinators: self.coordinators.clone(),
                routes: self.routes.clone(),
                policy_registry: self.policy_registry.clone(),
                asset_policy_registry: self.asset_policy_registry.clone(),
                occurrence: self.occurrence.clone(),
                module_input: self.module_input.clone(),
            }
        }
    }

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
            semantic_version: "1.0.0-epoch-projection-admission-test".to_owned(),
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

    struct AcceptingModuleReceiptVerifier;

    impl LaneModuleSuccinctReceiptVerifierV1 for AcceptingModuleReceiptVerifier {
        fn verify_succinct_receipt(
            &self,
            receipt_bytes: &[u8],
            _expected_image_id: &RootV1,
            _expected_journal_bytes: &[u8],
        ) -> AbiResultV1<()> {
            if receipt_bytes.is_empty() {
                return Err(AbiErrorV1::InvalidBinding(
                    "epoch projection test receipt must not be empty",
                ));
            }
            Ok(())
        }
    }

    fn configured_governance(
        custody: Vec<EconomicAmountV1>,
    ) -> (
        Governance,
        EconomicCommandAuthorizationRegistryV1,
        EconomicCommandSignatureVerifierRegistryV1,
    ) {
        let mut governance = Governance::build(&Options::matching(custody));
        let signature_verifier_registry = signature_verifier_registry();
        let authorization_registry = authorization_registry(&governance.routes.routes[0]);
        let policy_registry = receipt_policy_registry(
            &authorization_registry,
            &signature_verifier_registry,
            &governance.asset_policy_registry,
        );
        let release_id = governance
            .lanes
            .release_for(LaneIdV1::ASSET_TRANSFER)
            .expect("asset release")
            .release_id
            .clone();
        let profile = profile_snapshot(
            &governance.lanes,
            &governance.coordinators,
            &governance.routes,
            policy_registry.registry_root().unwrap(),
            governance.profile.status,
            governance.profile.authority_epoch,
        );
        let occurrence = occurrence(&profile, &governance.routes.routes[0]);
        let module_input = module_input(
            &profile,
            &release_id,
            &occurrence,
            governance.module_input.custody.clone(),
        );
        governance.profile = profile;
        governance.policy_registry = policy_registry;
        governance.occurrence = occurrence;
        governance.module_input = module_input;
        governance.profile.validate().unwrap();
        governance.module_input.validate().unwrap();
        (
            governance,
            authorization_registry,
            signature_verifier_registry,
        )
    }

    fn authenticated_command(
        governance: &Governance,
        authorization_registry: &EconomicCommandAuthorizationRegistryV1,
        signature_verifier_registry: &EconomicCommandSignatureVerifierRegistryV1,
    ) -> AuthenticatedEconomicCommandV1 {
        let occurrence = &governance.occurrence;
        let authorization = authorization_registry
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
                &governance.module_input.command.command_kind,
                &governance.module_input.command,
            )
            .unwrap(),
            signer_key_id: authorization.signer_key_id.clone(),
            signer_public_key: authorization.signer_public_key.clone(),
            signature_algorithm: authorization.signature_algorithm.clone(),
            signature_bytes: b"epoch-projection-admission-test-signature".to_vec(),
        };
        let manifest = signature_verifier_manifest();
        let deployment = bind_economic_command_signature_verifier_deployment_v1(
            &signature_verifier_registry.releases[0],
            &manifest,
            COMMAND_SIGNATURE_VERIFIER_ARTIFACT_V1,
            &occurrence.deployment_root,
            &occurrence.profile_root,
            AcceptingCommandSignatureVerifierV1,
        )
        .unwrap();
        let authenticated_intent = authenticate_economic_command_intent_v1(
            &EconomicCommandAuthenticationCandidateV1 {
                profile: &governance.profile,
                routes: &governance.routes,
                policy_registry: &governance.policy_registry,
                authorization_registry,
                signature_verifier_registry,
                intent: &intent,
                envelope: &envelope,
            },
            &deployment,
        )
        .unwrap();
        bind_authenticated_intent_to_occurrence_v1(&authenticated_intent, occurrence).unwrap()
    }

    fn witness(
        governance: &Governance,
        authorization_registry: &EconomicCommandAuthorizationRegistryV1,
        signature_verifier_registry: &EconomicCommandSignatureVerifierRegistryV1,
        accepted: &AssetTransferLaneModuleAcceptedV1,
    ) -> VerifiedLaneModuleTransitionV1 {
        let authenticated = authenticated_command(
            governance,
            authorization_registry,
            signature_verifier_registry,
        );
        let release_route_binding = governance.bind_custody(accepted).unwrap();
        verify_asset_transfer_lane_module_custody_receipt_v1(
            AssetTransferLaneModuleReceiptCandidateV1 {
                profile: &governance.profile,
                policy_registry: &governance.policy_registry,
                asset_policy_registry: &governance.asset_policy_registry,
                lanes: &governance.lanes,
                coordinators: &governance.coordinators,
                routes: &governance.routes,
                authenticated_command: &authenticated,
                module_input: &governance.module_input,
                accepted,
                release_route_binding: &release_route_binding,
                receipt: LaneModuleReceiptEnvelopeV1 {
                    receipt_kind: ReceiptKindV1::SUCCINCT,
                    receipt_bytes: b"epoch-projection-admission-test-receipt",
                },
            },
            &AcceptingModuleReceiptVerifier,
        )
        .expect("custody witness must be admitted by the synthetic test backend")
    }

    fn empty_global_state() -> GlobalEconomicStateV1 {
        let fixture: Value = serde_json::from_str(include_str!(
            "../../../tests/data/global_accounting_allocation_projection_v1_golden.json"
        ))
        .expect("global state fixture JSON");
        serde_json::from_value(fixture["vectors"]["empty"]["state"].clone())
            .expect("empty global state")
    }

    fn source_state(
        accepted: &AssetTransferLaneModuleAcceptedV1,
        governance: &Governance,
    ) -> GlobalEconomicStateV1 {
        let journal = &accepted.module_journal;
        let private_pre = &accepted.private_port.pre_state;
        let mut source = empty_global_state();
        source.chain_id = journal.chain_id.clone();
        source.deployment_root = journal.deployment_root.clone();
        source.profile_root = journal.profile_root.clone();
        source.writer_epoch = journal.writer_epoch;
        source.height = governance
            .occurrence
            .height
            .checked_sub(1)
            .expect("epoch fixture height nonzero");
        source.lane_roots[0] = LaneStateRootV1 {
            lane_id: LaneIdV1::ASSET_TRANSFER,
            module_release_id: journal.module_release_id.clone(),
            enabled: true,
            state_root: private_pre.state_root().unwrap(),
        };
        source.balances = private_pre.balances.clone();
        source.custody = private_pre.custody.clone();
        source.supplies = private_pre.supplies.clone();
        source.liabilities = vec![EconomicAmountV1 {
            owner: "alice".to_owned(),
            asset: "USD".to_owned(),
            custody_domain: "escrow".to_owned(),
            amount_atoms: private_pre.custody.iter().map(|row| row.amount_atoms).sum(),
        }];
        source.validate().unwrap();
        source
    }

    fn current_state(
        predecessor: &GlobalEconomicStateV1,
        occurrence: &EconomicCommandOccurrenceV1,
        accepted: &AssetTransferLaneModuleAcceptedV1,
        insert_replay: bool,
    ) -> GlobalEconomicStateV1 {
        let mut current = predecessor.clone();
        current.height = occurrence.height;
        current.lane_roots[0].state_root = accepted.private_port.post_state.state_root().unwrap();
        current.balances = accepted.private_port.post_state.balances.clone();
        current.supplies = accepted.private_port.post_state.supplies.clone();
        if insert_replay {
            current.replay_state.push(ReplayStateV1 {
                replay_id: occurrence.replay_id().unwrap().as_str().to_owned(),
                occurrence_id: occurrence.occurrence_id().unwrap(),
            });
        }
        current
            .replay_state
            .sort_by(|left, right| left.replay_id.cmp(&right.replay_id));
        current.validate().unwrap();
        current
    }

    struct EpochFixture {
        governance: Governance,
        source: GlobalEconomicStateV1,
        predecessor: GlobalEconomicStateV1,
        current: GlobalEconomicStateV1,
        accepted: AssetTransferLaneModuleAcceptedV1,
        witness: VerifiedLaneModuleTransitionV1,
    }

    fn epoch_fixture(replay_state: Vec<ReplayStateV1>, insert_replay: bool) -> EpochFixture {
        let (mut governance, authorization_registry, signature_verifier_registry) =
            configured_governance(custody_rows(7));
        let initial_accepted = governance.custody_accepted();
        let mut source = source_state(&initial_accepted, &governance);
        source.replay_state = replay_state;
        source
            .replay_state
            .sort_by(|left, right| left.replay_id.cmp(&right.replay_id));
        source.validate().unwrap();
        governance.occurrence.pre_state_root = source.state_root().unwrap();
        governance.module_input.context.command_occurrence_id =
            governance.occurrence.occurrence_id().unwrap();
        let accepted = governance.custody_accepted();
        let witness = witness(
            &governance,
            &authorization_registry,
            &signature_verifier_registry,
            &accepted,
        );
        let current = current_state(&source, &governance.occurrence, &accepted, insert_replay);
        EpochFixture {
            governance,
            source: source.clone(),
            predecessor: source,
            current,
            accepted,
            witness,
        }
    }

    fn second_epoch_fixture(first: &EpochFixture) -> EpochFixture {
        let (authorization_registry, signature_verifier_registry) = {
            let (_, authorization_registry, signature_verifier_registry) =
                configured_governance(first.governance.module_input.custody.clone());
            (authorization_registry, signature_verifier_registry)
        };
        let mut governance = first.governance.clone();
        governance.occurrence.tx_index += 1;
        governance.occurrence.nonce += 1;
        governance.occurrence.pre_state_root = first.current.state_root().unwrap();
        governance.module_input.pre_state = first.accepted.post_state.clone();
        governance.module_input.context.command_occurrence_id =
            governance.occurrence.occurrence_id().unwrap();
        let accepted = governance.custody_accepted();
        let witness = witness(
            &governance,
            &authorization_registry,
            &signature_verifier_registry,
            &accepted,
        );
        let current = current_state(&first.current, &governance.occurrence, &accepted, true);
        EpochFixture {
            governance,
            source: first.source.clone(),
            predecessor: first.current.clone(),
            current,
            accepted,
            witness,
        }
    }

    fn admit(
        fixture: &EpochFixture,
        occurrence_index: usize,
    ) -> Result<VerifiedLaneAllocationFragmentV1, GlobalAssetTransferFragmentAdmissionRejectedV1>
    {
        verify_asset_transfer_epoch_fragment_receipt_v1(
            &fixture.witness,
            AssetTransferGlobalAllocationCandidateV1 {
                accepted: &fixture.accepted,
                occurrence: &fixture.governance.occurrence,
                predecessor: &fixture.predecessor,
                current: &fixture.current,
            },
            AssetTransferEpochPositionV1 {
                epoch_source: &fixture.source,
                occurrence_index,
            },
        )
        .expect("epoch allocation boundary must return a typed result")
    }

    fn assert_full_frame_preserved(
        predecessor: &GlobalEconomicStateV1,
        current: &GlobalEconomicStateV1,
        accepted: &AssetTransferLaneModuleAcceptedV1,
    ) {
        assert_eq!(current.chain_id, predecessor.chain_id);
        assert_eq!(current.deployment_root, predecessor.deployment_root);
        assert_eq!(current.profile_root, predecessor.profile_root);
        assert_eq!(current.writer_epoch, predecessor.writer_epoch);
        assert_eq!(current.lane_roots[1..], predecessor.lane_roots[1..]);
        assert_eq!(current.custody, predecessor.custody);
        assert_eq!(current.liabilities, predecessor.liabilities);
        assert_eq!(current.reserves, predecessor.reserves);
        assert_eq!(current.oracle_occurrences, predecessor.oracle_occurrences);
        assert_eq!(
            current.terminal_obligations,
            predecessor.terminal_obligations
        );
        assert_eq!(current.history_root, predecessor.history_root);
        assert_eq!(current.outbox, predecessor.outbox);
        assert_eq!(
            current.lane_roots[0].state_root,
            accepted.private_port.post_state.state_root().unwrap()
        );
    }

    #[test]
    fn first_and_second_positions_admit_real_custody_transfers_and_preserve_the_frame() {
        let first = epoch_fixture(Vec::new(), true);
        let first_before = (first.predecessor.clone(), first.current.clone());
        let first_fragment = admit(&first, 0).expect("first position admits");
        assert_full_frame_preserved(&first.predecessor, &first.current, &first.accepted);
        assert_eq!(
            first_fragment.fragment().lane_state_root,
            first.current.lane_roots[0].state_root
        );
        assert_eq!(
            (first.predecessor.clone(), first.current.clone()),
            first_before
        );

        let second = second_epoch_fixture(&first);
        let second_before = (second.predecessor.clone(), second.current.clone());
        let second_fragment = admit(&second, 1).expect("second position admits");
        assert_eq!(second.predecessor.height, first.current.height);
        assert_full_frame_preserved(&second.predecessor, &second.current, &second.accepted);
        assert_eq!(
            second_fragment.fragment().lane_state_root,
            second.current.lane_roots[0].state_root
        );
        assert_eq!(
            (second.predecessor.clone(), second.current.clone()),
            second_before
        );
    }

    #[test]
    fn allocation_guards_reject_replay_identity_collision_and_capacity_before_projection() {
        let base = epoch_fixture(Vec::new(), true);
        let replay_id = base.governance.occurrence.replay_id().unwrap();
        let mut duplicate_rows = vec![ReplayStateV1 {
            replay_id: replay_id.as_str().to_owned(),
            occurrence_id: root(0xabc),
        }];
        duplicate_rows.sort_by(|left, right| left.replay_id.cmp(&right.replay_id));
        let duplicate = epoch_fixture(duplicate_rows, false);
        assert_eq!(duplicate.predecessor.replay_state.len(), 1);
        assert_eq!(
            duplicate.predecessor.replay_state[0].replay_id,
            duplicate
                .governance
                .occurrence
                .replay_id()
                .unwrap()
                .as_str()
        );
        assert_ne!(
            duplicate.predecessor.replay_state[0].occurrence_id,
            duplicate.governance.occurrence.occurrence_id().unwrap()
        );
        let duplicate_before = (duplicate.predecessor.clone(), duplicate.current.clone());
        let duplicate_result = admit(&duplicate, 0).expect_err("duplicate replay must reject");
        assert_eq!(
            duplicate_result,
            GlobalAssetTransferFragmentAdmissionRejectedV1::Binding(
                GlobalAllocationBindingRejectCodeV1::GLOBAL_REPLAY_CONTINUITY_DRIFT
            )
        );
        assert_eq!(
            (duplicate.predecessor.clone(), duplicate.current.clone()),
            duplicate_before
        );

        let capacity_rows = (0..MAX_GLOBAL_REPLAY_ROWS_V1)
            .map(|index| ReplayStateV1 {
                replay_id: format!("epoch-replay-{index:04}"),
                occurrence_id: root(0x1000 + u64::try_from(index).unwrap()),
            })
            .collect();
        let capacity = epoch_fixture(capacity_rows, false);
        assert_eq!(
            capacity.predecessor.replay_state.len(),
            MAX_GLOBAL_REPLAY_ROWS_V1
        );
        assert_eq!(
            capacity.current.replay_state,
            capacity.predecessor.replay_state
        );
        let new_replay = capacity.governance.occurrence.replay_id().unwrap();
        let new_occurrence = capacity.governance.occurrence.occurrence_id().unwrap();
        assert!(capacity.predecessor.replay_state.iter().all(|row| {
            row.replay_id != new_replay.as_str() && row.occurrence_id != new_occurrence
        }));
        let capacity_before = (capacity.predecessor.clone(), capacity.current.clone());
        let capacity_result = admit(&capacity, 0).expect_err("full replay table must reject");
        assert_eq!(
            capacity_result,
            GlobalAssetTransferFragmentAdmissionRejectedV1::Binding(
                GlobalAllocationBindingRejectCodeV1::GLOBAL_REPLAY_CONTINUITY_DRIFT
            )
        );
        assert_eq!(
            (capacity.predecessor.clone(), capacity.current.clone()),
            capacity_before
        );
    }

    #[test]
    fn occurrence_guard_precedes_projection_and_preserves_exact_rejection_precedence() {
        let mut fixture = epoch_fixture(Vec::new(), true);
        fixture.current.height += 1;
        fixture.current.validate().unwrap();
        let result = admit(&fixture, 0).expect_err("height drift must reject");
        assert_eq!(
            result,
            GlobalAssetTransferFragmentAdmissionRejectedV1::Binding(
                GlobalAllocationBindingRejectCodeV1::GLOBAL_OCCURRENCE_DRIFT
            )
        );
    }
}
