use tau_state_proof_risc0_shared::{
    compose_spot_recursive_leaf_summary_v1, DexBalanceEntryV1, DexIntentV1, DexPoolEntryV1,
    DexSnapshotV1, DexStateV1, FeeAccumulatorV1, ProtocolFeeConfig, SignedIntentV1,
    SpotRecursiveLeafInputV1, StateProofInputV1, SwapExactInIntentV1, TauTxAppOpsV1, TauTxV1,
    TxIngressFactV1,
};
use zenodex_zrpf_protocol_v3::{
    decode_exact_settlement_admission_journal_v1, decode_exact_settlement_effect_plan_v2,
    derive_sparse_merkle_root_v1, encode_node_journal_v3, encode_value_aggregate_proposal_v5,
    ApplicationIdV3, CommitmentV3, DomainIdV3, FullBlobDataAvailabilityCertificateInputV1,
    FullBlobDataAvailabilityCertificateV1, ProfileIdV3, ProgramIdV3, ProposedValueAggregateV5,
    SparseMerkleCellTransitionWitnessInputV1, SparseMerkleCellTransitionWitnessV1,
    SparseMerkleSiblingPathV1, ValueAggregateChildDescriptorInputV5,
    ValueAggregateChildDescriptorV5, ValueAggregateOperationalCommitmentsInputV5,
    ValueAggregateOperationalCommitmentsV5, ValueAggregateProposalInputV5, ValueHashV2,
    MAX_FULL_BLOB_DA_BYTES_V1, SPARSE_MERKLE_TREE_DEPTH_V1, SPARSE_MERKLE_WITNESS_VERSION_V1,
};
use zenodex_zrpf_risc0_semantic_shared::{
    derive_spot_settlement_projection_v1, propose_spot_settlement_state_projection_v2,
    OrdinarySpotSettlementGuestInputV2, OrdinarySpotSettlementReplayDataV2,
    SpotSettlementAuthorizationInputV1,
};
use zenodex_zrpf_risc0_shared::{project_policy_bound_v2_journal, source_policy_v2, SourceKindV2};
use zenodex_zrpf_risc0_spot_settlement_v6_shared::{
    compose_source_opened_spot_settlement_output_after_l2_verification_v3,
    decode_exact_source_opened_spot_settlement_guest_envelope_v3,
    decode_exact_source_opened_spot_settlement_replay_v3,
    encode_source_opened_spot_settlement_guest_input_v3,
    encode_source_opened_spot_settlement_replay_v3,
    source_opened_spot_settlement_replay_schema_id_v3,
    validate_singleton_source_opened_spot_relation_v6, SourceOpenedSpotSettlementErrorV6,
    SourceOpenedSpotSettlementGuestInputV3, MAX_SOURCE_OPENED_SPOT_SETTLEMENT_GUEST_INPUT_BYTES_V3,
};
use zenodex_zrpf_risc0_spot_value_aggregate_l1_policy_v6::pinned_source_opened_spot_value_leaf_identity_v6;
use zenodex_zrpf_risc0_spot_value_aggregate_l2_policy_v6::pinned_source_opened_spot_value_aggregate_l1_identity_v6;
use zenodex_zrpf_risc0_spot_value_leaf_v6_shared::{
    encode_source_opened_spot_value_leaf_statement_v6,
    recompose_source_opened_spot_value_leaf_statement_v6, SourceOpenedSpotValueLeafEnvelopeV6,
    SourceOpenedSpotValueLeafStatementV6, PINNED_SOURCE_OPENED_V6_ADAPTER_IMAGE_ID,
};
use zenodex_zrpf_risc0_value_aggregate_shared::{
    recompose_expected_source_opened_spot_value_aggregate_level_one_v6,
    recompose_expected_value_aggregate_level_two_v5, ValueAggregateLevelOneInputV5,
    ValueAggregateLevelTwoInputV5, ValueAggregateRecompositionPolicyV5,
};

const ASSET0: &str = "0x1111111111111111111111111111111111111111111111111111111111111111";
const ASSET1: &str = "0x2222222222222222222222222222222222222222222222222222222222222222";
const SENDER: &str =
    "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
const RECIPIENT: &str =
    "0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";
const POOL_ID: &str = "0xcc9c112f06b5ba4cd276419759e7b3e203ede2c64aa45ba75e24fa4609d9c686";

struct Fixture {
    source: SourceOpenedSpotValueLeafEnvelopeV6,
    statement: SourceOpenedSpotValueLeafStatementV6,
    proposal: ProposedValueAggregateV5,
    authorization: SpotSettlementAuthorizationInputV1,
    witness: SparseMerkleCellTransitionWitnessV1,
}

impl Fixture {
    fn new() -> Self {
        let source = source_envelope();
        let statement = recompose_source_opened_spot_value_leaf_statement_v6(&source).unwrap();
        let proposal = l2_proposal(&statement);
        let authorization = SpotSettlementAuthorizationInputV1 {
            authorization_subject_id: statement.authorization_subject_id(),
            authorization_scope_id: statement.authorization_scope_id(),
            authorization_nonce: statement.authorization_nonce(),
            authorization_grant_id: statement.authorization_grant_id(),
        };
        let witness = settlement_witness(&proposal, authorization);
        Self {
            source,
            statement,
            proposal,
            authorization,
            witness,
        }
    }

    fn replay_bytes(&self) -> Vec<u8> {
        let base = OrdinarySpotSettlementReplayDataV2::recompose(
            &self.proposal,
            self.authorization,
            &self.witness,
        )
        .unwrap();
        encode_source_opened_spot_settlement_replay_v3(&base, &self.source).unwrap()
    }

    fn input_with_blob(&self, blob: &[u8]) -> SourceOpenedSpotSettlementGuestInputV3 {
        let certificate = da_certificate(&self.proposal, blob);
        let base = OrdinarySpotSettlementGuestInputV2::new(
            encode_value_aggregate_proposal_v5(&self.proposal).unwrap(),
            self.authorization,
            self.witness.clone(),
            certificate,
        )
        .unwrap();
        SourceOpenedSpotSettlementGuestInputV3::new(base, self.source.clone()).unwrap()
    }

    fn input(&self) -> SourceOpenedSpotSettlementGuestInputV3 {
        self.input_with_blob(&self.replay_bytes())
    }
}

#[test]
fn exact_source_l1_l2_da_and_admission_journal_round_trip() {
    let fixture = Fixture::new();
    let input = fixture.input();
    let bytes = encode_source_opened_spot_settlement_guest_input_v3(&input).unwrap();
    let envelope = decode_exact_source_opened_spot_settlement_guest_envelope_v3(&bytes).unwrap();
    assert_eq!(envelope.proposal_bytes(), input.base().proposal_bytes());
    let output = compose_source_opened_spot_settlement_output_after_l2_verification_v3(
        &input,
        commitment(201),
    )
    .unwrap();
    let admission = decode_exact_settlement_admission_journal_v1(&output).unwrap();
    assert_eq!(admission.action_count(), 1);
    assert_eq!(admission.consumed_object_count(), 1);
    let plan = decode_exact_settlement_effect_plan_v2(admission.effect_plan_bytes()).unwrap();
    assert_eq!(
        plan.economic_action_batch().actions()[0]
            .record()
            .consumed_object_ids(),
        &[fixture.statement.semantic_subtree().leaf_records()[0].transaction_root()]
    );
}

#[test]
fn exact_replay_opening_round_trip_exposes_only_proposed_source_bytes() {
    let fixture = Fixture::new();
    let bytes = fixture.replay_bytes();
    let replay = decode_exact_source_opened_spot_settlement_replay_v3(&bytes).unwrap();

    assert_eq!(replay.source(), &fixture.source);
    assert_eq!(replay.source().assigned_leaf_ordinal(), 0);
    assert_eq!(
        replay.source().source_input_bytes(),
        fixture.source.source_input_bytes()
    );
    assert_eq!(
        replay.source().source_journal_bytes(),
        fixture.source.source_journal_bytes()
    );
    assert_eq!(
        replay.base().settlement_effect_plan_bytes(),
        OrdinarySpotSettlementReplayDataV2::recompose(
            &fixture.proposal,
            fixture.authorization,
            &fixture.witness,
        )
        .unwrap()
        .settlement_effect_plan_bytes()
    );
}

#[test]
fn replay_opening_framing_and_inner_mutations_fail_closed() {
    let fixture = Fixture::new();
    let canonical = fixture.replay_bytes();

    for end in 0..canonical.len() {
        assert!(decode_exact_source_opened_spot_settlement_replay_v3(&canonical[..end]).is_err());
    }

    let mut trailing = canonical.clone();
    trailing.push(0);
    assert!(matches!(
        decode_exact_source_opened_spot_settlement_replay_v3(&trailing),
        Err(SourceOpenedSpotSettlementErrorV6::TrailingBytes)
    ));

    let mut wrong_version = canonical.clone();
    wrong_version[..2].copy_from_slice(&4_u16.to_be_bytes());
    assert!(matches!(
        decode_exact_source_opened_spot_settlement_replay_v3(&wrong_version),
        Err(SourceOpenedSpotSettlementErrorV6::InvalidVersion(4))
    ));

    let mut empty_base = canonical.clone();
    empty_base[2..6].copy_from_slice(&0_u32.to_be_bytes());
    assert!(matches!(
        decode_exact_source_opened_spot_settlement_replay_v3(&empty_base),
        Err(SourceOpenedSpotSettlementErrorV6::EmptyComponent(
            "base replay"
        ))
    ));

    let mut changed_source = canonical;
    let base_length = u32::from_be_bytes(changed_source[2..6].try_into().unwrap()) as usize;
    let source_offset = 2 + 4 + base_length + 4;
    changed_source[source_offset] ^= 1;
    assert!(decode_exact_source_opened_spot_settlement_replay_v3(&changed_source).is_err());

    assert!(matches!(
        decode_exact_source_opened_spot_settlement_replay_v3(&vec![
            0;
            MAX_FULL_BLOB_DA_BYTES_V1 + 1
        ]),
        Err(SourceOpenedSpotSettlementErrorV6::InputTooLarge { .. })
    ));
}

#[test]
fn caller_selected_authorization_rejects() {
    let fixture = Fixture::new();
    let mut authorization = fixture.authorization;
    authorization.authorization_nonce = authorization.authorization_nonce.checked_add(1).unwrap();
    let base = OrdinarySpotSettlementGuestInputV2::new(
        encode_value_aggregate_proposal_v5(&fixture.proposal).unwrap(),
        authorization,
        fixture.witness.clone(),
        da_certificate(&fixture.proposal, &fixture.replay_bytes()),
    )
    .unwrap();
    assert!(matches!(
        SourceOpenedSpotSettlementGuestInputV3::new(base, fixture.source),
        Err(SourceOpenedSpotSettlementErrorV6::InvalidSingletonRelation(
            "source-bound authorization"
        ))
    ));
}

#[test]
fn every_l2_child_descriptor_identity_mutation_rejects() {
    let fixture = Fixture::new();
    let child = &fixture.proposal.children()[0];
    let mut inputs = Vec::new();
    let baseline = child_input(child);

    let mut value = baseline.clone();
    value.verified_program_id = ProgramIdV3::new([121; 32]).unwrap();
    inputs.push(value);
    let mut value = baseline.clone();
    value.proof_profile_id = ProfileIdV3::new([122; 32]).unwrap();
    inputs.push(value);
    let mut value = baseline.clone();
    value.program_manifest_root = commitment(123);
    inputs.push(value);
    let mut value = baseline.clone();
    value.journal_hash = commitment(124);
    inputs.push(value);
    let mut value = baseline.clone();
    value.claim_binding = commitment(125);
    inputs.push(value);
    let mut value = baseline.clone();
    value.semantic_subtree_root = commitment(126);
    inputs.push(value);
    let mut value = baseline;
    let operational = value.operational_commitments;
    value.operational_commitments =
        ValueAggregateOperationalCommitmentsV5::new(ValueAggregateOperationalCommitmentsInputV5 {
            data_availability_root: operational.data_availability_root(),
            data_availability_certificate_root: operational.data_availability_certificate_root(),
            conflict_schedule_root: operational.conflict_schedule_root(),
            cross_lane_outbox_root: operational.cross_lane_outbox_root(),
            cross_lane_inbox_root: operational.cross_lane_inbox_root(),
            cross_lane_message_ids_root: operational.cross_lane_message_ids_root(),
            carry_queue_pre_root: commitment(127),
            carry_queue_post_root: operational.carry_queue_post_root(),
        })
        .unwrap();
    inputs.push(value);

    for input in inputs {
        let mutated = ProposedValueAggregateV5::derive(ValueAggregateProposalInputV5 {
            aggregate_level: 2,
            scope: fixture.proposal.scope().clone(),
            semantic_subtree: fixture.proposal.semantic_subtree().clone(),
            children: vec![ValueAggregateChildDescriptorV5::new(input).unwrap()],
        })
        .unwrap();
        assert!(
            validate_singleton_source_opened_spot_relation_v6(&mutated, &fixture.source).is_err()
        );
    }
}

#[test]
fn wrong_da_blob_carry_mutation_and_framing_fail_closed() {
    let fixture = Fixture::new();
    let mut wrong_blob = fixture.replay_bytes();
    let last = wrong_blob.len() - 1;
    wrong_blob[last] ^= 1;
    let input = fixture.input_with_blob(&wrong_blob);
    assert!(
        compose_source_opened_spot_settlement_output_after_l2_verification_v3(
            &input,
            commitment(201)
        )
        .is_err()
    );

    let canonical = encode_source_opened_spot_settlement_guest_input_v3(&fixture.input()).unwrap();
    for end in 0..canonical.len() {
        assert!(
            decode_exact_source_opened_spot_settlement_guest_envelope_v3(&canonical[..end])
                .is_err()
        );
    }
    let mut trailing = canonical;
    trailing.push(0);
    assert!(decode_exact_source_opened_spot_settlement_guest_envelope_v3(&trailing).is_err());
    assert!(
        decode_exact_source_opened_spot_settlement_guest_envelope_v3(&vec![
            0;
            MAX_SOURCE_OPENED_SPOT_SETTLEMENT_GUEST_INPUT_BYTES_V3
                + 1
        ])
        .is_err()
    );
}

fn l2_proposal(statement: &SourceOpenedSpotValueLeafStatementV6) -> ProposedValueAggregateV5 {
    let l1_input = ValueAggregateLevelOneInputV5::new(vec![
        encode_source_opened_spot_value_leaf_statement_v6(statement).unwrap(),
    ])
    .unwrap();
    let l1_policy = ValueAggregateRecompositionPolicyV5::new(
        statement.structural_adapter_journal().scope().clone(),
        vec![pinned_source_opened_spot_value_leaf_identity_v6().unwrap()],
    )
    .unwrap();
    let l1 =
        recompose_expected_source_opened_spot_value_aggregate_level_one_v6(&l1_input, &l1_policy)
            .unwrap();
    let l2_input =
        ValueAggregateLevelTwoInputV5::new(vec![encode_value_aggregate_proposal_v5(&l1).unwrap()])
            .unwrap();
    let l2_policy = ValueAggregateRecompositionPolicyV5::new(
        l1.scope().clone(),
        vec![pinned_source_opened_spot_value_aggregate_l1_identity_v6().unwrap()],
    )
    .unwrap();
    recompose_expected_value_aggregate_level_two_v5(&l2_input, &l2_policy).unwrap()
}

fn child_input(child: &ValueAggregateChildDescriptorV5) -> ValueAggregateChildDescriptorInputV5 {
    ValueAggregateChildDescriptorInputV5 {
        child_level: child.child_level(),
        partition: child.partition(),
        verified_program_id: child.verified_program_id(),
        proof_profile_id: child.proof_profile_id(),
        program_manifest_root: child.program_manifest_root(),
        journal_hash: child.journal_hash(),
        claim_binding: child.claim_binding(),
        semantic_subtree_root: child.semantic_subtree_root(),
        operational_commitments: child.operational_commitments(),
    }
}

fn source_envelope() -> SourceOpenedSpotValueLeafEnvelopeV6 {
    let input = source_input();
    let summary = compose_spot_recursive_leaf_summary_v1(input.clone()).unwrap();
    let source_journal_bytes = postcard::to_allocvec(&summary).unwrap();
    let adapter = project_policy_bound_v2_journal(
        SourceKindV2::Spot,
        &source_journal_bytes,
        0,
        PINNED_SOURCE_OPENED_V6_ADAPTER_IMAGE_ID,
    )
    .unwrap();
    SourceOpenedSpotValueLeafEnvelopeV6::new(
        0,
        encode_node_journal_v3(&adapter.journal).unwrap(),
        postcard::to_allocvec(&input).unwrap(),
        source_journal_bytes,
    )
    .unwrap()
}

fn source_input() -> SpotRecursiveLeafInputV1 {
    let snapshot = DexSnapshotV1 {
        version: 1,
        balances: vec![DexBalanceEntryV1 {
            pubkey: SENDER.into(),
            asset: ASSET0.into(),
            amount: 1_000,
        }],
        pools: vec![DexPoolEntryV1 {
            pool_id: POOL_ID.into(),
            asset0: ASSET0.into(),
            asset1: ASSET1.into(),
            reserve0: 10_000,
            reserve1: 10_000,
            fee_bps: 30,
            lp_supply: 10_000,
            status: "ACTIVE".into(),
            created_at: 0,
        }],
        lp_balances: vec![],
        fee_accumulator: FeeAccumulatorV1 { dust: 0 },
        vault: None,
        oracle: None,
    };
    let pre = DexStateV1::from_snapshot(snapshot.clone())
        .unwrap()
        .canonical_app_hash_sha256();
    let transaction = TauTxV1 {
        sender_pubkey: SENDER.into(),
        app_ops: TauTxAppOpsV1 {
            has_faucet: false,
            faucet_mint: vec![],
            has_intents: true,
            intents: vec![SignedIntentV1 {
                signature: None,
                intent: DexIntentV1::SwapExactIn(SwapExactInIntentV1 {
                    module: "TauSwap".into(),
                    version: "v1".into(),
                    intent_id: "settlement-v6-swap".into(),
                    sender_pubkey: SENDER.into(),
                    deadline: 100,
                    pool_id: POOL_ID.into(),
                    asset_in: ASSET0.into(),
                    asset_out: ASSET1.into(),
                    amount_in: 1_000,
                    min_amount_out: 900,
                    recipient: RECIPIENT.into(),
                    salt: None,
                }),
            }],
        },
    };
    let mut post_state = DexStateV1::from_snapshot(snapshot.clone()).unwrap();
    post_state
        .apply_tx(&transaction, 1, &ProtocolFeeConfig::default())
        .unwrap();
    let post = post_state.canonical_app_hash_sha256();
    SpotRecursiveLeafInputV1 {
        chain_id: "tau-devnet-zrpf-source-opened".into(),
        epoch_id: 1,
        lane_id: "spot-source-opened-lane-0001".into(),
        risc0_image_id: source_policy_v2(SourceKindV2::Spot).unwrap().image_id,
        public_policy_hash: [8; 32],
        feature_suite_hash: [9; 32],
        dependency_lock_hash: [10; 32],
        toolchain_lock_hash: [11; 32],
        spot_input: StateProofInputV1 {
            state_hash: post,
            block_timestamp: 1,
            pre_app_hash_present: true,
            pre_app_hash: pre,
            pre_state: snapshot,
            txs: vec![transaction],
            pre_nonces: vec![],
            tx_ingress: vec![TxIngressFactV1 {
                sender_pubkey: SENDER.into(),
                nonce: 0,
            }],
            chain_balances_post: vec![],
            expected_post_app_hash: post,
            protocol_fee_share_bps: 0,
            protocol_fee_recipient_pubkey: None,
            tx_execution_order: vec![0],
            route_price_intervals: vec![],
            route_price_interval_authority: None,
            route_price_interval_authority_policy: None,
            route_price_interval_max_width_bps: None,
            shared_pool_frontier_signature_certificates: vec![],
        },
    }
}

fn settlement_witness(
    proposal: &ProposedValueAggregateV5,
    authorization: SpotSettlementAuthorizationInputV1,
) -> SparseMerkleCellTransitionWitnessV1 {
    let projection = derive_spot_settlement_projection_v1(proposal, authorization).unwrap();
    let cell_key = projection.cell_key();
    let pre_value_hash = ValueHashV2::new(
        proposal
            .semantic_subtree()
            .raw_subtree_pre_state_root()
            .into_bytes(),
    );
    let post_value_hash = ValueHashV2::new(
        proposal
            .semantic_subtree()
            .raw_subtree_post_state_root()
            .into_bytes(),
    );
    let siblings = SparseMerkleSiblingPathV1::new([commitment(90); SPARSE_MERKLE_TREE_DEPTH_V1]);
    let pre_root = derive_sparse_merkle_root_v1(cell_key, pre_value_hash, &siblings).unwrap();
    let post_root = derive_sparse_merkle_root_v1(cell_key, post_value_hash, &siblings).unwrap();
    let proposed =
        propose_spot_settlement_state_projection_v2(proposal, authorization, pre_root, post_root)
            .unwrap();
    SparseMerkleCellTransitionWitnessV1::new(SparseMerkleCellTransitionWitnessInputV1 {
        witness_version: SPARSE_MERKLE_WITNESS_VERSION_V1,
        economic_action_id: proposed.economic_action_id(),
        cell_key,
        pre_value_hash,
        post_value_hash,
        sibling_commitments: siblings,
        claimed_pre_root: pre_root,
        claimed_post_root: post_root,
    })
    .unwrap()
}

fn da_certificate(
    proposal: &ProposedValueAggregateV5,
    blob: &[u8],
) -> FullBlobDataAvailabilityCertificateV1 {
    assert!(blob.len() <= MAX_FULL_BLOB_DA_BYTES_V1);
    FullBlobDataAvailabilityCertificateV1::derive(FullBlobDataAvailabilityCertificateInputV1 {
        application_id: ApplicationIdV3::new(proposal.scope().application_id().into_bytes())
            .unwrap(),
        chain_or_domain_id: DomainIdV3::new(proposal.scope().chain_or_domain_id().into_bytes())
            .unwrap(),
        epoch_id: proposal.scope().epoch_start(),
        data_schema_id: source_opened_spot_settlement_replay_schema_id_v3().unwrap(),
        blob,
        retention_through_epoch: proposal.scope().epoch_start() + 10,
        storage_policy_hash: proposal.scope().public_policy_hash(),
    })
    .unwrap()
}

fn commitment(seed: u8) -> CommitmentV3 {
    CommitmentV3::new([seed.max(1); 32]).unwrap()
}
