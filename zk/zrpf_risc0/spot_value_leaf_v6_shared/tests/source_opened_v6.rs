use tau_state_proof_risc0_shared::{
    compose_spot_recursive_leaf_summary_v1, DexBalanceEntryV1, DexIntentV1, DexPoolEntryV1,
    DexSnapshotV1, DexStateV1, FeeAccumulatorV1, NonceEntryV1, ProtocolFeeConfig, SignedIntentV1,
    SpotRecursiveLeafInputV1, StateProofInputV1, SwapExactInIntentV1, TauTxAppOpsV1, TauTxV1,
    TxIngressFactV1,
};
use zenodex_zrpf_protocol_v3::{
    encode_node_journal_v3, merge_semantic_subtrees_v2, ValueNodeErrorV4,
};
use zenodex_zrpf_risc0_shared::{project_policy_bound_v2_journal, source_policy_v2, SourceKindV2};
use zenodex_zrpf_risc0_spot_value_leaf_v6_shared::{
    decode_exact_source_opened_spot_value_leaf_input_v6,
    decode_exact_source_opened_spot_value_leaf_statement_v6,
    encode_source_opened_spot_value_leaf_input_v6,
    encode_source_opened_spot_value_leaf_statement_v6,
    recompose_source_opened_spot_value_leaf_statement_v6, SourceOpenedSpotValueLeafEnvelopeV6,
    SourceOpenedSpotValueLeafErrorV6, SourceOpenedSpotValueLeafStatementV6,
    PINNED_SOURCE_OPENED_V6_ADAPTER_IMAGE_ID,
};

const ASSET0: &str = "0x1111111111111111111111111111111111111111111111111111111111111111";
const ASSET1: &str = "0x2222222222222222222222222222222222222222222222222222222222222222";
const SENDER: &str =
    "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
const RECIPIENT: &str =
    "0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";
const POOL_ID: &str = "0xcc9c112f06b5ba4cd276419759e7b3e203ede2c64aa45ba75e24fa4609d9c686";

fn fixture(intent_id: &str, ordinal: u64) -> SourceOpenedSpotValueLeafEnvelopeV6 {
    envelope_from_input(source_input(intent_id), ordinal)
}

fn source_input(intent_id: &str) -> SpotRecursiveLeafInputV1 {
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
                    intent_id: intent_id.into(),
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

fn envelope_from_input(
    input: SpotRecursiveLeafInputV1,
    ordinal: u64,
) -> SourceOpenedSpotValueLeafEnvelopeV6 {
    let summary = compose_spot_recursive_leaf_summary_v1(input.clone()).unwrap();
    let source_input_bytes = postcard::to_allocvec(&input).unwrap();
    let source_journal_bytes = postcard::to_allocvec(&summary).unwrap();
    let adapter = project_policy_bound_v2_journal(
        SourceKindV2::Spot,
        &source_journal_bytes,
        ordinal,
        PINNED_SOURCE_OPENED_V6_ADAPTER_IMAGE_ID,
    )
    .unwrap();
    SourceOpenedSpotValueLeafEnvelopeV6::new(
        ordinal,
        encode_node_journal_v3(&adapter.journal).unwrap(),
        source_input_bytes,
        source_journal_bytes,
    )
    .unwrap()
}

fn statement(
    envelope: &SourceOpenedSpotValueLeafEnvelopeV6,
) -> SourceOpenedSpotValueLeafStatementV6 {
    recompose_source_opened_spot_value_leaf_statement_v6(envelope).unwrap()
}

#[test]
fn source_opened_swap_derives_balanced_flows_and_topology_independent_nullifier() {
    let left = statement(&fixture("swap-1", 0));
    let right = statement(&fixture("swap-1", 7));
    let record = &left.semantic_subtree().leaf_records()[0];
    let flows = left.semantic_subtree().asset_flows();

    assert_eq!(flows.len(), 2);
    assert_eq!(flows[0].outflow_atoms(), 1_000);
    assert_eq!(flows[0].inflow_atoms(), 1_000);
    assert_eq!(flows[1].outflow_atoms(), 906);
    assert_eq!(flows[1].inflow_atoms(), 906);
    assert_ne!(
        record.transaction_root(),
        left.source_transaction_commitment()
    );
    assert_eq!(
        record.transaction_root(),
        right.semantic_subtree().leaf_records()[0].transaction_root()
    );
    assert_eq!(left.action_nullifier_root(), right.action_nullifier_root());
    assert_eq!(left.carry_queue_pre_root(), left.carry_queue_post_root());
    left.operational_commitments_v5().unwrap();
}

#[test]
fn canonical_input_and_statement_round_trip_exactly() {
    let input = fixture("swap-1", 0);
    let input_bytes = encode_source_opened_spot_value_leaf_input_v6(&input).unwrap();
    assert_eq!(
        decode_exact_source_opened_spot_value_leaf_input_v6(&input_bytes).unwrap(),
        input
    );
    let expected = statement(&input);
    let statement_bytes = encode_source_opened_spot_value_leaf_statement_v6(&expected).unwrap();
    assert_eq!(
        decode_exact_source_opened_spot_value_leaf_statement_v6(&statement_bytes).unwrap(),
        expected
    );
}

#[test]
fn exact_source_or_adapter_mutation_rejects() {
    let input = fixture("swap-1", 0);
    let canonical = encode_source_opened_spot_value_leaf_input_v6(&input).unwrap();
    for index in [16, canonical.len() / 2, canonical.len() - 1] {
        let mut mutated = canonical.clone();
        mutated[index] ^= 1;
        if let Ok(decoded) = decode_exact_source_opened_spot_value_leaf_input_v6(&mutated) {
            assert!(recompose_source_opened_spot_value_leaf_statement_v6(&decoded).is_err());
        }
    }
}

#[test]
fn unsupported_protocol_fee_rejects_before_semantic_composition() {
    let mut source_input = source_input("swap-1");
    source_input.spot_input.protocol_fee_recipient_pubkey = Some(RECIPIENT.into());
    let rejected = envelope_from_input(source_input, 0);
    assert!(matches!(
        recompose_source_opened_spot_value_leaf_statement_v6(&rejected),
        Err(SourceOpenedSpotValueLeafErrorV6::SourceProfileRejected(
            "external or protocol fee effects"
        ))
    ));
}

#[test]
fn distinct_intent_changes_action_nullifier() {
    let first = statement(&fixture("swap-1", 0));
    let second = statement(&fixture("swap-2", 0));
    assert_ne!(
        first.action_nullifier_root(),
        second.action_nullifier_root()
    );
    assert_ne!(
        first.canonical_tx_commitment(),
        second.canonical_tx_commitment()
    );
}

#[test]
fn global_action_nullifier_ignores_epoch_lane_and_proof_topology() {
    let baseline = source_input("global-swap-1");
    let mut relocated = baseline.clone();
    relocated.epoch_id = 77;
    relocated.lane_id = "spot-source-opened-lane-0099".into();
    let first = statement(&envelope_from_input(baseline, 0));
    let second = statement(&envelope_from_input(relocated, 51));
    assert_eq!(
        first.action_nullifier_root(),
        second.action_nullifier_root()
    );
    assert_eq!(
        first.semantic_subtree().leaf_records()[0].transaction_root(),
        second.semantic_subtree().leaf_records()[0].transaction_root()
    );
}

#[test]
fn existing_sender_nonce_is_supported_and_bound_into_the_nullifier() {
    let baseline = statement(&fixture("nonce-swap", 0));
    let mut input = source_input("nonce-swap");
    input.spot_input.pre_nonces = vec![NonceEntryV1 {
        pubkey: SENDER.into(),
        next_nonce: 9,
    }];
    input.spot_input.tx_ingress[0].nonce = 9;
    let existing = statement(&envelope_from_input(input, 0));
    assert_ne!(
        baseline.action_nullifier_root(),
        existing.action_nullifier_root()
    );
}

#[test]
fn forged_source_state_or_asset_root_rejects_before_statement_construction() {
    let input = source_input("forged-source");
    let summary = compose_spot_recursive_leaf_summary_v1(input.clone()).unwrap();
    let source_journal_bytes = postcard::to_allocvec(&summary).unwrap();
    let adapter = project_policy_bound_v2_journal(
        SourceKindV2::Spot,
        &source_journal_bytes,
        0,
        PINNED_SOURCE_OPENED_V6_ADAPTER_IMAGE_ID,
    )
    .unwrap();

    let mut forged_pre = input.clone();
    forged_pre.spot_input.pre_app_hash[0] ^= 1;
    let forged_pre = SourceOpenedSpotValueLeafEnvelopeV6::new(
        0,
        encode_node_journal_v3(&adapter.journal).unwrap(),
        postcard::to_allocvec(&forged_pre).unwrap(),
        source_journal_bytes.clone(),
    )
    .unwrap();
    assert!(recompose_source_opened_spot_value_leaf_statement_v6(&forged_pre).is_err());

    let mut forged_summary = summary;
    forged_summary.asset_delta_root[0] ^= 1;
    let forged_asset = SourceOpenedSpotValueLeafEnvelopeV6::new(
        0,
        encode_node_journal_v3(&adapter.journal).unwrap(),
        postcard::to_allocvec(&input).unwrap(),
        postcard::to_allocvec(&forged_summary).unwrap(),
    )
    .unwrap();
    assert!(recompose_source_opened_spot_value_leaf_statement_v6(&forged_asset).is_err());
}

#[test]
fn replayed_source_transition_rejects_at_state_continuity_boundary() {
    let left = statement(&fixture("swap-1", 0));
    let right = statement(&fixture("swap-1", 1));
    assert!(matches!(
        merge_semantic_subtrees_v2(&[
            left.semantic_subtree().clone(),
            right.semantic_subtree().clone(),
        ]),
        Err(ValueNodeErrorV4::SemanticChildStateDiscontinuity { child: 1 })
    ));
}
