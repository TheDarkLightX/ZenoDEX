use risc0_zkvm::{FakeReceipt, Receipt, ReceiptClaim};
use zenodex_global_settlement_abi_v1::{
    candidate_zdex_fee_allocation_policy_v1, AbiErrorV1, RootV1, ZDEXFeeAllocationCommandV1,
    ZDEXFeeAllocationContextV1, ZDEXFeeDestinationAmountV1, ZDEXFeeStateV1,
    ZDEXLaneSuccinctReceiptVerifierV1, ZDEX_FEE_DESTINATIONS_V1,
};
use zenodex_zdex_fee_allocation_risc0_host::{
    build_zdex_fee_allocation_executor_env_v1, decode_canonical_zdex_fee_allocation_receipt_v1,
    encode_zdex_fee_allocation_receipt_v1, prove_zdex_fee_allocation_succinct_v1,
    require_zdex_fee_allocation_receipt_bytes_len_v1, verify_zdex_fee_allocation_receipt_v1,
    PinnedZDEXFeeAllocationReceiptVerifierV1, ZDEXFeeAllocationHostErrorV1,
    MAX_ZDEX_FEE_ALLOCATION_RECEIPT_BYTES_V1,
};
use zenodex_zdex_fee_allocation_risc0_shared::{
    ZDEXFeeAllocationGuestErrorV1, ZDEXFeeAllocationGuestInputV1,
    ZDEX_FEE_ALLOCATION_GUEST_INPUT_SCHEMA_V1,
};

fn root(value: u64) -> RootV1 {
    RootV1::parse(
        format!("0x{value:064x}"),
        "ZDEX fee-allocation host test root",
        false,
    )
    .unwrap()
}

fn guest_input(fee_charged_atoms: u128) -> ZDEXFeeAllocationGuestInputV1 {
    let policy = candidate_zdex_fee_allocation_policy_v1();
    let policy_root = policy.policy_root().unwrap();
    ZDEXFeeAllocationGuestInputV1 {
        schema: ZDEX_FEE_ALLOCATION_GUEST_INPUT_SCHEMA_V1.to_owned(),
        context: ZDEXFeeAllocationContextV1 {
            chain_id: "zenodex-fee-host-test".to_owned(),
            deployment_root: root(1),
            profile_root: root(2),
            writer_epoch: 11,
            allocation_route_release_id: root(3),
            authorized_buyback_route_release_id: root(4),
            tokenomics_module_release_id: root(5),
            command_occurrence_id: root(6),
            policy_root: policy_root.clone(),
        },
        pre_state: ZDEXFeeStateV1 {
            fee_asset_id: root(40),
            policy_root,
            fee_ingress_atoms: 50_000,
            unallocated_reserve_atoms: 700,
            destination_balances: ZDEX_FEE_DESTINATIONS_V1
                .into_iter()
                .zip([10, 20, 30, 40, 50, 60])
                .map(
                    |(destination, allocation_atoms)| ZDEXFeeDestinationAmountV1 {
                        destination,
                        allocation_atoms,
                    },
                )
                .collect(),
            owned_and_custodied_atoms: 1_000_000,
            supply_atoms: 1_000_000,
        },
        policy,
        command: ZDEXFeeAllocationCommandV1 { fee_charged_atoms },
    }
}

#[test]
fn host_preflight_uses_the_same_transition_and_rejects_economic_denial() {
    // Arrange / Act
    let (_, accepted) = build_zdex_fee_allocation_executor_env_v1(&guest_input(10_003)).unwrap();
    let rejected = build_zdex_fee_allocation_executor_env_v1(&guest_input(0));

    // Assert
    assert_eq!(accepted.accepted.post_state.fee_ingress_atoms, 39_997);
    assert_eq!(accepted.accepted.occurrence.buyback_quote_atoms(), 2_000);
    assert!(matches!(
        rejected,
        Err(ZDEXFeeAllocationHostErrorV1::Guest(
            ZDEXFeeAllocationGuestErrorV1::Rejected(
                zenodex_global_settlement_abi_v1::ZDEXFeeAllocationRejectCodeV1::ZERO_FEE
            )
        ))
    ));
}

#[test]
fn placeholder_method_and_fake_receipt_fail_before_authority() {
    // Arrange
    let (_, prepared) = build_zdex_fee_allocation_executor_env_v1(&guest_input(10_003)).unwrap();
    let fake: Receipt =
        FakeReceipt::new(ReceiptClaim::ok([1_u32; 8], prepared.journal_bytes.clone()))
            .try_into()
            .unwrap();

    // Act / Assert
    assert!(matches!(
        prove_zdex_fee_allocation_succinct_v1(&guest_input(10_003)),
        Err(ZDEXFeeAllocationHostErrorV1::PlaceholderMethod)
    ));
    assert!(matches!(
        verify_zdex_fee_allocation_receipt_v1(&fake, &prepared.journal_bytes),
        Err(ZDEXFeeAllocationHostErrorV1::ReceiptKind)
    ));
}

#[test]
fn receipt_json_must_be_the_exact_canonical_host_encoding() {
    // Arrange
    let (_, prepared) = build_zdex_fee_allocation_executor_env_v1(&guest_input(10_003)).unwrap();
    let fake: Receipt =
        FakeReceipt::new(ReceiptClaim::ok([1_u32; 8], prepared.journal_bytes.clone()))
            .try_into()
            .unwrap();
    let canonical = encode_zdex_fee_allocation_receipt_v1(&fake).unwrap();
    let mut padded = Vec::with_capacity(canonical.len() + 1);
    padded.push(b' ');
    padded.extend_from_slice(&canonical);

    // Act / Assert
    assert!(decode_canonical_zdex_fee_allocation_receipt_v1(&canonical).is_ok());
    assert!(matches!(
        decode_canonical_zdex_fee_allocation_receipt_v1(&padded),
        Err(ZDEXFeeAllocationHostErrorV1::ReceiptNonCanonical)
    ));
}

#[test]
fn receipt_byte_ceiling_rejects_zero_and_maximum_plus_one_before_decoding() {
    // Arrange / Act / Assert: BVA around the resource-admission ceiling.
    assert!(matches!(
        require_zdex_fee_allocation_receipt_bytes_len_v1(0),
        Err(ZDEXFeeAllocationHostErrorV1::ReceiptSize)
    ));
    assert!(require_zdex_fee_allocation_receipt_bytes_len_v1(
        MAX_ZDEX_FEE_ALLOCATION_RECEIPT_BYTES_V1
    )
    .is_ok());
    assert!(matches!(
        require_zdex_fee_allocation_receipt_bytes_len_v1(
            MAX_ZDEX_FEE_ALLOCATION_RECEIPT_BYTES_V1 + 1
        ),
        Err(ZDEXFeeAllocationHostErrorV1::ReceiptSize)
    ));

    let verifier = PinnedZDEXFeeAllocationReceiptVerifierV1;
    assert!(matches!(
        verifier.verify_succinct_receipt(&[], &root(91), &[]),
        Err(AbiErrorV1::InvalidBounds(_))
    ));
    let oversized = vec![0_u8; MAX_ZDEX_FEE_ALLOCATION_RECEIPT_BYTES_V1 + 1];
    assert!(matches!(
        verifier.verify_succinct_receipt(&oversized, &root(91), &[]),
        Err(AbiErrorV1::InvalidBounds(_))
    ));
}
