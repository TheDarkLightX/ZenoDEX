use zenodex_global_settlement_abi_v1::{
    candidate_zdex_fee_allocation_policy_v1, canonical_bytes_v1, transition_zdex_fee_allocation_v1,
    RootV1, ZDEXFeeAllocationCommandV1, ZDEXFeeAllocationContextV1, ZDEXFeeAllocationRejectCodeV1,
    ZDEXFeeAllocationResultV1, ZDEXFeeDestinationAmountV1, ZDEXFeeStateV1,
    ZDEX_FEE_DESTINATIONS_V1,
};
use zenodex_zdex_fee_allocation_risc0_shared::{
    canonical_zdex_fee_allocation_guest_input_bytes_v1,
    prepare_zdex_fee_allocation_from_canonical_bytes_v1, prepare_zdex_fee_allocation_v1,
    ZDEXFeeAllocationGuestErrorV1, ZDEXFeeAllocationGuestInputV1,
    ZDEX_FEE_ALLOCATION_GUEST_INPUT_SCHEMA_V1,
};

fn root(value: u64) -> RootV1 {
    RootV1::parse(
        format!("0x{value:064x}"),
        "ZDEX fee-allocation guest test root",
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
            chain_id: "zenodex-fee-guest-test".to_owned(),
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
fn exact_core_acceptance_commits_only_the_canonical_occurrence_journal() {
    // Arrange
    let input = guest_input(10_003);
    let input_bytes = canonical_zdex_fee_allocation_guest_input_bytes_v1(&input).unwrap();

    // Act
    let prepared = prepare_zdex_fee_allocation_from_canonical_bytes_v1(&input_bytes).unwrap();

    // Assert
    assert_eq!(prepared.input, input);
    assert_eq!(prepared.accepted.post_state.fee_ingress_atoms, 39_997);
    assert_eq!(prepared.accepted.occurrence.buyback_quote_atoms(), 2_000);
    assert_eq!(prepared.accepted.occurrence.carried_residue_atoms, 2_503);
    assert_eq!(
        prepared.journal_bytes,
        canonical_bytes_v1(&prepared.accepted.occurrence).unwrap()
    );
}

#[test]
fn amount_boundaries_accept_or_reject_with_exact_typed_results() {
    // Arrange / Act / Assert: zero, one atom, exact ingress, next atom, effect-width edge.
    for amount in [1, 50_000] {
        let prepared = prepare_zdex_fee_allocation_v1(guest_input(amount)).unwrap();
        assert_eq!(
            prepared.accepted.post_state.fee_ingress_atoms,
            50_000 - amount
        );
    }
    for (amount, expected) in [
        (0, ZDEXFeeAllocationRejectCodeV1::ZERO_FEE),
        (
            50_001,
            ZDEXFeeAllocationRejectCodeV1::INSUFFICIENT_FEE_INGRESS,
        ),
        (
            i128::MAX.unsigned_abs() + 1,
            ZDEXFeeAllocationRejectCodeV1::EFFECT_WIDTH_EXCEEDED,
        ),
    ] {
        assert!(matches!(
            prepare_zdex_fee_allocation_v1(guest_input(amount)),
            Err(ZDEXFeeAllocationGuestErrorV1::Rejected(code)) if code == expected
        ));
    }
}

#[test]
fn typed_rejection_is_an_exact_noop_and_produces_no_guest_journal() {
    // Arrange
    let input = guest_input(0);

    // Act
    let direct = transition_zdex_fee_allocation_v1(
        &input.context,
        &input.pre_state,
        &input.policy,
        &input.command,
    )
    .unwrap();
    let guest = prepare_zdex_fee_allocation_v1(input);

    // Assert
    let ZDEXFeeAllocationResultV1::Rejected(rejected) = direct else {
        panic!("zero fee must reject")
    };
    assert_eq!(rejected.code, ZDEXFeeAllocationRejectCodeV1::ZERO_FEE);
    assert_eq!(rejected.pre_state, rejected.post_state);
    assert!(rejected.effects.is_empty());
    assert!(matches!(
        guest,
        Err(ZDEXFeeAllocationGuestErrorV1::Rejected(
            ZDEXFeeAllocationRejectCodeV1::ZERO_FEE
        ))
    ));
}

#[test]
fn empty_oversized_unknown_schema_and_noncanonical_inputs_fail_closed() {
    // Arrange
    let canonical =
        canonical_zdex_fee_allocation_guest_input_bytes_v1(&guest_input(10_003)).unwrap();
    let mut trailing = canonical.clone();
    trailing.push(b'\n');
    let mut unknown: serde_json::Value = serde_json::from_slice(&canonical).unwrap();
    unknown
        .as_object_mut()
        .unwrap()
        .insert("unexpected".to_owned(), serde_json::Value::Bool(true));
    let unknown = serde_json::to_vec(&unknown).unwrap();
    let mut wrong_schema: serde_json::Value = serde_json::from_slice(&canonical).unwrap();
    wrong_schema["schema"] = serde_json::Value::String("unsupported/v2".to_owned());
    let wrong_schema = canonical_bytes_v1(&wrong_schema).unwrap();
    let one_byte = b"{";
    let at_limit = vec![b' '; 1_048_576];
    let oversized = vec![0_u8; 1_048_577];

    // Act / Assert
    assert!(matches!(
        prepare_zdex_fee_allocation_from_canonical_bytes_v1(&[]),
        Err(ZDEXFeeAllocationGuestErrorV1::EmptyInput)
    ));
    assert!(matches!(
        prepare_zdex_fee_allocation_from_canonical_bytes_v1(one_byte),
        Err(ZDEXFeeAllocationGuestErrorV1::Decode)
    ));
    assert!(matches!(
        prepare_zdex_fee_allocation_from_canonical_bytes_v1(&at_limit),
        Err(ZDEXFeeAllocationGuestErrorV1::Decode)
    ));
    assert!(matches!(
        prepare_zdex_fee_allocation_from_canonical_bytes_v1(&oversized),
        Err(ZDEXFeeAllocationGuestErrorV1::InputTooLarge)
    ));
    assert!(matches!(
        prepare_zdex_fee_allocation_from_canonical_bytes_v1(&unknown),
        Err(ZDEXFeeAllocationGuestErrorV1::Decode)
    ));
    assert!(matches!(
        prepare_zdex_fee_allocation_from_canonical_bytes_v1(&wrong_schema),
        Err(ZDEXFeeAllocationGuestErrorV1::Schema)
    ));
    assert!(matches!(
        prepare_zdex_fee_allocation_from_canonical_bytes_v1(&trailing),
        Err(ZDEXFeeAllocationGuestErrorV1::NonCanonicalInput)
    ));
}

#[test]
fn policy_root_drift_is_rejected_before_journal_commit() {
    // Arrange
    let mut input = guest_input(1);
    input.context.policy_root = root(99);

    // Act / Assert
    assert!(matches!(
        prepare_zdex_fee_allocation_v1(input),
        Err(ZDEXFeeAllocationGuestErrorV1::Rejected(
            ZDEXFeeAllocationRejectCodeV1::POLICY_MISMATCH
        ))
    ));
}
