//! Projection tests reuse the enclosing receipt harness's bounded test verifier.
//! The verifier is a recording mock; these tests establish binding/row behavior,
//! never a cryptographic receipt qualification or authenticated-store claim.

use super::*;

fn empty_projection_state() -> GlobalEconomicStateV1 {
    let fixture: serde_json::Value = serde_json::from_str(include_str!(
        "../../../../tests/data/global_accounting_allocation_projection_v1_golden.json"
    ))
    .expect("projection fixture JSON");
    serde_json::from_value(fixture["vectors"]["empty"]["state"].clone()).expect("empty state")
}

fn projection_module_fixture() -> VerifiedAssetLaneFixture {
    let mut fixture = verified_asset_lane_fixture();
    fixture.input.custody = vec![EconomicAmountV1 {
        owner: "custodian".to_owned(),
        asset: "USD".to_owned(),
        custody_domain: "vault".to_owned(),
        amount_atoms: 100,
    }];
    let supply = fixture
        .input
        .pre_state
        .supplies
        .iter_mut()
        .find(|row| row.asset == "USD")
        .expect("USD supply");
    supply.amount_atoms = supply
        .amount_atoms
        .checked_add(100)
        .expect("test amount fits");
    remint_projection_module(&mut fixture);
    fixture
}

fn remint_projection_module(fixture: &mut VerifiedAssetLaneFixture) {
    let AssetTransferLaneModuleResultV1::Accepted(accepted) =
        transition_asset_transfer_lane_module_v1(&fixture.input).expect("transition boundary")
    else {
        panic!("custody-bearing test transition accepts")
    };
    let bound = bind_transfer(
        &fixture.refs(),
        &fixture.occurrence,
        &fixture.input,
        &accepted,
    )
    .expect("release binding");
    let authenticated = authenticate_occurrence(
        &fixture.profile,
        &fixture.routes,
        &fixture.occurrence,
        canonical_economic_command_body_bytes_v1(
            &fixture.input.command.command_kind,
            &fixture.input.command,
        )
        .expect("command bytes"),
    );
    fixture.verified = verify_asset_transfer_lane_module_receipt_v1(
        AssetTransferLaneModuleReceiptCandidateV1 {
            profile: &fixture.profile,
            policy_registry: &fixture.registries.policy_registry,
            asset_policy_registry: &fixture.registries.asset_policy_registry,
            lanes: &fixture.lanes,
            coordinators: &fixture.coordinators,
            routes: &fixture.routes,
            authenticated_command: &authenticated,
            module_input: &fixture.input,
            accepted: &accepted,
            release_route_binding: &bound,
            receipt: LaneModuleReceiptEnvelopeV1 {
                receipt_kind: ReceiptKindV1::SUCCINCT,
                receipt_bytes: b"projection-test-mock-receipt",
            },
        },
        &RecordingModuleReceiptVerifier::default(),
    )
    .expect("mock receipt admission");
    fixture.accepted = accepted;
}

fn projection_witness_and_state() -> (VerifiedLaneAllocationFragmentV1, GlobalEconomicStateV1) {
    let fixture = projection_module_fixture();
    let (lane_root, prior, entitlements) = receipt_admission_inputs(&fixture);
    let witness = verify_asset_transfer_fragment_receipt_v1(
        &fixture.verified,
        &fixture.accepted,
        &lane_root,
        &prior,
        &entitlements,
    )
    .expect("fragment boundary")
    .expect("fragment admission");
    let mut state = empty_projection_state();
    state.chain_id = witness.chain_id().to_owned();
    state.deployment_root = witness.deployment_root().clone();
    state.profile_root = witness.profile_root().clone();
    state.writer_epoch = witness.writer_epoch();
    state.lane_roots[0] = lane_root;
    state.custody = fixture.input.custody;
    state.liabilities = entitlements
        .into_iter()
        .map(|row| EconomicAmountV1 {
            owner: row.claimant,
            asset: row.asset,
            custody_domain: row.control_domain,
            amount_atoms: row.amount_atoms,
        })
        .collect();
    (witness, state)
}

fn global_allocation_receipt_fixture() -> (
    VerifiedAssetLaneFixture,
    GlobalEconomicStateV1,
    GlobalEconomicStateV1,
) {
    let mut fixture = projection_module_fixture();
    let mut pre = empty_projection_state();
    let journal = &fixture.accepted.module_journal;
    pre.chain_id = journal.chain_id.clone();
    pre.deployment_root = journal.deployment_root.clone();
    pre.profile_root = journal.profile_root.clone();
    pre.writer_epoch = journal.writer_epoch;
    pre.height = fixture
        .occurrence
        .height
        .checked_sub(1)
        .expect("fixture height nonzero");
    pre.lane_roots[0] = LaneStateRootV1 {
        lane_id: LaneIdV1::ASSET_TRANSFER,
        module_release_id: journal.module_release_id.clone(),
        enabled: true,
        state_root: fixture
            .accepted
            .private_port
            .pre_state
            .state_root()
            .unwrap(),
    };
    pre.balances = fixture.accepted.private_port.pre_state.balances.clone();
    pre.custody = fixture.accepted.private_port.pre_state.custody.clone();
    pre.supplies = fixture.accepted.private_port.pre_state.supplies.clone();
    pre.liabilities = vec![EconomicAmountV1 {
        owner: "alice".to_owned(),
        asset: "USD".to_owned(),
        custody_domain: "vault".to_owned(),
        amount_atoms: 100,
    }];
    fixture.occurrence.pre_state_root = pre.state_root().unwrap();
    fixture.input.context.command_occurrence_id = fixture.occurrence.occurrence_id().unwrap();
    remint_projection_module(&mut fixture);
    let mut post = pre.clone();
    post.height = fixture.occurrence.height;
    post.lane_roots[0].state_root = fixture
        .accepted
        .private_port
        .post_state
        .state_root()
        .unwrap();
    post.balances = fixture.accepted.private_port.post_state.balances.clone();
    post.supplies = fixture.accepted.private_port.post_state.supplies.clone();
    post.replay_state = vec![ReplayStateV1 {
        replay_id: fixture.occurrence.replay_id().unwrap().as_str().to_owned(),
        occurrence_id: fixture.occurrence.occurrence_id().unwrap(),
    }];
    (fixture, pre, post)
}

#[test]
fn allocation_projection_global_receipt_preserves_distinct_roots_and_claimants() {
    let (fixture, pre, post) = global_allocation_receipt_fixture();
    let before = (pre.clone(), post.clone());
    let witness = verify_asset_transfer_global_fragment_receipt_v1(
        &fixture.verified,
        AssetTransferGlobalAllocationCandidateV1 {
            accepted: &fixture.accepted,
            occurrence: &fixture.occurrence,
            predecessor: &pre,
            current: &post,
        },
    )
    .expect("global boundary")
    .expect("global admission");
    assert_ne!(
        fixture.accepted.module_journal.post_lane_root,
        post.lane_roots[0].state_root
    );
    assert_eq!(
        witness.fragment().lane_state_root,
        post.lane_roots[0].state_root
    );
    assert_eq!(
        witness.fragment().claimant_entitlements[0].claimant,
        "alice"
    );
    assert_eq!(
        witness.fragment().controlled_locations[0].controlling_principal,
        "custodian"
    );
    let mut slots = EMPTY_LANE_WITNESS_SLOTS_V1;
    slots[0] = Some(&witness);
    let roots = [(LaneIdV1::ASSET_TRANSFER, witness.receipt_root().clone())];
    let projected = project_allocation_certificate_v1(&post, &roots, &slots)
        .unwrap()
        .unwrap();
    assert!(matches!(
        check_global_accounting_allocation_certificate_v1(&projected, &post, &slots).unwrap(),
        AllocationCertificateOutcomeV1::Accepted(_)
    ));
    assert_eq!((pre, post), before);
}

#[test]
fn allocation_epoch_position_admits_second_pair_without_rewriting_height() {
    let (mut fixture, source, first_post) = global_allocation_receipt_fixture();
    fixture.occurrence.pre_state_root = first_post.state_root().unwrap();
    fixture.occurrence.tx_index += 1;
    fixture.occurrence.nonce += 1;
    fixture.input.pre_state = fixture.accepted.post_state.clone();
    fixture.input.context.command_occurrence_id = fixture.occurrence.occurrence_id().unwrap();
    remint_projection_module(&mut fixture);
    let mut post = first_post.clone();
    post.lane_roots[0].state_root = fixture
        .accepted
        .private_port
        .post_state
        .state_root()
        .unwrap();
    post.balances = fixture.accepted.private_port.post_state.balances.clone();
    post.supplies = fixture.accepted.private_port.post_state.supplies.clone();
    post.replay_state.push(ReplayStateV1 {
        replay_id: fixture.occurrence.replay_id().unwrap().as_str().to_owned(),
        occurrence_id: fixture.occurrence.occurrence_id().unwrap(),
    });
    post.replay_state
        .sort_by(|a, b| a.replay_id.cmp(&b.replay_id));
    let pair = || AssetTransferGlobalAllocationCandidateV1 {
        accepted: &fixture.accepted,
        occurrence: &fixture.occurrence,
        predecessor: &first_post,
        current: &post,
    };
    assert_eq!(
        check_asset_transfer_global_allocation_v1(pair()).unwrap(),
        Some(GlobalAllocationBindingRejectCodeV1::GLOBAL_OCCURRENCE_DRIFT)
    );
    let witness = verify_asset_transfer_epoch_fragment_receipt_v1(
        &fixture.verified,
        pair(),
        AssetTransferEpochPositionV1 {
            epoch_source: &source,
            occurrence_index: 1,
        },
    )
    .unwrap()
    .expect("second prospective pair admits");
    assert_eq!(first_post.height, post.height);
    assert_eq!(
        witness.fragment().lane_state_root,
        post.lane_roots[0].state_root
    );
    let mut slots = EMPTY_LANE_WITNESS_SLOTS_V1;
    slots[0] = Some(&witness);
    let roots = [(LaneIdV1::ASSET_TRANSFER, witness.receipt_root().clone())];
    let projected = project_allocation_certificate_v1(&post, &roots, &slots)
        .unwrap()
        .unwrap();
    assert!(matches!(
        check_global_accounting_allocation_certificate_v1(&projected, &post, &slots).unwrap(),
        AllocationCertificateOutcomeV1::Accepted(_)
    ));
}

#[test]
fn allocation_projection_global_receipt_rejects_conserved_predecessor_or_current_substitution() {
    let (fixture, pre, post) = global_allocation_receipt_fixture();
    for previous in [true, false] {
        let mut changed_pre = pre.clone();
        let mut changed_post = post.clone();
        if previous {
            changed_pre.liabilities[0].owner = "mallory".to_owned();
        } else {
            changed_post.liabilities[0].owner = "mallory".to_owned();
        }
        let before = (changed_pre.clone(), changed_post.clone());
        let result = verify_asset_transfer_global_fragment_receipt_v1(
            &fixture.verified,
            AssetTransferGlobalAllocationCandidateV1 {
                accepted: &fixture.accepted,
                occurrence: &fixture.occurrence,
                predecessor: &changed_pre,
                current: &changed_post,
            },
        )
        .expect("global boundary")
        .expect_err("claimant substitution rejects");
        assert_eq!(
            result,
            GlobalAssetTransferFragmentAdmissionRejectedV1::Binding(if previous {
                GlobalAllocationBindingRejectCodeV1::GLOBAL_OCCURRENCE_DRIFT
            } else {
                GlobalAllocationBindingRejectCodeV1::GLOBAL_CLAIMANT_CONTINUITY_DRIFT
            })
        );
        assert_eq!((changed_pre, changed_post), before);
    }
    let foreign = verified_asset_lane_fixture();
    assert!(matches!(
        verify_asset_transfer_global_fragment_receipt_v1(
            &foreign.verified,
            AssetTransferGlobalAllocationCandidateV1 {
                accepted: &fixture.accepted,
                occurrence: &fixture.occurrence,
                predecessor: &pre,
                current: &post,
            },
        )
        .unwrap(),
        Err(GlobalAssetTransferFragmentAdmissionRejectedV1::Admission(
            AssetTransferFragmentAdmissionRejectedV1::Witness(ReceiptWitnessRejectedV1 {
                code: ReceiptWitnessRejectCodeV1::WITNESS_JOURNAL_ROOT_DRIFT,
                ..
            })
        ))
    ));
}

#[test]
fn allocation_projection_reproduces_nonempty_admitted_fragment_and_independent_certificate() {
    let (witness, state) = projection_witness_and_state();
    let mut slots = EMPTY_LANE_WITNESS_SLOTS_V1;
    slots[0] = Some(&witness);
    let roots = [(LaneIdV1::ASSET_TRANSFER, witness.receipt_root().clone())];
    let before = state.clone();
    let projected = project_allocation_certificate_v1(&state, &roots, &slots)
        .expect("boundary")
        .expect("projection");
    assert_eq!(projected.ordered_lane_fragments[0], *witness.fragment());
    assert_eq!(
        projected.ordered_lane_fragments[0]
            .controlled_locations
            .len(),
        1
    );
    assert_eq!(
        projected.canonical_allocation_rows,
        witness.fragment().claimant_entitlements
    );
    let mut independent = build_registered_empty_certificate_v1(&state).expect("empty certificate");
    independent.ordered_lane_fragments[0] = witness.fragment().clone();
    independent.canonical_allocation_rows = witness.fragment().claimant_entitlements.clone();
    independent.field_ownership_root =
        derive_field_ownership_root_v1(&independent.ordered_lane_fragments)
            .expect("ownership root");
    independent.terminal_binding_root =
        derive_terminal_binding_root_v1(&independent.ordered_lane_fragments)
            .expect("terminal root");
    independent.allocation_root = derive_allocation_root_v1(
        &independent.ordered_lane_fragments,
        &independent.canonical_allocation_rows,
    )
    .expect("allocation root");
    assert_eq!(
        canonical_bytes_v1(&projected).expect("projection bytes"),
        canonical_bytes_v1(&independent).expect("independent bytes")
    );
    assert!(matches!(
        check_global_accounting_allocation_certificate_v1(&projected, &state, &slots)
            .expect("checker boundary"),
        AllocationCertificateOutcomeV1::Accepted(_)
    ));
    assert_eq!(state, before);
}

#[test]
fn allocation_projection_rejects_header_drift_and_conserved_claimant_substitution() {
    let (witness, state) = projection_witness_and_state();
    let mut slots = EMPTY_LANE_WITNESS_SLOTS_V1;
    slots[0] = Some(&witness);
    let roots = [(LaneIdV1::ASSET_TRANSFER, witness.receipt_root().clone())];
    for field in [
        "chain",
        "deployment",
        "profile",
        "epoch",
        "claimant",
        "custodian",
    ] {
        let mut changed = state.clone();
        match field {
            "chain" => changed.chain_id = "foreign-chain".to_owned(),
            "deployment" => changed.deployment_root = root(999),
            "profile" => changed.profile_root = root(999),
            "epoch" => changed.writer_epoch += 1,
            "claimant" => changed.liabilities[0].owner = "mallory".to_owned(),
            "custodian" => changed.custody[0].owner = "mallory".to_owned(),
            _ => unreachable!("fixed test cases"),
        }
        let before = changed.clone();
        let rejected = project_allocation_certificate_v1(&changed, &roots, &slots)
            .expect("boundary")
            .expect_err("drift rejects");
        let expected = if field == "claimant" || field == "custodian" {
            AllocationProjectionRejectCodeV1::PROJECTION_WITNESS_FRAGMENT_DRIFT
        } else {
            AllocationProjectionRejectCodeV1::PROJECTION_WITNESS_HEADER_DRIFT
        };
        assert_eq!(rejected.code, expected, "{field}");
        assert_eq!(
            rejected.state_root,
            changed.state_root().expect("state root")
        );
        assert_eq!(changed, before);
    }
}

#[test]
fn allocation_projection_rejects_every_unexpected_witness_slot() {
    let (witness, _) = projection_witness_and_state();
    let state = empty_projection_state();
    for index in 0..ALL_LANE_IDS_V1.len() {
        let mut slots = EMPTY_LANE_WITNESS_SLOTS_V1;
        slots[index] = Some(&witness);
        let rejected = project_allocation_certificate_v1(&state, &[], &slots)
            .expect("boundary")
            .expect_err("unexpected witness");
        assert_eq!(
            rejected.code,
            AllocationProjectionRejectCodeV1::PROJECTION_WITNESS_UNEXPECTED
        );
        assert_eq!(rejected.state_root, state.state_root().expect("state root"));
    }
}
