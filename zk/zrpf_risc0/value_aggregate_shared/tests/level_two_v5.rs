mod support;

use zenodex_zrpf_protocol_v3::{
    encode_value_aggregate_proposal_v5, ProposedValueAggregateV5, ValueNodeErrorV4,
};
use zenodex_zrpf_risc0_value_aggregate_shared::{
    compose_value_aggregate_level_two_after_receipt_verification_v5,
    decode_exact_value_aggregate_guest_input_v5, encode_value_aggregate_guest_input_v5,
    recompose_expected_value_aggregate_level_one_v5,
    recompose_expected_value_aggregate_level_two_v5, GovernedValueChildIdentityV5,
    ValueAggregateGuestInputV5, ValueAggregateLevelOneInputV5, ValueAggregateLevelTwoInputV5,
    ValueAggregateRecompositionErrorV5,
};

use support::{identity, indexed, leaf_bytes, policy, scope, scope_with_application};

fn level_one(
    start: u64,
    scope: zenodex_zrpf_protocol_v3::NodeScopeV3,
    leaf_identity: GovernedValueChildIdentityV5,
) -> ProposedValueAggregateV5 {
    let input = ValueAggregateLevelOneInputV5::new(vec![
        leaf_bytes(
            start,
            indexed(60, start),
            indexed(60, start + 1),
            scope.clone(),
            leaf_identity,
        ),
        leaf_bytes(
            start + 1,
            indexed(60, start + 1),
            indexed(60, start + 2),
            scope.clone(),
            leaf_identity,
        ),
    ])
    .unwrap();
    recompose_expected_value_aggregate_level_one_v5(
        &input,
        &policy(scope, vec![leaf_identity, leaf_identity]),
    )
    .unwrap()
}

fn valid_level_one_bytes() -> Vec<Vec<u8>> {
    let leaf_identity = identity(100, 70, 71);
    vec![
        encode_value_aggregate_proposal_v5(&level_one(0, scope(), leaf_identity)).unwrap(),
        encode_value_aggregate_proposal_v5(&level_one(2, scope(), leaf_identity)).unwrap(),
    ]
}

#[test]
fn exact_level_two_recomposition_uses_policy_bound_child_identities() {
    let children = valid_level_one_bytes();
    let left_identity = identity(300, 80, 81);
    let right_identity = identity(400, 82, 83);
    let input = ValueAggregateLevelTwoInputV5::new(children.clone()).unwrap();
    let policy = policy(scope(), vec![left_identity, right_identity]);
    let recomposed = recompose_expected_value_aggregate_level_two_v5(&input, &policy).unwrap();
    let composed =
        compose_value_aggregate_level_two_after_receipt_verification_v5(&input, &policy).unwrap();
    let framed =
        encode_value_aggregate_guest_input_v5(&ValueAggregateGuestInputV5::LevelTwo(input.clone()))
            .unwrap();
    let ValueAggregateGuestInputV5::LevelTwo(decoded) =
        decode_exact_value_aggregate_guest_input_v5(&framed).unwrap()
    else {
        panic!("level-two guest input changed wire kind")
    };

    assert_eq!(recomposed, composed);
    assert_eq!(
        recomposed,
        recompose_expected_value_aggregate_level_two_v5(&decoded, &policy).unwrap()
    );
    assert_eq!(recomposed.aggregate_level(), 2);
    assert_eq!(recomposed.scope(), &scope());
    assert_eq!(recomposed.semantic_subtree().partition().start(), 0);
    assert_eq!(recomposed.semantic_subtree().partition().end_exclusive(), 4);
    assert_eq!(recomposed.children().len(), 2);
    assert_eq!(
        recomposed.children()[0].verified_program_id(),
        left_identity.expected_program_id()
    );
    assert_eq!(
        recomposed.children()[1].proof_profile_id(),
        right_identity.expected_profile_id()
    );
    assert_eq!(
        recomposed.children()[1].program_manifest_root(),
        right_identity.expected_manifest_root()
    );
    for (descriptor, encoded_child) in recomposed.children().iter().zip(children.iter()) {
        let child =
            zenodex_zrpf_protocol_v3::decode_exact_value_aggregate_proposal_v5(encoded_child)
                .unwrap();
        assert_eq!(descriptor.child_level(), 1);
        assert_eq!(descriptor.journal_hash(), child.proposal_commitment());
        assert_eq!(
            descriptor.semantic_subtree_root(),
            child.semantic_subtree().canonical_hash().unwrap()
        );
    }
}

#[test]
fn level_scope_and_valid_proposal_substitution_reject() {
    let leaf_identity = identity(100, 70, 71);
    let l1_left = level_one(0, scope(), leaf_identity);
    let l1_right = level_one(2, scope(), leaf_identity);
    let aggregate_identity = identity(300, 80, 81);
    let base_input = ValueAggregateLevelTwoInputV5::new(vec![
        encode_value_aggregate_proposal_v5(&l1_left).unwrap(),
        encode_value_aggregate_proposal_v5(&l1_right).unwrap(),
    ])
    .unwrap();
    let root = recompose_expected_value_aggregate_level_two_v5(
        &base_input,
        &policy(scope(), vec![aggregate_identity, aggregate_identity]),
    )
    .unwrap();
    let wrong_level = ValueAggregateLevelTwoInputV5::new(vec![encode_value_aggregate_proposal_v5(
        &root,
    )
    .unwrap()])
    .unwrap();
    assert_eq!(
        recompose_expected_value_aggregate_level_two_v5(
            &wrong_level,
            &policy(scope(), vec![aggregate_identity])
        ),
        Err(ValueAggregateRecompositionErrorV5::ChildLevelMismatch {
            child: 0,
            actual: 2,
        })
    );

    let foreign_scope = scope_with_application(9);
    let foreign = level_one(2, foreign_scope.clone(), leaf_identity);
    let substituted = ValueAggregateLevelTwoInputV5::new(vec![
        encode_value_aggregate_proposal_v5(&l1_left).unwrap(),
        encode_value_aggregate_proposal_v5(&foreign).unwrap(),
    ])
    .unwrap();
    assert_eq!(
        recompose_expected_value_aggregate_level_two_v5(
            &substituted,
            &policy(scope(), vec![aggregate_identity, aggregate_identity])
        ),
        Err(ValueAggregateRecompositionErrorV5::ChildScopeMismatch(1))
    );

    let reversed = ValueAggregateLevelTwoInputV5::new(vec![
        encode_value_aggregate_proposal_v5(&l1_right).unwrap(),
        encode_value_aggregate_proposal_v5(&l1_left).unwrap(),
    ])
    .unwrap();
    assert_eq!(
        recompose_expected_value_aggregate_level_two_v5(
            &reversed,
            &policy(scope(), vec![aggregate_identity, aggregate_identity])
        ),
        Err(ValueAggregateRecompositionErrorV5::SemanticMerge(
            ValueNodeErrorV4::NonCanonicalSemanticChildOrder { child: 1 }
        ))
    );
}

#[test]
fn duplicate_claim_and_journal_are_independently_rejected() {
    let child = valid_level_one_bytes().remove(0);
    let identity_a = identity(300, 80, 81);
    let identity_b = identity(400, 82, 83);
    let duplicate = ValueAggregateLevelTwoInputV5::new(vec![child.clone(), child]).unwrap();

    assert_eq!(
        recompose_expected_value_aggregate_level_two_v5(
            &duplicate,
            &policy(scope(), vec![identity_a, identity_a])
        ),
        Err(ValueAggregateRecompositionErrorV5::DuplicateChildClaim)
    );
    assert_eq!(
        recompose_expected_value_aggregate_level_two_v5(
            &duplicate,
            &policy(scope(), vec![identity_a, identity_b])
        ),
        Err(ValueAggregateRecompositionErrorV5::DuplicateChildJournal)
    );
}

#[test]
fn child_program_profile_and_manifest_policy_substitution_changes_parent_commitment() {
    let child = valid_level_one_bytes().remove(0);
    let input = ValueAggregateLevelTwoInputV5::new(vec![child]).unwrap();
    let baseline_identity = identity(300, 80, 81);
    let baseline = recompose_expected_value_aggregate_level_two_v5(
        &input,
        &policy(scope(), vec![baseline_identity]),
    )
    .unwrap();

    for substituted_identity in [
        identity(301, 80, 81),
        identity(300, 82, 81),
        identity(300, 80, 83),
    ] {
        let substituted = recompose_expected_value_aggregate_level_two_v5(
            &input,
            &policy(scope(), vec![substituted_identity]),
        )
        .unwrap();
        assert_ne!(
            substituted.proposal_commitment(),
            baseline.proposal_commitment()
        );
        assert_ne!(substituted.children()[0], baseline.children()[0]);
    }
}

#[test]
fn policy_count_and_noncanonical_child_proposal_reject() {
    let mut children = valid_level_one_bytes();
    let first = children.remove(0);
    let identity = identity(300, 80, 81);
    let input = ValueAggregateLevelTwoInputV5::new(vec![first.clone()]).unwrap();
    assert_eq!(
        recompose_expected_value_aggregate_level_two_v5(
            &input,
            &policy(scope(), vec![identity, identity])
        ),
        Err(
            ValueAggregateRecompositionErrorV5::PolicyChildCountMismatch {
                policy: 2,
                input: 1
            }
        )
    );

    let mut trailing = first;
    trailing.push(0);
    let input = ValueAggregateLevelTwoInputV5::new(vec![trailing]).unwrap();
    assert_eq!(
        recompose_expected_value_aggregate_level_two_v5(&input, &policy(scope(), vec![identity])),
        Err(ValueAggregateRecompositionErrorV5::ChildV5ProposalDecode(0))
    );
}
