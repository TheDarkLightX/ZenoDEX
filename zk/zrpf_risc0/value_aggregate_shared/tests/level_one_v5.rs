mod support;

use zenodex_zrpf_protocol_v3::{
    encode_node_journal_v4, ValueNodeErrorV4, MAX_NODE_JOURNAL_BYTES_V4,
};
use zenodex_zrpf_risc0_shared::derive_risc0_verified_claim_binding_v1;
use zenodex_zrpf_risc0_value_aggregate_shared::{
    compose_value_aggregate_level_one_after_receipt_verification_v5,
    decode_exact_value_aggregate_guest_input_v5, encode_value_aggregate_guest_input_v5,
    recompose_expected_value_aggregate_level_one_v5, GovernedValueChildIdentityV5,
    ValueAggregateGuestInputV5, ValueAggregateLevelOneInputV5, ValueAggregateRecompositionErrorV5,
};

use support::{
    aggregate_v4_bytes, commitment, identity, image, indexed, leaf_bytes, leaf_journal, policy,
    program_from_image, scope, scope_with_application,
};

fn valid_children() -> (
    Vec<Vec<u8>>,
    zenodex_zrpf_risc0_value_aggregate_shared::GovernedValueChildIdentityV5,
) {
    let identity = identity(100, 70, 71);
    let children = vec![
        leaf_bytes(0, indexed(60, 0), indexed(60, 1), scope(), identity),
        leaf_bytes(1, indexed(60, 1), indexed(60, 2), scope(), identity),
    ];
    (children, identity)
}

#[test]
fn exact_level_one_recomposition_derives_every_child_binding() {
    let (children, identity) = valid_children();
    let input = ValueAggregateLevelOneInputV5::new(children.clone()).unwrap();
    let policy = policy(scope(), vec![identity, identity]);
    let recomposed = recompose_expected_value_aggregate_level_one_v5(&input, &policy).unwrap();
    let composed =
        compose_value_aggregate_level_one_after_receipt_verification_v5(&input, &policy).unwrap();
    let framed =
        encode_value_aggregate_guest_input_v5(&ValueAggregateGuestInputV5::LevelOne(input.clone()))
            .unwrap();
    let ValueAggregateGuestInputV5::LevelOne(decoded) =
        decode_exact_value_aggregate_guest_input_v5(&framed).unwrap()
    else {
        panic!("level-one guest input changed wire kind")
    };

    assert_eq!(recomposed, composed);
    assert_eq!(
        recomposed,
        recompose_expected_value_aggregate_level_one_v5(&decoded, &policy).unwrap()
    );
    assert_eq!(recomposed.aggregate_level(), 1);
    assert_eq!(recomposed.scope(), &scope());
    assert_eq!(recomposed.semantic_subtree().partition().start(), 0);
    assert_eq!(recomposed.semantic_subtree().partition().end_exclusive(), 2);
    assert_eq!(recomposed.children().len(), 2);
    for (index, (descriptor, journal_bytes)) in recomposed
        .children()
        .iter()
        .zip(children.iter())
        .enumerate()
    {
        assert_eq!(descriptor.child_level(), 0);
        assert_eq!(descriptor.partition().start(), index as u64);
        assert_eq!(
            descriptor.claim_binding(),
            derive_risc0_verified_claim_binding_v1(image(100), journal_bytes).unwrap()
        );
        let journal =
            zenodex_zrpf_protocol_v3::decode_exact_node_journal_v4(journal_bytes).unwrap();
        assert_eq!(descriptor.journal_hash(), journal.canonical_hash().unwrap());
        assert_eq!(
            descriptor.semantic_subtree_root(),
            journal.semantic_subtree().canonical_hash().unwrap()
        );
    }
}

#[test]
fn governed_image_program_profile_manifest_and_scope_mismatches_reject() {
    let expected = identity(100, 70, 71);
    let bytes = leaf_bytes(0, indexed(60, 0), indexed(60, 1), scope(), expected);
    let input = ValueAggregateLevelOneInputV5::new(vec![bytes]).unwrap();

    let wrong_image = image(200);
    assert_eq!(
        GovernedValueChildIdentityV5::new(
            wrong_image,
            expected.expected_program_id(),
            expected.expected_profile_id(),
            expected.expected_manifest_root(),
        ),
        Err(ValueAggregateRecompositionErrorV5::InvalidPolicy(
            "child_image_program_binding"
        ))
    );

    for (child_policy, expected_error) in [
        (
            identity(200, 70, 71),
            ValueAggregateRecompositionErrorV5::ChildProgramMismatch(0),
        ),
        (
            GovernedValueChildIdentityV5::new(
                image(100),
                program_from_image(image(100)),
                zenodex_zrpf_protocol_v3::ProfileIdV3::new([72; 32]).unwrap(),
                commitment(71),
            )
            .unwrap(),
            ValueAggregateRecompositionErrorV5::ChildProfileMismatch(0),
        ),
        (
            GovernedValueChildIdentityV5::new(
                image(100),
                program_from_image(image(100)),
                expected.expected_profile_id(),
                commitment(73),
            )
            .unwrap(),
            ValueAggregateRecompositionErrorV5::ChildManifestMismatch(0),
        ),
    ] {
        assert_eq!(
            recompose_expected_value_aggregate_level_one_v5(
                &input,
                &policy(scope(), vec![child_policy])
            ),
            Err(expected_error)
        );
    }

    assert_eq!(
        recompose_expected_value_aggregate_level_one_v5(
            &input,
            &policy(scope_with_application(9), vec![expected])
        ),
        Err(ValueAggregateRecompositionErrorV5::ChildScopeMismatch(0))
    );
}

#[test]
fn level_shape_order_and_state_continuity_fail_closed() {
    let identity = identity(100, 70, 71);
    let aggregate =
        ValueAggregateLevelOneInputV5::new(vec![aggregate_v4_bytes(0, scope(), identity)]).unwrap();
    assert_eq!(
        recompose_expected_value_aggregate_level_one_v5(
            &aggregate,
            &policy(scope(), vec![identity])
        ),
        Err(ValueAggregateRecompositionErrorV5::ChildLevelMismatch {
            child: 0,
            actual: 1
        })
    );

    let (mut children, identity) = valid_children();
    children.reverse();
    let reversed = ValueAggregateLevelOneInputV5::new(children).unwrap();
    assert_eq!(
        recompose_expected_value_aggregate_level_one_v5(
            &reversed,
            &policy(scope(), vec![identity, identity])
        ),
        Err(ValueAggregateRecompositionErrorV5::SemanticMerge(
            ValueNodeErrorV4::NonCanonicalSemanticChildOrder { child: 1 }
        ))
    );

    let discontinuous = ValueAggregateLevelOneInputV5::new(vec![
        leaf_bytes(0, indexed(60, 0), indexed(60, 1), scope(), identity),
        leaf_bytes(1, indexed(60, 9), indexed(60, 10), scope(), identity),
    ])
    .unwrap();
    assert_eq!(
        recompose_expected_value_aggregate_level_one_v5(
            &discontinuous,
            &policy(scope(), vec![identity, identity])
        ),
        Err(ValueAggregateRecompositionErrorV5::SemanticMerge(
            ValueNodeErrorV4::SemanticChildStateDiscontinuity { child: 1 }
        ))
    );
}

#[test]
fn duplicate_claim_and_noncanonical_or_oversized_journals_reject() {
    let identity = identity(100, 70, 71);
    let bytes = leaf_bytes(0, indexed(60, 0), indexed(60, 1), scope(), identity);
    let duplicate = ValueAggregateLevelOneInputV5::new(vec![bytes.clone(), bytes.clone()]).unwrap();
    assert_eq!(
        recompose_expected_value_aggregate_level_one_v5(
            &duplicate,
            &policy(scope(), vec![identity, identity])
        ),
        Err(ValueAggregateRecompositionErrorV5::DuplicateChildClaim)
    );

    let mut trailing = bytes;
    trailing.push(0);
    let trailing = ValueAggregateLevelOneInputV5::new(vec![trailing]).unwrap();
    assert_eq!(
        recompose_expected_value_aggregate_level_one_v5(
            &trailing,
            &policy(scope(), vec![identity])
        ),
        Err(ValueAggregateRecompositionErrorV5::ChildV4JournalDecode(0))
    );
    assert_eq!(
        ValueAggregateLevelOneInputV5::new(vec![vec![0; MAX_NODE_JOURNAL_BYTES_V4 + 1]]),
        Err(ValueAggregateRecompositionErrorV5::ChildBytesTooLarge {
            child: 0,
            actual: MAX_NODE_JOURNAL_BYTES_V4 + 1,
            maximum: MAX_NODE_JOURNAL_BYTES_V4,
        })
    );
}

#[test]
fn exact_valid_journal_with_substituted_statement_changes_child_identity() {
    let identity = identity(100, 70, 71);
    let baseline = leaf_journal(0, 0, indexed(60, 0), indexed(60, 1), scope(), identity);
    let substituted = leaf_journal(0, 99, indexed(60, 0), indexed(60, 1), scope(), identity);
    let baseline =
        ValueAggregateLevelOneInputV5::new(vec![encode_node_journal_v4(&baseline).unwrap()])
            .unwrap();
    let substituted =
        ValueAggregateLevelOneInputV5::new(vec![encode_node_journal_v4(&substituted).unwrap()])
            .unwrap();
    let policy = policy(scope(), vec![identity]);
    let baseline = recompose_expected_value_aggregate_level_one_v5(&baseline, &policy).unwrap();
    let substituted =
        recompose_expected_value_aggregate_level_one_v5(&substituted, &policy).unwrap();
    assert_ne!(
        baseline.proposal_commitment(),
        substituted.proposal_commitment()
    );
    assert_ne!(
        baseline.children()[0].claim_binding(),
        substituted.children()[0].claim_binding()
    );
}
