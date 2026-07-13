use zenodex_zrpf_risc0_semantic_shared::{
    bind_semantic_guest_input_after_level_one_verification_v1, SemanticGuestBindingErrorV1,
    SemanticGuestInputV1, SemanticGuestLeafDisclosureV1, SemanticGuestLevelOneDisclosureV1,
};

const SELF_IMAGE_ID: [u32; 8] = [1, 2, 3, 4, 5, 6, 7, 8];

fn raw_input(opening: [u8; 32]) -> SemanticGuestInputV1 {
    let leaf = SemanticGuestLeafDisclosureV1::new(vec![1, 2, 3], opening).unwrap();
    let level_one = SemanticGuestLevelOneDisclosureV1::new(vec![4, 5, 6], vec![leaf]).unwrap();
    SemanticGuestInputV1::new(SELF_IMAGE_ID, vec![level_one]).unwrap()
}

#[test]
fn bounded_raw_disclosures_convert_without_interpreting_journal_bytes() {
    let bound =
        bind_semantic_guest_input_after_level_one_verification_v1(&raw_input([9; 32])).unwrap();

    assert_eq!(bound.expected_semantic_self_image_id(), SELF_IMAGE_ID);
    assert_eq!(bound.recomposition().level_one_nodes().len(), 1);
    assert_eq!(
        bound.recomposition().level_one_nodes()[0].adapter_leaves()[0]
            .semantic_opening()
            .semantic_source_binding_hash()
            .as_bytes(),
        &[9; 32]
    );
}

#[test]
fn zero_semantic_opening_rejects_at_the_post_verification_binding_boundary() {
    assert_eq!(
        bind_semantic_guest_input_after_level_one_verification_v1(&raw_input([0; 32])),
        Err(SemanticGuestBindingErrorV1::ZeroSemanticOpening {
            subtree: 0,
            child: 0,
        })
    );
}
