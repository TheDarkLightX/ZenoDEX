#![no_std]
#![no_main]

extern crate alloc;

use alloc::vec;
use risc0_zkvm::guest::{abort, env};
use zenodex_zrpf_protocol_v3::{
    encode_semantic_epoch_proposal_v2, MAX_SEMANTIC_EPOCH_PROPOSAL_BYTES_V2,
};
use zenodex_zrpf_risc0_semantic_shared::{
    bind_semantic_guest_input_after_level_one_verification_v2,
    compose_semantic_epoch_after_level_one_verification_v2, decode_exact_semantic_guest_input_v2,
    SemanticEpochCompositionErrorV2, SemanticEpochCompositionPolicyV2,
    SemanticRecompositionErrorV1, MAX_SEMANTIC_GUEST_INPUT_BYTES_V2,
};

risc0_zkvm::guest::entry!(main);

const _: () = assert!(MAX_SEMANTIC_GUEST_INPUT_BYTES_V2 == 297_115);
const _: () = assert!(MAX_SEMANTIC_EPOCH_PROPOSAL_BYTES_V2 == 4_096);

// These dependency identities were derived by the staged A -> B -> C build.
// Runtime image D is absent from the guest input and proposal. The sealed outer
// verifier attaches D only after it cryptographically verifies this receipt.
const PINNED_ADAPTER_IMAGE_ID_A: [u32; 8] = [
    2_750_530_258,
    37_668_129,
    744_178_984,
    4_248_971_762,
    810_572_263,
    4_257_446_307,
    1_152_353_364,
    1_683_867_498,
];
const PINNED_LEVEL_ONE_IMAGE_ID_B: [u32; 8] = [
    145_746_289,
    1_948_307_068,
    2_821_597_170,
    1_671_545_822,
    336_618_883,
    1_593_244_911,
    2_328_107_180,
    2_850_628_135,
];
const PINNED_LEVEL_TWO_IMAGE_ID_C: [u32; 8] = [
    3_297_652_393,
    2_852_053_573,
    3_760_724_470,
    622_457_309,
    406_848_594,
    614_446_304,
    1_509_575_479,
    3_011_858_596,
];

pub fn main() {
    let input_bytes = read_bounded_input();
    let raw_input = match decode_exact_semantic_guest_input_v2(&input_bytes) {
        Ok(value) => value,
        Err(_) => abort("ZRPF semantic epoch input rejected"),
    };

    // Only bounded framing is interpreted before this loop. Every exact L1
    // journal is authenticated before leaf journals or openings gain meaning.
    for disclosure in raw_input.level_one_disclosures() {
        match env::verify(PINNED_LEVEL_ONE_IMAGE_ID_B, disclosure.journal_bytes()) {
            Ok(()) => {}
            Err(never) => match never {},
        }
    }

    let semantic_input = match bind_semantic_guest_input_after_level_one_verification_v2(&raw_input)
    {
        Ok(value) => value,
        Err(_) => abort("ZRPF semantic epoch disclosure binding rejected"),
    };
    let policy = match SemanticEpochCompositionPolicyV2::new(
        PINNED_ADAPTER_IMAGE_ID_A,
        PINNED_LEVEL_ONE_IMAGE_ID_B,
        PINNED_LEVEL_TWO_IMAGE_ID_C,
    ) {
        Ok(value) => value,
        Err(_) => abort("ZRPF semantic epoch dependency policy rejected"),
    };
    let projection =
        match compose_semantic_epoch_after_level_one_verification_v2(&semantic_input, policy) {
            Ok(value) => value,
            Err(SemanticEpochCompositionErrorV2::SemanticRecomposition(
                SemanticRecompositionErrorV1::DuplicateSemanticSource,
            )) => abort("ZRPF semantic epoch duplicate semantic source rejected"),
            Err(_) => abort("ZRPF semantic epoch composition rejected"),
        };
    let proposal_bytes = match encode_semantic_epoch_proposal_v2(projection.proposal()) {
        Ok(value) => value,
        Err(_) => abort("ZRPF semantic epoch proposal encoding failed"),
    };
    if proposal_bytes.len() > MAX_SEMANTIC_EPOCH_PROPOSAL_BYTES_V2 {
        abort("ZRPF semantic epoch proposal exceeds bound");
    }
    env::commit_slice(&proposal_bytes);
}

fn read_bounded_input() -> alloc::vec::Vec<u8> {
    let mut input_len = 0u32;
    env::read_slice(core::slice::from_mut(&mut input_len));
    let input_len = match usize::try_from(input_len) {
        Ok(value) if value > 0 && value <= MAX_SEMANTIC_GUEST_INPUT_BYTES_V2 => value,
        _ => abort("ZRPF semantic epoch input length unsupported"),
    };
    let mut input_bytes = vec![0u8; input_len];
    env::read_slice(&mut input_bytes);
    input_bytes
}
