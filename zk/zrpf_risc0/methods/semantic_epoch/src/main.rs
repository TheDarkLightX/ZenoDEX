#![no_std]
#![no_main]

extern crate alloc;

use alloc::vec;
use risc0_zkvm::guest::{abort, env};
use zenodex_zrpf_protocol_v3::{
    encode_semantic_epoch_proposal_v1, MAX_SEMANTIC_EPOCH_PROPOSAL_BYTES_V1,
};
use zenodex_zrpf_risc0_semantic_shared::{
    bind_semantic_guest_input_after_level_one_verification_v1,
    compose_semantic_epoch_after_level_one_verification_v1, decode_exact_semantic_guest_input_v1,
    SemanticEpochCompositionPolicyV1, MAX_SEMANTIC_GUEST_INPUT_BYTES_V1,
};

risc0_zkvm::guest::entry!(main);

const _: () = assert!(MAX_SEMANTIC_GUEST_INPUT_BYTES_V1 == 297_147);
const _: () = assert!(MAX_SEMANTIC_EPOCH_PROPOSAL_BYTES_V1 == 4_096);

// These historical temporary-path image IDs calibrate the first semantic guest
// build only. Any source change invalidates them. The staged A -> B -> C -> D
// rebuild must replace A, B, and C before fresh semantic proof evidence exists.
const CALIBRATION_HISTORICAL_ADAPTER_IMAGE_ID_A: [u32; 8] = [
    3_045_257_841,
    281_444_177,
    3_435_235_465,
    2_147_567_259,
    867_057_786,
    252_644_892,
    735_118_677,
    1_951_735_332,
];
const CALIBRATION_HISTORICAL_LEVEL_ONE_IMAGE_ID_B: [u32; 8] = [
    1_371_435_586,
    694_089_317,
    2_169_443_275,
    3_295_636_573,
    692_682_509,
    144_110_969,
    3_272_649_772,
    725_406_960,
];
const CALIBRATION_HISTORICAL_LEVEL_TWO_IMAGE_ID_C: [u32; 8] = [
    294_487_355,
    2_991_960_380,
    1_931_243_156,
    3_848_265_535,
    4_100_664_153,
    171_806_828,
    540_212_028,
    911_705_241,
];

pub fn main() {
    let input_bytes = read_bounded_input();
    let raw_input = match decode_exact_semantic_guest_input_v1(&input_bytes) {
        Ok(value) => value,
        Err(_) => abort("ZRPF semantic epoch input rejected"),
    };

    // Only bounded framing is interpreted before this loop. Every exact L1
    // journal is authenticated before leaf journals or openings gain meaning.
    for disclosure in raw_input.level_one_disclosures() {
        match env::verify(
            CALIBRATION_HISTORICAL_LEVEL_ONE_IMAGE_ID_B,
            disclosure.journal_bytes(),
        ) {
            Ok(()) => {}
            Err(never) => match never {},
        }
    }

    let semantic_input = match bind_semantic_guest_input_after_level_one_verification_v1(&raw_input)
    {
        Ok(value) => value,
        Err(_) => abort("ZRPF semantic epoch disclosure binding rejected"),
    };
    // This self-image value is a circular-build escape hatch. It gains
    // authority only when the sealed outer verifier compares it with the image
    // whose semantic receipt it cryptographically verified.
    let policy = match SemanticEpochCompositionPolicyV1::new(
        CALIBRATION_HISTORICAL_ADAPTER_IMAGE_ID_A,
        CALIBRATION_HISTORICAL_LEVEL_ONE_IMAGE_ID_B,
        CALIBRATION_HISTORICAL_LEVEL_TWO_IMAGE_ID_C,
    ) {
        Ok(value) => value,
        Err(_) => abort("ZRPF semantic epoch calibration policy rejected"),
    };
    let projection =
        match compose_semantic_epoch_after_level_one_verification_v1(&semantic_input, policy) {
            Ok(value) => value,
            Err(_) => abort("ZRPF semantic epoch composition rejected"),
        };
    let proposal_bytes = match encode_semantic_epoch_proposal_v1(projection.proposal()) {
        Ok(value) => value,
        Err(_) => abort("ZRPF semantic epoch proposal encoding failed"),
    };
    if proposal_bytes.len() > MAX_SEMANTIC_EPOCH_PROPOSAL_BYTES_V1 {
        abort("ZRPF semantic epoch proposal exceeds bound");
    }
    env::commit_slice(&proposal_bytes);
}

fn read_bounded_input() -> alloc::vec::Vec<u8> {
    let mut input_len = 0u32;
    env::read_slice(core::slice::from_mut(&mut input_len));
    let input_len = match usize::try_from(input_len) {
        Ok(value) if value > 0 && value <= MAX_SEMANTIC_GUEST_INPUT_BYTES_V1 => value,
        _ => abort("ZRPF semantic epoch input length unsupported"),
    };
    let mut input_bytes = vec![0u8; input_len];
    env::read_slice(&mut input_bytes);
    input_bytes
}
