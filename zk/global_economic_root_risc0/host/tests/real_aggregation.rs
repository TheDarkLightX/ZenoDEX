//! Actual recursive dispatch with structural route children; no route economics claim.

#[path = "../../test_support/mod.rs"]
mod support;

use risc0_zkvm::{default_prover, ExecutorEnv, ProverOpts, Receipt};
use zenodex_epoch_test_methods::{
    ZENODEX_ROUTE_STRUCTURAL_TEST_LEAF_ELF, ZENODEX_ROUTE_STRUCTURAL_TEST_LEAF_ID,
};
use zenodex_global_economic_epoch_risc0_shared as epoch;
use zenodex_global_economic_root_risc0_host::*;
use zenodex_global_economic_root_risc0_methods::ZENODEX_ECONOMIC_ROOT_GUEST_ID;
use zenodex_global_economic_root_risc0_shared::*;

fn route_receipt(journal: &[u8]) -> Receipt {
    let env = ExecutorEnv::builder()
        .write_slice(&[u32::try_from(journal.len()).unwrap()])
        .write_slice(journal)
        .build()
        .unwrap();
    let receipt = default_prover()
        .prove_with_opts(
            env,
            ZENODEX_ROUTE_STRUCTURAL_TEST_LEAF_ELF,
            &ProverOpts::succinct(),
        )
        .unwrap()
        .receipt;
    receipt
        .verify(ZENODEX_ROUTE_STRUCTURAL_TEST_LEAF_ID)
        .unwrap();
    assert_eq!(receipt.journal.bytes, journal);
    receipt
}

#[test]
#[ignore = "nine real route children, two command aggregations and one recursive epoch"]
fn real_nine_command_epoch_resolves_ordered_same_image_aggregations() {
    prove_aggregated_epoch(9);
}

#[test]
#[ignore = "64 real route children, eight aggregations and one epoch at the admitted ceiling"]
fn real_64_command_epoch_resolves_and_65_rejects_before_proving() {
    let image = economic_root_image_root_v1().unwrap();
    let initial = support::initial_input(&image);
    let over = support::epoch_input(&initial, 65, ZENODEX_ROUTE_STRUCTURAL_TEST_LEAF_ID);
    let at_bound = support::epoch_input(&initial, 64, ZENODEX_ROUTE_STRUCTURAL_TEST_LEAF_ID);
    let mut malformed = support::aggregated_input(&at_bound, ZENODEX_ECONOMIC_ROOT_GUEST_ID);
    malformed.certificate_journal_bytes = over.certificate_journal_bytes;
    let rejected = RootGuestInputV1::RecursiveEpochV1(
        epoch::GlobalEconomicRecursiveGuestInputV1::AggregatedEpoch(malformed),
    );
    let rejection = canonical_root_input_bytes_v1(&rejected).unwrap_err();
    assert!(matches!(
        rejection,
        RootGuestErrorV1::Epoch(epoch::EconomicEpochGuestErrorV1::InvalidBounds(
            "epoch command count"
        ))
    ));
    println!("65-command preflight rejection: {rejection:?}");
    prove_aggregated_epoch(64);
}

fn prove_aggregated_epoch(count: usize) {
    let started = std::time::Instant::now();
    let image = economic_root_image_root_v1().unwrap();
    let initial = support::initial_input(&image);
    let direct = support::epoch_input(&initial, count, ZENODEX_ROUTE_STRUCTURAL_TEST_LEAF_ID);
    let directory = std::env::var_os("ZENODEX_ROOT_EVIDENCE_DIR").map(std::path::PathBuf::from);
    if let Some(directory) = &directory {
        std::fs::create_dir_all(directory).unwrap();
    }
    let mut groups = Vec::new();
    for (index, group) in support::aggregation_inputs(&direct).into_iter().enumerate() {
        let children = group
            .route_receipts
            .iter()
            .map(|claim| route_receipt(&claim.journal_bytes))
            .collect();
        let input = RootGuestInputV1::RecursiveEpochV1(
            epoch::GlobalEconomicRecursiveGuestInputV1::CommandAggregation(group),
        );
        let receipt = prove_economic_root_succinct_v1(&input, children).unwrap();
        if let Some(directory) = &directory {
            std::fs::write(
                directory.join(format!("command-group-{index}.receipt")),
                postcard::to_allocvec(&receipt).unwrap(),
            )
            .unwrap();
            std::fs::write(
                directory.join(format!("command-group-{index}.input")),
                canonical_root_input_bytes_v1(&input).unwrap(),
            )
            .unwrap();
        }
        groups.push(receipt);
    }
    let input = RootGuestInputV1::RecursiveEpochV1(
        epoch::GlobalEconomicRecursiveGuestInputV1::AggregatedEpoch(support::aggregated_input(
            &direct,
            ZENODEX_ECONOMIC_ROOT_GUEST_ID,
        )),
    );
    assert_eq!(groups.len(), count.div_ceil(8));
    let mut reversed = groups.clone();
    reversed.reverse();
    assert!(matches!(
        build_economic_root_executor_env_v1(&input, reversed),
        Err(EconomicRootHostErrorV1::ReceiptJournal)
    ));
    let receipt = prove_economic_root_succinct_v1(&input, groups).unwrap();
    assert_eq!(receipt.journal.bytes, direct.certificate_journal_bytes);
    let measurement = serde_json::json!({
        "commands": count, "command_aggregations": count.div_ceil(8),
        "succinct_proofs": count + count.div_ceil(8) + 1,
        "elapsed_millis": started.elapsed().as_millis(),
        "epoch_input_bytes": canonical_root_input_bytes_v1(&input).unwrap().len(),
        "epoch_journal_bytes": receipt.journal.bytes.len(),
        "epoch_receipt_bytes": postcard::to_allocvec(&receipt).unwrap().len(),
        "root_image_words": ZENODEX_ECONOMIC_ROOT_GUEST_ID,
        "economic_route_semantics_proved": false, "production_authority": false,
    });
    println!("{measurement}");
    if let Some(directory) = directory {
        std::fs::write(
            directory.join("aggregation-measurements.json"),
            serde_json::to_vec_pretty(&measurement).unwrap(),
        )
        .unwrap();
        std::fs::write(
            directory.join("aggregated-epoch.receipt"),
            postcard::to_allocvec(&receipt).unwrap(),
        )
        .unwrap();
        std::fs::write(
            directory.join("aggregated-epoch.input"),
            canonical_root_input_bytes_v1(&input).unwrap(),
        )
        .unwrap();
    }
}
