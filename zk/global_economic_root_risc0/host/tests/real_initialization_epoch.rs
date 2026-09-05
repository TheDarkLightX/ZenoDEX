//! Same-image dispatch evidence only: the child guest commits structural bytes.
//! This test grants no economic source legitimacy, route semantics or publication.

#[path = "../../test_support/mod.rs"]
mod support;

use risc0_zkvm::{default_prover, ExecutorEnv, FakeReceipt, ProverOpts, Receipt, ReceiptClaim};
use zenodex_epoch_test_methods::{
    ZENODEX_ROUTE_STRUCTURAL_TEST_LEAF_ELF, ZENODEX_ROUTE_STRUCTURAL_TEST_LEAF_ID,
};
use zenodex_global_economic_epoch_risc0_shared as epoch;
use zenodex_global_economic_root_risc0_host::*;
use zenodex_global_economic_root_risc0_methods::{
    ZENODEX_ECONOMIC_ROOT_GUEST_ELF, ZENODEX_ECONOMIC_ROOT_GUEST_ID,
};
use zenodex_global_economic_root_risc0_shared::*;

fn structural_receipt(journal: &[u8]) -> Receipt {
    assert!(!ZENODEX_ROUTE_STRUCTURAL_TEST_LEAF_ELF.is_empty());
    let length = u32::try_from(journal.len()).unwrap();
    let env = ExecutorEnv::builder()
        .write_slice(&[length])
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
#[ignore = "one genuine foreign-image receipt for an exact supplied bounded journal"]
fn real_foreign_image_for_exact_journal() {
    use std::io::Read;
    let mut journal = Vec::new();
    std::fs::File::open(std::env::var_os("ZENODEX_FOREIGN_JOURNAL_FILE").unwrap())
        .unwrap()
        .take(2 * 1024 * 1024 + 1)
        .read_to_end(&mut journal)
        .unwrap();
    assert!(!journal.is_empty() && journal.len() <= 2 * 1024 * 1024);
    let receipt = structural_receipt(&journal);
    let directory =
        std::path::PathBuf::from(std::env::var_os("ZENODEX_FOREIGN_EVIDENCE_DIR").unwrap());
    std::fs::create_dir_all(&directory).unwrap();
    std::fs::write(
        directory.join("foreign.receipt.json"),
        serde_json::to_vec(&receipt).unwrap(),
    )
    .unwrap();
    std::fs::write(directory.join("foreign.journal"), journal).unwrap();
    std::fs::write(
        directory.join("foreign.elf"),
        ZENODEX_ROUTE_STRUCTURAL_TEST_LEAF_ELF,
    )
    .unwrap();
    std::fs::write(
        directory.join("foreign-image-words.json"),
        serde_json::to_vec(&ZENODEX_ROUTE_STRUCTURAL_TEST_LEAF_ID).unwrap(),
    )
    .unwrap();
}

#[test]
#[ignore = "four real Succinct receipts; isolated same-image structural dispatch qualification"]
fn real_genesis_then_epoch_share_one_profile_image_and_reject_foreign_receipts() {
    let image = economic_root_image_root_v1().unwrap();
    let initial = support::initial_input(&image);
    let genesis_input = support::initial_root_input(&image);
    let genesis_frame = canonical_root_input_bytes_v1(&genesis_input).unwrap();
    let genesis_prepared = prepare_root_input_v1(&genesis_frame).unwrap();
    let direct = support::epoch_input(&initial, 1, ZENODEX_ROUTE_STRUCTURAL_TEST_LEAF_ID);
    let epoch_input = RootGuestInputV1::RecursiveEpochV1(
        epoch::GlobalEconomicRecursiveGuestInputV1::DirectEpoch(direct.clone()),
    );
    let epoch_frame = canonical_root_input_bytes_v1(&epoch_input).unwrap();
    let epoch_prepared = prepare_root_input_v1(&epoch_frame).unwrap();
    assert_eq!(
        genesis_prepared.root_image_id(),
        epoch_prepared.root_image_id()
    );
    let certificate: epoch::GlobalEconomicEpochJournalV1 =
        serde_json::from_slice(epoch_prepared.journal_bytes()).unwrap();
    assert_eq!(
        initial.statement.state_root.as_str(),
        certificate.pre_state_root.as_str()
    );
    assert_eq!(
        initial.profile.profile_id.as_str(),
        certificate.profile_root.as_str()
    );

    let genesis = prove_economic_root_succinct_v1(&genesis_input, vec![]).unwrap();
    let child = structural_receipt(&direct.route_receipts[0].journal_bytes);
    assert!(matches!(
        build_economic_root_executor_env_v1(&epoch_input, vec![]),
        Err(EconomicRootHostErrorV1::ReceiptCount)
    ));
    let mut corrupt_child = child.clone();
    corrupt_child.journal.bytes.push(0);
    assert!(matches!(
        build_economic_root_executor_env_v1(&epoch_input, vec![corrupt_child]),
        Err(EconomicRootHostErrorV1::ReceiptJournal)
    ));
    let fake: Receipt = FakeReceipt::new(ReceiptClaim::ok(
        ZENODEX_ROUTE_STRUCTURAL_TEST_LEAF_ID,
        child.journal.bytes.clone(),
    ))
    .try_into()
    .unwrap();
    assert!(matches!(
        build_economic_root_executor_env_v1(&epoch_input, vec![fake]),
        Err(EconomicRootHostErrorV1::ReceiptKind)
    ));
    let epoch = prove_economic_root_succinct_v1(&epoch_input, vec![child.clone()]).unwrap();
    verify_economic_root_receipt_v1(&genesis, &genesis_prepared).unwrap();
    verify_economic_root_receipt_v1(&epoch, &epoch_prepared).unwrap();
    assert!(matches!(
        verify_economic_root_receipt_v1(&genesis, &epoch_prepared),
        Err(EconomicRootHostErrorV1::ReceiptJournal)
    ));
    assert!(matches!(
        verify_economic_root_receipt_v1(&epoch, &genesis_prepared),
        Err(EconomicRootHostErrorV1::ReceiptJournal)
    ));
    let mut changed_context = certificate;
    changed_context.height += 1;
    let mut context_input = direct;
    context_input.certificate_journal_bytes =
        epoch::canonical_json_bytes_v1(&changed_context, "changed context").unwrap();
    let context_prepared = prepare_root_input_v1(
        &canonical_root_input_bytes_v1(&RootGuestInputV1::RecursiveEpochV1(
            epoch::GlobalEconomicRecursiveGuestInputV1::DirectEpoch(context_input),
        ))
        .unwrap(),
    )
    .unwrap();
    assert!(matches!(
        verify_economic_root_receipt_v1(&epoch, &context_prepared),
        Err(EconomicRootHostErrorV1::ReceiptJournal)
    ));
    // This genuine receipt has the exact epoch bytes under a foreign image.
    let foreign = structural_receipt(epoch_prepared.journal_bytes());
    assert!(matches!(
        verify_economic_root_receipt_v1(&foreign, &epoch_prepared),
        Err(EconomicRootHostErrorV1::ReceiptVerification)
    ));

    if let Some(directory) = std::env::var_os("ZENODEX_ROOT_EVIDENCE_DIR") {
        let directory = std::path::PathBuf::from(directory);
        std::fs::create_dir_all(&directory).unwrap();
        for (name, receipt) in [
            ("genesis", &genesis),
            ("epoch", &epoch),
            ("structural-child", &child),
            ("foreign-epoch", &foreign),
        ] {
            std::fs::write(
                directory.join(format!("{name}.receipt")),
                postcard::to_allocvec(receipt).unwrap(),
            )
            .unwrap();
            std::fs::write(
                directory.join(format!("{name}.journal")),
                &receipt.journal.bytes,
            )
            .unwrap();
        }
        std::fs::write(directory.join("root.elf"), ZENODEX_ECONOMIC_ROOT_GUEST_ELF).unwrap();
        std::fs::write(
            directory.join("structural-child.elf"),
            ZENODEX_ROUTE_STRUCTURAL_TEST_LEAF_ELF,
        )
        .unwrap();
        std::fs::write(directory.join("genesis.input"), genesis_frame).unwrap();
        std::fs::write(directory.join("epoch.input"), epoch_frame).unwrap();
        std::fs::write(
            directory.join("subject.json"),
            serde_json::to_vec_pretty(&serde_json::json!({
                "root_image_id": image, "root_image_words": ZENODEX_ECONOMIC_ROOT_GUEST_ID,
                "structural_child_image_words": ZENODEX_ROUTE_STRUCTURAL_TEST_LEAF_ID,
                "receipt_count": 4, "economic_route_semantics_proved": false,
                "publication_qualified": false, "production_authority": false,
            }))
            .unwrap(),
        )
        .unwrap();
    }
}
