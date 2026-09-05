//! Raw executor controls independently exercise the guest's assumption loop.
//! A valid retained positive control makes an unrelated input refusal insufficient.

use risc0_zkvm::{default_prover, ExecutorEnv, ProverOpts, Receipt};
use zenodex_global_economic_root_risc0_host::verify_economic_root_receipt_v1;
use zenodex_global_economic_root_risc0_methods::{
    ZENODEX_ECONOMIC_ROOT_GUEST_ELF, ZENODEX_ECONOMIC_ROOT_GUEST_ID,
};
use zenodex_global_economic_root_risc0_shared::prepare_root_input_v1;

#[test]
#[ignore = "requires retained genuine direct-epoch control and actual root guest execution"]
fn raw_guest_cannot_resolve_missing_or_wrong_child_assumptions() {
    let directory = std::path::PathBuf::from(
        std::env::var_os("ZENODEX_ROOT_EVIDENCE_DIR").expect("retained proof directory"),
    );
    let frame = std::fs::read(directory.join("epoch.input")).unwrap();
    let prepared = prepare_root_input_v1(&frame).unwrap();
    assert_eq!(prepared.child_claims().len(), 1);
    let read_receipt = |name: &str| -> Receipt {
        postcard::from_bytes(&std::fs::read(directory.join(name)).unwrap()).unwrap()
    };
    let positive = read_receipt("epoch.receipt");
    verify_economic_root_receipt_v1(&positive, &prepared).unwrap();
    let wrong = read_receipt("foreign-epoch.receipt");
    assert_ne!(
        wrong.journal.bytes,
        prepared.child_claims()[0].journal_bytes()
    );
    let mut results = Vec::new();
    for (name, assumption) in [("missing", None), ("wrong-journal", Some(wrong))] {
        // Deliberately bypass the host admission guard in this negative test.
        let mut builder = ExecutorEnv::builder();
        builder
            .write_slice(&[u32::try_from(frame.len()).unwrap()])
            .write_slice(&frame);
        if let Some(receipt) = assumption {
            builder.add_assumption(receipt);
        }
        let outcome = default_prover().prove_with_opts(
            builder.build().unwrap(),
            ZENODEX_ECONOMIC_ROOT_GUEST_ELF,
            &ProverOpts::succinct(),
        );
        let result = match outcome {
            Err(error) => serde_json::json!({
                "case": name, "outcome": "prover_rejected", "error": error.to_string(),
            }),
            Ok(info) => {
                assert!(
                    info.receipt.verify(ZENODEX_ECONOMIC_ROOT_GUEST_ID).is_err(),
                    "guest admitted a complete receipt without its required child"
                );
                std::fs::write(
                    directory.join(format!("unresolved-{name}.receipt")),
                    postcard::to_allocvec(&info.receipt).unwrap(),
                )
                .unwrap();
                serde_json::json!({"case": name, "outcome": "receipt_verifier_rejected"})
            }
        };
        println!("{result}");
        results.push(result);
    }
    std::fs::write(
        directory.join("guest-assumption-controls.json"),
        serde_json::to_vec_pretty(&serde_json::json!({
            "positive_control": "genuine exact epoch receipt verified",
            "cases": results, "production_authority": false,
        }))
        .unwrap(),
    )
    .unwrap();
}
