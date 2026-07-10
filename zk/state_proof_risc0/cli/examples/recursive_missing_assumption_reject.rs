use std::io::Read;

use risc0_zkvm::{
    default_executor,
    sha::{Digest, Digestible},
    ExecutorEnv, MaybePruned, ReceiptClaim,
};
use serde_json::{json, Value};
use tau_state_proof_risc0_methods::TAU_STATE_PROOF_RISC0_AGGREGATE_ELF;
use tau_state_proof_risc0_shared::{
    compose_recursive_epoch_journal_v1, RecursiveCompositionInputV1,
    RECURSIVE_AGGREGATE_MAX_INPUT_BYTES,
};

const MAX_REQUEST_BYTES: usize = 16 * 1024 * 1024;

fn expected_missing_assumption_reason(
    input: &RecursiveCompositionInputV1,
) -> Result<String, String> {
    let child = input
        .children
        .first()
        .ok_or_else(|| "recursive child set empty".to_string())?;
    let journal_digest = child.child_journal_bytes.as_slice().digest();
    let claim_digest = ReceiptClaim::ok(
        child.descriptor.child_image_id,
        MaybePruned::<Vec<u8>>::Pruned(journal_digest),
    )
    .digest();
    Ok(format!(
        "sys_verify_integrity: no receipt found to resolve assumption: claim digest {claim_digest}, control root {}",
        Digest::ZERO
    ))
}

fn is_exact_missing_assumption_reason(reason: &str, expected_reason: &str) -> bool {
    reason == expected_reason
}

fn main() {
    if let Err(error) = run() {
        eprintln!("{error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    if TAU_STATE_PROOF_RISC0_AGGREGATE_ELF.is_empty() {
        return Err("aggregate ELF is empty".to_string());
    }
    let mut bytes = Vec::new();
    std::io::stdin()
        .take((MAX_REQUEST_BYTES + 1) as u64)
        .read_to_end(&mut bytes)
        .map_err(|error| format!("failed to read request: {error}"))?;
    if bytes.len() > MAX_REQUEST_BYTES {
        return Err("request exceeds harness byte limit".to_string());
    }
    let request: Value =
        serde_json::from_slice(&bytes).map_err(|error| format!("invalid request JSON: {error}"))?;
    let input: RecursiveCompositionInputV1 = serde_json::from_value(
        request
            .get("recursive_input")
            .cloned()
            .ok_or_else(|| "recursive_input missing".to_string())?,
    )
    .map_err(|error| format!("recursive_input schema mismatch: {error}"))?;
    compose_recursive_epoch_journal_v1(&input)
        .map_err(|error| format!("recursive_input rejected: {error:?}"))?;

    let input_bytes =
        postcard::to_allocvec(&input).map_err(|error| format!("postcard failed: {error}"))?;
    if input_bytes.is_empty() || input_bytes.len() > RECURSIVE_AGGREGATE_MAX_INPUT_BYTES as usize {
        return Err("aggregate input byte length unsupported".to_string());
    }
    let input_len = u32::try_from(input_bytes.len())
        .map_err(|_| "aggregate input length exceeds u32".to_string())?;
    let env = ExecutorEnv::builder()
        .write_slice(&[input_len])
        .write_slice(&input_bytes)
        .build()
        .map_err(|error| format!("executor environment failed: {error}"))?;
    let expected_reason = expected_missing_assumption_reason(&input)?;

    match default_executor().execute(env, TAU_STATE_PROOF_RISC0_AGGREGATE_ELF) {
        Ok(_) => {
            Err("aggregate execution unexpectedly accepted missing child assumption".to_string())
        }
        Err(error)
            if error.chain().any(|cause| {
                is_exact_missing_assumption_reason(&cause.to_string(), &expected_reason)
            }) =>
        {
            println!(
                "{}",
                json!({
                    "ok": true,
                    "status": "missing_child_assumption_rejected",
                })
            );
            Ok(())
        }
        Err(error) => Err(format!(
            "aggregate execution failed without the expected missing child assumption: {error:#}"
        )),
    }
}

#[cfg(test)]
mod tests {
    use super::is_exact_missing_assumption_reason;

    const EXPECTED: &str = "sys_verify_integrity: no receipt found to resolve assumption: claim digest 1234, control root 0000";

    #[test]
    fn accepts_only_the_exact_expected_risc0_reason() {
        assert!(is_exact_missing_assumption_reason(EXPECTED, EXPECTED));
        assert!(!is_exact_missing_assumption_reason(
            "executor environment failed: unavailable",
            EXPECTED
        ));
        assert!(!is_exact_missing_assumption_reason(
            "sys_verify_integrity: no receipt found to resolve assumption: claim digest 9999, control root 0000",
            EXPECTED
        ));
        assert!(!is_exact_missing_assumption_reason(
            &format!("unrelated executor failure: {EXPECTED}"),
            EXPECTED
        ));
    }
}
