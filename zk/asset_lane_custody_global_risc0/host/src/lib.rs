//! Bounded receipt codec and input validation for the fixed custody guest.
//!
//! Native validation establishes only exact transport, statement bytes, and
//! receipt encoding. The feature-gated prover separately binds the compiled
//! image, receipt kind, journal, and cryptographic proof.

use core::fmt;
use risc0_zkvm::Receipt;
use std::io::Read;
use zenodex_global_settlement_abi_v2::{
    prepare_asset_lane_custody_global_frame_v2, AssetLaneCustodyStatementResultV2,
    MAX_ASSET_LANE_CUSTODY_GLOBAL_FRAME_BYTES_V2,
};

#[cfg(any(feature = "compiled-guest", test))]
use risc0_zkvm::ExecutorEnv;
#[cfg(feature = "compiled-guest")]
use risc0_zkvm::InnerReceipt;
#[cfg(feature = "compiled-guest")]
use risc0_zkvm::{compute_image_id, default_prover, ProverOpts};
#[cfg(feature = "compiled-guest")]
use zenodex_asset_lane_custody_global_risc0_methods::{
    ZENODEX_ASSET_LANE_CUSTODY_GLOBAL_GUEST_ELF, ZENODEX_ASSET_LANE_CUSTODY_GLOBAL_GUEST_ID,
};

pub const MAX_ASSET_LANE_CUSTODY_RECEIPT_BYTES_V2: usize = 16 * 1024 * 1024;
pub const MAX_ASSET_LANE_CUSTODY_GUEST_INPUT_BYTES_V2: usize =
    4 + MAX_ASSET_LANE_CUSTODY_GLOBAL_FRAME_BYTES_V2;
/// Provisional operational ceiling; it does not claim all valid states fit.
pub const MAX_ASSET_LANE_CUSTODY_GLOBAL_CYCLES_V2: u64 = 16 * 1024 * 1024;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AssetLaneCustodyReceiptDecodeErrorV2 {
    InvalidBounds,
    InvalidEncoding,
    NonCanonical,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AssetLaneCustodyProofHostErrorV2 {
    Arguments,
    InputIo,
    InputBounds,
    InputTrailing,
    StatementRejected,
    StatementInvalid,
    DevelopmentModeConfigured,
    PlaceholderMethod,
    MethodBinding,
    Environment,
    ProverConfiguration,
    Proving,
    ReceiptKind,
    ReceiptJournal,
    ReceiptVerification,
    ReceiptEncoding,
}

impl fmt::Display for AssetLaneCustodyProofHostErrorV2 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "asset lane custody proof host rejected: {self:?}"
        )
    }
}

impl std::error::Error for AssetLaneCustodyProofHostErrorV2 {}

/// Reads the guest's exact outer `u32LE` frame and requires EOF after it.
pub fn read_asset_lane_custody_guest_input_v2(
    input: &mut impl Read,
) -> Result<Vec<u8>, AssetLaneCustodyProofHostErrorV2> {
    let mut length_bytes = [0_u8; 4];
    input
        .read_exact(&mut length_bytes)
        .map_err(|_| AssetLaneCustodyProofHostErrorV2::InputIo)?;
    let length = usize::try_from(u32::from_le_bytes(length_bytes))
        .map_err(|_| AssetLaneCustodyProofHostErrorV2::InputBounds)?;
    if !(1..=MAX_ASSET_LANE_CUSTODY_GLOBAL_FRAME_BYTES_V2).contains(&length) {
        return Err(AssetLaneCustodyProofHostErrorV2::InputBounds);
    }
    let mut frame = vec![0_u8; length];
    input
        .read_exact(&mut frame)
        .map_err(|_| AssetLaneCustodyProofHostErrorV2::InputIo)?;
    if input
        .read(&mut [0_u8; 1])
        .map_err(|_| AssetLaneCustodyProofHostErrorV2::InputIo)?
        != 0
    {
        return Err(AssetLaneCustodyProofHostErrorV2::InputTrailing);
    }
    Ok(frame)
}

/// Recomputes the only statement bytes the custody guest may commit.
pub fn prepare_asset_lane_custody_statement_v2(
    frame: &[u8],
) -> Result<Vec<u8>, AssetLaneCustodyProofHostErrorV2> {
    match prepare_asset_lane_custody_global_frame_v2(frame)
        .map_err(|_| AssetLaneCustodyProofHostErrorV2::StatementInvalid)?
    {
        AssetLaneCustodyStatementResultV2::Statement(statement) => Ok(statement),
        AssetLaneCustodyStatementResultV2::Rejected(_) => {
            Err(AssetLaneCustodyProofHostErrorV2::StatementRejected)
        }
    }
}

pub fn encode_canonical_asset_lane_custody_receipt_v2(
    receipt: &Receipt,
) -> Result<Vec<u8>, AssetLaneCustodyReceiptDecodeErrorV2> {
    let canonical = serde_json::to_vec(receipt)
        .map_err(|_| AssetLaneCustodyReceiptDecodeErrorV2::InvalidEncoding)?;
    if !(1..=MAX_ASSET_LANE_CUSTODY_RECEIPT_BYTES_V2).contains(&canonical.len()) {
        return Err(AssetLaneCustodyReceiptDecodeErrorV2::InvalidBounds);
    }
    Ok(canonical)
}

/// Decodes one bounded, exact `serde_json` encoding of a RISC0 receipt.
pub fn decode_canonical_asset_lane_custody_receipt_v2(
    receipt_bytes: &[u8],
) -> Result<Receipt, AssetLaneCustodyReceiptDecodeErrorV2> {
    if !(1..=MAX_ASSET_LANE_CUSTODY_RECEIPT_BYTES_V2).contains(&receipt_bytes.len()) {
        return Err(AssetLaneCustodyReceiptDecodeErrorV2::InvalidBounds);
    }
    let receipt: Receipt = serde_json::from_slice(receipt_bytes)
        .map_err(|_| AssetLaneCustodyReceiptDecodeErrorV2::InvalidEncoding)?;
    let canonical = encode_canonical_asset_lane_custody_receipt_v2(&receipt)?;
    if canonical != receipt_bytes {
        return Err(AssetLaneCustodyReceiptDecodeErrorV2::NonCanonical);
    }
    Ok(receipt)
}

#[cfg(feature = "compiled-guest")]
fn require_compiled_custody_method_v2() -> Result<(), AssetLaneCustodyProofHostErrorV2> {
    if development_mode_requested_v2(std::env::var_os("RISC0_DEV_MODE").as_deref()) {
        return Err(AssetLaneCustodyProofHostErrorV2::DevelopmentModeConfigured);
    }
    if ZENODEX_ASSET_LANE_CUSTODY_GLOBAL_GUEST_ELF.is_empty()
        || ZENODEX_ASSET_LANE_CUSTODY_GLOBAL_GUEST_ID == [0; 8]
    {
        return Err(AssetLaneCustodyProofHostErrorV2::PlaceholderMethod);
    }
    let rebuilt = compute_image_id(ZENODEX_ASSET_LANE_CUSTODY_GLOBAL_GUEST_ELF)
        .map_err(|_| AssetLaneCustodyProofHostErrorV2::MethodBinding)?;
    if rebuilt.as_words() != ZENODEX_ASSET_LANE_CUSTODY_GLOBAL_GUEST_ID {
        return Err(AssetLaneCustodyProofHostErrorV2::MethodBinding);
    }
    Ok(())
}

#[cfg(any(feature = "compiled-guest", test))]
fn development_mode_requested_v2(value: Option<&std::ffi::OsStr>) -> bool {
    value.is_some_and(|value| {
        value
            .to_str()
            .is_none_or(|text| matches!(text.to_ascii_lowercase().as_str(), "1" | "true" | "yes"))
    })
}

/// Accepts only the SDK's default external IPC prover selection.
///
/// Unset, empty, or case-insensitive `ipc` resolve to the external `r0vm`
/// prover, which honours the executor session limit and the Succinct opts.
/// Every other explicit selector is refused. `actor` in particular is a host
/// compatibility hazard: the pinned SDK forwards `segment_limit_po2` but drops
/// `ExecutorEnv::session_limit` and ignores `ProverOpts`, so it would silently
/// bypass `MAX_ASSET_LANE_CUSTODY_GLOBAL_CYCLES_V2` and ignore the requested
/// proving options. The final receipt-kind check remains mandatory regardless
/// of backend. Non-Unicode values are refused rather than treated as unset.
/// The CLI environment must remain stable: the SDK rereads this selector.
/// Cycle enforcement relies on the pinned honest IPC server, not receipt metadata.
#[cfg(any(feature = "compiled-guest", test))]
fn require_external_ipc_prover_v2(
    value: Option<&std::ffi::OsStr>,
) -> Result<(), AssetLaneCustodyProofHostErrorV2> {
    let Some(value) = value else {
        return Ok(());
    };
    let text = value
        .to_str()
        .ok_or(AssetLaneCustodyProofHostErrorV2::ProverConfiguration)?;
    if text.is_empty() || text.eq_ignore_ascii_case("ipc") {
        Ok(())
    } else {
        Err(AssetLaneCustodyProofHostErrorV2::ProverConfiguration)
    }
}

#[cfg(any(feature = "compiled-guest", test))]
fn build_asset_lane_custody_executor_env_v2(
    frame: &[u8],
) -> Result<ExecutorEnv<'static>, AssetLaneCustodyProofHostErrorV2> {
    let length =
        u32::try_from(frame.len()).map_err(|_| AssetLaneCustodyProofHostErrorV2::InputBounds)?;
    let mut builder = ExecutorEnv::builder();
    builder.session_limit(Some(MAX_ASSET_LANE_CUSTODY_GLOBAL_CYCLES_V2));
    builder.write_slice(&length.to_le_bytes());
    builder.write_slice(frame);
    builder
        .build()
        .map_err(|_| AssetLaneCustodyProofHostErrorV2::Environment)
}

#[cfg(feature = "compiled-guest")]
fn verify_asset_lane_custody_succinct_receipt_v2(
    receipt: &Receipt,
    expected_statement: &[u8],
) -> Result<(), AssetLaneCustodyProofHostErrorV2> {
    if !matches!(&receipt.inner, InnerReceipt::Succinct(_)) {
        return Err(AssetLaneCustodyProofHostErrorV2::ReceiptKind);
    }
    if receipt.journal.bytes != expected_statement {
        return Err(AssetLaneCustodyProofHostErrorV2::ReceiptJournal);
    }
    require_compiled_custody_method_v2()?;
    receipt
        .verify(ZENODEX_ASSET_LANE_CUSTODY_GLOBAL_GUEST_ID)
        .map_err(|_| AssetLaneCustodyProofHostErrorV2::ReceiptVerification)
}

/// Produces and verifies one real Succinct receipt for the exact bounded frame.
#[cfg(feature = "compiled-guest")]
pub fn prove_asset_lane_custody_succinct_v2(
    frame: &[u8],
) -> Result<Receipt, AssetLaneCustodyProofHostErrorV2> {
    require_compiled_custody_method_v2()?;
    let statement = prepare_asset_lane_custody_statement_v2(frame)?;
    let env = build_asset_lane_custody_executor_env_v2(frame)?;
    require_external_ipc_prover_v2(std::env::var_os("RISC0_PROVER").as_deref())?;
    let prove_info = default_prover()
        .prove_with_opts(
            env,
            ZENODEX_ASSET_LANE_CUSTODY_GLOBAL_GUEST_ELF,
            &ProverOpts::succinct(),
        )
        .map_err(|_| AssetLaneCustodyProofHostErrorV2::Proving)?;
    verify_asset_lane_custody_succinct_receipt_v2(&prove_info.receipt, &statement)?;
    Ok(prove_info.receipt)
}

#[cfg(test)]
mod tests {
    use super::*;
    use risc0_zkvm::{FakeReceipt, InnerReceipt, ReceiptClaim};
    use serde_json::Value;
    use zenodex_global_settlement_abi_v2::{
        canonical_bytes_v2, AssetLaneCustodyStatementResultV2,
        ASSET_LANE_CUSTODY_GLOBAL_FRAME_MAGIC_V2,
    };

    const GOLDEN: &str =
        include_str!("../../../../tests/data/asset_lane_custody_statement_v2_golden.json");

    fn accepted_frame() -> (Vec<u8>, Vec<u8>) {
        let fixture: Value = serde_json::from_str(GOLDEN).unwrap();
        let case = fixture["cases"]
            .as_array()
            .unwrap()
            .iter()
            .find(|case| case["name"] == "transfer_with_claim")
            .unwrap();
        let route = match case["route"].as_str() {
            Some("TRANSFER") => 0,
            Some("MANAGED_LIFECYCLE") => 1,
            _ => panic!("golden fixture route must select a custody leaf"),
        };
        let mut frame = Vec::new();
        frame.extend_from_slice(ASSET_LANE_CUSTODY_GLOBAL_FRAME_MAGIC_V2);
        frame.push(route);
        for field in [
            "context",
            "pre_state",
            "command",
            "global_pre",
            "global_post",
        ] {
            let component = canonical_bytes_v2(&case[field]).unwrap();
            frame.extend_from_slice(&(component.len() as u32).to_le_bytes());
            frame.extend_from_slice(&component);
        }
        (frame, canonical_bytes_v2(&case["statement"]).unwrap())
    }

    fn outer_frame(frame: &[u8]) -> Vec<u8> {
        let mut input = u32::try_from(frame.len()).unwrap().to_le_bytes().to_vec();
        input.extend_from_slice(frame);
        input
    }

    fn fake_receipt_bytes() -> Vec<u8> {
        let receipt: Receipt = FakeReceipt::new(ReceiptClaim::ok([1; 8], b"journal".to_vec()))
            .try_into()
            .unwrap();
        serde_json::to_vec(&receipt).unwrap()
    }

    #[test]
    fn canonical_fake_receipt_round_trip_is_encoding_only() {
        let decoded =
            decode_canonical_asset_lane_custody_receipt_v2(&fake_receipt_bytes()).unwrap();

        assert_eq!(decoded.journal.bytes, b"journal");
        assert!(matches!(&decoded.inner, InnerReceipt::Fake(_)));
        assert!(decoded.verify([1; 8]).is_err());
    }

    #[test]
    fn bounded_guest_transport_and_native_statement_match_the_golden_vector() {
        let (frame, expected_statement) = accepted_frame();
        let input = outer_frame(&frame);
        let recovered = read_asset_lane_custody_guest_input_v2(&mut input.as_slice()).unwrap();
        assert_eq!(recovered, frame);
        assert_eq!(
            prepare_asset_lane_custody_statement_v2(&recovered),
            Ok(expected_statement.clone())
        );
        assert_eq!(
            prepare_asset_lane_custody_global_frame_v2(&recovered),
            Ok(AssetLaneCustodyStatementResultV2::Statement(
                expected_statement
            ))
        );
    }

    #[test]
    fn guest_transport_rejects_bad_outer_lengths_truncation_and_trailing_bytes() {
        for length in [
            0,
            MAX_ASSET_LANE_CUSTODY_GLOBAL_FRAME_BYTES_V2 as u32 + 1,
            u32::MAX,
        ] {
            assert_eq!(
                read_asset_lane_custody_guest_input_v2(&mut length.to_le_bytes().as_slice()),
                Err(AssetLaneCustodyProofHostErrorV2::InputBounds)
            );
        }
        let (frame, _) = accepted_frame();
        let input = outer_frame(&frame);
        let mut truncated = &input[..input.len() - 1];
        assert_eq!(
            read_asset_lane_custody_guest_input_v2(&mut truncated),
            Err(AssetLaneCustodyProofHostErrorV2::InputIo)
        );
        let mut trailing = input;
        trailing.push(0);
        assert_eq!(
            read_asset_lane_custody_guest_input_v2(&mut trailing.as_slice()),
            Err(AssetLaneCustodyProofHostErrorV2::InputTrailing)
        );
    }

    #[test]
    fn malformed_frame_cannot_reach_a_statement() {
        let malformed = vec![0; 1];
        assert_eq!(
            prepare_asset_lane_custody_statement_v2(&malformed),
            Err(AssetLaneCustodyProofHostErrorV2::StatementInvalid)
        );
    }

    #[test]
    fn truthy_development_mode_configuration_is_rejected() {
        assert!(!development_mode_requested_v2(None));
        assert!(!development_mode_requested_v2(Some(std::ffi::OsStr::new(
            "0"
        ))));
        for value in ["1", "TRUE", "yes"] {
            assert!(development_mode_requested_v2(Some(std::ffi::OsStr::new(
                value
            ))));
        }
    }

    #[test]
    fn default_and_explicit_ipc_prover_selections_are_accepted() {
        assert_eq!(require_external_ipc_prover_v2(None), Ok(()));
        for value in ["", "ipc", "IPC", "Ipc"] {
            assert_eq!(
                require_external_ipc_prover_v2(Some(std::ffi::OsStr::new(value))),
                Ok(()),
                "selector {value:?} must resolve to the external IPC prover"
            );
        }
    }

    #[test]
    fn non_ipc_prover_selectors_are_rejected_as_prover_configuration() {
        for value in [
            "actor", "ACTOR", "local", "bonsai", "unknown", " ipc", "ipc ", "ipc\n", " ",
        ] {
            assert_eq!(
                require_external_ipc_prover_v2(Some(std::ffi::OsStr::new(value))),
                Err(AssetLaneCustodyProofHostErrorV2::ProverConfiguration),
                "selector {value:?} must be refused"
            );
        }
    }

    #[cfg(unix)]
    #[test]
    fn non_unicode_prover_selector_is_rejected_as_prover_configuration() {
        use std::os::unix::ffi::OsStrExt;
        let value = std::ffi::OsStr::from_bytes(&[b'i', b'p', b'c', 0xff]);
        assert!(value.to_str().is_none());
        assert_eq!(
            require_external_ipc_prover_v2(Some(value)),
            Err(AssetLaneCustodyProofHostErrorV2::ProverConfiguration)
        );
    }

    #[test]
    fn client_executor_builds_the_bounded_custody_transport_environment() {
        let (frame, _) = accepted_frame();
        assert_eq!(MAX_ASSET_LANE_CUSTODY_GLOBAL_CYCLES_V2, 16 * 1024 * 1024);
        build_asset_lane_custody_executor_env_v2(&frame).unwrap();
    }

    #[test]
    fn malformed_truncated_and_appended_payloads_reject() {
        let canonical = fake_receipt_bytes();
        assert!(matches!(
            decode_canonical_asset_lane_custody_receipt_v2(b"malformed"),
            Err(AssetLaneCustodyReceiptDecodeErrorV2::InvalidEncoding)
        ));
        assert!(
            decode_canonical_asset_lane_custody_receipt_v2(&canonical[..canonical.len() - 1])
                .is_err()
        );
        let mut appended = canonical;
        appended.extend_from_slice(b"{}");
        assert!(decode_canonical_asset_lane_custody_receipt_v2(&appended).is_err());
    }

    #[test]
    fn equivalent_noncanonical_json_and_unknown_fields_reject() {
        let canonical = fake_receipt_bytes();
        let receipt: Receipt = serde_json::from_slice(&canonical).unwrap();
        let pretty = serde_json::to_vec_pretty(&receipt).unwrap();
        assert_ne!(pretty, canonical);
        assert!(matches!(
            decode_canonical_asset_lane_custody_receipt_v2(&pretty),
            Err(AssetLaneCustodyReceiptDecodeErrorV2::NonCanonical)
        ));

        let mut with_unknown: serde_json::Value = serde_json::from_slice(&canonical).unwrap();
        with_unknown
            .as_object_mut()
            .unwrap()
            .insert("verified".to_owned(), serde_json::Value::Bool(true));
        assert!(decode_canonical_asset_lane_custody_receipt_v2(
            &serde_json::to_vec(&with_unknown).unwrap()
        )
        .is_err());
    }

    #[test]
    fn receipt_size_bounds_reject_before_json_decoding() {
        assert!(matches!(
            decode_canonical_asset_lane_custody_receipt_v2(&[]),
            Err(AssetLaneCustodyReceiptDecodeErrorV2::InvalidBounds)
        ));
        let oversized = vec![b' '; MAX_ASSET_LANE_CUSTODY_RECEIPT_BYTES_V2 + 1];
        assert!(matches!(
            decode_canonical_asset_lane_custody_receipt_v2(&oversized),
            Err(AssetLaneCustodyReceiptDecodeErrorV2::InvalidBounds)
        ));

        let oversized_receipt: Receipt = FakeReceipt::new(ReceiptClaim::ok(
            [1; 8],
            vec![0; MAX_ASSET_LANE_CUSTODY_RECEIPT_BYTES_V2 + 1],
        ))
        .try_into()
        .unwrap();
        assert!(matches!(
            encode_canonical_asset_lane_custody_receipt_v2(&oversized_receipt),
            Err(AssetLaneCustodyReceiptDecodeErrorV2::InvalidBounds)
        ));
    }
}
