use core::fmt;

use risc0_zkvm::{default_prover, ExecutorEnv, InnerReceipt, ProverOpts, Receipt};
use zenodex_global_economic_epoch_risc0_methods::{
    ZENODEX_ECONOMIC_EPOCH_GUEST_ELF, ZENODEX_ECONOMIC_EPOCH_GUEST_ID,
};
use zenodex_global_economic_epoch_risc0_shared::{
    image_id_root_v1, preflight_aggregated_economic_epoch_guest_input_v1,
    preflight_command_aggregation_guest_input_v1, preflight_economic_epoch_guest_input_v1,
    AggregatedEconomicEpochGuestInputV1, CommandAggregationGuestInputV1, EconomicEpochGuestErrorV1,
    EconomicEpochGuestInputV1, GlobalEconomicRecursiveGuestInputV1, RootV1,
    MAX_EPOCH_GUEST_INPUT_BYTES_V1,
};

#[derive(Debug)]
pub enum EconomicEpochHostErrorV1 {
    Guest(EconomicEpochGuestErrorV1),
    Encoding,
    InputTooLarge,
    ReceiptCount,
    ReceiptKind,
    ReceiptJournal,
    ReceiptVerification,
    PlaceholderMethod,
    MethodBinding,
    Environment,
    Proving,
    RootReceiptKind,
    RootJournal,
    RootVerification,
}

impl fmt::Display for EconomicEpochHostErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "global economic epoch host rejected: {self:?}")
    }
}

impl std::error::Error for EconomicEpochHostErrorV1 {}

impl From<EconomicEpochGuestErrorV1> for EconomicEpochHostErrorV1 {
    fn from(value: EconomicEpochGuestErrorV1) -> Self {
        Self::Guest(value)
    }
}

struct HostAssumptionClaimV1 {
    image_id: [u32; 8],
    journal_bytes: Vec<u8>,
}

pub fn build_economic_epoch_executor_env_v1(
    input: &EconomicEpochGuestInputV1,
    receipts: Vec<Receipt>,
) -> Result<ExecutorEnv<'static>, EconomicEpochHostErrorV1> {
    let prepared = preflight_economic_epoch_guest_input_v1(input)?;
    let claims = prepared
        .route_claims
        .into_iter()
        .map(|claim| HostAssumptionClaimV1 {
            image_id: claim.image_id,
            journal_bytes: claim.journal_bytes,
        })
        .collect();
    build_recursive_executor_env_v1(
        GlobalEconomicRecursiveGuestInputV1::DirectEpoch(input.clone()),
        claims,
        receipts,
    )
}

pub fn build_command_aggregation_executor_env_v1(
    input: &CommandAggregationGuestInputV1,
    receipts: Vec<Receipt>,
) -> Result<ExecutorEnv<'static>, EconomicEpochHostErrorV1> {
    let prepared = preflight_command_aggregation_guest_input_v1(input)?;
    let claims = prepared
        .route_claims
        .into_iter()
        .map(|claim| HostAssumptionClaimV1 {
            image_id: claim.image_id,
            journal_bytes: claim.journal_bytes,
        })
        .collect();
    build_recursive_executor_env_v1(
        GlobalEconomicRecursiveGuestInputV1::CommandAggregation(input.clone()),
        claims,
        receipts,
    )
}

pub fn build_aggregated_economic_epoch_executor_env_v1(
    input: &AggregatedEconomicEpochGuestInputV1,
    receipts: Vec<Receipt>,
) -> Result<ExecutorEnv<'static>, EconomicEpochHostErrorV1> {
    let prepared = preflight_aggregated_economic_epoch_guest_input_v1(input)?;
    let claims = prepared
        .command_aggregation_claims
        .into_iter()
        .map(|claim| HostAssumptionClaimV1 {
            image_id: claim.image_id,
            journal_bytes: claim.journal_bytes,
        })
        .collect();
    build_recursive_executor_env_v1(
        GlobalEconomicRecursiveGuestInputV1::AggregatedEpoch(input.clone()),
        claims,
        receipts,
    )
}

fn build_recursive_executor_env_v1(
    input: GlobalEconomicRecursiveGuestInputV1,
    claims: Vec<HostAssumptionClaimV1>,
    receipts: Vec<Receipt>,
) -> Result<ExecutorEnv<'static>, EconomicEpochHostErrorV1> {
    if receipts.len() != claims.len() {
        return Err(EconomicEpochHostErrorV1::ReceiptCount);
    }
    let input_bytes =
        postcard::to_allocvec(&input).map_err(|_| EconomicEpochHostErrorV1::Encoding)?;
    let input_len =
        u32::try_from(input_bytes.len()).map_err(|_| EconomicEpochHostErrorV1::InputTooLarge)?;
    if input_len == 0 || input_len > MAX_EPOCH_GUEST_INPUT_BYTES_V1 {
        return Err(EconomicEpochHostErrorV1::InputTooLarge);
    }

    let mut builder = ExecutorEnv::builder();
    builder.write_slice(&[input_len]);
    builder.write_slice(&input_bytes);
    for (receipt, claim) in receipts.into_iter().zip(claims) {
        if !matches!(&receipt.inner, InnerReceipt::Succinct(_)) {
            return Err(EconomicEpochHostErrorV1::ReceiptKind);
        }
        if receipt.journal.bytes != claim.journal_bytes {
            return Err(EconomicEpochHostErrorV1::ReceiptJournal);
        }
        receipt
            .verify(claim.image_id)
            .map_err(|_| EconomicEpochHostErrorV1::ReceiptVerification)?;
        builder.add_assumption(receipt);
    }
    builder
        .build()
        .map_err(|_| EconomicEpochHostErrorV1::Environment)
}

pub fn prove_economic_epoch_succinct_v1(
    input: &EconomicEpochGuestInputV1,
    receipts: Vec<Receipt>,
) -> Result<Receipt, EconomicEpochHostErrorV1> {
    let prepared = preflight_economic_epoch_guest_input_v1(input)?;
    require_bound_root_method_v1(&prepared.root_image_id)?;
    let env = build_economic_epoch_executor_env_v1(input, receipts)?;
    prove_recursive_statement_succinct_v1(prepared.certificate_journal_bytes, env)
}

pub fn prove_command_aggregation_succinct_v1(
    input: &CommandAggregationGuestInputV1,
    receipts: Vec<Receipt>,
) -> Result<Receipt, EconomicEpochHostErrorV1> {
    require_real_method_v1()?;
    let prepared = preflight_command_aggregation_guest_input_v1(input)?;
    let env = build_command_aggregation_executor_env_v1(input, receipts)?;
    prove_recursive_statement_succinct_v1(prepared.aggregation_journal_bytes, env)
}

pub fn prove_aggregated_economic_epoch_succinct_v1(
    input: &AggregatedEconomicEpochGuestInputV1,
    receipts: Vec<Receipt>,
) -> Result<Receipt, EconomicEpochHostErrorV1> {
    let prepared = preflight_aggregated_economic_epoch_guest_input_v1(input)?;
    require_bound_root_method_v1(&prepared.root_image_id)?;
    let env = build_aggregated_economic_epoch_executor_env_v1(input, receipts)?;
    prove_recursive_statement_succinct_v1(prepared.certificate_journal_bytes, env)
}

fn prove_recursive_statement_succinct_v1(
    expected_journal: Vec<u8>,
    env: ExecutorEnv<'static>,
) -> Result<Receipt, EconomicEpochHostErrorV1> {
    let prove_info = default_prover()
        .prove_with_opts(
            env,
            ZENODEX_ECONOMIC_EPOCH_GUEST_ELF,
            &ProverOpts::succinct(),
        )
        .map_err(|_| EconomicEpochHostErrorV1::Proving)?;
    let receipt = prove_info.receipt;
    if !matches!(&receipt.inner, InnerReceipt::Succinct(_)) {
        return Err(EconomicEpochHostErrorV1::RootReceiptKind);
    }
    if receipt.journal.bytes != expected_journal {
        return Err(EconomicEpochHostErrorV1::RootJournal);
    }
    receipt
        .verify(ZENODEX_ECONOMIC_EPOCH_GUEST_ID)
        .map_err(|_| EconomicEpochHostErrorV1::RootVerification)?;
    Ok(receipt)
}

fn require_real_method_v1() -> Result<(), EconomicEpochHostErrorV1> {
    if ZENODEX_ECONOMIC_EPOCH_GUEST_ELF.is_empty() || ZENODEX_ECONOMIC_EPOCH_GUEST_ID == [0; 8] {
        Err(EconomicEpochHostErrorV1::PlaceholderMethod)
    } else {
        Ok(())
    }
}

fn require_bound_root_method_v1(root_image_id: &RootV1) -> Result<(), EconomicEpochHostErrorV1> {
    require_real_method_v1()?;
    let expected = image_id_root_v1(ZENODEX_ECONOMIC_EPOCH_GUEST_ID)
        .map_err(|_| EconomicEpochHostErrorV1::PlaceholderMethod)?;
    if &expected != root_image_id {
        return Err(EconomicEpochHostErrorV1::MethodBinding);
    }
    Ok(())
}
