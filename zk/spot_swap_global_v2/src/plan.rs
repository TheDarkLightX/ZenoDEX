//! Pure single-pool CPMM plan for the owned swap intent.
//!
//! Mirrors `src/core/spot_swap_plan_v2.py::plan_spot_swap_v2`. Context values
//! are independently supplied data; the plan is ordinary data with no global
//! or publication authority. Rejection precedence is the Python order:
//! UNSUPPORTED_FIELDS, SUBJECT_MISMATCH, EXPIRED, INVALID_NONCE, POOL_MISMATCH,
//! ASSET_MISMATCH, POOL_INACTIVE, UNSUPPORTED_CURVE, QUOTE_REJECTED,
//! SLIPPAGE_LIMIT, INSUFFICIENT_BALANCE, BALANCE_OVERFLOW.

use zenodex_global_settlement_abi_v2::{AbiErrorV2, AbiResultV2};

use crate::intent::{
    SpotSwapIntentV2, SpotSwapKindV2, SwapAmountBoundV2, SwapIntentFieldProfileV2,
};
use crate::quote::{
    quote_cpmm_swap_exact_in_v2, quote_cpmm_swap_exact_out_v2, SpotSwapQuoteV2,
    DEX_POOL_RESERVE_MAX_V2, DEX_SWAP_AMOUNT_MAX_V2,
};
use crate::state::SpotPoolSnapshotV2;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[allow(non_camel_case_types)]
pub enum SpotSwapRejectCodeV2 {
    SUBJECT_MISMATCH,
    EXPIRED,
    UNSUPPORTED_FIELDS,
    INVALID_NONCE,
    POOL_MISMATCH,
    ASSET_MISMATCH,
    POOL_INACTIVE,
    UNSUPPORTED_CURVE,
    QUOTE_REJECTED,
    SLIPPAGE_LIMIT,
    INSUFFICIENT_BALANCE,
    BALANCE_OVERFLOW,
}

impl SpotSwapRejectCodeV2 {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::SUBJECT_MISMATCH => "SUBJECT_MISMATCH",
            Self::EXPIRED => "EXPIRED",
            Self::UNSUPPORTED_FIELDS => "UNSUPPORTED_FIELDS",
            Self::INVALID_NONCE => "INVALID_NONCE",
            Self::POOL_MISMATCH => "POOL_MISMATCH",
            Self::ASSET_MISMATCH => "ASSET_MISMATCH",
            Self::POOL_INACTIVE => "POOL_INACTIVE",
            Self::UNSUPPORTED_CURVE => "UNSUPPORTED_CURVE",
            Self::QUOTE_REJECTED => "QUOTE_REJECTED",
            Self::SLIPPAGE_LIMIT => "SLIPPAGE_LIMIT",
            Self::INSUFFICIENT_BALANCE => "INSUFFICIENT_BALANCE",
            Self::BALANCE_OVERFLOW => "BALANCE_OVERFLOW",
        }
    }
}

pub const ALL_SPOT_SWAP_REJECT_CODES_V2: [SpotSwapRejectCodeV2; 12] = [
    SpotSwapRejectCodeV2::SUBJECT_MISMATCH,
    SpotSwapRejectCodeV2::EXPIRED,
    SpotSwapRejectCodeV2::UNSUPPORTED_FIELDS,
    SpotSwapRejectCodeV2::INVALID_NONCE,
    SpotSwapRejectCodeV2::POOL_MISMATCH,
    SpotSwapRejectCodeV2::ASSET_MISMATCH,
    SpotSwapRejectCodeV2::POOL_INACTIVE,
    SpotSwapRejectCodeV2::UNSUPPORTED_CURVE,
    SpotSwapRejectCodeV2::QUOTE_REJECTED,
    SpotSwapRejectCodeV2::SLIPPAGE_LIMIT,
    SpotSwapRejectCodeV2::INSUFFICIENT_BALANCE,
    SpotSwapRejectCodeV2::BALANCE_OVERFLOW,
];

/// Explicit acquired data; subject and timestamp are not authenticated here.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SpotSwapContextV2 {
    pub subject_id: String,
    pub block_timestamp: u64,
    pub sender_input_atoms: u128,
    pub recipient_output_atoms: u128,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SpotSwapDirectionV2 {
    Asset0ToAsset1,
    Asset1ToAsset0,
}

/// One owned pool/account update, without global or publication authority.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SpotSwapPlanV2 {
    pre_pool: SpotPoolSnapshotV2,
    post_pool: SpotPoolSnapshotV2,
    direction: SpotSwapDirectionV2,
    nonce: u32,
    amount_in_atoms: u128,
    amount_out_atoms: u128,
    fee_atoms: u128,
    post_sender_input_atoms: u128,
    post_recipient_output_atoms: u128,
}

impl SpotSwapPlanV2 {
    pub fn pre_pool(&self) -> &SpotPoolSnapshotV2 {
        &self.pre_pool
    }

    pub fn post_pool(&self) -> &SpotPoolSnapshotV2 {
        &self.post_pool
    }

    pub fn direction(&self) -> SpotSwapDirectionV2 {
        self.direction
    }

    pub fn nonce(&self) -> u32 {
        self.nonce
    }

    pub fn amount_in_atoms(&self) -> u128 {
        self.amount_in_atoms
    }

    pub fn amount_out_atoms(&self) -> u128 {
        self.amount_out_atoms
    }

    pub fn fee_atoms(&self) -> u128 {
        self.fee_atoms
    }

    pub fn post_sender_input_atoms(&self) -> u128 {
        self.post_sender_input_atoms
    }

    pub fn post_recipient_output_atoms(&self) -> u128 {
        self.post_recipient_output_atoms
    }

    /// Pool asset0 then asset1 physical deltas.
    pub fn pool_deltas(&self) -> (i128, i128) {
        let delta = |before: u64, after: u64| i128::from(after) - i128::from(before);
        (
            delta(self.pre_pool.reserve0, self.post_pool.reserve0),
            delta(self.pre_pool.reserve1, self.post_pool.reserve1),
        )
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
#[must_use]
pub enum SpotSwapPlanResultV2 {
    Planned(Box<SpotSwapPlanV2>),
    Rejected(SpotSwapRejectCodeV2),
}

fn intent_reject(
    context: &SpotSwapContextV2,
    pool: &SpotPoolSnapshotV2,
    intent: &SpotSwapIntentV2,
) -> Result<(u32, SpotSwapDirectionV2), SpotSwapRejectCodeV2> {
    if context.subject_id != intent.sender_pubkey() {
        return Err(SpotSwapRejectCodeV2::SUBJECT_MISMATCH);
    }
    if intent.deadline() < context.block_timestamp {
        return Err(SpotSwapRejectCodeV2::EXPIRED);
    }
    let nonce = intent.nonce().ok_or(SpotSwapRejectCodeV2::INVALID_NONCE)?;
    if intent.pool_id() != pool.pool_id {
        return Err(SpotSwapRejectCodeV2::POOL_MISMATCH);
    }
    let direction = if intent.asset_in() == pool.asset0 && intent.asset_out() == pool.asset1 {
        SpotSwapDirectionV2::Asset0ToAsset1
    } else if intent.asset_in() == pool.asset1 && intent.asset_out() == pool.asset0 {
        SpotSwapDirectionV2::Asset1ToAsset0
    } else {
        return Err(SpotSwapRejectCodeV2::ASSET_MISMATCH);
    };
    Ok((nonce, direction))
}

fn quote_for(
    intent: &SpotSwapIntentV2,
    reserve_in: u128,
    reserve_out: u128,
    fee_bps: u128,
) -> Option<SpotSwapQuoteV2> {
    match intent.kind() {
        SpotSwapKindV2::SWAP_EXACT_IN => {
            quote_cpmm_swap_exact_in_v2(reserve_in, reserve_out, intent.amount_in()?, fee_bps).ok()
        }
        SpotSwapKindV2::SWAP_EXACT_OUT => {
            quote_cpmm_swap_exact_out_v2(reserve_in, reserve_out, intent.amount_out()?, fee_bps)
                .ok()
        }
    }
}

/// `_quote_fits`: reconcile physical deltas and the next input's resource domain.
fn quote_fits(quote: &SpotSwapQuoteV2) -> bool {
    let in_domain = |value: u128, maximum: u128| value > 0 && value <= maximum;
    let product_after = quote.reserve_in_after.checked_mul(quote.reserve_out_after);
    let product_before = quote
        .reserve_in_before
        .checked_mul(quote.reserve_out_before);
    let product_holds = match (product_after, product_before) {
        (Some(after), Some(before)) => after >= before,
        _ => false,
    };
    in_domain(quote.amount_in, DEX_SWAP_AMOUNT_MAX_V2)
        && in_domain(quote.amount_out, DEX_SWAP_AMOUNT_MAX_V2)
        && quote.fee_paid < quote.amount_in
        && quote.reserve_in_before.checked_add(quote.amount_in) == Some(quote.reserve_in_after)
        && quote.reserve_out_before.checked_sub(quote.amount_out) == Some(quote.reserve_out_after)
        && in_domain(quote.reserve_in_after, DEX_POOL_RESERVE_MAX_V2)
        && in_domain(quote.reserve_out_after, DEX_POOL_RESERVE_MAX_V2)
        && product_holds
}

fn slippage_exceeded(intent: &SpotSwapIntentV2, quote: &SpotSwapQuoteV2) -> bool {
    match intent.kind() {
        SpotSwapKindV2::SWAP_EXACT_IN => match intent.min_amount_out() {
            SwapAmountBoundV2::Atoms(minimum) => quote.amount_out < minimum,
            SwapAmountBoundV2::BeyondU128 => true,
        },
        SpotSwapKindV2::SWAP_EXACT_OUT => match intent.max_amount_in() {
            SwapAmountBoundV2::Atoms(maximum) => quote.amount_in > maximum,
            SwapAmountBoundV2::BeyondU128 => false,
        },
    }
}

fn narrow_reserve(value: u128) -> AbiResultV2<u64> {
    u64::try_from(value).map_err(|_| AbiErrorV2::InvalidBounds("Spot post reserve"))
}

/// Validate the typed inputs, then reject without effects or return a plan.
///
/// Structural failures are typed errors. Economic rejections return a closed
/// reason with no successor. The supplied block timestamp retains the existing
/// deadline semantics (`deadline < block_timestamp` expires).
pub fn plan_spot_swap_v2(
    context: &SpotSwapContextV2,
    pool: &SpotPoolSnapshotV2,
    intent: &SpotSwapIntentV2,
) -> AbiResultV2<SpotSwapPlanResultV2> {
    if context.subject_id.is_empty() || context.subject_id.chars().count() > 512 {
        return Err(AbiErrorV2::InvalidBounds("Spot context subject"));
    }
    pool.validate()?;
    intent.validate()?;
    if intent.field_profile()? == SwapIntentFieldProfileV2::Unsupported {
        return Ok(SpotSwapPlanResultV2::Rejected(
            SpotSwapRejectCodeV2::UNSUPPORTED_FIELDS,
        ));
    }
    let (nonce, direction) = match intent_reject(context, pool, intent) {
        Ok(value) => value,
        Err(code) => return Ok(SpotSwapPlanResultV2::Rejected(code)),
    };
    if !pool.is_active() {
        return Ok(SpotSwapPlanResultV2::Rejected(
            SpotSwapRejectCodeV2::POOL_INACTIVE,
        ));
    }
    if !pool.is_cpmm() {
        return Ok(SpotSwapPlanResultV2::Rejected(
            SpotSwapRejectCodeV2::UNSUPPORTED_CURVE,
        ));
    }
    let (reserve_in, reserve_out) = match direction {
        SpotSwapDirectionV2::Asset0ToAsset1 => (pool.reserve0, pool.reserve1),
        SpotSwapDirectionV2::Asset1ToAsset0 => (pool.reserve1, pool.reserve0),
    };
    let quote = match quote_for(
        intent,
        u128::from(reserve_in),
        u128::from(reserve_out),
        u128::from(pool.fee_bps),
    ) {
        Some(quote) if quote_fits(&quote) => quote,
        _ => {
            return Ok(SpotSwapPlanResultV2::Rejected(
                SpotSwapRejectCodeV2::QUOTE_REJECTED,
            ))
        }
    };
    if slippage_exceeded(intent, &quote) {
        return Ok(SpotSwapPlanResultV2::Rejected(
            SpotSwapRejectCodeV2::SLIPPAGE_LIMIT,
        ));
    }
    if context.sender_input_atoms < quote.amount_in {
        return Ok(SpotSwapPlanResultV2::Rejected(
            SpotSwapRejectCodeV2::INSUFFICIENT_BALANCE,
        ));
    }
    let Some(post_recipient_output_atoms) =
        context.recipient_output_atoms.checked_add(quote.amount_out)
    else {
        return Ok(SpotSwapPlanResultV2::Rejected(
            SpotSwapRejectCodeV2::BALANCE_OVERFLOW,
        ));
    };
    let post_sender_input_atoms = context
        .sender_input_atoms
        .checked_sub(quote.amount_in)
        .ok_or(AbiErrorV2::InvalidBounds("Spot sender balance"))?;
    let (reserve0_after, reserve1_after) = match direction {
        SpotSwapDirectionV2::Asset0ToAsset1 => (quote.reserve_in_after, quote.reserve_out_after),
        SpotSwapDirectionV2::Asset1ToAsset0 => (quote.reserve_out_after, quote.reserve_in_after),
    };
    let post_pool = pool.with_reserves(
        narrow_reserve(reserve0_after)?,
        narrow_reserve(reserve1_after)?,
    );
    Ok(SpotSwapPlanResultV2::Planned(Box::new(SpotSwapPlanV2 {
        pre_pool: pool.clone(),
        post_pool,
        direction,
        nonce,
        amount_in_atoms: quote.amount_in,
        amount_out_atoms: quote.amount_out,
        fee_atoms: quote.fee_paid,
        post_sender_input_atoms,
        post_recipient_output_atoms,
    })))
}
