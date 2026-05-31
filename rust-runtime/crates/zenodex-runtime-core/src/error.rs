//! Typed rejection reasons for runtime transitions.
//!
//! Each variant has a stable machine `code()` that matches the Python
//! reference (`src/core/fee_router.py`) and the strings recorded in golden
//! traces. Structural rejections produced *before* a transition runs
//! (`malformed_tx`, `unknown_tx_kind`, `unknown_field`, `negative_amount`) live
//! in the CLI/trace layer. This enum is the semantic-transition
//! rejection surface only.

use std::fmt;

use thiserror::Error;

/// Sub-reason for [`RejectedReason::DomainConstraintViolated`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DomainConstraint {
    /// dex/perps: `buyburn_bps` is below the 5000 bps floor.
    BuyburnBelowFloor,
    /// borrow: `stakers_bps` is below the 5000 bps floor.
    StakersBelowFloor,
    /// redemption: `buyburn_bps` must be exactly 0.
    RedemptionBuyburnMustBeZero,
    /// redemption: `hosts_bps` must be exactly 0.
    RedemptionHostsMustBeZero,
    /// redemption: `reserve_bps` is below the 2000 bps floor.
    RedemptionReserveBelowFloor,
}

impl DomainConstraint {
    /// Stable detail code (matches the Python `DETAIL_*` constants).
    pub fn detail(self) -> &'static str {
        match self {
            DomainConstraint::BuyburnBelowFloor => "buyburn_below_floor",
            DomainConstraint::StakersBelowFloor => "stakers_below_floor",
            DomainConstraint::RedemptionBuyburnMustBeZero => "redemption_buyburn_must_be_zero",
            DomainConstraint::RedemptionHostsMustBeZero => "redemption_hosts_must_be_zero",
            DomainConstraint::RedemptionReserveBelowFloor => "redemption_reserve_below_floor",
        }
    }
}

impl fmt::Display for DomainConstraint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.detail())
    }
}

/// Why a transition rejected an input. Never silently dropped (Hard Rule #10).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Error)]
pub enum RejectedReason {
    #[error("amount exceeds MAX_FEE_AMOUNT")]
    AmountTooLarge,
    #[error("a split component is outside [0, 10000]")]
    SplitComponentOutOfRange,
    #[error("split bps do not sum to 10000")]
    SplitDoesNotSumTo10000,
    #[error("unknown fee domain")]
    UnknownDomain,
    #[error("domain constraint violated: {0}")]
    DomainConstraintViolated(DomainConstraint),
    #[error("arithmetic overflow")]
    ArithmeticOverflow,
    #[error("fee route conservation violated")]
    ConservationViolation,
}

impl RejectedReason {
    /// Stable top-level machine code.
    pub fn code(self) -> &'static str {
        match self {
            RejectedReason::AmountTooLarge => "amount_too_large",
            RejectedReason::SplitComponentOutOfRange => "split_component_out_of_range",
            RejectedReason::SplitDoesNotSumTo10000 => "split_does_not_sum_to_10000",
            RejectedReason::UnknownDomain => "unknown_domain",
            RejectedReason::DomainConstraintViolated(_) => "domain_constraint_violated",
            RejectedReason::ArithmeticOverflow => "arithmetic_overflow",
            RejectedReason::ConservationViolation => "conservation_violation",
        }
    }

    /// Canonical reason string used in golden traces: `code` or `code:detail`.
    pub fn reason_str(self) -> String {
        match self {
            RejectedReason::DomainConstraintViolated(d) => {
                format!("domain_constraint_violated:{}", d.detail())
            }
            other => other.code().to_string(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn codes_are_stable() {
        assert_eq!(RejectedReason::AmountTooLarge.code(), "amount_too_large");
        assert_eq!(RejectedReason::UnknownDomain.reason_str(), "unknown_domain");
        assert_eq!(
            RejectedReason::ConservationViolation.reason_str(),
            "conservation_violation"
        );
        assert_eq!(
            RejectedReason::DomainConstraintViolated(DomainConstraint::RedemptionBuyburnMustBeZero)
                .reason_str(),
            "domain_constraint_violated:redemption_buyburn_must_be_zero"
        );
    }
}
