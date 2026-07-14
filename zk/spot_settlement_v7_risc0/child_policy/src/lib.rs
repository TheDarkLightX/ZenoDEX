#![no_std]

//! Governed child identity for the Spot settlement V7 recursive guest.
//!
//! The all-zero value is an intentional fail-closed placeholder. It must be
//! replaced only after the final V6 source closure and image identity have
//! been materialized and independently checked. No guest or host verifier may
//! silently accept the placeholder.

/// Intentionally unavailable until final V6 C1 identity materialization.
pub const FINAL_SOURCE_OPENED_SPOT_SETTLEMENT_V6_IMAGE_ID_V1: [u32; 8] = [0; 8];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SpotSettlementV7ChildPolicyErrorV1 {
    FinalV6ImageIdUnmaterialized,
}

impl SpotSettlementV7ChildPolicyErrorV1 {
    pub const fn code(self) -> &'static str {
        match self {
            Self::FinalV6ImageIdUnmaterialized => "final_v6_image_id_unmaterialized",
        }
    }
}

/// Returns the final V6 child image only after the placeholder is replaced.
pub fn final_source_opened_spot_settlement_v6_image_id_v1(
) -> Result<[u32; 8], SpotSettlementV7ChildPolicyErrorV1> {
    if FINAL_SOURCE_OPENED_SPOT_SETTLEMENT_V6_IMAGE_ID_V1
        .iter()
        .all(|word| *word == 0)
    {
        return Err(SpotSettlementV7ChildPolicyErrorV1::FinalV6ImageIdUnmaterialized);
    }
    Ok(FINAL_SOURCE_OPENED_SPOT_SETTLEMENT_V6_IMAGE_ID_V1)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn policy_result_matches_materialization_state() {
        // This checks local API semantics; it is not post-pin release authority.
        let configured = FINAL_SOURCE_OPENED_SPOT_SETTLEMENT_V6_IMAGE_ID_V1;
        let result = final_source_opened_spot_settlement_v6_image_id_v1();
        if configured.iter().all(|word| *word == 0) {
            assert_eq!(
                result,
                Err(SpotSettlementV7ChildPolicyErrorV1::FinalV6ImageIdUnmaterialized)
            );
        } else {
            assert_eq!(result, Ok(configured));
        }
    }
}
