// Appended only to a verified temporary copy of the actual asset_transfer module.
#[cfg(kani)]
mod kani_asset_arithmetic_v1 {
    use super::{apply_delta, checked_negative_sum, AssetTransferRejectCodeV1};

    #[kani::proof]
    fn apply_delta_full_width_exact_outcome() {
        let current: u128 = kani::any();
        let delta: i128 = kani::any();
        let result = apply_delta(current, delta);
        if delta < 0 {
            // Two's-complement magnitude; independent of the implementation's unsigned_abs.
            let magnitude = (!(delta as u128)) + 1;
            if current < magnitude {
                assert_eq!(result, Err(AssetTransferRejectCodeV1::INSUFFICIENT_BALANCE));
            } else {
                let post = result.expect("funded debit must succeed");
                assert!(post <= current);
                assert_eq!(current - post, magnitude);
            }
        } else {
            let magnitude = delta as u128;
            if current > u128::MAX - magnitude {
                assert_eq!(result, Err(AssetTransferRejectCodeV1::BALANCE_OVERFLOW));
            } else {
                let post = result.expect("in-range credit must succeed");
                assert!(post >= current);
                assert_eq!(post - current, magnitude);
            }
        }
        assert_eq!(
            apply_delta(0, i128::MIN),
            Err(AssetTransferRejectCodeV1::INSUFFICIENT_BALANCE)
        );
        assert_eq!(apply_delta(1_u128 << 127, i128::MIN), Ok(0));
        assert_eq!(apply_delta(u128::MAX, i128::MIN), Ok((1_u128 << 127) - 1));
        assert_eq!(
            apply_delta(u128::MAX, 1),
            Err(AssetTransferRejectCodeV1::BALANCE_OVERFLOW)
        );
        assert_eq!(apply_delta(u128::MAX, 0), Ok(u128::MAX));
    }

    #[kani::proof]
    fn checked_negative_sum_full_width_exact_outcome() {
        let left: u128 = kani::any();
        let right: u128 = kani::any();
        let limit = 1_u128 << 127;
        let result = checked_negative_sum(left, right);
        if left <= limit && right <= limit - left {
            let negative = result.expect("representable debit must succeed");
            assert!(negative <= 0);
            // Inverse representation, including the unique minimum signed integer.
            let magnitude = if negative == i128::MIN {
                limit
            } else {
                (-negative) as u128
            };
            assert!(magnitude >= right);
            assert_eq!(magnitude - right, left);
        } else {
            assert_eq!(
                result,
                Err(AssetTransferRejectCodeV1::EFFECT_DELTA_OVERFLOW)
            );
        }
        assert_eq!(checked_negative_sum(0, 0), Ok(0));
        assert_eq!(checked_negative_sum(limit - 1, 1), Ok(i128::MIN));
        assert_eq!(
            checked_negative_sum(limit, 1),
            Err(AssetTransferRejectCodeV1::EFFECT_DELTA_OVERFLOW)
        );
        assert_eq!(
            checked_negative_sum(u128::MAX, 1),
            Err(AssetTransferRejectCodeV1::EFFECT_DELTA_OVERFLOW)
        );
    }
}
