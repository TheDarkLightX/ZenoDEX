use crate::canonical::{AbiErrorV2, AbiResultV2};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct SignedAtomsDeltaV2 {
    negative: bool,
    magnitude: u128,
}

impl SignedAtomsDeltaV2 {
    pub(crate) fn between(post_atoms: u128, pre_atoms: u128) -> Self {
        if post_atoms >= pre_atoms {
            Self {
                negative: false,
                magnitude: post_atoms - pre_atoms,
            }
        } else {
            Self {
                negative: true,
                magnitude: pre_atoms - post_atoms,
            }
        }
    }

    pub(crate) fn is_zero(self) -> bool {
        self.magnitude == 0
    }
}

pub(crate) fn checked_signed_delta_v2(post_atoms: u128, pre_atoms: u128) -> AbiResultV2<i128> {
    if post_atoms >= pre_atoms {
        i128::try_from(post_atoms - pre_atoms)
            .map_err(|_| AbiErrorV2::InvalidBounds("global refinement signed state delta"))
    } else {
        negative_i128_from_magnitude_v2(pre_atoms - post_atoms).ok_or(AbiErrorV2::InvalidBounds(
            "global refinement signed state delta",
        ))
    }
}

fn negative_i128_from_magnitude_v2(magnitude: u128) -> Option<i128> {
    if magnitude == (1_u128 << 127) {
        Some(i128::MIN)
    } else {
        i128::try_from(magnitude).ok().map(|value| -value)
    }
}

fn checked_add_positive_magnitude_v2(current: i128, magnitude: u128) -> Option<i128> {
    if current >= 0 {
        let current_atoms = u128::try_from(current).ok()?;
        i128::try_from(current_atoms.checked_add(magnitude)?).ok()
    } else {
        let negative_magnitude = current.unsigned_abs();
        if magnitude >= negative_magnitude {
            i128::try_from(magnitude - negative_magnitude).ok()
        } else {
            negative_i128_from_magnitude_v2(negative_magnitude - magnitude)
        }
    }
}

fn checked_subtract_positive_magnitude_v2(current: i128, magnitude: u128) -> Option<i128> {
    if current <= 0 {
        negative_i128_from_magnitude_v2(current.unsigned_abs().checked_add(magnitude)?)
    } else {
        let current_atoms = u128::try_from(current).ok()?;
        if current_atoms >= magnitude {
            i128::try_from(current_atoms - magnitude).ok()
        } else {
            negative_i128_from_magnitude_v2(magnitude - current_atoms)
        }
    }
}

pub(crate) fn checked_add_atoms_difference_v2(
    current: i128,
    post_atoms: u128,
    pre_atoms: u128,
    overflow_label: &'static str,
) -> AbiResultV2<i128> {
    let value = if post_atoms >= pre_atoms {
        checked_add_positive_magnitude_v2(current, post_atoms - pre_atoms)
    } else {
        checked_subtract_positive_magnitude_v2(current, pre_atoms - post_atoms)
    };
    value.ok_or(AbiErrorV2::InvalidBounds(overflow_label))
}

#[cfg(test)]
mod tests {
    use super::checked_add_atoms_difference_v2;

    const LABEL: &str = "test aggregate delta overflow";

    #[test]
    fn aggregate_accepts_full_u128_terms_only_when_the_running_total_fits() {
        assert_eq!(
            checked_add_atoms_difference_v2(i128::MIN, u128::MAX, 0, LABEL),
            Ok(i128::MAX)
        );
        assert_eq!(
            checked_add_atoms_difference_v2(i128::MAX, 0, u128::MAX, LABEL),
            Ok(i128::MIN)
        );
        assert!(checked_add_atoms_difference_v2(0, u128::MAX, 0, LABEL).is_err());
        assert!(checked_add_atoms_difference_v2(0, 0, u128::MAX, LABEL).is_err());
    }
}
