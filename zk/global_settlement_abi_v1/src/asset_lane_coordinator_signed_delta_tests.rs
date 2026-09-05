//! Boundary oracle: signed movement depends on the difference of u128 holdings.
use super::*;
use crate::asset_lane_projection::ASSET_LANE_STATE_PROJECTION_SCHEMA_V1;
use crate::canonical::RootV1;
use crate::state::{AssetSupplyV1, EconomicAmountV1};

fn projection(amount: u128, custody: bool) -> AssetLaneStateProjectionV1 {
    let domain = if custody { "vault" } else { "accounts" };
    let rows = if amount == 0 {
        vec![]
    } else {
        vec![EconomicAmountV1 {
            owner: "alice".to_owned(),
            asset: "USD".to_owned(),
            custody_domain: domain.to_owned(),
            amount_atoms: amount,
        }]
    };
    let root = RootV1::parse(format!("0x{}", "01".repeat(32)), "test root", false).unwrap();
    let value = AssetLaneStateProjectionV1 {
        schema: ASSET_LANE_STATE_PROJECTION_SCHEMA_V1.to_owned(),
        asset_policy_registry_root: root.clone(),
        fee_policy_registry_root: root,
        balances: if custody { vec![] } else { rows.clone() },
        custody: if custody { rows } else { vec![] },
        supplies: vec![AssetSupplyV1 {
            asset: "USD".to_owned(),
            amount_atoms: amount,
        }],
    };
    value.validate().unwrap();
    value
}

#[test]
fn signed_movement_bounds_apply_to_difference_not_absolute_holdings() {
    let half = 1_u128 << 127;
    let max = u128::MAX;
    // Expected integers are independent boundary values, not a copy of the helper.
    let cases = [
        (0, 0, Some(0)),
        (half, half, Some(0)),
        (max, max, Some(0)),
        (half, half + 1, Some(1)),
        (half + 1, half, Some(-1)),
        (max - 1, max, Some(1)),
        (max, max - 1, Some(-1)),
        (0, half - 1, Some(i128::MAX)),
        (half, max, Some(i128::MAX)),
        (half, 0, Some(i128::MIN)),
        (max, half - 1, Some(i128::MIN)),
        (0, half, None),
        (half + 1, 0, None),
        (max, half - 2, None),
        (0, max, None),
        (max, 0, None),
    ];
    for custody in [false, true] {
        let key = (
            "USD".to_owned(),
            "alice".to_owned(),
            if custody { "vault" } else { "accounts" }.to_owned(),
        );
        for (pre, post, expected) in cases {
            let actual =
                expected_movement_deltas(&projection(pre, custody), &projection(post, custody));
            match expected {
                None => assert!(actual.is_none(), "pre={pre} post={post} custody={custody}"),
                Some(delta) => {
                    let expected = if delta == 0 {
                        BTreeMap::new()
                    } else {
                        BTreeMap::from([(key.clone(), delta)])
                    };
                    assert_eq!(
                        actual,
                        Some(expected),
                        "pre={pre} post={post} custody={custody}"
                    );
                }
            }
        }
    }
}

#[test]
fn failed_movement_derivations_never_establish_agreement() {
    // Benign unavailable-result sentinels; no transaction or invalid effect is built.
    assert!(!movement_derivations_match(None, None));
    assert!(!movement_derivations_match(None, Some(BTreeMap::new())));
    assert!(!movement_derivations_match(Some(BTreeMap::new()), None));
    assert!(movement_derivations_match(
        Some(BTreeMap::new()),
        Some(BTreeMap::new())
    ));
    let row = (
        ("USD".to_owned(), "alice".to_owned(), "accounts".to_owned()),
        1,
    );
    let movement = BTreeMap::from([row]);
    assert!(movement_derivations_match(
        Some(movement.clone()),
        Some(movement.clone())
    ));
    assert!(!movement_derivations_match(
        Some(movement),
        Some(BTreeMap::new())
    ));
}
