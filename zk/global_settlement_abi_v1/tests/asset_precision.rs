use zenodex_global_settlement_abi_v1::{
    admit_burn_v1, admit_tau_amount_v1, exact_rescale_atoms_v1, quote_floor_bps_burn_v1,
    AssetPrecisionPolicyV1, AssetPrecisionRegistryV1, AssetPrecisionRejectCodeV1,
    BurnDispositionV1, ScaleChangePolicyV1, TauAmountWidthV1, CURRENT_TAU_TESTNET_DECIMALS_V1,
    GLOBAL_SETTLEMENT_ABI_V1, MAX_ASSET_DECIMALS_V1, MAX_ASSET_PRECISION_POLICIES_V1,
    MAX_SETTLEMENT_DELTA_ATOMS_V1, TARGET_COMMON_DECIMALS_V1,
};

fn policy(asset: &str, source_decimals: u8, width: TauAmountWidthV1) -> AssetPrecisionPolicyV1 {
    AssetPrecisionPolicyV1 {
        asset: asset.to_owned(),
        source_decimals,
        ledger_decimals: TARGET_COMMON_DECIMALS_V1,
        tau_amount_width: Some(width),
        max_supply_atoms: 2_000_000_000 * 100_000_000,
        max_ledger_transfer_atoms: 1_000_000_000 * 100_000_000,
        scale_change_policy: ScaleChangePolicyV1::NewAssetOrProvedMigrationOnly,
    }
}

#[test]
fn given_tau_testnet_atoms_when_upscaled_then_conversion_is_exact() {
    // Arrange
    let tau_atoms = 16_777_215_u128;

    // Act
    let ledger_atoms = exact_rescale_atoms_v1(
        tau_atoms,
        CURRENT_TAU_TESTNET_DECIMALS_V1,
        TARGET_COMMON_DECIMALS_V1,
    )
    .expect("four-decimal Tau test atoms must upscale exactly");

    // Assert
    assert_eq!(ledger_atoms, 167_772_150_000);
    assert_eq!(
        exact_rescale_atoms_v1(
            ledger_atoms,
            TARGET_COMMON_DECIMALS_V1,
            CURRENT_TAU_TESTNET_DECIMALS_V1,
        )
        .expect("the exact inverse conversion must succeed"),
        tau_atoms
    );
}

#[test]
fn given_sub_atom_tau_withdrawal_when_downscaled_then_residue_rejects() {
    let rejected = exact_rescale_atoms_v1(10_001, 8, 4)
        .expect_err("a non-divisible withdrawal must not round");

    assert_eq!(rejected.code, AssetPrecisionRejectCodeV1::InexactRescale);
}

#[test]
fn rescale_bva_covers_decimal_and_signed_effect_bounds() {
    assert_eq!(exact_rescale_atoms_v1(1, 0, 18).unwrap(), 10_u128.pow(18));
    assert_eq!(
        exact_rescale_atoms_v1(MAX_SETTLEMENT_DELTA_ATOMS_V1, 18, 18).unwrap(),
        MAX_SETTLEMENT_DELTA_ATOMS_V1
    );
    assert_eq!(
        exact_rescale_atoms_v1(MAX_SETTLEMENT_DELTA_ATOMS_V1, 8, 9)
            .unwrap_err()
            .code,
        AssetPrecisionRejectCodeV1::AmountOutOfRange
    );
    assert_eq!(
        exact_rescale_atoms_v1(1, MAX_ASSET_DECIMALS_V1 + 1, 8)
            .unwrap_err()
            .code,
        AssetPrecisionRejectCodeV1::DecimalsOutOfRange
    );
}

#[test]
fn exact_rescale_round_trip_holds_across_every_registered_scale() {
    for source_decimals in 0..=MAX_ASSET_DECIMALS_V1 {
        for destination_decimals in 0..=MAX_ASSET_DECIMALS_V1 {
            let source_atoms = 123_u128 * 10_u128.pow(u32::from(source_decimals));
            let destination_atoms =
                exact_rescale_atoms_v1(source_atoms, source_decimals, destination_decimals)
                    .expect("whole-token values must rescale exactly");

            assert_eq!(
                exact_rescale_atoms_v1(destination_atoms, destination_decimals, source_decimals,)
                    .expect("exact rescaling must be reversible"),
                source_atoms
            );
        }
    }
}

#[test]
fn tau_wire_bva_distinguishes_current_and_target_profiles() {
    let bv24_max = TauAmountWidthV1::Bv24.max_atoms();
    let bv64_max = TauAmountWidthV1::Bv64.max_atoms();

    assert_eq!(
        admit_tau_amount_v1(bv24_max, TauAmountWidthV1::Bv24),
        Ok(bv24_max)
    );
    assert_eq!(
        admit_tau_amount_v1(bv24_max + 1, TauAmountWidthV1::Bv24)
            .unwrap_err()
            .code,
        AssetPrecisionRejectCodeV1::TauAmountOutOfRange
    );
    assert_eq!(
        admit_tau_amount_v1(bv64_max, TauAmountWidthV1::Bv64),
        Ok(bv64_max)
    );
    assert_eq!(
        admit_tau_amount_v1(0, TauAmountWidthV1::Bv64)
            .unwrap_err()
            .code,
        AssetPrecisionRejectCodeV1::TauAmountOutOfRange
    );
}

#[test]
fn terminal_burn_requires_explicit_asset_retirement() {
    let preserved = admit_burn_v1(2, 1, BurnDispositionV1::PreserveAsset).unwrap();
    assert_eq!(preserved.supply_after_atoms, 1);

    assert_eq!(
        admit_burn_v1(1, 1, BurnDispositionV1::PreserveAsset)
            .unwrap_err()
            .code,
        AssetPrecisionRejectCodeV1::FinalAtomRequiresRetirement
    );
    assert_eq!(
        admit_burn_v1(2, 1, BurnDispositionV1::RetireAsset)
            .unwrap_err()
            .code,
        AssetPrecisionRejectCodeV1::RetirementRequiresZeroSupply
    );
    assert_eq!(
        admit_burn_v1(1, 1, BurnDispositionV1::RetireAsset)
            .unwrap()
            .supply_after_atoms,
        0
    );
}

#[test]
fn burn_bva_rejects_zero_and_supply_underflow() {
    assert_eq!(
        admit_burn_v1(1, 0, BurnDispositionV1::PreserveAsset)
            .unwrap_err()
            .code,
        AssetPrecisionRejectCodeV1::BurnAmountZero
    );
    assert_eq!(
        admit_burn_v1(1, 2, BurnDispositionV1::PreserveAsset)
            .unwrap_err()
            .code,
        AssetPrecisionRejectCodeV1::BurnExceedsSupply
    );
}

#[test]
fn floor_bps_quote_preserves_fractional_residue_without_overflow() {
    let one_atom = quote_floor_bps_burn_v1(1, 5_000).unwrap();
    assert_eq!(one_atom.burn_atoms, 0);
    assert_eq!(one_atom.residue_numerator, 5_000);
    assert_eq!(one_atom.residue_denominator, 10_000);

    let maximum = quote_floor_bps_burn_v1(MAX_SETTLEMENT_DELTA_ATOMS_V1, 10_000).unwrap();
    assert_eq!(maximum.burn_atoms, MAX_SETTLEMENT_DELTA_ATOMS_V1);
    assert_eq!(maximum.residue_numerator, 0);

    assert_eq!(
        quote_floor_bps_burn_v1(1, 10_001).unwrap_err().code,
        AssetPrecisionRejectCodeV1::BasisPointsOutOfRange
    );
}

#[test]
fn registry_is_closed_ordered_and_rooted() {
    let registry = AssetPrecisionRegistryV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        policies: vec![
            policy("TAU", 4, TauAmountWidthV1::Bv24),
            policy("ZDEX", 8, TauAmountWidthV1::Bv64),
            policy("zUSD", 8, TauAmountWidthV1::Bv64),
        ],
    };

    registry
        .validate()
        .expect("the exact ordered registry must validate");
    assert!(registry.registry_root().is_ok());
    assert_eq!(registry.policy_for("ZDEX").unwrap().ledger_decimals, 8);

    let mut reordered = registry.clone();
    reordered.policies.swap(0, 1);
    assert!(reordered.validate().is_err());

    let mut excessive = registry;
    excessive.policies = (0..=MAX_ASSET_PRECISION_POLICIES_V1)
        .map(|index| policy(&format!("asset-{index:03}"), 8, TauAmountWidthV1::Bv64))
        .collect();
    assert!(excessive.validate().is_err());
}
