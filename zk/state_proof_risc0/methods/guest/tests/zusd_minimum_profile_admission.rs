use tau_state_proof_risc0_guest::{
    validate_zusd_minimum_profile_input_v1, ZusdMinimumAdmissionError,
    ZUSD_LIQUITY_V1_MINIMUM_MCR_BPS,
};
use tau_state_proof_risc0_shared::{
    OracleBindingV1, ZusdBalanceEntryV1, ZusdOperationV1, ZusdSnapshotV1,
    ZusdTransitionInputV1, ZusdVaultEntryV1,
};

const E8: u128 = 100_000_000;

fn oracle() -> OracleBindingV1 {
    OracleBindingV1 {
        oracle_bridge_id: "verified-oracle".to_string(),
        oracle_bridge_hash: "11".repeat(32),
        price_e8: E8 as i128,
        price_timestamp: 10,
        max_staleness_seconds: 5,
        observed_at: 12,
        pre_price_batch_commitment: "22".repeat(32),
    }
}

fn input_with(pre_state: ZusdSnapshotV1, mcr_bps: u32) -> ZusdTransitionInputV1 {
    ZusdTransitionInputV1 {
        state_hash: [7u8; 32],
        chain_id: "devnet".to_string(),
        pre_app_hash_present: true,
        pre_app_hash: [8u8; 32],
        pre_state,
        operation: ZusdOperationV1::DepositMint {
            pubkey: "wallet-a".to_string(),
            collateral_asset: "tAGRS".to_string(),
            deposit_amount_e8: 2_000 * E8,
            mint_amount_e8: 1_000 * E8,
            oracle: oracle(),
            mcr_bps,
            nonce: 1,
        },
        expected_post_app_hash: [9u8; 32],
        risc0_image_id: [1, 2, 3, 4, 5, 6, 7, 8],
    }
}

fn empty_input() -> ZusdTransitionInputV1 {
    input_with(
        ZusdSnapshotV1::empty(),
        ZUSD_LIQUITY_V1_MINIMUM_MCR_BPS,
    )
}

#[test]
fn exact_empty_minimum_profile_prestate_is_admitted() {
    assert_eq!(
        validate_zusd_minimum_profile_input_v1(&empty_input()),
        Ok(())
    );
}

#[test]
fn imported_balance_supply_must_equal_scoped_debt() {
    let snapshot = ZusdSnapshotV1 {
        version: 1,
        vaults: vec![ZusdVaultEntryV1 {
            pubkey: "wallet-a".to_string(),
            collateral_asset: "tAGRS".to_string(),
            collateral_amount_e8: 2_000 * E8,
            debt_zusd_e8: 1_000 * E8,
            nonce: 1,
        }],
        balances: vec![ZusdBalanceEntryV1 {
            pubkey: "wallet-a".to_string(),
            amount_e8: 999 * E8,
        }],
        total_debt_zusd_e8: 1_000 * E8,
    };

    assert_eq!(
        validate_zusd_minimum_profile_input_v1(&input_with(
            snapshot,
            ZUSD_LIQUITY_V1_MINIMUM_MCR_BPS,
        )),
        Err(ZusdMinimumAdmissionError::BalanceSupplyMismatch)
    );
}

#[test]
fn imported_balance_sum_overflow_rejects_before_transition() {
    let snapshot = ZusdSnapshotV1 {
        version: 1,
        vaults: vec![],
        balances: vec![
            ZusdBalanceEntryV1 {
                pubkey: "wallet-a".to_string(),
                amount_e8: u128::MAX,
            },
            ZusdBalanceEntryV1 {
                pubkey: "wallet-b".to_string(),
                amount_e8: 1,
            },
        ],
        total_debt_zusd_e8: 0,
    };

    assert_eq!(
        validate_zusd_minimum_profile_input_v1(&input_with(
            snapshot,
            ZUSD_LIQUITY_V1_MINIMUM_MCR_BPS,
        )),
        Err(ZusdMinimumAdmissionError::BalanceSupplyOverflow)
    );
}

#[test]
fn caller_cannot_weaken_or_strengthen_the_pinned_mcr() {
    for mcr_bps in [10_001, 10_999, 11_001, 15_000] {
        assert_eq!(
            validate_zusd_minimum_profile_input_v1(&input_with(
                ZusdSnapshotV1::empty(),
                mcr_bps,
            )),
            Err(ZusdMinimumAdmissionError::McrMismatch)
        );
    }
}

#[test]
fn optional_prestate_commitment_has_no_minimum_profile_authority() {
    let mut input = empty_input();
    input.pre_app_hash_present = false;
    input.pre_app_hash = [0u8; 32];

    assert_eq!(
        validate_zusd_minimum_profile_input_v1(&input),
        Err(ZusdMinimumAdmissionError::MissingPreAppHash)
    );
}

#[test]
fn imported_vault_debt_must_equal_declared_scoped_debt() {
    let snapshot = ZusdSnapshotV1 {
        version: 1,
        vaults: vec![ZusdVaultEntryV1 {
            pubkey: "wallet-a".to_string(),
            collateral_asset: "tAGRS".to_string(),
            collateral_amount_e8: 2_000 * E8,
            debt_zusd_e8: 1_000 * E8,
            nonce: 1,
        }],
        balances: vec![],
        total_debt_zusd_e8: 0,
    };

    assert_eq!(
        validate_zusd_minimum_profile_input_v1(&input_with(
            snapshot,
            ZUSD_LIQUITY_V1_MINIMUM_MCR_BPS,
        )),
        Err(ZusdMinimumAdmissionError::VaultDebtMismatch)
    );
}
