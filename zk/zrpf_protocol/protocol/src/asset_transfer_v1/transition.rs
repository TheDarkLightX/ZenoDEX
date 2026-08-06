use super::hash::{derive_receipt_hash_v1, AssetTransferReceiptHashInputV1};
use super::{
    AssetTransferAccountIdV1, AssetTransferAssetIdV1, AssetTransferErrorV1,
    AssetTransferLeafInputV1, AssetTransferStateV1,
};
use crate::{
    CommitmentV3, EconomicLaneIdV1, GlobalAccountMovementInputV1, GlobalEconomicEffectPlanErrorV1,
    GlobalEconomicEffectRowV1, LaneModuleRejectCodeV1,
};
use zenodex_asset_transfer_core::{settle_transfer_balances_v1, AssetTransferArithmeticRejectV1};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AssetTransferMovementV1 {
    source_account_id: AssetTransferAccountIdV1,
    destination_account_id: AssetTransferAccountIdV1,
    asset_id: AssetTransferAssetIdV1,
    amount_atoms: u128,
}

impl AssetTransferMovementV1 {
    pub const fn source_account_id(&self) -> AssetTransferAccountIdV1 {
        self.source_account_id
    }

    pub const fn destination_account_id(&self) -> AssetTransferAccountIdV1 {
        self.destination_account_id
    }

    pub const fn asset_id(&self) -> AssetTransferAssetIdV1 {
        self.asset_id
    }

    pub const fn amount_atoms(&self) -> u128 {
        self.amount_atoms
    }

    pub fn to_global_effect_row(
        self,
    ) -> Result<GlobalEconomicEffectRowV1, GlobalEconomicEffectPlanErrorV1> {
        let asset_id = CommitmentV3::new(self.asset_id.into_bytes())
            .map_err(|_| GlobalEconomicEffectPlanErrorV1::InvalidDerivedCommitment("asset_id"))?;
        let source_id = CommitmentV3::new(self.source_account_id.into_bytes())
            .map_err(|_| GlobalEconomicEffectPlanErrorV1::InvalidDerivedCommitment("source_id"))?;
        let destination_id =
            CommitmentV3::new(self.destination_account_id.into_bytes()).map_err(|_| {
                GlobalEconomicEffectPlanErrorV1::InvalidDerivedCommitment("destination_id")
            })?;
        GlobalEconomicEffectRowV1::account_movement(GlobalAccountMovementInputV1 {
            lane_id: EconomicLaneIdV1::AssetTransfer,
            asset_id,
            source_id,
            destination_id,
            amount_atoms: self.amount_atoms,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AssetTransferAcceptedV1 {
    post_state: AssetTransferStateV1,
    movement: AssetTransferMovementV1,
    pre_asset_total_atoms: u128,
    post_asset_total_atoms: u128,
    receipt_hash: CommitmentV3,
}

impl AssetTransferAcceptedV1 {
    pub const fn post_state(&self) -> &AssetTransferStateV1 {
        &self.post_state
    }

    pub const fn movement(&self) -> AssetTransferMovementV1 {
        self.movement
    }

    pub const fn pre_asset_total_atoms(&self) -> u128 {
        self.pre_asset_total_atoms
    }

    pub const fn post_asset_total_atoms(&self) -> u128 {
        self.post_asset_total_atoms
    }

    pub const fn receipt_hash(&self) -> CommitmentV3 {
        self.receipt_hash
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AssetTransferRejectCodeV1 {
    PreStateRootMismatch,
    CommandHashMismatch,
    AuthorizationSubjectMismatch,
    InsufficientBalance,
    BalanceOverflow,
    StateCapacityExceeded,
}

impl AssetTransferRejectCodeV1 {
    pub const ALL: [Self; 6] = [
        Self::PreStateRootMismatch,
        Self::CommandHashMismatch,
        Self::AuthorizationSubjectMismatch,
        Self::InsufficientBalance,
        Self::BalanceOverflow,
        Self::StateCapacityExceeded,
    ];

    pub const fn code(self) -> u32 {
        match self {
            Self::PreStateRootMismatch => 1_001,
            Self::CommandHashMismatch => 1_002,
            Self::AuthorizationSubjectMismatch => 1_003,
            Self::InsufficientBalance => 1_004,
            Self::BalanceOverflow => 1_005,
            Self::StateCapacityExceeded => 1_006,
        }
    }

    pub fn to_lane_module_reject_code(
        self,
    ) -> Result<LaneModuleRejectCodeV1, crate::LaneModuleTransitionJournalErrorV1> {
        LaneModuleRejectCodeV1::new(self.code())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
// Keeping the accepted state inline makes the rejection variant structurally incapable of
// carrying a candidate post-state or effects. That property is part of this boundary contract.
#[allow(clippy::large_enum_variant)]
pub enum AssetTransferLeafOutcomeV1 {
    Accepted(AssetTransferAcceptedV1),
    Rejected(AssetTransferRejectCodeV1),
}

pub fn execute_asset_transfer_leaf_v1(
    input: &AssetTransferLeafInputV1,
) -> Result<AssetTransferLeafOutcomeV1, AssetTransferErrorV1> {
    if input.pre_state().state_root() != input.expected_pre_state_root() {
        return Ok(AssetTransferLeafOutcomeV1::Rejected(
            AssetTransferRejectCodeV1::PreStateRootMismatch,
        ));
    }
    if input.command().canonical_hash()? != input.expected_command_hash() {
        return Ok(AssetTransferLeafOutcomeV1::Rejected(
            AssetTransferRejectCodeV1::CommandHashMismatch,
        ));
    }
    if input.command().source_account_id().as_bytes()
        != input.expected_authorization_subject_id().as_bytes()
    {
        return Ok(AssetTransferLeafOutcomeV1::Rejected(
            AssetTransferRejectCodeV1::AuthorizationSubjectMismatch,
        ));
    }

    let command = input.command();
    let source_pre_atoms = input
        .pre_state()
        .balance_of(command.source_account_id(), command.asset_id());
    let destination_pre_atoms = input
        .pre_state()
        .balance_of(command.destination_account_id(), command.asset_id());
    let post_balances = match settle_transfer_balances_v1(
        source_pre_atoms,
        destination_pre_atoms,
        command.amount_atoms(),
    ) {
        Ok(post) => post,
        Err(AssetTransferArithmeticRejectV1::InsufficientBalance) => {
            return Ok(AssetTransferLeafOutcomeV1::Rejected(
                AssetTransferRejectCodeV1::InsufficientBalance,
            ));
        }
        Err(AssetTransferArithmeticRejectV1::BalanceOverflow) => {
            return Ok(AssetTransferLeafOutcomeV1::Rejected(
                AssetTransferRejectCodeV1::BalanceOverflow,
            ));
        }
    };

    let post_state = match input.pre_state().with_transfer_post(
        command.source_account_id(),
        command.destination_account_id(),
        command.asset_id(),
        post_balances.source_atoms(),
        post_balances.destination_atoms(),
    ) {
        Ok(state) => state,
        Err(AssetTransferErrorV1::TooManyBalances { .. }) => {
            return Ok(AssetTransferLeafOutcomeV1::Rejected(
                AssetTransferRejectCodeV1::StateCapacityExceeded,
            ));
        }
        Err(error) => return Err(error),
    };

    let pre_asset_total_atoms = input.pre_state().asset_total_atoms(command.asset_id())?;
    let post_asset_total_atoms = post_state.asset_total_atoms(command.asset_id())?;
    if pre_asset_total_atoms != post_asset_total_atoms {
        return Err(AssetTransferErrorV1::AssetConservationViolation);
    }
    let movement = AssetTransferMovementV1 {
        source_account_id: command.source_account_id(),
        destination_account_id: command.destination_account_id(),
        asset_id: command.asset_id(),
        amount_atoms: command.amount_atoms(),
    };
    let receipt_hash = derive_receipt_hash_v1(AssetTransferReceiptHashInputV1 {
        expected_pre_state_root: input.expected_pre_state_root(),
        expected_command_hash: input.expected_command_hash(),
        expected_authorization_subject_id: input.expected_authorization_subject_id(),
        command,
        post_state_root: post_state.state_root(),
        movement,
        pre_asset_total_atoms,
        post_asset_total_atoms,
    })?;

    Ok(AssetTransferLeafOutcomeV1::Accepted(
        AssetTransferAcceptedV1 {
            post_state,
            movement,
            pre_asset_total_atoms,
            post_asset_total_atoms,
            receipt_hash,
        },
    ))
}
