use alloc::vec::Vec;

use serde::{de, Deserialize, Deserializer, Serialize};

use super::{
    EconomicCommandOccurrenceIdV1, EconomicLaneIdV1, EconomicProfileIdV1,
    GlobalEconomicEffectPlanErrorV1, GlobalEconomicStateRootV1, RouteReleaseIdV1,
};
use crate::{
    ActionAuthorizationBindingIdV1, ApplicationIdV3, AuthorizationScopeIdV1, CommitmentV3,
    DomainIdV3,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum GlobalIssueBurnKindV1 {
    Issue,
    Burn,
}

impl GlobalIssueBurnKindV1 {
    pub const fn code(self) -> u8 {
        match self {
            Self::Issue => 0,
            Self::Burn => 1,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum GlobalRewardSlashKindV1 {
    Reward,
    Slash,
}

impl GlobalRewardSlashKindV1 {
    pub const fn code(self) -> u8 {
        match self {
            Self::Reward => 0,
            Self::Slash => 1,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum GlobalOccurrenceConsumptionKindV1 {
    ConsumedObject,
    AuthorizationGrantSpend,
}

impl GlobalOccurrenceConsumptionKindV1 {
    pub const fn code(self) -> u8 {
        match self {
            Self::ConsumedObject => 0,
            Self::AuthorizationGrantSpend => 1,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GlobalEconomicEffectKindV1 {
    AccountMovement,
    IssueBurn,
    Custody,
    Liability,
    Reserve,
    Fee,
    RewardSlash,
    LaneWrite,
    OccurrenceConsumption,
    TerminalObligation,
    ExternalOutboxEnqueue,
}

impl GlobalEconomicEffectKindV1 {
    pub const fn code(self) -> u8 {
        match self {
            Self::AccountMovement => 0,
            Self::IssueBurn => 1,
            Self::Custody => 2,
            Self::Liability => 3,
            Self::Reserve => 4,
            Self::Fee => 5,
            Self::RewardSlash => 6,
            Self::LaneWrite => 7,
            Self::OccurrenceConsumption => 8,
            Self::TerminalObligation => 9,
            Self::ExternalOutboxEnqueue => 10,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) enum GlobalEconomicEffectContentV1 {
    AccountMovement {
        lane_id: EconomicLaneIdV1,
        asset_id: CommitmentV3,
        source_id: CommitmentV3,
        destination_id: CommitmentV3,
        amount_atoms: u128,
    },
    IssueBurn {
        lane_id: EconomicLaneIdV1,
        asset_id: CommitmentV3,
        kind: GlobalIssueBurnKindV1,
        bucket_id: CommitmentV3,
        amount_atoms: u128,
        authority_scope_id: AuthorizationScopeIdV1,
        action_authorization_binding: ActionAuthorizationBindingIdV1,
    },
    Custody {
        lane_id: EconomicLaneIdV1,
        asset_id: CommitmentV3,
        custody_id: CommitmentV3,
        custody_pre_atoms: u128,
        custody_post_atoms: u128,
        claimant_entitlements_pre_atoms: u128,
        claimant_entitlements_post_atoms: u128,
        unencumbered_reserves_pre_atoms: u128,
        unencumbered_reserves_post_atoms: u128,
    },
    Liability {
        lane_id: EconomicLaneIdV1,
        asset_id: CommitmentV3,
        liability_id: CommitmentV3,
        pre_atoms: u128,
        post_atoms: u128,
    },
    Reserve {
        lane_id: EconomicLaneIdV1,
        asset_id: CommitmentV3,
        reserve_id: CommitmentV3,
        pre_atoms: u128,
        post_atoms: u128,
    },
    Fee {
        lane_id: EconomicLaneIdV1,
        asset_id: CommitmentV3,
        fee_id: CommitmentV3,
        charged_atoms: u128,
        allocated_atoms: u128,
        carried_residue_atoms: u128,
    },
    RewardSlash {
        lane_id: EconomicLaneIdV1,
        asset_id: CommitmentV3,
        kind: GlobalRewardSlashKindV1,
        source_id: CommitmentV3,
        destination_id: CommitmentV3,
        amount_atoms: u128,
        authority_scope_id: AuthorizationScopeIdV1,
        action_authorization_binding: ActionAuthorizationBindingIdV1,
    },
    LaneWrite {
        lane_id: EconomicLaneIdV1,
        object_id: CommitmentV3,
        pre_value_hash: CommitmentV3,
        post_value_hash: CommitmentV3,
    },
    OccurrenceConsumption {
        kind: GlobalOccurrenceConsumptionKindV1,
        consumption_id: CommitmentV3,
    },
    TerminalObligation {
        lane_id: EconomicLaneIdV1,
        obligation_id: CommitmentV3,
        pre_status_hash: CommitmentV3,
        post_status_hash: CommitmentV3,
    },
    ExternalOutboxEnqueue {
        lane_id: EconomicLaneIdV1,
        outbox_id: CommitmentV3,
        destination_domain_id: DomainIdV3,
        asset_id: CommitmentV3,
        amount_atoms: u128,
        value_effect_id: CommitmentV3,
        payload_commitment: CommitmentV3,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct GlobalEconomicEffectRowV1 {
    content: GlobalEconomicEffectContentV1,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct GlobalLaneWriteV1 {
    lane_id: EconomicLaneIdV1,
    object_id: CommitmentV3,
    pre_value_hash: CommitmentV3,
    post_value_hash: CommitmentV3,
}

impl GlobalLaneWriteV1 {
    pub const fn lane_id(self) -> EconomicLaneIdV1 {
        self.lane_id
    }

    pub const fn object_id(self) -> CommitmentV3 {
        self.object_id
    }

    pub const fn pre_value_hash(self) -> CommitmentV3 {
        self.pre_value_hash
    }

    pub const fn post_value_hash(self) -> CommitmentV3 {
        self.post_value_hash
    }
}

impl GlobalEconomicEffectRowV1 {
    pub(super) fn from_content(
        content: GlobalEconomicEffectContentV1,
    ) -> Result<Self, GlobalEconomicEffectPlanErrorV1> {
        super::global_economic_effect_plan_validate::validate_effect_content_v1(&content)?;
        Ok(Self { content })
    }

    pub(super) const fn content(&self) -> &GlobalEconomicEffectContentV1 {
        &self.content
    }

    pub const fn kind(&self) -> GlobalEconomicEffectKindV1 {
        match self.content {
            GlobalEconomicEffectContentV1::AccountMovement { .. } => {
                GlobalEconomicEffectKindV1::AccountMovement
            }
            GlobalEconomicEffectContentV1::IssueBurn { .. } => {
                GlobalEconomicEffectKindV1::IssueBurn
            }
            GlobalEconomicEffectContentV1::Custody { .. } => GlobalEconomicEffectKindV1::Custody,
            GlobalEconomicEffectContentV1::Liability { .. } => {
                GlobalEconomicEffectKindV1::Liability
            }
            GlobalEconomicEffectContentV1::Reserve { .. } => GlobalEconomicEffectKindV1::Reserve,
            GlobalEconomicEffectContentV1::Fee { .. } => GlobalEconomicEffectKindV1::Fee,
            GlobalEconomicEffectContentV1::RewardSlash { .. } => {
                GlobalEconomicEffectKindV1::RewardSlash
            }
            GlobalEconomicEffectContentV1::LaneWrite { .. } => {
                GlobalEconomicEffectKindV1::LaneWrite
            }
            GlobalEconomicEffectContentV1::OccurrenceConsumption { .. } => {
                GlobalEconomicEffectKindV1::OccurrenceConsumption
            }
            GlobalEconomicEffectContentV1::TerminalObligation { .. } => {
                GlobalEconomicEffectKindV1::TerminalObligation
            }
            GlobalEconomicEffectContentV1::ExternalOutboxEnqueue { .. } => {
                GlobalEconomicEffectKindV1::ExternalOutboxEnqueue
            }
        }
    }

    pub const fn lane_id(&self) -> Option<EconomicLaneIdV1> {
        match self.content {
            GlobalEconomicEffectContentV1::AccountMovement { lane_id, .. }
            | GlobalEconomicEffectContentV1::IssueBurn { lane_id, .. }
            | GlobalEconomicEffectContentV1::Custody { lane_id, .. }
            | GlobalEconomicEffectContentV1::Liability { lane_id, .. }
            | GlobalEconomicEffectContentV1::Reserve { lane_id, .. }
            | GlobalEconomicEffectContentV1::Fee { lane_id, .. }
            | GlobalEconomicEffectContentV1::RewardSlash { lane_id, .. }
            | GlobalEconomicEffectContentV1::LaneWrite { lane_id, .. }
            | GlobalEconomicEffectContentV1::TerminalObligation { lane_id, .. }
            | GlobalEconomicEffectContentV1::ExternalOutboxEnqueue { lane_id, .. } => Some(lane_id),
            GlobalEconomicEffectContentV1::OccurrenceConsumption { .. } => None,
        }
    }

    pub const fn as_lane_write(&self) -> Option<GlobalLaneWriteV1> {
        match self.content {
            GlobalEconomicEffectContentV1::LaneWrite {
                lane_id,
                object_id,
                pre_value_hash,
                post_value_hash,
            } => Some(GlobalLaneWriteV1 {
                lane_id,
                object_id,
                pre_value_hash,
                post_value_hash,
            }),
            _ => None,
        }
    }

    pub fn canonical_id(&self) -> Result<CommitmentV3, GlobalEconomicEffectPlanErrorV1> {
        super::global_economic_effect_plan_hash::effect_row_id_v1(self)
    }
}

impl<'de> Deserialize<'de> for GlobalEconomicEffectRowV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let content = GlobalEconomicEffectContentV1::deserialize(deserializer)?;
        Self::from_content(content).map_err(de::Error::custom)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct GlobalAssetReconciliationInputV1 {
    pub asset_id: CommitmentV3,
    pub owned_and_custodied_pre_atoms: u128,
    pub owned_and_custodied_post_atoms: u128,
    pub supply_pre_atoms: u128,
    pub supply_post_atoms: u128,
    pub liabilities_pre_atoms: u128,
    pub liabilities_post_atoms: u128,
    pub named_reserves_pre_atoms: u128,
    pub named_reserves_post_atoms: u128,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct GlobalAssetReconciliationV1 {
    asset_id: CommitmentV3,
    owned_and_custodied_pre_atoms: u128,
    owned_and_custodied_post_atoms: u128,
    supply_pre_atoms: u128,
    supply_post_atoms: u128,
    liabilities_pre_atoms: u128,
    liabilities_post_atoms: u128,
    named_reserves_pre_atoms: u128,
    named_reserves_post_atoms: u128,
}

impl GlobalAssetReconciliationV1 {
    pub const fn new(input: GlobalAssetReconciliationInputV1) -> Self {
        Self {
            asset_id: input.asset_id,
            owned_and_custodied_pre_atoms: input.owned_and_custodied_pre_atoms,
            owned_and_custodied_post_atoms: input.owned_and_custodied_post_atoms,
            supply_pre_atoms: input.supply_pre_atoms,
            supply_post_atoms: input.supply_post_atoms,
            liabilities_pre_atoms: input.liabilities_pre_atoms,
            liabilities_post_atoms: input.liabilities_post_atoms,
            named_reserves_pre_atoms: input.named_reserves_pre_atoms,
            named_reserves_post_atoms: input.named_reserves_post_atoms,
        }
    }
    pub const fn asset_id(self) -> CommitmentV3 {
        self.asset_id
    }
    pub const fn owned_and_custodied_pre_atoms(self) -> u128 {
        self.owned_and_custodied_pre_atoms
    }
    pub const fn owned_and_custodied_post_atoms(self) -> u128 {
        self.owned_and_custodied_post_atoms
    }
    pub const fn supply_pre_atoms(self) -> u128 {
        self.supply_pre_atoms
    }
    pub const fn supply_post_atoms(self) -> u128 {
        self.supply_post_atoms
    }
    pub const fn liabilities_pre_atoms(self) -> u128 {
        self.liabilities_pre_atoms
    }
    pub const fn liabilities_post_atoms(self) -> u128 {
        self.liabilities_post_atoms
    }
    pub const fn named_reserves_pre_atoms(self) -> u128 {
        self.named_reserves_pre_atoms
    }
    pub const fn named_reserves_post_atoms(self) -> u128 {
        self.named_reserves_post_atoms
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GlobalEconomicEffectBodyInputV1 {
    pub post_state_root: GlobalEconomicStateRootV1,
    pub effects: Vec<GlobalEconomicEffectRowV1>,
    pub reconciliations: Vec<GlobalAssetReconciliationV1>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GlobalEconomicEffectPlanInputV1 {
    pub application_id: ApplicationIdV3,
    pub chain_or_domain_id: DomainIdV3,
    pub profile_id: EconomicProfileIdV1,
    pub writer_epoch: u64,
    pub occurrence_id: EconomicCommandOccurrenceIdV1,
    pub route_release_id: RouteReleaseIdV1,
    pub pre_state_root: GlobalEconomicStateRootV1,
    pub body: super::GlobalEconomicEffectBodyV1,
}
