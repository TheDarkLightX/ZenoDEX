//! Closed values for the Python Asset Origin Registry V2 SHADOW mirror.
//!
//! Public Rust construction is untrusted. Callers must validate these values,
//! and the transition validates every input before protocol dispatch. These
//! values grant no RISC0, runtime, migration, settlement, release, or
//! production authority.

use std::collections::BTreeSet;

use serde::{Deserialize, Deserializer, Serialize};

use crate::asset_transfer_types::{
    require_asset_class_namespace_v2, AssetClassV2, ASSET_ATOM_DECIMALS_V2,
    ASSET_LANE_PRODUCTION_AUTHORITY_V2,
};
use crate::canonical::{
    hash_economic_command_body_v2, hash_global_v2, validate_schema_v2, validate_token_v2,
    AbiErrorV2, AbiResultV2, RootV2, ValidateCanonicalV2,
};
use crate::effects::{GlobalEconomicEffectPlanV2, LaneIdV2, LaneWriteV2};
use crate::proof::{EconomicCommandOccurrenceV2, LaneModuleTransitionJournalV2};

pub const ASSET_ORIGIN_REGISTRY_SCHEMA_V2: &str = "zenodex/asset-origin-registry/v2";
pub const ASSET_ORIGIN_REGISTRATION_COMMAND_V2: &str = "register_asset_origin";
pub const MAX_ASSET_ORIGIN_REGISTRY_ASSETS_V2: usize = 256;

fn deserialize_required_option<'de, D, T>(deserializer: D) -> Result<Option<T>, D::Error>
where
    D: Deserializer<'de>,
    T: Deserialize<'de>,
{
    Option::<T>::deserialize(deserializer)
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[allow(non_camel_case_types)]
pub enum AssetOriginKindV2 {
    NATIVE,
    TAU_ORIGINATED,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[allow(non_camel_case_types)]
pub enum AssetOriginRegistrationRejectCodeV2 {
    MISSING_OCCURRENCE,
    OCCURRENCE_BINDING_MISMATCH,
    RELEASE_MISMATCH,
    UNKNOWN_COMMAND,
    OCCURRENCE_COMMAND_MISMATCH,
    UNAUTHORIZED_SUBJECT,
    GRANT_MISMATCH,
    DECIMAL_SCALE_MISMATCH,
    DISABLED_ORIGIN_KIND,
    NATIVE_ASSET_ACCOUNTING_UNIMPLEMENTED,
    DUPLICATE_ASSET,
    DUPLICATE_ORIGIN,
    REGISTRY_CAPACITY_EXCEEDED,
}

impl AssetOriginRegistrationRejectCodeV2 {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::MISSING_OCCURRENCE => "MISSING_OCCURRENCE",
            Self::OCCURRENCE_BINDING_MISMATCH => "OCCURRENCE_BINDING_MISMATCH",
            Self::RELEASE_MISMATCH => "RELEASE_MISMATCH",
            Self::UNKNOWN_COMMAND => "UNKNOWN_COMMAND",
            Self::OCCURRENCE_COMMAND_MISMATCH => "OCCURRENCE_COMMAND_MISMATCH",
            Self::UNAUTHORIZED_SUBJECT => "UNAUTHORIZED_SUBJECT",
            Self::GRANT_MISMATCH => "GRANT_MISMATCH",
            Self::DECIMAL_SCALE_MISMATCH => "DECIMAL_SCALE_MISMATCH",
            Self::DISABLED_ORIGIN_KIND => "DISABLED_ORIGIN_KIND",
            Self::NATIVE_ASSET_ACCOUNTING_UNIMPLEMENTED => "NATIVE_ASSET_ACCOUNTING_UNIMPLEMENTED",
            Self::DUPLICATE_ASSET => "DUPLICATE_ASSET",
            Self::DUPLICATE_ORIGIN => "DUPLICATE_ORIGIN",
            Self::REGISTRY_CAPACITY_EXCEEDED => "REGISTRY_CAPACITY_EXCEEDED",
        }
    }
}

pub const ALL_ASSET_ORIGIN_REGISTRATION_REJECT_CODES_V2: [AssetOriginRegistrationRejectCodeV2; 13] = [
    AssetOriginRegistrationRejectCodeV2::MISSING_OCCURRENCE,
    AssetOriginRegistrationRejectCodeV2::OCCURRENCE_BINDING_MISMATCH,
    AssetOriginRegistrationRejectCodeV2::RELEASE_MISMATCH,
    AssetOriginRegistrationRejectCodeV2::UNKNOWN_COMMAND,
    AssetOriginRegistrationRejectCodeV2::OCCURRENCE_COMMAND_MISMATCH,
    AssetOriginRegistrationRejectCodeV2::UNAUTHORIZED_SUBJECT,
    AssetOriginRegistrationRejectCodeV2::GRANT_MISMATCH,
    AssetOriginRegistrationRejectCodeV2::DECIMAL_SCALE_MISMATCH,
    AssetOriginRegistrationRejectCodeV2::DISABLED_ORIGIN_KIND,
    AssetOriginRegistrationRejectCodeV2::NATIVE_ASSET_ACCOUNTING_UNIMPLEMENTED,
    AssetOriginRegistrationRejectCodeV2::DUPLICATE_ASSET,
    AssetOriginRegistrationRejectCodeV2::DUPLICATE_ORIGIN,
    AssetOriginRegistrationRejectCodeV2::REGISTRY_CAPACITY_EXCEEDED,
];

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AssetOriginRecordV2 {
    pub asset: String,
    pub origin_kind: AssetOriginKindV2,
    pub origin_root: RootV2,
    pub transfer_policy_root: RootV2,
    pub issue_policy_root: RootV2,
    pub decimals: u64,
    pub asset_class: AssetClassV2,
}

impl AssetOriginRecordV2 {
    pub fn validate(&self) -> AbiResultV2<()> {
        validate_token_v2(&self.asset, "asset origin asset")?;
        self.origin_root.validate("asset origin root", false)?;
        self.transfer_policy_root
            .validate("asset transfer policy root", false)?;
        self.issue_policy_root
            .validate("asset issue policy root", true)?;
        if self.decimals != u64::from(ASSET_ATOM_DECIMALS_V2) {
            return Err(AbiErrorV2::InvalidBinding("asset origin atom scale"));
        }
        require_asset_class_namespace_v2(&self.asset, self.asset_class)?;
        if (self.origin_kind == AssetOriginKindV2::NATIVE)
            != (self.asset_class == AssetClassV2::TauNativeCoin)
        {
            return Err(AbiErrorV2::InvalidBinding(
                "asset origin kind and native class",
            ));
        }
        Ok(())
    }

    pub fn record_root(&self) -> AbiResultV2<RootV2> {
        self.validate()?;
        hash_global_v2("asset-origin-record-v2", self)
    }
}

impl ValidateCanonicalV2 for AssetOriginRecordV2 {
    fn validate_canonical_v2(&self) -> AbiResultV2<()> {
        self.validate()
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AssetOriginRegistrationPolicyV2 {
    pub authority_subject: String,
    pub authority_grant_root: RootV2,
    pub allow_native: bool,
    pub allow_tau_originated: bool,
}

impl AssetOriginRegistrationPolicyV2 {
    pub fn validate(&self) -> AbiResultV2<()> {
        validate_token_v2(&self.authority_subject, "asset registration authority")?;
        self.authority_grant_root
            .validate("asset registration grant", false)
    }
}

impl ValidateCanonicalV2 for AssetOriginRegistrationPolicyV2 {
    fn validate_canonical_v2(&self) -> AbiResultV2<()> {
        self.validate()
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AssetOriginRegistryStateV2 {
    pub schema: String,
    pub module_release_id: RootV2,
    pub policy: AssetOriginRegistrationPolicyV2,
    pub assets: Vec<AssetOriginRecordV2>,
}

impl AssetOriginRegistryStateV2 {
    pub fn validate(&self) -> AbiResultV2<()> {
        validate_schema_v2(
            &self.schema,
            ASSET_ORIGIN_REGISTRY_SCHEMA_V2,
            "asset origin registry state",
        )?;
        self.module_release_id
            .validate("asset origin registry module release", false)?;
        if self.assets.len() > MAX_ASSET_ORIGIN_REGISTRY_ASSETS_V2 {
            return Err(AbiErrorV2::InvalidBounds("asset origin registry assets"));
        }
        self.policy.validate()?;
        for row in &self.assets {
            row.validate()?;
        }
        if self
            .assets
            .windows(2)
            .any(|pair| pair[0].asset >= pair[1].asset)
        {
            return Err(AbiErrorV2::InvalidOrder("asset origin registry rows"));
        }
        let mut origin_roots = BTreeSet::new();
        if self
            .assets
            .iter()
            .any(|row| !origin_roots.insert(row.origin_root.as_str()))
        {
            return Err(AbiErrorV2::InvalidOrder("asset origin roots"));
        }
        if self
            .assets
            .iter()
            .filter(|row| row.origin_kind == AssetOriginKindV2::NATIVE)
            .count()
            > 1
        {
            return Err(AbiErrorV2::InvalidBinding("native asset uniqueness"));
        }
        Ok(())
    }

    pub fn state_root(&self) -> AbiResultV2<RootV2> {
        self.validate()?;
        hash_global_v2("asset-origin-registry-state-v2", self)
    }

    pub fn record_for(&self, asset: &str) -> AbiResultV2<Option<&AssetOriginRecordV2>> {
        validate_token_v2(asset, "asset origin registry lookup")?;
        Ok(self.assets.iter().find(|row| row.asset == asset))
    }
}

impl ValidateCanonicalV2 for AssetOriginRegistryStateV2 {
    fn validate_canonical_v2(&self) -> AbiResultV2<()> {
        self.validate()
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AssetOriginRegistrationContextV2 {
    pub writer_epoch: u64,
    pub module_release_id: RootV2,
    pub global_pre_state_root: RootV2,
    #[serde(deserialize_with = "deserialize_required_option")]
    pub occurrence: Option<EconomicCommandOccurrenceV2>,
}

impl AssetOriginRegistrationContextV2 {
    pub fn validate(&self) -> AbiResultV2<()> {
        self.module_release_id
            .validate("asset origin registration module release", false)?;
        self.global_pre_state_root
            .validate("asset origin registration global pre-state root", false)?;
        if let Some(occurrence) = &self.occurrence {
            occurrence.validate()?;
        }
        Ok(())
    }
}

impl ValidateCanonicalV2 for AssetOriginRegistrationContextV2 {
    fn validate_canonical_v2(&self) -> AbiResultV2<()> {
        self.validate()
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AssetOriginRegistrationCommandV2 {
    pub command_kind: String,
    pub asset: String,
    pub origin_kind: AssetOriginKindV2,
    pub origin_root: RootV2,
    pub transfer_policy_root: RootV2,
    pub issue_policy_root: RootV2,
    pub decimals: u64,
    pub asset_class: AssetClassV2,
}

impl AssetOriginRegistrationCommandV2 {
    pub fn validate(&self) -> AbiResultV2<()> {
        validate_token_v2(&self.command_kind, "asset origin registration command")?;
        validate_token_v2(&self.asset, "asset origin registration asset")?;
        self.origin_root
            .validate("asset origin registration root", false)?;
        self.transfer_policy_root
            .validate("asset origin registration transfer policy root", false)?;
        self.issue_policy_root
            .validate("asset origin registration issue policy root", true)?;
        require_asset_class_namespace_v2(&self.asset, self.asset_class)?;
        if (self.origin_kind == AssetOriginKindV2::NATIVE)
            != (self.asset_class == AssetClassV2::TauNativeCoin)
        {
            return Err(AbiErrorV2::InvalidBinding(
                "asset origin command kind and native class",
            ));
        }
        Ok(())
    }

    pub fn command_body_hash(&self) -> AbiResultV2<RootV2> {
        self.validate()?;
        hash_economic_command_body_v2(&self.command_kind, self)
    }
}

impl ValidateCanonicalV2 for AssetOriginRegistrationCommandV2 {
    fn validate_canonical_v2(&self) -> AbiResultV2<()> {
        self.validate()
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AssetOriginRegistrationAcceptedV2 {
    pub post_state: AssetOriginRegistryStateV2,
    pub effects: GlobalEconomicEffectPlanV2,
    pub module_journal: LaneModuleTransitionJournalV2,
}

impl AssetOriginRegistrationAcceptedV2 {
    pub fn validate(&self) -> AbiResultV2<()> {
        self.post_state.validate()?;
        self.effects.validate()?;
        self.module_journal.validate()?;
        let expected_lane_write = LaneWriteV2 {
            lane_id: LaneIdV2::ASSET_TRANSFER,
            pre_root: self.module_journal.pre_lane_root.clone(),
            post_root: self.module_journal.post_lane_root.clone(),
        };
        if !self.effects.rows.is_empty()
            || !self.effects.asset_conservation.is_empty()
            || !self.effects.fee_conservation.is_empty()
        {
            return Err(AbiErrorV2::InvalidBinding(
                "asset origin registration created an economic value effect",
            ));
        }
        if !self.effects.external_outbox_enqueue.is_empty() {
            return Err(AbiErrorV2::InvalidBinding(
                "asset origin registration created an external outbox effect",
            ));
        }
        if self.module_journal.lane_id != LaneIdV2::ASSET_TRANSFER
            || self.module_journal.post_lane_root != self.post_state.state_root()?
            || self.module_journal.effect_plan_root != self.effects.effect_plan_root()?
            || self.effects.occurrence_consumptions
                != vec![self.module_journal.command_occurrence_id.clone()]
            || self.effects.lane_writes != vec![expected_lane_write]
        {
            return Err(AbiErrorV2::InvalidBinding("asset origin accepted bindings"));
        }
        if !self.module_journal.private_port_root.is_zero()
            || !self.module_journal.terminal_obligations_root.is_zero()
            || !self.module_journal.oracle_occurrence_plan_root.is_zero()
        {
            return Err(AbiErrorV2::InvalidBinding(
                "asset origin registration created an unrelated plan",
            ));
        }
        Ok(())
    }

    pub fn receipt_root(&self) -> &RootV2 {
        &self.module_journal.receipt_root
    }

    pub const fn production_authority(&self) -> &'static str {
        ASSET_LANE_PRODUCTION_AUTHORITY_V2
    }
}

impl ValidateCanonicalV2 for AssetOriginRegistrationAcceptedV2 {
    fn validate_canonical_v2(&self) -> AbiResultV2<()> {
        self.validate()
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AssetOriginRegistrationRejectedV2 {
    pub code: AssetOriginRegistrationRejectCodeV2,
    pub pre_state_root: RootV2,
    pub post_state_root: RootV2,
    pub effects: GlobalEconomicEffectPlanV2,
}

impl AssetOriginRegistrationRejectedV2 {
    pub fn validate(&self) -> AbiResultV2<()> {
        self.pre_state_root
            .validate("asset origin rejected pre root", false)?;
        self.post_state_root
            .validate("asset origin rejected post root", false)?;
        self.effects.validate()?;
        if self.pre_state_root != self.post_state_root || !self.effects.is_empty() {
            return Err(AbiErrorV2::InvalidBinding(
                "asset origin registration rejection is not a no-op",
            ));
        }
        Ok(())
    }
}

impl ValidateCanonicalV2 for AssetOriginRegistrationRejectedV2 {
    fn validate_canonical_v2(&self) -> AbiResultV2<()> {
        self.validate()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
#[must_use]
pub enum AssetOriginRegistrationResultV2 {
    Accepted(Box<AssetOriginRegistrationAcceptedV2>),
    Rejected(Box<AssetOriginRegistrationRejectedV2>),
}
