use serde::{Deserialize, Serialize};

use crate::canonical::{
    hash_global_v1, validate_schema_v1, validate_token_v1, AbiErrorV1, AbiResultV1, RootV1,
};
use crate::proof::ReceiptKindV1;

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[allow(non_camel_case_types)]
pub enum MigrationObjectClassV1 {
    MIGRATED,
    RETAINED_FOR_DRAIN,
    CLOSED,
    TOMBSTONED,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct MigrationObjectRowV1 {
    pub source_object_id: String,
    pub source_release_id: RootV1,
    pub target_release_id: RootV1,
    pub classification: MigrationObjectClassV1,
    pub source_object_root: RootV1,
    pub target_object_root: RootV1,
    pub continuity_root: RootV1,
}

impl MigrationObjectRowV1 {
    fn validate(&self) -> AbiResultV1<()> {
        validate_token_v1(&self.source_object_id, "migration source object id")?;
        for root in [
            &self.source_release_id,
            &self.target_release_id,
            &self.source_object_root,
            &self.continuity_root,
        ] {
            root.validate("migration object required root", false)?;
        }
        self.target_object_root
            .validate("migration target object root", true)?;
        if self.classification == MigrationObjectClassV1::MIGRATED
            && self.target_object_root.is_zero()
        {
            return Err(AbiErrorV1::InvalidBinding("migrated target object root"));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct StateMigrationCertificateV1 {
    pub schema: String,
    pub source_profile_root: RootV1,
    pub target_profile_root: RootV1,
    pub predecessor_profile_root: RootV1,
    pub source_state_root: RootV1,
    pub target_state_root: RootV1,
    pub source_writer_epoch: u64,
    pub target_writer_epoch: u64,
    pub object_rows: Vec<MigrationObjectRowV1>,
    pub custody_continuity_root: RootV1,
    pub liability_continuity_root: RootV1,
    pub terminal_continuity_root: RootV1,
    pub replay_continuity_root: RootV1,
    pub root_image_id: RootV1,
    pub proof_receipt_root: RootV1,
    pub receipt_kind: ReceiptKindV1,
}

impl StateMigrationCertificateV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        validate_schema_v1(&self.schema)?;
        for root in [
            &self.source_profile_root,
            &self.target_profile_root,
            &self.predecessor_profile_root,
            &self.source_state_root,
            &self.target_state_root,
            &self.custody_continuity_root,
            &self.liability_continuity_root,
            &self.terminal_continuity_root,
            &self.replay_continuity_root,
            &self.root_image_id,
            &self.proof_receipt_root,
        ] {
            root.validate("migration certificate root", false)?;
        }
        let next_epoch = self
            .source_writer_epoch
            .checked_add(1)
            .ok_or(AbiErrorV1::InvalidBounds("migration writer epoch"))?;
        if self.target_writer_epoch != next_epoch {
            return Err(AbiErrorV1::InvalidBinding(
                "migration writer epoch rotation",
            ));
        }
        if self.source_profile_root == self.target_profile_root
            || self.predecessor_profile_root != self.source_profile_root
        {
            return Err(AbiErrorV1::InvalidBinding("migration profile lineage"));
        }
        for row in &self.object_rows {
            row.validate()?;
        }
        if self
            .object_rows
            .windows(2)
            .any(|pair| pair[0].source_object_id >= pair[1].source_object_id)
        {
            return Err(AbiErrorV1::InvalidOrder("migration object rows"));
        }
        if self.receipt_kind != ReceiptKindV1::SUCCINCT {
            return Err(AbiErrorV1::InvalidBinding("migration receipt kind"));
        }
        Ok(())
    }

    pub fn certificate_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("state-migration-certificate-v1", self)
    }
}
