//! Opaque binding to the externally verified current ZDEX authority head.
//!
//! The functional core cannot discover durable currentness by itself. The
//! imperative shell supplies a verifier for the exact canonical statement;
//! downstream governed witnesses retain every authority coordinate. A test
//! verifier is evidence only for structural binding, not deployed currentness.

use serde::{Deserialize, Serialize};

use crate::canonical::{canonical_bytes_v1, hash_global_v1, AbiErrorV1, AbiResultV1, RootV1};
use crate::release::EconomicProfileSnapshotV1;

pub const ZDEX_CURRENT_AUTHORITY_STATEMENT_SCHEMA_V1: &str =
    "zenodex/zdex-current-authority-statement/v1";

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ZDEXCurrentAuthorityStatementV1 {
    pub schema: String,
    pub profile_root: RootV1,
    pub authority_epoch: u64,
    pub authority_generation: u64,
    pub policy_registry_root: RootV1,
    pub verifier_registry_root: RootV1,
    pub root_image_id: RootV1,
    pub receipt_verifier_binding_root: RootV1,
}

impl ZDEXCurrentAuthorityStatementV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        if self.schema != ZDEX_CURRENT_AUTHORITY_STATEMENT_SCHEMA_V1 {
            return Err(AbiErrorV1::InvalidSchema);
        }
        for root in [
            &self.profile_root,
            &self.policy_registry_root,
            &self.verifier_registry_root,
            &self.root_image_id,
            &self.receipt_verifier_binding_root,
        ] {
            root.validate("ZDEX current authority root", false)?;
        }
        Ok(())
    }

    pub fn authority_head_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("zdex-current-authority-head-v1", self)
    }
}

pub trait ZDEXCurrentAuthorityVerifierV1 {
    fn verify_current_authority(&self, expected_statement_bytes: &[u8]) -> AbiResultV1<()>;
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VerifiedZDEXCurrentAuthorityV1 {
    statement: ZDEXCurrentAuthorityStatementV1,
    authority_head_root: RootV1,
}

impl VerifiedZDEXCurrentAuthorityV1 {
    pub fn profile_root(&self) -> &RootV1 {
        &self.statement.profile_root
    }

    pub fn authority_epoch(&self) -> u64 {
        self.statement.authority_epoch
    }

    pub fn authority_generation(&self) -> u64 {
        self.statement.authority_generation
    }

    pub fn policy_registry_root(&self) -> &RootV1 {
        &self.statement.policy_registry_root
    }

    pub fn verifier_registry_root(&self) -> &RootV1 {
        &self.statement.verifier_registry_root
    }

    pub fn root_image_id(&self) -> &RootV1 {
        &self.statement.root_image_id
    }

    pub fn receipt_verifier_binding_root(&self) -> &RootV1 {
        &self.statement.receipt_verifier_binding_root
    }

    pub fn authority_head_root(&self) -> &RootV1 {
        &self.authority_head_root
    }
}

pub fn verify_zdex_current_authority_v1(
    statement: &ZDEXCurrentAuthorityStatementV1,
    profile: &EconomicProfileSnapshotV1,
    verifier: &impl ZDEXCurrentAuthorityVerifierV1,
) -> AbiResultV1<VerifiedZDEXCurrentAuthorityV1> {
    statement.validate()?;
    profile.validate()?;
    if statement.profile_root != profile.profile_id
        || statement.authority_epoch != profile.authority_epoch
        || statement.policy_registry_root != profile.policy_registry_root
        || statement.verifier_registry_root != profile.verifier_registry_root
        || statement.root_image_id != profile.root_image_id
    {
        return Err(AbiErrorV1::InvalidBinding("ZDEX current authority profile"));
    }
    let statement_bytes = canonical_bytes_v1(statement)?;
    verifier.verify_current_authority(&statement_bytes)?;
    Ok(VerifiedZDEXCurrentAuthorityV1 {
        statement: statement.clone(),
        authority_head_root: statement.authority_head_root()?,
    })
}

pub fn zdex_current_authority_statement_v1(
    profile: &EconomicProfileSnapshotV1,
    authority_generation: u64,
    receipt_verifier_binding_root: RootV1,
) -> AbiResultV1<ZDEXCurrentAuthorityStatementV1> {
    profile.validate()?;
    let statement = ZDEXCurrentAuthorityStatementV1 {
        schema: ZDEX_CURRENT_AUTHORITY_STATEMENT_SCHEMA_V1.to_owned(),
        profile_root: profile.profile_id.clone(),
        authority_epoch: profile.authority_epoch,
        authority_generation,
        policy_registry_root: profile.policy_registry_root.clone(),
        verifier_registry_root: profile.verifier_registry_root.clone(),
        root_image_id: profile.root_image_id.clone(),
        receipt_verifier_binding_root,
    };
    statement.validate()?;
    Ok(statement)
}
