//! Receipt-bound genesis or migration certificate shape.

use serde::{Deserialize, Serialize};

use crate::canonical::{
    canonical_bytes_v1, hash_bytes_sha256_v1, hash_global_v1, validate_schema_v1,
    validate_token_v1, AbiErrorV1, AbiResultV1, RootV1, GLOBAL_SETTLEMENT_ABI_V1,
    MAX_CYCLE_BUDGET_V1, MAX_JOURNAL_BYTES_V1,
};
use crate::proof::ReceiptKindV1;
use crate::release::{EconomicProfileSnapshotV1, ProfileStatusV1};
use crate::state::GlobalEconomicStateV1;

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub enum EconomicInitialStateKindV1 {
    GENESIS,
    MIGRATION,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct EconomicInitialStateCertificateV1 {
    pub schema: String,
    pub kind: EconomicInitialStateKindV1,
    pub chain_id: String,
    pub deployment_root: RootV1,
    pub profile_root: RootV1,
    pub writer_epoch: u64,
    pub height: u64,
    pub state_root: RootV1,
    pub source_profile_root: RootV1,
    pub source_state_root: RootV1,
    pub source_writer_epoch: u64,
    pub source_height: u64,
    pub state_atom_coverage_root: RootV1,
    pub lane_object_coverage_root: RootV1,
    pub replay_continuity_root: RootV1,
    pub terminal_continuity_root: RootV1,
    pub outbox_continuity_root: RootV1,
    pub source_manifest_root: RootV1,
    pub toolchain_manifest_root: RootV1,
    pub root_image_id: RootV1,
    pub receipt_root: RootV1,
    pub receipt_kind: ReceiptKindV1,
    pub journal_bytes: u64,
    pub cycle_budget: u64,
}

#[derive(Serialize)]
struct EconomicInitialStateJournalV1<'a> {
    schema: &'static str,
    kind: EconomicInitialStateKindV1,
    chain_id: &'a str,
    deployment_root: &'a RootV1,
    profile_root: &'a RootV1,
    writer_epoch: u64,
    height: u64,
    state_root: &'a RootV1,
    source_profile_root: &'a RootV1,
    source_state_root: &'a RootV1,
    source_writer_epoch: u64,
    source_height: u64,
    state_atom_coverage_root: &'a RootV1,
    lane_object_coverage_root: &'a RootV1,
    replay_continuity_root: &'a RootV1,
    terminal_continuity_root: &'a RootV1,
    outbox_continuity_root: &'a RootV1,
    source_manifest_root: &'a RootV1,
    toolchain_manifest_root: &'a RootV1,
    root_image_id: &'a RootV1,
}

impl EconomicInitialStateCertificateV1 {
    fn journal(&self) -> EconomicInitialStateJournalV1<'_> {
        EconomicInitialStateJournalV1 {
            schema: GLOBAL_SETTLEMENT_ABI_V1,
            kind: self.kind,
            chain_id: &self.chain_id,
            deployment_root: &self.deployment_root,
            profile_root: &self.profile_root,
            writer_epoch: self.writer_epoch,
            height: self.height,
            state_root: &self.state_root,
            source_profile_root: &self.source_profile_root,
            source_state_root: &self.source_state_root,
            source_writer_epoch: self.source_writer_epoch,
            source_height: self.source_height,
            state_atom_coverage_root: &self.state_atom_coverage_root,
            lane_object_coverage_root: &self.lane_object_coverage_root,
            replay_continuity_root: &self.replay_continuity_root,
            terminal_continuity_root: &self.terminal_continuity_root,
            outbox_continuity_root: &self.outbox_continuity_root,
            source_manifest_root: &self.source_manifest_root,
            toolchain_manifest_root: &self.toolchain_manifest_root,
            root_image_id: &self.root_image_id,
        }
    }

    pub fn validate(&self) -> AbiResultV1<()> {
        validate_schema_v1(&self.schema)?;
        validate_token_v1(&self.chain_id, "initial state chain id")?;
        for root in [
            &self.deployment_root,
            &self.profile_root,
            &self.state_root,
            &self.state_atom_coverage_root,
            &self.lane_object_coverage_root,
            &self.replay_continuity_root,
            &self.terminal_continuity_root,
            &self.outbox_continuity_root,
            &self.source_manifest_root,
            &self.toolchain_manifest_root,
            &self.root_image_id,
            &self.receipt_root,
        ] {
            root.validate("initial state required root", false)?;
        }
        if self.journal_bytes == 0
            || self.journal_bytes > MAX_JOURNAL_BYTES_V1
            || self.cycle_budget == 0
            || self.cycle_budget > MAX_CYCLE_BUDGET_V1
        {
            return Err(AbiErrorV1::InvalidBounds("initial state proof resources"));
        }
        if self.receipt_kind != ReceiptKindV1::SUCCINCT {
            return Err(AbiErrorV1::InvalidBinding("initial state receipt kind"));
        }
        match self.kind {
            EconomicInitialStateKindV1::GENESIS => {
                self.source_profile_root
                    .validate("genesis source profile root", true)?;
                self.source_state_root
                    .validate("genesis source state root", true)?;
                if !self.source_profile_root.is_zero()
                    || !self.source_state_root.is_zero()
                    || self.source_writer_epoch != 0
                    || self.source_height != 0
                    || self.height != 0
                {
                    return Err(AbiErrorV1::InvalidBinding(
                        "genesis predecessor coordinates",
                    ));
                }
            }
            EconomicInitialStateKindV1::MIGRATION => {
                self.source_profile_root
                    .validate("migration source profile root", false)?;
                self.source_state_root
                    .validate("migration source state root", false)?;
                if self.source_profile_root == self.profile_root
                    || self.source_writer_epoch.checked_add(1) != Some(self.writer_epoch)
                    || self.source_height.checked_add(1) != Some(self.height)
                {
                    return Err(AbiErrorV1::InvalidBinding(
                        "migration initial state lineage",
                    ));
                }
            }
        }
        let canonical_journal_bytes = u64::try_from(self.canonical_journal_bytes()?.len())
            .map_err(|_| AbiErrorV1::InvalidBounds("initial state journal byte count"))?;
        if canonical_journal_bytes != self.journal_bytes {
            return Err(AbiErrorV1::InvalidBinding(
                "initial state journal byte count",
            ));
        }
        Ok(())
    }

    pub fn canonical_journal_bytes(&self) -> AbiResultV1<Vec<u8>> {
        canonical_bytes_v1(&self.journal())
    }

    pub fn certificate_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("economic-initial-state-certificate-v1", self)
    }
}

pub fn validate_economic_initial_state_bindings_v1(
    profile: &EconomicProfileSnapshotV1,
    state: &GlobalEconomicStateV1,
    certificate: &EconomicInitialStateCertificateV1,
    receipt_bytes: &[u8],
) -> AbiResultV1<()> {
    profile.validate()?;
    if profile.status != ProfileStatusV1::ACTIVE {
        return Err(AbiErrorV1::InvalidBinding(
            "economic initial state active profile",
        ));
    }
    state.validate_profile(profile)?;
    certificate.validate()?;
    let state_root = state.state_root()?;
    if certificate.chain_id != state.chain_id
        || certificate.deployment_root != state.deployment_root
        || certificate.profile_root != profile.profile_id
        || certificate.profile_root != state.profile_root
        || certificate.writer_epoch != profile.authority_epoch
        || certificate.writer_epoch != state.writer_epoch
        || certificate.height != state.height
        || certificate.state_root != state_root
        || certificate.root_image_id != profile.root_image_id
    {
        return Err(AbiErrorV1::InvalidBinding("economic initial state content"));
    }
    if receipt_bytes.is_empty()
        || certificate.receipt_root.as_str() != format!("0x{}", hash_bytes_sha256_v1(receipt_bytes))
    {
        return Err(AbiErrorV1::InvalidBinding(
            "economic initial state receipt root",
        ));
    }
    Ok(())
}
