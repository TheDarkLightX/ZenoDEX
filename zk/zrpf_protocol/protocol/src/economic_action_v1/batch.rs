use alloc::vec::Vec;

use super::batch_codec::{deserialize_actions, serialize_actions};
use super::batch_hash::{
    commitment, derive_batch_commitments, domain_hasher, validate_action_semantics,
    AUTHORIZED_ACTION_DOMAIN_V1,
};
use super::{
    ActionAuthorizationBindingIdV1, AuthorizationConsumptionNullifierV1, AuthorizationGrantIdV1,
    AuthorizationGrantSpendNullifierV1, EconomicActionBatchErrorV1, EconomicActionIdV1,
    EconomicActionRecordV1,
};
use crate::{ApplicationIdV3, CommitmentV3, DomainIdV3};
use serde::{de, Deserialize, Deserializer, Serialize};
use sha2::Digest;

pub const ECONOMIC_ACTION_BATCH_VERSION_V1: u16 = 1;
pub const MAX_ECONOMIC_ACTIONS_PER_BATCH_V1: usize = 64;
pub const MAX_ECONOMIC_ACTION_BATCH_BYTES_V1: usize = 524_288;

const BATCH_COMMITMENT_DOMAIN_V1: &[u8] = b"zenodex.zrpf.economic_action_batch.v1";

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct AuthorizedEconomicActionV1 {
    record: EconomicActionRecordV1,
    authorization_grant_id: AuthorizationGrantIdV1,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct AuthorizedEconomicActionWireV1 {
    record: EconomicActionRecordV1,
    authorization_grant_id: AuthorizationGrantIdV1,
}

impl AuthorizedEconomicActionV1 {
    pub fn new(
        record: EconomicActionRecordV1,
        authorization_grant_id: AuthorizationGrantIdV1,
    ) -> Result<Self, EconomicActionBatchErrorV1> {
        record.validate_self_consistency()?;
        Ok(Self {
            record,
            authorization_grant_id,
        })
    }

    pub const fn record(&self) -> &EconomicActionRecordV1 {
        &self.record
    }

    pub const fn authorization_grant_id(&self) -> AuthorizationGrantIdV1 {
        self.authorization_grant_id
    }

    pub fn action_id(&self) -> Result<EconomicActionIdV1, EconomicActionBatchErrorV1> {
        Ok(self.record.canonical_id()?)
    }

    pub fn action_authorization_binding(
        &self,
    ) -> Result<ActionAuthorizationBindingIdV1, EconomicActionBatchErrorV1> {
        Ok(AuthorizationConsumptionNullifierV1::derive(
            &self.record,
            self.authorization_grant_id,
        )?)
    }

    pub fn authorization_grant_spend(
        &self,
    ) -> Result<AuthorizationGrantSpendNullifierV1, EconomicActionBatchErrorV1> {
        Ok(AuthorizationGrantSpendNullifierV1::derive(
            &self.record,
            self.authorization_grant_id,
        )?)
    }

    pub fn canonical_hash(&self) -> Result<CommitmentV3, EconomicActionBatchErrorV1> {
        let mut hasher = domain_hasher(AUTHORIZED_ACTION_DOMAIN_V1)?;
        hasher.update(self.action_id()?.as_bytes());
        hasher.update(self.authorization_grant_id.as_bytes());
        hasher.update(self.action_authorization_binding()?.as_bytes());
        hasher.update(self.authorization_grant_spend()?.as_bytes());
        commitment(hasher, "authorized_action")
    }
}

impl<'de> Deserialize<'de> for AuthorizedEconomicActionV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = AuthorizedEconomicActionWireV1::deserialize(deserializer)?;
        Self::new(wire.record, wire.authorization_grant_id).map_err(de::Error::custom)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct EconomicActionBatchV1 {
    batch_version: u16,
    application_id: ApplicationIdV3,
    chain_or_domain_id: DomainIdV3,
    epoch_id: u64,
    pre_state_root: CommitmentV3,
    #[serde(serialize_with = "serialize_actions")]
    actions: Vec<AuthorizedEconomicActionV1>,
    action_ids_root: CommitmentV3,
    authorized_actions_root: CommitmentV3,
    action_authorization_bindings_root: CommitmentV3,
    authorization_grant_spends_root: CommitmentV3,
    effect_commitments_root: CommitmentV3,
    consumed_object_ids_root: CommitmentV3,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct EconomicActionBatchWireV1 {
    batch_version: u16,
    application_id: ApplicationIdV3,
    chain_or_domain_id: DomainIdV3,
    epoch_id: u64,
    pre_state_root: CommitmentV3,
    #[serde(deserialize_with = "deserialize_actions")]
    actions: Vec<AuthorizedEconomicActionV1>,
    action_ids_root: CommitmentV3,
    authorized_actions_root: CommitmentV3,
    action_authorization_bindings_root: CommitmentV3,
    authorization_grant_spends_root: CommitmentV3,
    effect_commitments_root: CommitmentV3,
    consumed_object_ids_root: CommitmentV3,
}

impl EconomicActionBatchV1 {
    pub fn new(
        epoch_id: u64,
        pre_state_root: CommitmentV3,
        actions: Vec<AuthorizedEconomicActionV1>,
    ) -> Result<Self, EconomicActionBatchErrorV1> {
        require_action_count(actions.len())?;
        let mut keyed_actions = actions
            .into_iter()
            .map(|action| Ok((action.action_id()?, action)))
            .collect::<Result<Vec<_>, EconomicActionBatchErrorV1>>()?;
        keyed_actions.sort_by_key(|(action_id, _)| *action_id);
        let actions = keyed_actions
            .into_iter()
            .map(|(_, action)| action)
            .collect::<Vec<_>>();
        let first = actions
            .first()
            .ok_or(EconomicActionBatchErrorV1::EmptyActions)?;
        let application_id = first.record.application_id();
        let chain_or_domain_id = first.record.chain_or_domain_id();
        let commitments = derive_batch_commitments(&actions)?;
        let batch = Self {
            batch_version: ECONOMIC_ACTION_BATCH_VERSION_V1,
            application_id,
            chain_or_domain_id,
            epoch_id,
            pre_state_root,
            actions,
            action_ids_root: commitments.action_ids_root,
            authorized_actions_root: commitments.authorized_actions_root,
            action_authorization_bindings_root: commitments.action_authorization_bindings_root,
            authorization_grant_spends_root: commitments.authorization_grant_spends_root,
            effect_commitments_root: commitments.effect_commitments_root,
            consumed_object_ids_root: commitments.consumed_object_ids_root,
        };
        batch.validate_self_consistency()?;
        Ok(batch)
    }

    /// Merges proof-neutral action batches disclosed by separate subtrees.
    ///
    /// This function authenticates no receipt. A receipt-verifying guest must
    /// first derive each input batch from its exact authenticated child. The
    /// merge then flattens all actions into one bounded canonical set, so the
    /// existing action, grant-spend, and consumed-object uniqueness checks run
    /// across subtree boundaries rather than once per child.
    pub fn merge_subtree_batches(batches: Vec<Self>) -> Result<Self, EconomicActionBatchErrorV1> {
        let first = batches
            .first()
            .ok_or(EconomicActionBatchErrorV1::EmptyActions)?;
        let application_id = first.application_id;
        let chain_or_domain_id = first.chain_or_domain_id;
        let epoch_id = first.epoch_id;
        let pre_state_root = first.pre_state_root;
        let mut action_count = 0_usize;

        for batch in &batches {
            batch.validate_self_consistency()?;
            if batch.application_id != application_id {
                return Err(EconomicActionBatchErrorV1::ApplicationMismatch);
            }
            if batch.chain_or_domain_id != chain_or_domain_id {
                return Err(EconomicActionBatchErrorV1::DomainMismatch);
            }
            if batch.epoch_id != epoch_id {
                return Err(EconomicActionBatchErrorV1::SubtreeEpochMismatch);
            }
            if batch.pre_state_root != pre_state_root {
                return Err(EconomicActionBatchErrorV1::PreStateMismatch);
            }
            action_count = action_count.checked_add(batch.actions.len()).ok_or(
                EconomicActionBatchErrorV1::ArithmeticOverflow("subtree_action_count"),
            )?;
            if action_count > MAX_ECONOMIC_ACTIONS_PER_BATCH_V1 {
                return Err(EconomicActionBatchErrorV1::TooManyActions {
                    actual: action_count,
                    maximum: MAX_ECONOMIC_ACTIONS_PER_BATCH_V1,
                });
            }
        }

        let mut actions = Vec::with_capacity(action_count);
        for batch in batches {
            actions.extend(batch.actions);
        }
        Self::new(epoch_id, pre_state_root, actions)
    }

    pub fn validate_self_consistency(&self) -> Result<(), EconomicActionBatchErrorV1> {
        if self.batch_version != ECONOMIC_ACTION_BATCH_VERSION_V1 {
            return Err(EconomicActionBatchErrorV1::InvalidVersion(
                self.batch_version,
            ));
        }
        require_action_count(self.actions.len())?;
        validate_action_semantics(
            &self.actions,
            self.application_id,
            self.chain_or_domain_id,
            self.epoch_id,
            self.pre_state_root,
        )?;
        let commitments = derive_batch_commitments(&self.actions)?;
        for (field, actual, expected) in [
            (
                "action_ids_root",
                self.action_ids_root,
                commitments.action_ids_root,
            ),
            (
                "authorized_actions_root",
                self.authorized_actions_root,
                commitments.authorized_actions_root,
            ),
            (
                "action_authorization_bindings_root",
                self.action_authorization_bindings_root,
                commitments.action_authorization_bindings_root,
            ),
            (
                "authorization_grant_spends_root",
                self.authorization_grant_spends_root,
                commitments.authorization_grant_spends_root,
            ),
            (
                "effect_commitments_root",
                self.effect_commitments_root,
                commitments.effect_commitments_root,
            ),
            (
                "consumed_object_ids_root",
                self.consumed_object_ids_root,
                commitments.consumed_object_ids_root,
            ),
        ] {
            if actual != expected {
                return Err(EconomicActionBatchErrorV1::CommitmentMismatch(field));
            }
        }
        Ok(())
    }

    pub const fn batch_version(&self) -> u16 {
        self.batch_version
    }

    pub const fn application_id(&self) -> ApplicationIdV3 {
        self.application_id
    }

    pub const fn chain_or_domain_id(&self) -> DomainIdV3 {
        self.chain_or_domain_id
    }

    pub const fn epoch_id(&self) -> u64 {
        self.epoch_id
    }

    pub const fn pre_state_root(&self) -> CommitmentV3 {
        self.pre_state_root
    }

    pub fn actions(&self) -> &[AuthorizedEconomicActionV1] {
        &self.actions
    }

    pub const fn action_ids_root(&self) -> CommitmentV3 {
        self.action_ids_root
    }

    pub const fn authorized_actions_root(&self) -> CommitmentV3 {
        self.authorized_actions_root
    }

    pub const fn action_authorization_bindings_root(&self) -> CommitmentV3 {
        self.action_authorization_bindings_root
    }

    pub const fn authorization_grant_spends_root(&self) -> CommitmentV3 {
        self.authorization_grant_spends_root
    }

    pub const fn effect_commitments_root(&self) -> CommitmentV3 {
        self.effect_commitments_root
    }

    pub const fn consumed_object_ids_root(&self) -> CommitmentV3 {
        self.consumed_object_ids_root
    }

    pub fn canonical_commitment(&self) -> Result<CommitmentV3, EconomicActionBatchErrorV1> {
        self.validate_self_consistency()?;
        let mut hasher = domain_hasher(BATCH_COMMITMENT_DOMAIN_V1)?;
        hasher.update(self.batch_version.to_be_bytes());
        hasher.update(self.application_id.as_bytes());
        hasher.update(self.chain_or_domain_id.as_bytes());
        hasher.update(self.epoch_id.to_be_bytes());
        hasher.update(self.pre_state_root.as_bytes());
        let count = u32::try_from(self.actions.len())
            .map_err(|_| EconomicActionBatchErrorV1::ArithmeticOverflow("action_count"))?;
        hasher.update(count.to_be_bytes());
        for root in [
            self.action_ids_root,
            self.authorized_actions_root,
            self.action_authorization_bindings_root,
            self.authorization_grant_spends_root,
            self.effect_commitments_root,
            self.consumed_object_ids_root,
        ] {
            hasher.update(root.as_bytes());
        }
        commitment(hasher, "batch_commitment")
    }
}

impl<'de> Deserialize<'de> for EconomicActionBatchV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = EconomicActionBatchWireV1::deserialize(deserializer)?;
        let batch = Self {
            batch_version: wire.batch_version,
            application_id: wire.application_id,
            chain_or_domain_id: wire.chain_or_domain_id,
            epoch_id: wire.epoch_id,
            pre_state_root: wire.pre_state_root,
            actions: wire.actions,
            action_ids_root: wire.action_ids_root,
            authorized_actions_root: wire.authorized_actions_root,
            action_authorization_bindings_root: wire.action_authorization_bindings_root,
            authorization_grant_spends_root: wire.authorization_grant_spends_root,
            effect_commitments_root: wire.effect_commitments_root,
            consumed_object_ids_root: wire.consumed_object_ids_root,
        };
        batch
            .validate_self_consistency()
            .map_err(de::Error::custom)?;
        Ok(batch)
    }
}

fn require_action_count(count: usize) -> Result<(), EconomicActionBatchErrorV1> {
    if count == 0 {
        return Err(EconomicActionBatchErrorV1::EmptyActions);
    }
    if count > MAX_ECONOMIC_ACTIONS_PER_BATCH_V1 {
        return Err(EconomicActionBatchErrorV1::TooManyActions {
            actual: count,
            maximum: MAX_ECONOMIC_ACTIONS_PER_BATCH_V1,
        });
    }
    Ok(())
}
