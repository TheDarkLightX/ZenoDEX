use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use sha2::{Digest, Sha256};

use super::{
    ActionAuthorizationBindingIdV1, AuthorizationGrantSpendNullifierV1, AuthorizedEconomicActionV1,
    EconomicActionBatchErrorV1, EconomicActionIdV1,
};
use crate::{ApplicationIdV3, CommitmentV3, DomainIdV3};

pub(super) const AUTHORIZED_ACTION_DOMAIN_V1: &[u8] = b"zenodex.zrpf.authorized_economic_action.v1";
const ACTION_IDS_ROOT_DOMAIN_V1: &[u8] = b"zenodex.zrpf.economic_action_ids_root.v1";
const AUTHORIZED_ACTIONS_ROOT_DOMAIN_V1: &[u8] =
    b"zenodex.zrpf.authorized_economic_actions_root.v1";
const ACTION_BINDINGS_ROOT_DOMAIN_V1: &[u8] = b"zenodex.zrpf.action_authorization_bindings_root.v1";
const GRANT_SPENDS_ROOT_DOMAIN_V1: &[u8] = b"zenodex.zrpf.authorization_grant_spends_root.v1";
const EFFECT_COMMITMENTS_ROOT_DOMAIN_V1: &[u8] =
    b"zenodex.zrpf.economic_effect_commitments_root.v1";
const CONSUMED_OBJECTS_ROOT_DOMAIN_V1: &[u8] = b"zenodex.zrpf.economic_consumed_objects_root.v1";

#[derive(Clone, Copy)]
pub(super) struct BatchCommitmentsV1 {
    pub(super) action_ids_root: CommitmentV3,
    pub(super) authorized_actions_root: CommitmentV3,
    pub(super) action_authorization_bindings_root: CommitmentV3,
    pub(super) authorization_grant_spends_root: CommitmentV3,
    pub(super) effect_commitments_root: CommitmentV3,
    pub(super) consumed_object_ids_root: CommitmentV3,
}

pub(super) fn validate_action_semantics(
    actions: &[AuthorizedEconomicActionV1],
    application_id: ApplicationIdV3,
    chain_or_domain_id: DomainIdV3,
    epoch_id: u64,
    pre_state_root: CommitmentV3,
) -> Result<(), EconomicActionBatchErrorV1> {
    let mut prior_action_id = None;
    let mut action_bindings = BTreeSet::new();
    let mut grant_spends = BTreeSet::new();
    let mut consumed_objects = BTreeSet::new();
    for action in actions {
        let record = action.record();
        record.validate_self_consistency()?;
        if record.application_id() != application_id {
            return Err(EconomicActionBatchErrorV1::ApplicationMismatch);
        }
        if record.chain_or_domain_id() != chain_or_domain_id {
            return Err(EconomicActionBatchErrorV1::DomainMismatch);
        }
        if epoch_id < record.valid_from_epoch() || epoch_id > record.valid_through_epoch() {
            return Err(EconomicActionBatchErrorV1::EpochOutsideActionValidity);
        }
        if record.pre_state_root() != pre_state_root {
            return Err(EconomicActionBatchErrorV1::PreStateMismatch);
        }
        let action_id = action.action_id()?;
        if prior_action_id.is_some_and(|prior| prior >= action_id) {
            return Err(if prior_action_id == Some(action_id) {
                EconomicActionBatchErrorV1::DuplicateAction
            } else {
                EconomicActionBatchErrorV1::NonCanonicalActionOrder
            });
        }
        prior_action_id = Some(action_id);
        if !action_bindings.insert(action.action_authorization_binding()?) {
            return Err(EconomicActionBatchErrorV1::DuplicateActionAuthorizationBinding);
        }
        if !grant_spends.insert(action.authorization_grant_spend()?) {
            return Err(EconomicActionBatchErrorV1::DuplicateAuthorizationGrantSpend);
        }
        for object_id in record.consumed_object_ids() {
            if !consumed_objects.insert(*object_id) {
                return Err(EconomicActionBatchErrorV1::DuplicateConsumedObject);
            }
        }
    }
    Ok(())
}

pub(super) fn derive_batch_commitments(
    actions: &[AuthorizedEconomicActionV1],
) -> Result<BatchCommitmentsV1, EconomicActionBatchErrorV1> {
    let action_ids = actions
        .iter()
        .map(AuthorizedEconomicActionV1::action_id)
        .collect::<Result<Vec<_>, _>>()?;
    let authorized_actions = actions
        .iter()
        .map(AuthorizedEconomicActionV1::canonical_hash)
        .collect::<Result<Vec<_>, _>>()?;
    let mut action_bindings = actions
        .iter()
        .map(AuthorizedEconomicActionV1::action_authorization_binding)
        .collect::<Result<Vec<_>, _>>()?;
    action_bindings.sort_unstable();
    let mut grant_spends = actions
        .iter()
        .map(AuthorizedEconomicActionV1::authorization_grant_spend)
        .collect::<Result<Vec<_>, _>>()?;
    grant_spends.sort_unstable();
    let effect_commitments = actions
        .iter()
        .map(|action| action.record().effect_commitment())
        .collect::<Vec<_>>();
    let mut consumed_objects = actions
        .iter()
        .flat_map(|action| action.record().consumed_object_ids().iter().copied())
        .collect::<Vec<_>>();
    consumed_objects.sort_unstable();
    Ok(BatchCommitmentsV1 {
        action_ids_root: list_root(
            ACTION_IDS_ROOT_DOMAIN_V1,
            action_ids.iter().map(EconomicActionIdV1::as_bytes),
            "action_ids_root",
        )?,
        authorized_actions_root: list_root(
            AUTHORIZED_ACTIONS_ROOT_DOMAIN_V1,
            authorized_actions.iter().map(CommitmentV3::as_bytes),
            "authorized_actions_root",
        )?,
        action_authorization_bindings_root: list_root(
            ACTION_BINDINGS_ROOT_DOMAIN_V1,
            action_bindings
                .iter()
                .map(ActionAuthorizationBindingIdV1::as_bytes),
            "action_authorization_bindings_root",
        )?,
        authorization_grant_spends_root: list_root(
            GRANT_SPENDS_ROOT_DOMAIN_V1,
            grant_spends
                .iter()
                .map(AuthorizationGrantSpendNullifierV1::as_bytes),
            "authorization_grant_spends_root",
        )?,
        effect_commitments_root: list_root(
            EFFECT_COMMITMENTS_ROOT_DOMAIN_V1,
            effect_commitments.iter().map(CommitmentV3::as_bytes),
            "effect_commitments_root",
        )?,
        consumed_object_ids_root: list_root(
            CONSUMED_OBJECTS_ROOT_DOMAIN_V1,
            consumed_objects.iter().map(CommitmentV3::as_bytes),
            "consumed_object_ids_root",
        )?,
    })
}

fn list_root<'a>(
    domain: &'static [u8],
    values: impl ExactSizeIterator<Item = &'a [u8; 32]>,
    field: &'static str,
) -> Result<CommitmentV3, EconomicActionBatchErrorV1> {
    let mut hasher = domain_hasher(domain)?;
    let count = u32::try_from(values.len())
        .map_err(|_| EconomicActionBatchErrorV1::ArithmeticOverflow(field))?;
    hasher.update(count.to_be_bytes());
    for value in values {
        hasher.update(value);
    }
    commitment(hasher, field)
}

pub(super) fn domain_hasher(domain: &[u8]) -> Result<Sha256, EconomicActionBatchErrorV1> {
    let length = u16::try_from(domain.len())
        .map_err(|_| EconomicActionBatchErrorV1::ArithmeticOverflow("hash_domain"))?;
    let mut hasher = Sha256::new();
    hasher.update(length.to_be_bytes());
    hasher.update(domain);
    Ok(hasher)
}

pub(super) fn commitment(
    hasher: Sha256,
    field: &'static str,
) -> Result<CommitmentV3, EconomicActionBatchErrorV1> {
    CommitmentV3::new(hasher.finalize().into())
        .map_err(|_| EconomicActionBatchErrorV1::InvalidDerivedCommitment(field))
}
