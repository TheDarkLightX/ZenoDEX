use alloc::vec::Vec;
use core::fmt;

use serde::{
    de::{self, SeqAccess, Visitor},
    Deserialize, Deserializer, Serialize,
};
use sha2::{Digest, Sha256};

use super::{
    AuthorizationConsumptionNullifierV1, AuthorizationGrantIdV1,
    AuthorizationGrantSpendNullifierV1, AuthorizationScopeIdV1, AuthorizationSubjectIdV1,
    EconomicActionErrorV1, EconomicActionIdV1, EconomicActionTypeIdV1,
    AUTHORIZATION_CONSUMPTION_NULLIFIER_VERSION_V1, AUTHORIZATION_GRANT_SPEND_NULLIFIER_VERSION_V1,
    ECONOMIC_ACTION_RECORD_VERSION_V1, MAX_CONSUMED_OBJECTS_PER_ACTION_V1,
};
use crate::{ApplicationIdV3, CommitmentV3, DomainIdV3};

const ECONOMIC_ACTION_ID_DOMAIN_V1: &[u8] = b"zenodex.zrpf.economic_action_id.v1";
const AUTHORIZATION_CONSUMPTION_NULLIFIER_DOMAIN_V1: &[u8] =
    b"zenodex.zrpf.authorization_consumption_nullifier.v1";
const AUTHORIZATION_GRANT_SPEND_NULLIFIER_DOMAIN_V1: &[u8] =
    b"zenodex.zrpf.authorization_grant_spend_nullifier.v1";

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EconomicActionRecordInputV1 {
    pub application_id: ApplicationIdV3,
    pub chain_or_domain_id: DomainIdV3,
    pub action_type_id: EconomicActionTypeIdV1,
    pub authorization_subject_id: AuthorizationSubjectIdV1,
    pub authorization_scope_id: AuthorizationScopeIdV1,
    pub authorization_nonce: u64,
    pub valid_from_epoch: u64,
    pub valid_through_epoch: u64,
    pub pre_state_root: CommitmentV3,
    pub action_semantics_hash: CommitmentV3,
    pub effect_commitment: CommitmentV3,
    pub consumed_object_ids: Vec<CommitmentV3>,
}

/// Canonical semantic action identity material without proof-envelope fields.
///
/// A proof program, receipt encoding, intent salt, or signature representation
/// has no field in this object. An upstream semantic profile remains responsible
/// for deriving `action_semantics_hash` and `effect_commitment` correctly.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct EconomicActionRecordV1 {
    record_version: u16,
    application_id: ApplicationIdV3,
    chain_or_domain_id: DomainIdV3,
    action_type_id: EconomicActionTypeIdV1,
    authorization_subject_id: AuthorizationSubjectIdV1,
    authorization_scope_id: AuthorizationScopeIdV1,
    authorization_nonce: u64,
    valid_from_epoch: u64,
    valid_through_epoch: u64,
    pre_state_root: CommitmentV3,
    action_semantics_hash: CommitmentV3,
    effect_commitment: CommitmentV3,
    consumed_object_ids: Vec<CommitmentV3>,
}

fn deserialize_consumed_object_ids<'de, D>(deserializer: D) -> Result<Vec<CommitmentV3>, D::Error>
where
    D: Deserializer<'de>,
{
    struct ConsumedObjectIdsVisitor;

    impl<'de> Visitor<'de> for ConsumedObjectIdsVisitor {
        type Value = Vec<CommitmentV3>;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(
                formatter,
                "at most {MAX_CONSUMED_OBJECTS_PER_ACTION_V1} consumed object identifiers"
            )
        }

        fn visit_seq<A>(self, mut sequence: A) -> Result<Self::Value, A::Error>
        where
            A: SeqAccess<'de>,
        {
            let declared = sequence.size_hint().unwrap_or(0);
            if declared > MAX_CONSUMED_OBJECTS_PER_ACTION_V1 {
                return Err(de::Error::custom(
                    EconomicActionErrorV1::TooManyConsumedObjects {
                        actual: declared,
                        maximum: MAX_CONSUMED_OBJECTS_PER_ACTION_V1,
                    },
                ));
            }

            let mut object_ids = Vec::with_capacity(declared);
            while let Some(object_id) = sequence.next_element()? {
                if object_ids.len() == MAX_CONSUMED_OBJECTS_PER_ACTION_V1 {
                    return Err(de::Error::custom(
                        EconomicActionErrorV1::TooManyConsumedObjects {
                            actual: MAX_CONSUMED_OBJECTS_PER_ACTION_V1 + 1,
                            maximum: MAX_CONSUMED_OBJECTS_PER_ACTION_V1,
                        },
                    ));
                }
                object_ids.push(object_id);
            }
            Ok(object_ids)
        }
    }

    deserializer.deserialize_seq(ConsumedObjectIdsVisitor)
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct EconomicActionRecordWireV1 {
    record_version: u16,
    application_id: ApplicationIdV3,
    chain_or_domain_id: DomainIdV3,
    action_type_id: EconomicActionTypeIdV1,
    authorization_subject_id: AuthorizationSubjectIdV1,
    authorization_scope_id: AuthorizationScopeIdV1,
    authorization_nonce: u64,
    valid_from_epoch: u64,
    valid_through_epoch: u64,
    pre_state_root: CommitmentV3,
    action_semantics_hash: CommitmentV3,
    effect_commitment: CommitmentV3,
    #[serde(deserialize_with = "deserialize_consumed_object_ids")]
    consumed_object_ids: Vec<CommitmentV3>,
}

impl EconomicActionRecordV1 {
    pub fn new(input: EconomicActionRecordInputV1) -> Result<Self, EconomicActionErrorV1> {
        Self::from_parts(ECONOMIC_ACTION_RECORD_VERSION_V1, input)
    }

    fn from_parts(
        record_version: u16,
        mut input: EconomicActionRecordInputV1,
    ) -> Result<Self, EconomicActionErrorV1> {
        if input.consumed_object_ids.len() > MAX_CONSUMED_OBJECTS_PER_ACTION_V1 {
            return Err(EconomicActionErrorV1::TooManyConsumedObjects {
                actual: input.consumed_object_ids.len(),
                maximum: MAX_CONSUMED_OBJECTS_PER_ACTION_V1,
            });
        }
        input.consumed_object_ids.sort_unstable();
        if input
            .consumed_object_ids
            .windows(2)
            .any(|pair| pair[0] == pair[1])
        {
            return Err(EconomicActionErrorV1::DuplicateConsumedObject);
        }
        let record = Self {
            record_version,
            application_id: input.application_id,
            chain_or_domain_id: input.chain_or_domain_id,
            action_type_id: input.action_type_id,
            authorization_subject_id: input.authorization_subject_id,
            authorization_scope_id: input.authorization_scope_id,
            authorization_nonce: input.authorization_nonce,
            valid_from_epoch: input.valid_from_epoch,
            valid_through_epoch: input.valid_through_epoch,
            pre_state_root: input.pre_state_root,
            action_semantics_hash: input.action_semantics_hash,
            effect_commitment: input.effect_commitment,
            consumed_object_ids: input.consumed_object_ids,
        };
        record.validate_self_consistency()?;
        Ok(record)
    }

    pub fn validate_self_consistency(&self) -> Result<(), EconomicActionErrorV1> {
        if self.record_version != ECONOMIC_ACTION_RECORD_VERSION_V1 {
            return Err(EconomicActionErrorV1::InvalidRecordVersion(
                self.record_version,
            ));
        }
        if self.valid_from_epoch > self.valid_through_epoch {
            return Err(EconomicActionErrorV1::InvalidValidityRange);
        }
        if self.consumed_object_ids.len() > MAX_CONSUMED_OBJECTS_PER_ACTION_V1 {
            return Err(EconomicActionErrorV1::TooManyConsumedObjects {
                actual: self.consumed_object_ids.len(),
                maximum: MAX_CONSUMED_OBJECTS_PER_ACTION_V1,
            });
        }
        if self
            .consumed_object_ids
            .windows(2)
            .any(|pair| pair[0] >= pair[1])
        {
            return Err(EconomicActionErrorV1::DuplicateConsumedObject);
        }
        Ok(())
    }

    pub fn canonical_id(&self) -> Result<EconomicActionIdV1, EconomicActionErrorV1> {
        self.validate_self_consistency()?;
        let mut hasher = domain_hasher(ECONOMIC_ACTION_ID_DOMAIN_V1)?;
        hasher.update(self.record_version.to_be_bytes());
        hasher.update(self.application_id.as_bytes());
        hasher.update(self.chain_or_domain_id.as_bytes());
        hasher.update(self.action_type_id.as_bytes());
        hasher.update(self.authorization_subject_id.as_bytes());
        hasher.update(self.authorization_scope_id.as_bytes());
        hasher.update(self.authorization_nonce.to_be_bytes());
        hasher.update(self.valid_from_epoch.to_be_bytes());
        hasher.update(self.valid_through_epoch.to_be_bytes());
        hasher.update(self.pre_state_root.as_bytes());
        hasher.update(self.action_semantics_hash.as_bytes());
        hasher.update(self.effect_commitment.as_bytes());
        let consumed_object_count = u32::try_from(self.consumed_object_ids.len())
            .map_err(|_| EconomicActionErrorV1::ArithmeticOverflow("consumed_object_count"))?;
        hasher.update(consumed_object_count.to_be_bytes());
        for object_id in &self.consumed_object_ids {
            hasher.update(object_id.as_bytes());
        }
        EconomicActionIdV1::new(hasher.finalize().into())
    }

    pub const fn record_version(&self) -> u16 {
        self.record_version
    }

    pub const fn application_id(&self) -> ApplicationIdV3 {
        self.application_id
    }

    pub const fn chain_or_domain_id(&self) -> DomainIdV3 {
        self.chain_or_domain_id
    }

    pub const fn action_type_id(&self) -> EconomicActionTypeIdV1 {
        self.action_type_id
    }

    pub const fn authorization_subject_id(&self) -> AuthorizationSubjectIdV1 {
        self.authorization_subject_id
    }

    pub const fn authorization_scope_id(&self) -> AuthorizationScopeIdV1 {
        self.authorization_scope_id
    }

    pub const fn authorization_nonce(&self) -> u64 {
        self.authorization_nonce
    }

    pub const fn valid_from_epoch(&self) -> u64 {
        self.valid_from_epoch
    }

    pub const fn valid_through_epoch(&self) -> u64 {
        self.valid_through_epoch
    }

    pub const fn pre_state_root(&self) -> CommitmentV3 {
        self.pre_state_root
    }

    pub const fn action_semantics_hash(&self) -> CommitmentV3 {
        self.action_semantics_hash
    }

    pub const fn effect_commitment(&self) -> CommitmentV3 {
        self.effect_commitment
    }

    pub fn consumed_object_ids(&self) -> &[CommitmentV3] {
        &self.consumed_object_ids
    }
}

impl<'de> Deserialize<'de> for EconomicActionRecordV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = EconomicActionRecordWireV1::deserialize(deserializer)?;
        Self::from_parts(
            wire.record_version,
            EconomicActionRecordInputV1 {
                application_id: wire.application_id,
                chain_or_domain_id: wire.chain_or_domain_id,
                action_type_id: wire.action_type_id,
                authorization_subject_id: wire.authorization_subject_id,
                authorization_scope_id: wire.authorization_scope_id,
                authorization_nonce: wire.authorization_nonce,
                valid_from_epoch: wire.valid_from_epoch,
                valid_through_epoch: wire.valid_through_epoch,
                pre_state_root: wire.pre_state_root,
                action_semantics_hash: wire.action_semantics_hash,
                effect_commitment: wire.effect_commitment,
                consumed_object_ids: wire.consumed_object_ids,
            },
        )
        .map_err(de::Error::custom)
    }
}

impl AuthorizationConsumptionNullifierV1 {
    /// Derives an action-bound authorization binding for audit and replay.
    ///
    /// This value changes when the canonical action changes. Use
    /// `AuthorizationGrantSpendNullifierV1` for single-use grant-nonce
    /// enforcement.
    pub fn derive(
        record: &EconomicActionRecordV1,
        authorization_grant_id: AuthorizationGrantIdV1,
    ) -> Result<Self, EconomicActionErrorV1> {
        record.validate_self_consistency()?;
        let action_id = record.canonical_id()?;
        let mut hasher = domain_hasher(AUTHORIZATION_CONSUMPTION_NULLIFIER_DOMAIN_V1)?;
        hasher.update(AUTHORIZATION_CONSUMPTION_NULLIFIER_VERSION_V1.to_be_bytes());
        hasher.update(record.application_id.as_bytes());
        hasher.update(record.chain_or_domain_id.as_bytes());
        hasher.update(action_id.as_bytes());
        hasher.update(record.authorization_subject_id.as_bytes());
        hasher.update(authorization_grant_id.as_bytes());
        hasher.update(record.authorization_scope_id.as_bytes());
        hasher.update(record.authorization_nonce.to_be_bytes());
        hasher.update(record.pre_state_root.as_bytes());
        Self::new(hasher.finalize().into())
    }
}

impl AuthorizationGrantSpendNullifierV1 {
    /// Derives the single-use key for one grant nonce in one application domain.
    ///
    /// The preimage deliberately excludes the action, effect, pre-state,
    /// subject, scope, proof, receipt, signature, and salt representations.
    pub fn derive(
        record: &EconomicActionRecordV1,
        authorization_grant_id: AuthorizationGrantIdV1,
    ) -> Result<Self, EconomicActionErrorV1> {
        record.validate_self_consistency()?;
        let mut hasher = domain_hasher(AUTHORIZATION_GRANT_SPEND_NULLIFIER_DOMAIN_V1)?;
        hasher.update(AUTHORIZATION_GRANT_SPEND_NULLIFIER_VERSION_V1.to_be_bytes());
        hasher.update(record.application_id.as_bytes());
        hasher.update(record.chain_or_domain_id.as_bytes());
        hasher.update(authorization_grant_id.as_bytes());
        hasher.update(record.authorization_nonce.to_be_bytes());
        Self::new(hasher.finalize().into())
    }
}

fn domain_hasher(domain: &[u8]) -> Result<Sha256, EconomicActionErrorV1> {
    let domain_length = u16::try_from(domain.len())
        .map_err(|_| EconomicActionErrorV1::ArithmeticOverflow("hash_domain"))?;
    let mut hasher = Sha256::new();
    hasher.update(domain_length.to_be_bytes());
    hasher.update(domain);
    Ok(hasher)
}
