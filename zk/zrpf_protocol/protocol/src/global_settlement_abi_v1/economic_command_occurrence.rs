use alloc::vec::Vec;

use serde::{de, Deserialize, Deserializer, Serialize, Serializer};
use sha2::{Digest, Sha256};

use super::{
    EconomicCommandOccurrenceErrorV1, EconomicProfileIdV1, EconomicProfileSnapshotV1,
    RouteReleaseIdV1, RouteReleaseRegistryV1, RouteReleaseV1,
    ECONOMIC_COMMAND_OCCURRENCE_VERSION_V1, MAX_ECONOMIC_COMMAND_OCCURRENCE_BYTES_V1,
};
use crate::AuthorizedEconomicActionV1;

const OCCURRENCE_ID_DOMAIN_V1: &[u8] =
    b"zenodex.global_settlement.economic_command_occurrence_id.v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct EconomicCommandOccurrenceIdV1([u8; 32]);

impl EconomicCommandOccurrenceIdV1 {
    pub fn new(bytes: [u8; 32]) -> Result<Self, EconomicCommandOccurrenceErrorV1> {
        if bytes == [0; 32] {
            return Err(EconomicCommandOccurrenceErrorV1::ZeroOccurrenceId);
        }
        Ok(Self(bytes))
    }

    pub const fn as_bytes(&self) -> &[u8; 32] {
        &self.0
    }

    pub const fn into_bytes(self) -> [u8; 32] {
        self.0
    }
}

impl Serialize for EconomicCommandOccurrenceIdV1 {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.0.serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for EconomicCommandOccurrenceIdV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let bytes = <[u8; 32]>::deserialize(deserializer)?;
        Self::new(bytes).map_err(de::Error::custom)
    }
}

/// Canonical ledger position for one command within a published block body.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct EconomicOccurrencePositionV1 {
    height: u64,
    tx_index: u32,
    op_index: u32,
}

impl EconomicOccurrencePositionV1 {
    pub const fn new(height: u64, tx_index: u32, op_index: u32) -> Self {
        Self {
            height,
            tx_index,
            op_index,
        }
    }

    pub const fn height(self) -> u64 {
        self.height
    }

    pub const fn tx_index(self) -> u32 {
        self.tx_index
    }

    pub const fn op_index(self) -> u32 {
        self.op_index
    }
}

/// Complete ordinary-data preimage for one governed economic command occurrence.
///
/// Subject, grant, nonce, pre-state, effects, and consumed objects remain owned
/// by the nested authorized action. This prevents a second, drift-prone copy of
/// those authority-bearing fields in the occurrence envelope.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct EconomicCommandOccurrenceContentV1 {
    position: EconomicOccurrencePositionV1,
    profile_id: EconomicProfileIdV1,
    writer_epoch: u64,
    route_release_id: RouteReleaseIdV1,
    authorized_action: AuthorizedEconomicActionV1,
}

impl EconomicCommandOccurrenceContentV1 {
    /// Constructs the complete identity preimage in one call.
    ///
    /// The five arguments are independently committed fields. A staged builder
    /// would permit an incomplete occurrence to exist between calls.
    pub fn new(
        position: EconomicOccurrencePositionV1,
        profile_id: EconomicProfileIdV1,
        writer_epoch: u64,
        route_release_id: RouteReleaseIdV1,
        authorized_action: AuthorizedEconomicActionV1,
    ) -> Result<Self, EconomicCommandOccurrenceErrorV1> {
        authorized_action.canonical_hash()?;
        Ok(Self {
            position,
            profile_id,
            writer_epoch,
            route_release_id,
            authorized_action,
        })
    }

    pub const fn position(&self) -> EconomicOccurrencePositionV1 {
        self.position
    }

    pub const fn profile_id(&self) -> EconomicProfileIdV1 {
        self.profile_id
    }

    pub const fn writer_epoch(&self) -> u64 {
        self.writer_epoch
    }

    pub const fn route_release_id(&self) -> RouteReleaseIdV1 {
        self.route_release_id
    }

    pub const fn authorized_action(&self) -> &AuthorizedEconomicActionV1 {
        &self.authorized_action
    }

    fn validate_self_consistency(&self) -> Result<(), EconomicCommandOccurrenceErrorV1> {
        self.authorized_action.canonical_hash()?;
        Ok(())
    }

    fn update_hasher(&self, hasher: &mut Sha256) -> Result<(), EconomicCommandOccurrenceErrorV1> {
        self.validate_self_consistency()?;
        hasher.update(self.position.height.to_be_bytes());
        hasher.update(self.position.tx_index.to_be_bytes());
        hasher.update(self.position.op_index.to_be_bytes());
        hasher.update(self.profile_id.as_bytes());
        hasher.update(self.writer_epoch.to_be_bytes());
        hasher.update(self.route_release_id.as_bytes());
        hasher.update(self.authorized_action.canonical_hash()?.as_bytes());
        Ok(())
    }
}

impl<'de> Deserialize<'de> for EconomicCommandOccurrenceContentV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        #[derive(Deserialize)]
        #[serde(deny_unknown_fields)]
        struct Wire {
            position: EconomicOccurrencePositionV1,
            profile_id: EconomicProfileIdV1,
            writer_epoch: u64,
            route_release_id: RouteReleaseIdV1,
            authorized_action: AuthorizedEconomicActionV1,
        }

        let wire = Wire::deserialize(deserializer)?;
        Self::new(
            wire.position,
            wire.profile_id,
            wire.writer_epoch,
            wire.route_release_id,
            wire.authorized_action,
        )
        .map_err(de::Error::custom)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[must_use = "an economic command occurrence is ordinary data until an active profile binds it"]
pub struct EconomicCommandOccurrenceV1 {
    occurrence_version: u16,
    occurrence_id: EconomicCommandOccurrenceIdV1,
    content: EconomicCommandOccurrenceContentV1,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct EconomicCommandOccurrenceWireV1 {
    occurrence_version: u16,
    occurrence_id: EconomicCommandOccurrenceIdV1,
    content: EconomicCommandOccurrenceContentV1,
}

impl EconomicCommandOccurrenceV1 {
    pub fn new(
        content: EconomicCommandOccurrenceContentV1,
    ) -> Result<Self, EconomicCommandOccurrenceErrorV1> {
        let occurrence_id = derive_occurrence_id(&content)?;
        Self::from_parts(
            ECONOMIC_COMMAND_OCCURRENCE_VERSION_V1,
            occurrence_id,
            content,
        )
    }

    fn from_parts(
        occurrence_version: u16,
        occurrence_id: EconomicCommandOccurrenceIdV1,
        content: EconomicCommandOccurrenceContentV1,
    ) -> Result<Self, EconomicCommandOccurrenceErrorV1> {
        if occurrence_version != ECONOMIC_COMMAND_OCCURRENCE_VERSION_V1 {
            return Err(EconomicCommandOccurrenceErrorV1::InvalidOccurrenceVersion(
                occurrence_version,
            ));
        }
        content.validate_self_consistency()?;
        if derive_occurrence_id(&content)? != occurrence_id {
            return Err(EconomicCommandOccurrenceErrorV1::CounterfeitOccurrenceId);
        }
        Ok(Self {
            occurrence_version,
            occurrence_id,
            content,
        })
    }

    pub fn validate_self_consistency(&self) -> Result<(), EconomicCommandOccurrenceErrorV1> {
        if self.occurrence_version != ECONOMIC_COMMAND_OCCURRENCE_VERSION_V1 {
            return Err(EconomicCommandOccurrenceErrorV1::InvalidOccurrenceVersion(
                self.occurrence_version,
            ));
        }
        self.content.validate_self_consistency()?;
        if derive_occurrence_id(&self.content)? != self.occurrence_id {
            return Err(EconomicCommandOccurrenceErrorV1::CounterfeitOccurrenceId);
        }
        Ok(())
    }

    pub const fn occurrence_version(&self) -> u16 {
        self.occurrence_version
    }

    pub const fn occurrence_id(&self) -> EconomicCommandOccurrenceIdV1 {
        self.occurrence_id
    }

    pub const fn content(&self) -> &EconomicCommandOccurrenceContentV1 {
        &self.content
    }
}

impl<'de> Deserialize<'de> for EconomicCommandOccurrenceV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = EconomicCommandOccurrenceWireV1::deserialize(deserializer)?;
        Self::from_parts(wire.occurrence_version, wire.occurrence_id, wire.content)
            .map_err(de::Error::custom)
    }
}

/// Constructor-private structural witness for exact active-profile route binding.
///
/// This type is intentionally neither serializable nor a cryptographic authority
/// witness. A verifier must recompute it from the current profile and registry.
/// Its private fields prevent downstream code from minting the witness directly.
///
/// ```compile_fail
/// use zenodex_zrpf_protocol_v3::{
///     EconomicCommandOccurrenceV1, ProfileBoundEconomicCommandOccurrenceV1,
///     RouteReleaseV1,
/// };
///
/// fn forge<'a>(
///     occurrence: &'a EconomicCommandOccurrenceV1,
///     route_release: &'a RouteReleaseV1,
/// ) -> ProfileBoundEconomicCommandOccurrenceV1<'a> {
///     ProfileBoundEconomicCommandOccurrenceV1 { occurrence, route_release }
/// }
/// ```
///
/// ```compile_fail
/// use zenodex_zrpf_protocol_v3::ProfileBoundEconomicCommandOccurrenceV1;
///
/// fn require_serializable<T: serde::Serialize>() {}
/// fn cannot_serialize() {
///     require_serializable::<ProfileBoundEconomicCommandOccurrenceV1<'static>>();
/// }
/// ```
#[derive(Debug)]
#[must_use = "the profile-bound occurrence must be consumed by the next verification stage"]
pub struct ProfileBoundEconomicCommandOccurrenceV1<'a> {
    occurrence: &'a EconomicCommandOccurrenceV1,
    route_release: &'a RouteReleaseV1,
}

impl<'a> ProfileBoundEconomicCommandOccurrenceV1<'a> {
    pub const fn occurrence(&self) -> &'a EconomicCommandOccurrenceV1 {
        self.occurrence
    }

    pub const fn route_release(&self) -> &'a RouteReleaseV1 {
        self.route_release
    }
}

pub fn bind_economic_command_occurrence_to_active_profile_v1<'a>(
    active_profile: &EconomicProfileSnapshotV1,
    route_registry: &'a RouteReleaseRegistryV1,
    occurrence: &'a EconomicCommandOccurrenceV1,
) -> Result<ProfileBoundEconomicCommandOccurrenceV1<'a>, EconomicCommandOccurrenceErrorV1> {
    occurrence.validate_self_consistency()?;
    let content = occurrence.content();
    if content.profile_id() != active_profile.profile_id() {
        return Err(EconomicCommandOccurrenceErrorV1::ProfileIdMismatch);
    }
    if content.writer_epoch() != active_profile.content().writer_epoch() {
        return Err(EconomicCommandOccurrenceErrorV1::WriterEpochMismatch);
    }
    if active_profile
        .content()
        .registry_roots()
        .route_release_registry_root()
        != route_registry.canonical_root()?
    {
        return Err(EconomicCommandOccurrenceErrorV1::RouteRegistryRootMismatch);
    }
    let route_release = route_registry
        .routes()
        .iter()
        .find(|route| route.route_release_id() == content.route_release_id())
        .ok_or(EconomicCommandOccurrenceErrorV1::UnknownRouteRelease)?;
    if route_release.content().command_variant_root().as_bytes()
        != content
            .authorized_action()
            .record()
            .action_type_id()
            .as_bytes()
    {
        return Err(EconomicCommandOccurrenceErrorV1::CommandVariantMismatch);
    }
    Ok(ProfileBoundEconomicCommandOccurrenceV1 {
        occurrence,
        route_release,
    })
}

pub fn encode_economic_command_occurrence_v1(
    occurrence: &EconomicCommandOccurrenceV1,
) -> Result<Vec<u8>, EconomicCommandOccurrenceErrorV1> {
    occurrence.validate_self_consistency()?;
    let bytes = postcard::to_allocvec(occurrence)
        .map_err(|_| EconomicCommandOccurrenceErrorV1::PostcardDecode)?;
    require_bounded_input(bytes.len())?;
    Ok(bytes)
}

pub fn decode_exact_economic_command_occurrence_v1(
    bytes: &[u8],
) -> Result<EconomicCommandOccurrenceV1, EconomicCommandOccurrenceErrorV1> {
    require_bounded_input(bytes.len())?;
    let (wire, remainder) = postcard::take_from_bytes::<EconomicCommandOccurrenceWireV1>(bytes)
        .map_err(|_| EconomicCommandOccurrenceErrorV1::PostcardDecode)?;
    if !remainder.is_empty() {
        return Err(EconomicCommandOccurrenceErrorV1::TrailingBytes);
    }
    let occurrence = EconomicCommandOccurrenceV1::from_parts(
        wire.occurrence_version,
        wire.occurrence_id,
        wire.content,
    )?;
    if encode_economic_command_occurrence_v1(&occurrence)?.as_slice() != bytes {
        return Err(EconomicCommandOccurrenceErrorV1::NonCanonicalEncoding);
    }
    Ok(occurrence)
}

fn derive_occurrence_id(
    content: &EconomicCommandOccurrenceContentV1,
) -> Result<EconomicCommandOccurrenceIdV1, EconomicCommandOccurrenceErrorV1> {
    let domain_length = u16::try_from(OCCURRENCE_ID_DOMAIN_V1.len())
        .map_err(|_| EconomicCommandOccurrenceErrorV1::ArithmeticOverflow("hash_domain_length"))?;
    let mut hasher = Sha256::new();
    hasher.update(domain_length.to_be_bytes());
    hasher.update(OCCURRENCE_ID_DOMAIN_V1);
    hasher.update(ECONOMIC_COMMAND_OCCURRENCE_VERSION_V1.to_be_bytes());
    content.update_hasher(&mut hasher)?;
    EconomicCommandOccurrenceIdV1::new(hasher.finalize().into())
        .map_err(|_| EconomicCommandOccurrenceErrorV1::InvalidDerivedCommitment)
}

fn require_bounded_input(size: usize) -> Result<(), EconomicCommandOccurrenceErrorV1> {
    if size == 0 {
        return Err(EconomicCommandOccurrenceErrorV1::EmptyInput);
    }
    if size > MAX_ECONOMIC_COMMAND_OCCURRENCE_BYTES_V1 {
        return Err(EconomicCommandOccurrenceErrorV1::InputTooLarge {
            actual: size,
            maximum: MAX_ECONOMIC_COMMAND_OCCURRENCE_BYTES_V1,
        });
    }
    Ok(())
}
