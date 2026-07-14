use alloc::vec::Vec;
use core::fmt;

use serde::{
    de::{self, SeqAccess, Visitor},
    Deserialize, Deserializer, Serialize,
};
use sha2::Digest;

use super::hash::{domain_hasher, registry_id};
use super::resolution::validate_shape_manifest_contract_v1;
use super::{
    resolve_assumptions_v1, AssumptionManifestIdV1, AssumptionManifestV1, AssumptionResolutionV1,
    ProofShapeErrorV1, ProofShapeIdV1, ProofShapeRegistryIdV1, ProofShapeV1, ResolvedChildClaimV1,
    MAX_PROOF_SHAPE_REGISTRY_ENTRIES_V1, PROOF_SHAPE_REGISTRY_VERSION_V1,
};

const PROOF_SHAPE_REGISTRY_ID_DOMAIN_V1: &[u8] = b"zkpf.proof_shape_registry_id.v1";

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ProofShapeRegistrationV1 {
    shape: ProofShapeV1,
    assumption_manifest: AssumptionManifestV1,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ProofShapeRegistrationWireV1 {
    shape: ProofShapeV1,
    assumption_manifest: AssumptionManifestV1,
}

impl ProofShapeRegistrationV1 {
    pub fn new(
        shape: ProofShapeV1,
        assumption_manifest: AssumptionManifestV1,
    ) -> Result<Self, ProofShapeErrorV1> {
        validate_shape_manifest_contract_v1(&shape, &assumption_manifest)?;
        Ok(Self {
            shape,
            assumption_manifest,
        })
    }

    pub fn validate(&self) -> Result<(), ProofShapeErrorV1> {
        validate_shape_manifest_contract_v1(&self.shape, &self.assumption_manifest)
    }

    pub const fn shape(&self) -> &ProofShapeV1 {
        &self.shape
    }

    pub const fn assumption_manifest(&self) -> &AssumptionManifestV1 {
        &self.assumption_manifest
    }
}

impl<'de> Deserialize<'de> for ProofShapeRegistrationV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = ProofShapeRegistrationWireV1::deserialize(deserializer)?;
        Self::new(wire.shape, wire.assumption_manifest).map_err(de::Error::custom)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ProofShapeRegistryV1 {
    registry_version: u16,
    registry_id: ProofShapeRegistryIdV1,
    registrations: Vec<ProofShapeRegistrationV1>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ProofShapeRegistryWireV1 {
    registry_version: u16,
    registry_id: ProofShapeRegistryIdV1,
    #[serde(deserialize_with = "deserialize_bounded_registrations")]
    registrations: Vec<ProofShapeRegistrationV1>,
}

impl ProofShapeRegistryV1 {
    pub fn derive(
        mut registrations: Vec<ProofShapeRegistrationV1>,
    ) -> Result<Self, ProofShapeErrorV1> {
        validate_registration_count(registrations.len())?;
        registrations.sort_by_key(|registration| registration.shape().shape_id());
        let registry_id = derive_registry_id_parts_v1(&registrations)?;
        let value = Self {
            registry_version: PROOF_SHAPE_REGISTRY_VERSION_V1,
            registry_id,
            registrations,
        };
        value.validate()?;
        Ok(value)
    }

    pub fn validate(&self) -> Result<(), ProofShapeErrorV1> {
        if self.registry_version != PROOF_SHAPE_REGISTRY_VERSION_V1 {
            return Err(ProofShapeErrorV1::InvalidVersion {
                field: "proof_shape_registry",
                actual: self.registry_version,
            });
        }
        validate_registrations(&self.registrations)?;
        if self.registry_id != derive_registry_id_v1(self)? {
            return Err(ProofShapeErrorV1::InvalidDerivedIdentity(
                "proof_shape_registry_id",
            ));
        }
        Ok(())
    }

    pub const fn registry_id(&self) -> ProofShapeRegistryIdV1 {
        self.registry_id
    }

    pub fn registrations(&self) -> &[ProofShapeRegistrationV1] {
        &self.registrations
    }

    pub fn shape(&self, shape_id: ProofShapeIdV1) -> Option<&ProofShapeV1> {
        self.registrations
            .iter()
            .find(|registration| registration.shape().shape_id() == shape_id)
            .map(ProofShapeRegistrationV1::shape)
    }

    pub fn assumption_manifest(
        &self,
        manifest_id: AssumptionManifestIdV1,
    ) -> Option<&AssumptionManifestV1> {
        self.registrations
            .iter()
            .find(|registration| registration.assumption_manifest().manifest_id() == manifest_id)
            .map(ProofShapeRegistrationV1::assumption_manifest)
    }

    pub fn resolve(
        &self,
        manifest_id: AssumptionManifestIdV1,
        claims: Vec<ResolvedChildClaimV1>,
    ) -> Result<AssumptionResolutionV1, ProofShapeErrorV1> {
        let registration = self
            .registrations
            .iter()
            .find(|registration| registration.assumption_manifest().manifest_id() == manifest_id)
            .ok_or(ProofShapeErrorV1::UnknownAssumptionManifest)?;
        resolve_assumptions_v1(
            registration.shape(),
            registration.assumption_manifest(),
            claims,
        )
    }

    pub const fn proof_authority(&self) -> bool {
        false
    }

    pub const fn release_authority(&self) -> bool {
        false
    }

    pub const fn settlement_authority(&self) -> bool {
        false
    }

    pub const fn production_authority(&self) -> bool {
        false
    }
}

impl<'de> Deserialize<'de> for ProofShapeRegistryV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = ProofShapeRegistryWireV1::deserialize(deserializer)?;
        let value = Self {
            registry_version: wire.registry_version,
            registry_id: wire.registry_id,
            registrations: wire.registrations,
        };
        value.validate().map_err(de::Error::custom)?;
        Ok(value)
    }
}

fn validate_registrations(
    registrations: &[ProofShapeRegistrationV1],
) -> Result<(), ProofShapeErrorV1> {
    validate_registration_count(registrations.len())?;
    for (index, registration) in registrations.iter().enumerate() {
        registration.validate()?;
        if registrations[..index]
            .iter()
            .any(|prior| prior.shape().shape_id() == registration.shape().shape_id())
        {
            return Err(ProofShapeErrorV1::DuplicateProofShape);
        }
        if index > 0
            && registrations[index - 1].shape().shape_id() > registration.shape().shape_id()
        {
            return Err(ProofShapeErrorV1::NonCanonicalRegistryOrder);
        }
        if registrations[..index].iter().any(|prior| {
            prior.assumption_manifest().manifest_id()
                == registration.assumption_manifest().manifest_id()
        }) {
            return Err(ProofShapeErrorV1::DuplicateAssumptionManifest);
        }
    }
    Ok(())
}

fn validate_registration_count(count: usize) -> Result<(), ProofShapeErrorV1> {
    if count == 0 {
        return Err(ProofShapeErrorV1::EmptyRegistry);
    }
    if count > MAX_PROOF_SHAPE_REGISTRY_ENTRIES_V1 {
        return Err(ProofShapeErrorV1::TooManyRegistryEntries {
            actual: count,
            maximum: MAX_PROOF_SHAPE_REGISTRY_ENTRIES_V1,
        });
    }
    Ok(())
}

fn derive_registry_id_v1(
    registry: &ProofShapeRegistryV1,
) -> Result<ProofShapeRegistryIdV1, ProofShapeErrorV1> {
    derive_registry_id_parts_v1(&registry.registrations)
}

fn derive_registry_id_parts_v1(
    registrations: &[ProofShapeRegistrationV1],
) -> Result<ProofShapeRegistryIdV1, ProofShapeErrorV1> {
    let mut hasher = domain_hasher(PROOF_SHAPE_REGISTRY_ID_DOMAIN_V1)?;
    hasher.update(PROOF_SHAPE_REGISTRY_VERSION_V1.to_be_bytes());
    let count = u16::try_from(registrations.len())
        .map_err(|_| ProofShapeErrorV1::ArithmeticOverflow("registry_entry_count"))?;
    hasher.update(count.to_be_bytes());
    for registration in registrations {
        hasher.update(registration.shape().shape_id().as_bytes());
        hasher.update(registration.assumption_manifest().manifest_id().as_bytes());
    }
    registry_id(hasher)
}

fn deserialize_bounded_registrations<'de, D>(
    deserializer: D,
) -> Result<Vec<ProofShapeRegistrationV1>, D::Error>
where
    D: Deserializer<'de>,
{
    struct RegistrationsVisitor;

    impl<'de> Visitor<'de> for RegistrationsVisitor {
        type Value = Vec<ProofShapeRegistrationV1>;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(
                formatter,
                "at most {MAX_PROOF_SHAPE_REGISTRY_ENTRIES_V1} proof shape registrations"
            )
        }

        fn visit_seq<A>(self, mut sequence: A) -> Result<Self::Value, A::Error>
        where
            A: SeqAccess<'de>,
        {
            let declared = sequence.size_hint().unwrap_or(0);
            if declared > MAX_PROOF_SHAPE_REGISTRY_ENTRIES_V1 {
                return Err(de::Error::custom(
                    ProofShapeErrorV1::TooManyRegistryEntries {
                        actual: declared,
                        maximum: MAX_PROOF_SHAPE_REGISTRY_ENTRIES_V1,
                    },
                ));
            }
            let mut values = Vec::with_capacity(declared);
            while let Some(value) = sequence.next_element()? {
                if values.len() == MAX_PROOF_SHAPE_REGISTRY_ENTRIES_V1 {
                    return Err(de::Error::custom(
                        ProofShapeErrorV1::TooManyRegistryEntries {
                            actual: MAX_PROOF_SHAPE_REGISTRY_ENTRIES_V1 + 1,
                            maximum: MAX_PROOF_SHAPE_REGISTRY_ENTRIES_V1,
                        },
                    ));
                }
                values.push(value);
            }
            Ok(values)
        }
    }

    deserializer.deserialize_seq(RegistrationsVisitor)
}
