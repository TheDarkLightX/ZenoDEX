use alloc::vec::Vec;
use core::fmt;

use serde::{
    de::{self, SeqAccess, Visitor},
    Deserialize, Deserializer, Serialize,
};
use sha2::Digest;

use super::hash::{domain_hasher, registry_id};
use super::{
    resolve_assumptions_v1, AssumptionManifestV1, AssumptionResolutionV1, ProofShapeErrorV1,
    ProofShapeIdV1, ProofShapeRegistryIdV1, ProofShapeV1, ResolvedChildClaimV1,
    MAX_PROOF_SHAPE_REGISTRY_ENTRIES_V1, PROOF_SHAPE_REGISTRY_VERSION_V1,
};

const PROOF_SHAPE_REGISTRY_ID_DOMAIN_V1: &[u8] = b"zkpf.proof_shape_registry_id.v1";

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ProofShapeRegistryV1 {
    registry_version: u16,
    registry_id: ProofShapeRegistryIdV1,
    shapes: Vec<ProofShapeV1>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ProofShapeRegistryWireV1 {
    registry_version: u16,
    registry_id: ProofShapeRegistryIdV1,
    #[serde(deserialize_with = "deserialize_bounded_shapes")]
    shapes: Vec<ProofShapeV1>,
}

impl ProofShapeRegistryV1 {
    pub fn derive(mut shapes: Vec<ProofShapeV1>) -> Result<Self, ProofShapeErrorV1> {
        validate_shape_count(shapes.len())?;
        shapes.sort_by_key(ProofShapeV1::shape_id);
        let registry_id = derive_registry_id_parts_v1(&shapes)?;
        let value = Self {
            registry_version: PROOF_SHAPE_REGISTRY_VERSION_V1,
            registry_id,
            shapes,
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
        validate_shapes(&self.shapes)?;
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

    pub fn shapes(&self) -> &[ProofShapeV1] {
        &self.shapes
    }

    pub fn shape(&self, shape_id: ProofShapeIdV1) -> Option<&ProofShapeV1> {
        self.shapes
            .iter()
            .find(|shape| shape.shape_id() == shape_id)
    }

    pub fn resolve(
        &self,
        manifest: &AssumptionManifestV1,
        claims: Vec<ResolvedChildClaimV1>,
    ) -> Result<AssumptionResolutionV1, ProofShapeErrorV1> {
        let shape = self
            .shape(manifest.proof_shape_id())
            .ok_or(ProofShapeErrorV1::UnknownProofShape)?;
        resolve_assumptions_v1(shape, manifest, claims)
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
            shapes: wire.shapes,
        };
        value.validate().map_err(de::Error::custom)?;
        Ok(value)
    }
}

fn validate_shapes(shapes: &[ProofShapeV1]) -> Result<(), ProofShapeErrorV1> {
    validate_shape_count(shapes.len())?;
    for (index, shape) in shapes.iter().enumerate() {
        shape.validate()?;
        if shapes[..index]
            .iter()
            .any(|prior| prior.shape_id() == shape.shape_id())
        {
            return Err(ProofShapeErrorV1::DuplicateProofShape);
        }
        if index > 0 && shapes[index - 1].shape_id() > shape.shape_id() {
            return Err(ProofShapeErrorV1::NonCanonicalRegistryOrder);
        }
    }
    Ok(())
}

fn validate_shape_count(count: usize) -> Result<(), ProofShapeErrorV1> {
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
    derive_registry_id_parts_v1(&registry.shapes)
}

fn derive_registry_id_parts_v1(
    shapes: &[ProofShapeV1],
) -> Result<ProofShapeRegistryIdV1, ProofShapeErrorV1> {
    let mut hasher = domain_hasher(PROOF_SHAPE_REGISTRY_ID_DOMAIN_V1)?;
    hasher.update(PROOF_SHAPE_REGISTRY_VERSION_V1.to_be_bytes());
    let count = u16::try_from(shapes.len())
        .map_err(|_| ProofShapeErrorV1::ArithmeticOverflow("registry_entry_count"))?;
    hasher.update(count.to_be_bytes());
    for shape in shapes {
        hasher.update(shape.shape_id().as_bytes());
    }
    registry_id(hasher)
}

fn deserialize_bounded_shapes<'de, D>(deserializer: D) -> Result<Vec<ProofShapeV1>, D::Error>
where
    D: Deserializer<'de>,
{
    struct ShapesVisitor;

    impl<'de> Visitor<'de> for ShapesVisitor {
        type Value = Vec<ProofShapeV1>;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(
                formatter,
                "at most {MAX_PROOF_SHAPE_REGISTRY_ENTRIES_V1} proof shapes"
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

    deserializer.deserialize_seq(ShapesVisitor)
}
