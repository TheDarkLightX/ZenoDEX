use alloc::vec::Vec;
use core::fmt;

use serde::{
    de::{self, SeqAccess, Visitor},
    Deserialize, Deserializer, Serialize,
};
use sha2::Digest;

use super::hash::{assumption_id, domain_hasher, manifest_id};
use super::{
    AllowedChildBindingIdV1, AssumptionIdV1, AssumptionManifestIdV1, ProofShapeErrorV1,
    ProofShapeIdV1, ASSUMPTION_MANIFEST_VERSION_V1, ASSUMPTION_REQUIREMENT_VERSION_V1,
    MAX_REQUIRED_ASSUMPTIONS_V1,
};

const ASSUMPTION_ID_DOMAIN_V1: &[u8] = b"zkpf.assumption_id.v1";
const ASSUMPTION_MANIFEST_ID_DOMAIN_V1: &[u8] = b"zkpf.assumption_manifest_id.v1";

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AssumptionRequirementInputV1 {
    pub slot: u16,
    pub allowed_child_binding_id: AllowedChildBindingIdV1,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct AssumptionRequirementV1 {
    requirement_version: u16,
    assumption_id: AssumptionIdV1,
    slot: u16,
    allowed_child_binding_id: AllowedChildBindingIdV1,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct AssumptionRequirementWireV1 {
    requirement_version: u16,
    assumption_id: AssumptionIdV1,
    slot: u16,
    allowed_child_binding_id: AllowedChildBindingIdV1,
}

impl AssumptionRequirementV1 {
    pub fn derive(
        proof_shape_id: ProofShapeIdV1,
        input: AssumptionRequirementInputV1,
    ) -> Result<Self, ProofShapeErrorV1> {
        let assumption_id = derive_assumption_id_v1(proof_shape_id, &input)?;
        let value = Self {
            requirement_version: ASSUMPTION_REQUIREMENT_VERSION_V1,
            assumption_id,
            slot: input.slot,
            allowed_child_binding_id: input.allowed_child_binding_id,
        };
        value.validate(proof_shape_id)?;
        Ok(value)
    }

    pub fn validate(&self, proof_shape_id: ProofShapeIdV1) -> Result<(), ProofShapeErrorV1> {
        if self.requirement_version != ASSUMPTION_REQUIREMENT_VERSION_V1 {
            return Err(ProofShapeErrorV1::InvalidVersion {
                field: "assumption_requirement",
                actual: self.requirement_version,
            });
        }
        let input = self.input();
        if self.assumption_id != derive_assumption_id_v1(proof_shape_id, &input)? {
            return Err(ProofShapeErrorV1::InvalidDerivedIdentity("assumption_id"));
        }
        Ok(())
    }

    fn input(&self) -> AssumptionRequirementInputV1 {
        AssumptionRequirementInputV1 {
            slot: self.slot,
            allowed_child_binding_id: self.allowed_child_binding_id,
        }
    }

    pub const fn assumption_id(&self) -> AssumptionIdV1 {
        self.assumption_id
    }

    pub const fn slot(&self) -> u16 {
        self.slot
    }

    pub const fn allowed_child_binding_id(&self) -> AllowedChildBindingIdV1 {
        self.allowed_child_binding_id
    }
}

pub fn derive_assumption_id_v1(
    proof_shape_id: ProofShapeIdV1,
    input: &AssumptionRequirementInputV1,
) -> Result<AssumptionIdV1, ProofShapeErrorV1> {
    let mut hasher = domain_hasher(ASSUMPTION_ID_DOMAIN_V1)?;
    hasher.update(ASSUMPTION_REQUIREMENT_VERSION_V1.to_be_bytes());
    hasher.update(proof_shape_id.as_bytes());
    hasher.update(input.slot.to_be_bytes());
    hasher.update(input.allowed_child_binding_id.as_bytes());
    assumption_id(hasher)
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AssumptionManifestInputV1 {
    pub proof_shape_id: ProofShapeIdV1,
    pub required_assumptions: Vec<AssumptionRequirementInputV1>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct AssumptionManifestV1 {
    manifest_version: u16,
    manifest_id: AssumptionManifestIdV1,
    proof_shape_id: ProofShapeIdV1,
    required_assumptions: Vec<AssumptionRequirementV1>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct AssumptionManifestWireV1 {
    manifest_version: u16,
    manifest_id: AssumptionManifestIdV1,
    proof_shape_id: ProofShapeIdV1,
    #[serde(deserialize_with = "deserialize_bounded_requirement_wires")]
    required_assumptions: Vec<AssumptionRequirementWireV1>,
}

impl AssumptionManifestV1 {
    pub fn derive(input: AssumptionManifestInputV1) -> Result<Self, ProofShapeErrorV1> {
        if input.required_assumptions.len() > MAX_REQUIRED_ASSUMPTIONS_V1 {
            return Err(ProofShapeErrorV1::TooManyRequiredAssumptions {
                actual: input.required_assumptions.len(),
                maximum: MAX_REQUIRED_ASSUMPTIONS_V1,
            });
        }
        let mut required_assumptions = input
            .required_assumptions
            .into_iter()
            .map(|requirement| AssumptionRequirementV1::derive(input.proof_shape_id, requirement))
            .collect::<Result<Vec<_>, _>>()?;
        required_assumptions.sort_by_key(AssumptionRequirementV1::slot);
        let manifest_id =
            derive_assumption_manifest_id_parts_v1(input.proof_shape_id, &required_assumptions)?;
        let value = Self {
            manifest_version: ASSUMPTION_MANIFEST_VERSION_V1,
            manifest_id,
            proof_shape_id: input.proof_shape_id,
            required_assumptions,
        };
        value.validate()?;
        Ok(value)
    }

    pub fn validate(&self) -> Result<(), ProofShapeErrorV1> {
        if self.manifest_version != ASSUMPTION_MANIFEST_VERSION_V1 {
            return Err(ProofShapeErrorV1::InvalidVersion {
                field: "assumption_manifest",
                actual: self.manifest_version,
            });
        }
        validate_requirements(self.proof_shape_id, &self.required_assumptions)?;
        if self.manifest_id != derive_assumption_manifest_id_v1(self)? {
            return Err(ProofShapeErrorV1::InvalidDerivedIdentity(
                "assumption_manifest_id",
            ));
        }
        Ok(())
    }

    pub const fn manifest_id(&self) -> AssumptionManifestIdV1 {
        self.manifest_id
    }

    pub const fn proof_shape_id(&self) -> ProofShapeIdV1 {
        self.proof_shape_id
    }

    pub fn required_assumptions(&self) -> &[AssumptionRequirementV1] {
        &self.required_assumptions
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

impl<'de> Deserialize<'de> for AssumptionManifestV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = AssumptionManifestWireV1::deserialize(deserializer)?;
        let required_assumptions = wire
            .required_assumptions
            .into_iter()
            .map(|requirement| AssumptionRequirementV1 {
                requirement_version: requirement.requirement_version,
                assumption_id: requirement.assumption_id,
                slot: requirement.slot,
                allowed_child_binding_id: requirement.allowed_child_binding_id,
            })
            .collect();
        let value = Self {
            manifest_version: wire.manifest_version,
            manifest_id: wire.manifest_id,
            proof_shape_id: wire.proof_shape_id,
            required_assumptions,
        };
        value.validate().map_err(de::Error::custom)?;
        Ok(value)
    }
}

fn validate_requirements(
    proof_shape_id: ProofShapeIdV1,
    requirements: &[AssumptionRequirementV1],
) -> Result<(), ProofShapeErrorV1> {
    if requirements.len() > MAX_REQUIRED_ASSUMPTIONS_V1 {
        return Err(ProofShapeErrorV1::TooManyRequiredAssumptions {
            actual: requirements.len(),
            maximum: MAX_REQUIRED_ASSUMPTIONS_V1,
        });
    }
    for requirement in requirements {
        requirement.validate(proof_shape_id)?;
    }
    for (index, requirement) in requirements.iter().enumerate() {
        for prior in &requirements[..index] {
            if prior.slot() == requirement.slot() {
                return Err(ProofShapeErrorV1::DuplicateAssumptionSlot);
            }
            if prior.allowed_child_binding_id() == requirement.allowed_child_binding_id() {
                return Err(ProofShapeErrorV1::DuplicateRequiredBinding);
            }
        }
    }
    for (index, requirement) in requirements.iter().enumerate() {
        let expected = u16::try_from(index)
            .map_err(|_| ProofShapeErrorV1::ArithmeticOverflow("assumption_slot"))?;
        if requirement.slot() > expected {
            return Err(ProofShapeErrorV1::NonDenseAssumptionSlots);
        }
        if requirement.slot() < expected {
            return Err(ProofShapeErrorV1::NonCanonicalAssumptionOrder);
        }
    }
    Ok(())
}

fn derive_assumption_manifest_id_v1(
    manifest: &AssumptionManifestV1,
) -> Result<AssumptionManifestIdV1, ProofShapeErrorV1> {
    derive_assumption_manifest_id_parts_v1(manifest.proof_shape_id, &manifest.required_assumptions)
}

fn derive_assumption_manifest_id_parts_v1(
    proof_shape_id: ProofShapeIdV1,
    required_assumptions: &[AssumptionRequirementV1],
) -> Result<AssumptionManifestIdV1, ProofShapeErrorV1> {
    let mut hasher = domain_hasher(ASSUMPTION_MANIFEST_ID_DOMAIN_V1)?;
    hasher.update(ASSUMPTION_MANIFEST_VERSION_V1.to_be_bytes());
    hasher.update(proof_shape_id.as_bytes());
    let count = u16::try_from(required_assumptions.len())
        .map_err(|_| ProofShapeErrorV1::ArithmeticOverflow("required_assumption_count"))?;
    hasher.update(count.to_be_bytes());
    for requirement in required_assumptions {
        hasher.update(requirement.assumption_id().as_bytes());
    }
    manifest_id(hasher)
}

fn deserialize_bounded_requirement_wires<'de, D>(
    deserializer: D,
) -> Result<Vec<AssumptionRequirementWireV1>, D::Error>
where
    D: Deserializer<'de>,
{
    struct RequirementsVisitor;

    impl<'de> Visitor<'de> for RequirementsVisitor {
        type Value = Vec<AssumptionRequirementWireV1>;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(
                formatter,
                "at most {MAX_REQUIRED_ASSUMPTIONS_V1} assumptions"
            )
        }

        fn visit_seq<A>(self, mut sequence: A) -> Result<Self::Value, A::Error>
        where
            A: SeqAccess<'de>,
        {
            let declared = sequence.size_hint().unwrap_or(0);
            if declared > MAX_REQUIRED_ASSUMPTIONS_V1 {
                return Err(de::Error::custom(
                    ProofShapeErrorV1::TooManyRequiredAssumptions {
                        actual: declared,
                        maximum: MAX_REQUIRED_ASSUMPTIONS_V1,
                    },
                ));
            }
            let mut values = Vec::with_capacity(declared);
            while let Some(value) = sequence.next_element()? {
                if values.len() == MAX_REQUIRED_ASSUMPTIONS_V1 {
                    return Err(de::Error::custom(
                        ProofShapeErrorV1::TooManyRequiredAssumptions {
                            actual: MAX_REQUIRED_ASSUMPTIONS_V1 + 1,
                            maximum: MAX_REQUIRED_ASSUMPTIONS_V1,
                        },
                    ));
                }
                values.push(value);
            }
            Ok(values)
        }
    }

    deserializer.deserialize_seq(RequirementsVisitor)
}
