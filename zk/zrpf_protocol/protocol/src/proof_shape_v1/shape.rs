use alloc::vec::Vec;
use core::fmt;

use serde::{
    de::{self, SeqAccess, Visitor},
    Deserialize, Deserializer, Serialize,
};
use sha2::Digest;

use super::hash::{binding_id, domain_hasher, proof_shape_id};
use super::{
    AllowedChildBindingIdV1, ProofResourceCeilingsV1, ProofShapeErrorV1, ProofShapeIdV1,
    ALLOWED_CHILD_BINDING_VERSION_V1, MAX_ALLOWED_CHILD_BINDINGS_V1, MAX_SHAPE_JOURNAL_BYTES_V1,
    PROOF_SHAPE_VERSION_V1,
};
use crate::{CommitmentV3, ProfileIdV3, ProgramIdV3};

const ALLOWED_CHILD_BINDING_ID_DOMAIN_V1: &[u8] = b"zkpf.allowed_child_binding_id.v1";
const PROOF_SHAPE_ID_DOMAIN_V1: &[u8] = b"zkpf.proof_shape_id.v1";

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AllowedChildBindingInputV1 {
    pub child_shape_id: ProofShapeIdV1,
    pub child_program_id: ProgramIdV3,
    pub child_profile_id: ProfileIdV3,
    pub child_journal_hash: CommitmentV3,
    pub max_child_journal_bytes: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct AllowedChildBindingV1 {
    binding_version: u16,
    binding_id: AllowedChildBindingIdV1,
    child_shape_id: ProofShapeIdV1,
    child_program_id: ProgramIdV3,
    child_profile_id: ProfileIdV3,
    child_journal_hash: CommitmentV3,
    max_child_journal_bytes: u64,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct AllowedChildBindingWireV1 {
    binding_version: u16,
    binding_id: AllowedChildBindingIdV1,
    child_shape_id: ProofShapeIdV1,
    child_program_id: ProgramIdV3,
    child_profile_id: ProfileIdV3,
    child_journal_hash: CommitmentV3,
    max_child_journal_bytes: u64,
}

impl AllowedChildBindingV1 {
    pub fn derive(input: AllowedChildBindingInputV1) -> Result<Self, ProofShapeErrorV1> {
        validate_binding_input(&input)?;
        let binding_id = derive_allowed_child_binding_id_v1(&input)?;
        let value = Self {
            binding_version: ALLOWED_CHILD_BINDING_VERSION_V1,
            binding_id,
            child_shape_id: input.child_shape_id,
            child_program_id: input.child_program_id,
            child_profile_id: input.child_profile_id,
            child_journal_hash: input.child_journal_hash,
            max_child_journal_bytes: input.max_child_journal_bytes,
        };
        value.validate()?;
        Ok(value)
    }

    pub fn validate(&self) -> Result<(), ProofShapeErrorV1> {
        if self.binding_version != ALLOWED_CHILD_BINDING_VERSION_V1 {
            return Err(ProofShapeErrorV1::InvalidVersion {
                field: "allowed_child_binding",
                actual: self.binding_version,
            });
        }
        let input = self.input();
        validate_binding_input(&input)?;
        if self.binding_id != derive_allowed_child_binding_id_v1(&input)? {
            return Err(ProofShapeErrorV1::InvalidDerivedIdentity(
                "allowed_child_binding_id",
            ));
        }
        Ok(())
    }

    fn input(&self) -> AllowedChildBindingInputV1 {
        AllowedChildBindingInputV1 {
            child_shape_id: self.child_shape_id,
            child_program_id: self.child_program_id,
            child_profile_id: self.child_profile_id,
            child_journal_hash: self.child_journal_hash,
            max_child_journal_bytes: self.max_child_journal_bytes,
        }
    }

    pub const fn binding_id(&self) -> AllowedChildBindingIdV1 {
        self.binding_id
    }

    pub const fn child_shape_id(&self) -> ProofShapeIdV1 {
        self.child_shape_id
    }

    pub const fn child_program_id(&self) -> ProgramIdV3 {
        self.child_program_id
    }

    pub const fn child_profile_id(&self) -> ProfileIdV3 {
        self.child_profile_id
    }

    pub const fn child_journal_hash(&self) -> CommitmentV3 {
        self.child_journal_hash
    }

    pub const fn max_child_journal_bytes(&self) -> u64 {
        self.max_child_journal_bytes
    }
}

impl<'de> Deserialize<'de> for AllowedChildBindingV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = AllowedChildBindingWireV1::deserialize(deserializer)?;
        let value = Self {
            binding_version: wire.binding_version,
            binding_id: wire.binding_id,
            child_shape_id: wire.child_shape_id,
            child_program_id: wire.child_program_id,
            child_profile_id: wire.child_profile_id,
            child_journal_hash: wire.child_journal_hash,
            max_child_journal_bytes: wire.max_child_journal_bytes,
        };
        value.validate().map_err(de::Error::custom)?;
        Ok(value)
    }
}

pub fn derive_allowed_child_binding_id_v1(
    input: &AllowedChildBindingInputV1,
) -> Result<AllowedChildBindingIdV1, ProofShapeErrorV1> {
    validate_binding_input(input)?;
    let mut hasher = domain_hasher(ALLOWED_CHILD_BINDING_ID_DOMAIN_V1)?;
    hasher.update(ALLOWED_CHILD_BINDING_VERSION_V1.to_be_bytes());
    hasher.update(input.child_shape_id.as_bytes());
    hasher.update(input.child_program_id.as_bytes());
    hasher.update(input.child_profile_id.as_bytes());
    hasher.update(input.child_journal_hash.as_bytes());
    hasher.update(input.max_child_journal_bytes.to_be_bytes());
    binding_id(hasher)
}

fn validate_binding_input(input: &AllowedChildBindingInputV1) -> Result<(), ProofShapeErrorV1> {
    if input.max_child_journal_bytes == 0
        || input.max_child_journal_bytes > MAX_SHAPE_JOURNAL_BYTES_V1
    {
        return Err(ProofShapeErrorV1::InvalidChildJournalByteLimit);
    }
    Ok(())
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ProofShapeKindV1 {
    Leaf,
    Aggregate,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofShapeInputV1 {
    pub shape_kind: ProofShapeKindV1,
    pub program_id: ProgramIdV3,
    pub profile_id: ProfileIdV3,
    pub resource_ceilings: ProofResourceCeilingsV1,
    pub allowed_child_bindings: Vec<AllowedChildBindingInputV1>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ProofShapeV1 {
    shape_version: u16,
    shape_id: ProofShapeIdV1,
    shape_kind: ProofShapeKindV1,
    program_id: ProgramIdV3,
    profile_id: ProfileIdV3,
    resource_ceilings: ProofResourceCeilingsV1,
    allowed_child_bindings: Vec<AllowedChildBindingV1>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ProofShapeWireV1 {
    shape_version: u16,
    shape_id: ProofShapeIdV1,
    shape_kind: ProofShapeKindV1,
    program_id: ProgramIdV3,
    profile_id: ProfileIdV3,
    resource_ceilings: ProofResourceCeilingsV1,
    #[serde(deserialize_with = "deserialize_bounded_allowed_bindings")]
    allowed_child_bindings: Vec<AllowedChildBindingV1>,
}

impl ProofShapeV1 {
    pub fn derive(input: ProofShapeInputV1) -> Result<Self, ProofShapeErrorV1> {
        if input.allowed_child_bindings.len() > MAX_ALLOWED_CHILD_BINDINGS_V1 {
            return Err(ProofShapeErrorV1::TooManyAllowedChildBindings {
                actual: input.allowed_child_bindings.len(),
                maximum: MAX_ALLOWED_CHILD_BINDINGS_V1,
            });
        }
        let mut allowed_child_bindings = input
            .allowed_child_bindings
            .into_iter()
            .map(AllowedChildBindingV1::derive)
            .collect::<Result<Vec<_>, _>>()?;
        allowed_child_bindings.sort_by_key(AllowedChildBindingV1::binding_id);
        let shape_id = derive_proof_shape_id_parts_v1(
            input.shape_kind,
            input.program_id,
            input.profile_id,
            input.resource_ceilings,
            &allowed_child_bindings,
        )?;
        let value = Self {
            shape_version: PROOF_SHAPE_VERSION_V1,
            shape_id,
            shape_kind: input.shape_kind,
            program_id: input.program_id,
            profile_id: input.profile_id,
            resource_ceilings: input.resource_ceilings,
            allowed_child_bindings,
        };
        value.validate()?;
        Ok(value)
    }

    pub fn validate(&self) -> Result<(), ProofShapeErrorV1> {
        if self.shape_version != PROOF_SHAPE_VERSION_V1 {
            return Err(ProofShapeErrorV1::InvalidVersion {
                field: "proof_shape",
                actual: self.shape_version,
            });
        }
        self.resource_ceilings.validate()?;
        validate_allowed_bindings(&self.allowed_child_bindings)?;
        validate_shape_kind(self)?;
        if self.shape_id != derive_proof_shape_id_v1(self)? {
            return Err(ProofShapeErrorV1::InvalidDerivedIdentity("proof_shape_id"));
        }
        Ok(())
    }

    pub const fn shape_id(&self) -> ProofShapeIdV1 {
        self.shape_id
    }

    pub const fn shape_kind(&self) -> ProofShapeKindV1 {
        self.shape_kind
    }

    pub const fn program_id(&self) -> ProgramIdV3 {
        self.program_id
    }

    pub const fn profile_id(&self) -> ProfileIdV3 {
        self.profile_id
    }

    pub const fn resource_ceilings(&self) -> ProofResourceCeilingsV1 {
        self.resource_ceilings
    }

    pub fn allowed_child_bindings(&self) -> &[AllowedChildBindingV1] {
        &self.allowed_child_bindings
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

impl<'de> Deserialize<'de> for ProofShapeV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = ProofShapeWireV1::deserialize(deserializer)?;
        let value = Self {
            shape_version: wire.shape_version,
            shape_id: wire.shape_id,
            shape_kind: wire.shape_kind,
            program_id: wire.program_id,
            profile_id: wire.profile_id,
            resource_ceilings: wire.resource_ceilings,
            allowed_child_bindings: wire.allowed_child_bindings,
        };
        value.validate().map_err(de::Error::custom)?;
        Ok(value)
    }
}

fn validate_allowed_bindings(bindings: &[AllowedChildBindingV1]) -> Result<(), ProofShapeErrorV1> {
    if bindings.len() > MAX_ALLOWED_CHILD_BINDINGS_V1 {
        return Err(ProofShapeErrorV1::TooManyAllowedChildBindings {
            actual: bindings.len(),
            maximum: MAX_ALLOWED_CHILD_BINDINGS_V1,
        });
    }
    for (index, binding) in bindings.iter().enumerate() {
        binding.validate()?;
        if bindings[..index]
            .iter()
            .any(|prior| prior.binding_id() == binding.binding_id())
        {
            return Err(ProofShapeErrorV1::DuplicateAllowedChildBinding);
        }
        if index > 0 && bindings[index - 1].binding_id() > binding.binding_id() {
            return Err(ProofShapeErrorV1::NonCanonicalAllowedChildBindingOrder);
        }
        if bindings[..index]
            .iter()
            .any(|prior| prior.child_journal_hash() == binding.child_journal_hash())
        {
            return Err(ProofShapeErrorV1::DuplicateChildJournal);
        }
    }
    Ok(())
}

fn validate_shape_kind(shape: &ProofShapeV1) -> Result<(), ProofShapeErrorV1> {
    let resources = shape.resource_ceilings;
    match shape.shape_kind {
        ProofShapeKindV1::Leaf => {
            if !shape.allowed_child_bindings.is_empty()
                || resources.max_assumptions() != 0
                || resources.max_total_child_journal_bytes() != 0
            {
                return Err(ProofShapeErrorV1::LeafHasChildContract);
            }
        }
        ProofShapeKindV1::Aggregate => {
            if shape.allowed_child_bindings.is_empty()
                || resources.max_assumptions() == 0
                || resources.max_total_child_journal_bytes() == 0
            {
                return Err(ProofShapeErrorV1::AggregateHasNoChildContract);
            }
            if shape.allowed_child_bindings.iter().any(|binding| {
                binding.max_child_journal_bytes() > resources.max_total_child_journal_bytes()
            }) {
                return Err(ProofShapeErrorV1::InvalidChildJournalByteLimit);
            }
        }
    }
    Ok(())
}

fn derive_proof_shape_id_v1(shape: &ProofShapeV1) -> Result<ProofShapeIdV1, ProofShapeErrorV1> {
    derive_proof_shape_id_parts_v1(
        shape.shape_kind,
        shape.program_id,
        shape.profile_id,
        shape.resource_ceilings,
        &shape.allowed_child_bindings,
    )
}

fn derive_proof_shape_id_parts_v1(
    shape_kind: ProofShapeKindV1,
    program_id: ProgramIdV3,
    profile_id: ProfileIdV3,
    resources: ProofResourceCeilingsV1,
    allowed_child_bindings: &[AllowedChildBindingV1],
) -> Result<ProofShapeIdV1, ProofShapeErrorV1> {
    let mut hasher = domain_hasher(PROOF_SHAPE_ID_DOMAIN_V1)?;
    hasher.update(PROOF_SHAPE_VERSION_V1.to_be_bytes());
    hasher.update([shape_kind_tag(shape_kind)]);
    hasher.update(program_id.as_bytes());
    hasher.update(profile_id.as_bytes());
    for value in [
        resources.max_input_bytes(),
        resources.max_journal_bytes(),
        resources.max_proof_bytes(),
        resources.max_cycles(),
        resources.max_memory_bytes(),
        resources.max_assumptions(),
        resources.max_total_child_journal_bytes(),
    ] {
        hasher.update(value.to_be_bytes());
    }
    let count = u16::try_from(allowed_child_bindings.len())
        .map_err(|_| ProofShapeErrorV1::ArithmeticOverflow("allowed_child_binding_count"))?;
    hasher.update(count.to_be_bytes());
    for binding in allowed_child_bindings {
        hasher.update(binding.binding_id().as_bytes());
    }
    proof_shape_id(hasher)
}

const fn shape_kind_tag(kind: ProofShapeKindV1) -> u8 {
    match kind {
        ProofShapeKindV1::Leaf => 0,
        ProofShapeKindV1::Aggregate => 1,
    }
}

fn deserialize_bounded_allowed_bindings<'de, D>(
    deserializer: D,
) -> Result<Vec<AllowedChildBindingV1>, D::Error>
where
    D: Deserializer<'de>,
{
    struct BindingsVisitor;

    impl<'de> Visitor<'de> for BindingsVisitor {
        type Value = Vec<AllowedChildBindingV1>;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(
                formatter,
                "at most {MAX_ALLOWED_CHILD_BINDINGS_V1} child bindings"
            )
        }

        fn visit_seq<A>(self, mut sequence: A) -> Result<Self::Value, A::Error>
        where
            A: SeqAccess<'de>,
        {
            let declared = sequence.size_hint().unwrap_or(0);
            if declared > MAX_ALLOWED_CHILD_BINDINGS_V1 {
                return Err(de::Error::custom(
                    ProofShapeErrorV1::TooManyAllowedChildBindings {
                        actual: declared,
                        maximum: MAX_ALLOWED_CHILD_BINDINGS_V1,
                    },
                ));
            }
            let mut values = Vec::with_capacity(declared);
            while let Some(value) = sequence.next_element()? {
                if values.len() == MAX_ALLOWED_CHILD_BINDINGS_V1 {
                    return Err(de::Error::custom(
                        ProofShapeErrorV1::TooManyAllowedChildBindings {
                            actual: MAX_ALLOWED_CHILD_BINDINGS_V1 + 1,
                            maximum: MAX_ALLOWED_CHILD_BINDINGS_V1,
                        },
                    ));
                }
                values.push(value);
            }
            Ok(values)
        }
    }

    deserializer.deserialize_seq(BindingsVisitor)
}
