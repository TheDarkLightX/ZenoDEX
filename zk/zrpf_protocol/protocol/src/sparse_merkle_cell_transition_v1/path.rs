use core::fmt;

use serde::{
    de::{self, IgnoredAny, SeqAccess, Visitor},
    ser::SerializeTuple,
    Deserialize, Deserializer, Serialize, Serializer,
};

use super::SPARSE_MERKLE_TREE_DEPTH_V1;
use crate::CommitmentV3;

/// Exactly one nonzero sibling commitment for every root-to-leaf path depth.
///
/// Index zero is the root decision; index 255 is the leaf-parent decision.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SparseMerkleSiblingPathV1([CommitmentV3; SPARSE_MERKLE_TREE_DEPTH_V1]);

impl SparseMerkleSiblingPathV1 {
    pub const fn new(siblings: [CommitmentV3; SPARSE_MERKLE_TREE_DEPTH_V1]) -> Self {
        Self(siblings)
    }

    pub const fn as_array(&self) -> &[CommitmentV3; SPARSE_MERKLE_TREE_DEPTH_V1] {
        &self.0
    }

    pub const fn into_array(self) -> [CommitmentV3; SPARSE_MERKLE_TREE_DEPTH_V1] {
        self.0
    }
}

impl Serialize for SparseMerkleSiblingPathV1 {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut tuple = serializer.serialize_tuple(SPARSE_MERKLE_TREE_DEPTH_V1)?;
        for sibling in &self.0 {
            tuple.serialize_element(sibling)?;
        }
        tuple.end()
    }
}

impl<'de> Deserialize<'de> for SparseMerkleSiblingPathV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct SiblingPathVisitor;

        impl<'de> Visitor<'de> for SiblingPathVisitor {
            type Value = SparseMerkleSiblingPathV1;

            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(
                    formatter,
                    "exactly {SPARSE_MERKLE_TREE_DEPTH_V1} nonzero sibling commitments"
                )
            }

            fn visit_seq<A>(self, mut sequence: A) -> Result<Self::Value, A::Error>
            where
                A: SeqAccess<'de>,
            {
                let sentinel = CommitmentV3::new([1_u8; 32]).map_err(de::Error::custom)?;
                let mut siblings = [sentinel; SPARSE_MERKLE_TREE_DEPTH_V1];
                for (depth, sibling) in siblings.iter_mut().enumerate() {
                    *sibling = sequence
                        .next_element()?
                        .ok_or_else(|| de::Error::invalid_length(depth, &self))?;
                }
                if sequence.next_element::<IgnoredAny>()?.is_some() {
                    return Err(de::Error::invalid_length(
                        SPARSE_MERKLE_TREE_DEPTH_V1 + 1,
                        &self,
                    ));
                }
                Ok(SparseMerkleSiblingPathV1(siblings))
            }
        }

        deserializer.deserialize_tuple(SPARSE_MERKLE_TREE_DEPTH_V1, SiblingPathVisitor)
    }
}
