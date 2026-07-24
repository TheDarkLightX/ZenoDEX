use serde::{de, Deserialize, Deserializer, Serialize, Serializer};

use super::ProofShapeErrorV1;

macro_rules! nonzero_identifier {
    ($name:ident, $label:literal) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
        pub struct $name([u8; 32]);

        impl $name {
            pub fn new(bytes: [u8; 32]) -> Result<Self, ProofShapeErrorV1> {
                if bytes == [0; 32] {
                    return Err(ProofShapeErrorV1::ZeroIdentifier($label));
                }
                Ok(Self(bytes))
            }

            pub const fn as_bytes(&self) -> &[u8; 32] {
                &self.0
            }
        }

        impl Serialize for $name {
            fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
            where
                S: Serializer,
            {
                self.0.serialize(serializer)
            }
        }

        impl<'de> Deserialize<'de> for $name {
            fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
            where
                D: Deserializer<'de>,
            {
                Self::new(<[u8; 32]>::deserialize(deserializer)?).map_err(de::Error::custom)
            }
        }
    };
}

nonzero_identifier!(ProofShapeIdV1, "proof_shape_id");
nonzero_identifier!(AllowedChildBindingIdV1, "allowed_child_binding_id");
nonzero_identifier!(AssumptionIdV1, "assumption_id");
nonzero_identifier!(AssumptionManifestIdV1, "assumption_manifest_id");
nonzero_identifier!(AssumptionResolutionIdV1, "assumption_resolution_id");
nonzero_identifier!(ProofShapeRegistryIdV1, "proof_shape_registry_id");
