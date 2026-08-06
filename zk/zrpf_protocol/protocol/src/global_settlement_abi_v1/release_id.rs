use serde::{de, Deserialize, Deserializer, Serialize, Serializer};

use super::LaneModuleReleaseErrorV1;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LaneModuleReleaseIdV1([u8; 32]);

impl LaneModuleReleaseIdV1 {
    pub fn new(bytes: [u8; 32]) -> Result<Self, LaneModuleReleaseErrorV1> {
        if bytes == [0; 32] {
            return Err(LaneModuleReleaseErrorV1::ZeroReleaseId);
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

impl Serialize for LaneModuleReleaseIdV1 {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.0.serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for LaneModuleReleaseIdV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let bytes = <[u8; 32]>::deserialize(deserializer)?;
        Self::new(bytes).map_err(de::Error::custom)
    }
}
