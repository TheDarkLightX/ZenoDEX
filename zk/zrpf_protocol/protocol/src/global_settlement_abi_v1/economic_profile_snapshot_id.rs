use serde::{de, Deserialize, Deserializer, Serialize, Serializer};

use super::EconomicProfileSnapshotErrorV1;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct EconomicProfileIdV1([u8; 32]);

impl EconomicProfileIdV1 {
    pub fn new(bytes: [u8; 32]) -> Result<Self, EconomicProfileSnapshotErrorV1> {
        if bytes == [0; 32] {
            return Err(EconomicProfileSnapshotErrorV1::ZeroProfileId);
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

impl Serialize for EconomicProfileIdV1 {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.0.serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for EconomicProfileIdV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let bytes = <[u8; 32]>::deserialize(deserializer)?;
        Self::new(bytes).map_err(de::Error::custom)
    }
}
