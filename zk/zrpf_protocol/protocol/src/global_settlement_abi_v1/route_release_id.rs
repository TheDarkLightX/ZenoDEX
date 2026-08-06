use serde::{de, Deserialize, Deserializer, Serialize, Serializer};

use super::RouteReleaseErrorV1;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RouteReleaseIdV1([u8; 32]);

impl RouteReleaseIdV1 {
    pub fn new(bytes: [u8; 32]) -> Result<Self, RouteReleaseErrorV1> {
        if bytes == [0; 32] {
            return Err(RouteReleaseErrorV1::ZeroRouteReleaseId);
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

impl Serialize for RouteReleaseIdV1 {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.0.serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for RouteReleaseIdV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let bytes = <[u8; 32]>::deserialize(deserializer)?;
        Self::new(bytes).map_err(de::Error::custom)
    }
}
