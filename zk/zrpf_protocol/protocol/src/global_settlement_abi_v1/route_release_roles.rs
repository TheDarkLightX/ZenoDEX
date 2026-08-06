use serde::{de, Deserialize, Deserializer, Serialize, Serializer};

use super::RouteReleaseErrorV1;

const KNOWN_ROLE_BITS_V1: u8 = 0x7f;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum RouteDependencyRoleV1 {
    Primary,
    State,
    Oracle,
    Custody,
    Fee,
    IssueBurn,
    Terminal,
}

impl RouteDependencyRoleV1 {
    pub const fn bit(self) -> u8 {
        match self {
            Self::Primary => 1 << 0,
            Self::State => 1 << 1,
            Self::Oracle => 1 << 2,
            Self::Custody => 1 << 3,
            Self::Fee => 1 << 4,
            Self::IssueBurn => 1 << 5,
            Self::Terminal => 1 << 6,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RouteDependencyRolesV1(u8);

impl RouteDependencyRolesV1 {
    pub fn new(roles: &[RouteDependencyRoleV1]) -> Result<Self, RouteReleaseErrorV1> {
        if roles.is_empty() {
            return Err(RouteReleaseErrorV1::EmptyDependencyRoles);
        }
        let mut bits = 0u8;
        for role in roles {
            let bit = role.bit();
            if bits & bit != 0 {
                return Err(RouteReleaseErrorV1::DuplicateDependencyRole(*role));
            }
            bits |= bit;
        }
        Self::from_bits(bits)
    }

    fn from_bits(bits: u8) -> Result<Self, RouteReleaseErrorV1> {
        if bits == 0 {
            return Err(RouteReleaseErrorV1::EmptyDependencyRoles);
        }
        if bits & !KNOWN_ROLE_BITS_V1 != 0 {
            return Err(RouteReleaseErrorV1::UnknownDependencyRoleBits(bits));
        }
        Ok(Self(bits))
    }

    pub const fn contains(self, role: RouteDependencyRoleV1) -> bool {
        self.0 & role.bit() != 0
    }

    pub const fn bits(self) -> u8 {
        self.0
    }
}

impl Serialize for RouteDependencyRolesV1 {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_u8(self.0)
    }
}

impl<'de> Deserialize<'de> for RouteDependencyRolesV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let bits = u8::deserialize(deserializer)?;
        Self::from_bits(bits).map_err(de::Error::custom)
    }
}
