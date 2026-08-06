use serde::{de, Deserialize, Deserializer, Serialize};
use sha2::{Digest, Sha256};

use super::{
    GlobalEconomicStateContentV1, GlobalEconomicStateErrorV1, GlobalEconomicStateRootV1,
    GLOBAL_ECONOMIC_STATE_VERSION_V1,
};

const GLOBAL_ECONOMIC_STATE_ROOT_DOMAIN_V1: &[u8] =
    b"zenodex.global_settlement.global_economic_state_root.v1";

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[must_use = "the global economic state must be bound or published by a verifier-controlled shell"]
pub struct GlobalEconomicStateV1 {
    state_version: u16,
    state_root: GlobalEconomicStateRootV1,
    content: GlobalEconomicStateContentV1,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct GlobalEconomicStateWireV1 {
    pub state_version: u16,
    pub state_root: GlobalEconomicStateRootV1,
    pub content: GlobalEconomicStateContentV1,
}

impl GlobalEconomicStateV1 {
    pub fn new(content: GlobalEconomicStateContentV1) -> Result<Self, GlobalEconomicStateErrorV1> {
        let state_root = derive_state_root(&content)?;
        Self::from_parts(GLOBAL_ECONOMIC_STATE_VERSION_V1, state_root, content)
    }

    pub(super) fn from_parts(
        state_version: u16,
        state_root: GlobalEconomicStateRootV1,
        content: GlobalEconomicStateContentV1,
    ) -> Result<Self, GlobalEconomicStateErrorV1> {
        if state_version != GLOBAL_ECONOMIC_STATE_VERSION_V1 {
            return Err(GlobalEconomicStateErrorV1::InvalidStateVersion(
                state_version,
            ));
        }
        content.validate_self_consistency()?;
        if derive_state_root(&content)? != state_root {
            return Err(GlobalEconomicStateErrorV1::CounterfeitStateRoot);
        }
        Ok(Self {
            state_version,
            state_root,
            content,
        })
    }

    pub fn validate_self_consistency(&self) -> Result<(), GlobalEconomicStateErrorV1> {
        if self.state_version != GLOBAL_ECONOMIC_STATE_VERSION_V1 {
            return Err(GlobalEconomicStateErrorV1::InvalidStateVersion(
                self.state_version,
            ));
        }
        self.content.validate_self_consistency()?;
        if derive_state_root(&self.content)? != self.state_root {
            return Err(GlobalEconomicStateErrorV1::CounterfeitStateRoot);
        }
        Ok(())
    }

    pub const fn state_version(&self) -> u16 {
        self.state_version
    }

    pub const fn state_root(&self) -> GlobalEconomicStateRootV1 {
        self.state_root
    }

    pub const fn content(&self) -> &GlobalEconomicStateContentV1 {
        &self.content
    }
}

impl<'de> Deserialize<'de> for GlobalEconomicStateV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = GlobalEconomicStateWireV1::deserialize(deserializer)?;
        Self::from_parts(wire.state_version, wire.state_root, wire.content)
            .map_err(de::Error::custom)
    }
}

fn derive_state_root(
    content: &GlobalEconomicStateContentV1,
) -> Result<GlobalEconomicStateRootV1, GlobalEconomicStateErrorV1> {
    let domain_len = u16::try_from(GLOBAL_ECONOMIC_STATE_ROOT_DOMAIN_V1.len())
        .map_err(|_| GlobalEconomicStateErrorV1::ArithmeticOverflow("hash_domain_length"))?;
    let mut hasher = Sha256::new();
    hasher.update(domain_len.to_be_bytes());
    hasher.update(GLOBAL_ECONOMIC_STATE_ROOT_DOMAIN_V1);
    hasher.update(GLOBAL_ECONOMIC_STATE_VERSION_V1.to_be_bytes());
    content.update_hasher(&mut hasher)?;
    GlobalEconomicStateRootV1::new(hasher.finalize().into())
        .map_err(|_| GlobalEconomicStateErrorV1::InvalidDerivedCommitment("state_root"))
}
