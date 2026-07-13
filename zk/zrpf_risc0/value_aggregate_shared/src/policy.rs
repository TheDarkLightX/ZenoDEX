use alloc::vec::Vec;

use zenodex_zrpf_protocol_v3::{
    CommitmentV3, NodeScopeV3, ProfileIdV3, ProgramIdV3, MAX_IMMEDIATE_CHILDREN_V3,
};
use zenodex_zrpf_risc0_shared::program_id_from_risc0_words_v3;

use crate::ValueAggregateRecompositionErrorV5;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
/// Exact child runtime and statement identity supplied by governed guest code.
///
/// Construction binds the RISC0 image words to the corresponding protocol
/// program ID. It does not establish that governance selected this identity or
/// that any receipt was verified under it.
pub struct GovernedValueChildIdentityV5 {
    expected_image_id: [u32; 8],
    expected_program_id: ProgramIdV3,
    expected_profile_id: ProfileIdV3,
    expected_manifest_root: CommitmentV3,
}

impl GovernedValueChildIdentityV5 {
    pub fn new(
        expected_image_id: [u32; 8],
        expected_program_id: ProgramIdV3,
        expected_profile_id: ProfileIdV3,
        expected_manifest_root: CommitmentV3,
    ) -> Result<Self, ValueAggregateRecompositionErrorV5> {
        if expected_image_id.iter().all(|word| *word == 0) {
            return Err(ValueAggregateRecompositionErrorV5::InvalidPolicy(
                "child_image_id",
            ));
        }
        let derived = program_id_from_risc0_words_v3(expected_image_id).map_err(|_| {
            ValueAggregateRecompositionErrorV5::InvalidPolicy("child_program_derivation")
        })?;
        if expected_program_id != derived {
            return Err(ValueAggregateRecompositionErrorV5::InvalidPolicy(
                "child_image_program_binding",
            ));
        }
        Ok(Self {
            expected_image_id,
            expected_program_id,
            expected_profile_id,
            expected_manifest_root,
        })
    }

    pub const fn expected_image_id(self) -> [u32; 8] {
        self.expected_image_id
    }

    pub const fn expected_program_id(self) -> ProgramIdV3 {
        self.expected_program_id
    }

    pub const fn expected_profile_id(self) -> ProfileIdV3 {
        self.expected_profile_id
    }

    pub const fn expected_manifest_root(self) -> CommitmentV3 {
        self.expected_manifest_root
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
/// Ordered child identities and exact single-epoch scope for recomposition.
///
/// The identity order is consensus-relevant and must match the child-byte
/// order. Governance and receipt authentication remain outside this type.
pub struct ValueAggregateRecompositionPolicyV5 {
    expected_scope: NodeScopeV3,
    child_identities: Vec<GovernedValueChildIdentityV5>,
}

impl ValueAggregateRecompositionPolicyV5 {
    pub fn new(
        expected_scope: NodeScopeV3,
        child_identities: Vec<GovernedValueChildIdentityV5>,
    ) -> Result<Self, ValueAggregateRecompositionErrorV5> {
        expected_scope
            .validate()
            .map_err(|_| ValueAggregateRecompositionErrorV5::InvalidPolicy("scope"))?;
        if expected_scope.epoch_start() != expected_scope.epoch_end() {
            return Err(ValueAggregateRecompositionErrorV5::InvalidPolicy(
                "multi_epoch_scope",
            ));
        }
        if child_identities.is_empty() || child_identities.len() > MAX_IMMEDIATE_CHILDREN_V3 {
            return Err(ValueAggregateRecompositionErrorV5::InvalidChildCount {
                actual: child_identities.len(),
                maximum: MAX_IMMEDIATE_CHILDREN_V3,
            });
        }
        Ok(Self {
            expected_scope,
            child_identities,
        })
    }

    pub const fn expected_scope(&self) -> &NodeScopeV3 {
        &self.expected_scope
    }

    pub fn child_identities(&self) -> &[GovernedValueChildIdentityV5] {
        &self.child_identities
    }

    pub(crate) fn require_input_count(
        &self,
        input_count: usize,
    ) -> Result<(), ValueAggregateRecompositionErrorV5> {
        if self.child_identities.len() != input_count {
            return Err(
                ValueAggregateRecompositionErrorV5::PolicyChildCountMismatch {
                    policy: self.child_identities.len(),
                    input: input_count,
                },
            );
        }
        Ok(())
    }
}
