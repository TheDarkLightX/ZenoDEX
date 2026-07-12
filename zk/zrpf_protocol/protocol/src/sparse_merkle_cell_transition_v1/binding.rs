use super::{SparseMerkleCellTransitionErrorV1, SparseMerkleCellTransitionWitnessV1};
use crate::{CommitmentV3, EconomicActionIdV1, LedgerCellWriteV2, ValueHashV2};

/// Private validated projection of one witness bound to one complete cell write.
///
/// This type proves deterministic equality and root recomposition within this
/// process. It is not a proof receipt, ledger-admission capability, or
/// multi-write transition.
///
/// ```compile_fail
/// use zenodex_zrpf_protocol_v3::ValidatedSparseMerkleCellTransitionV1;
/// let transition: ValidatedSparseMerkleCellTransitionV1 = unimplemented!();
/// let _ = transition.ledger_authority();
/// ```
///
/// ```compile_fail
/// use zenodex_zrpf_protocol_v3::ValidatedSparseMerkleCellTransitionV1;
/// let _ = ValidatedSparseMerkleCellTransitionV1 {};
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ValidatedSparseMerkleCellTransitionV1 {
    economic_action_id: EconomicActionIdV1,
    cell_key: CommitmentV3,
    pre_value_hash: ValueHashV2,
    post_value_hash: ValueHashV2,
    derived_pre_root: CommitmentV3,
    derived_post_root: CommitmentV3,
}

pub fn bind_sparse_merkle_cell_transition_v1(
    witness: &SparseMerkleCellTransitionWitnessV1,
    cell_write: &LedgerCellWriteV2,
) -> Result<ValidatedSparseMerkleCellTransitionV1, SparseMerkleCellTransitionErrorV1> {
    witness.validate_self_consistency()?;
    if witness.economic_action_id() != cell_write.economic_action_id() {
        return Err(SparseMerkleCellTransitionErrorV1::EconomicActionMismatch);
    }
    if witness.cell_key() != cell_write.cell_key() {
        return Err(SparseMerkleCellTransitionErrorV1::CellKeyMismatch);
    }
    if witness.pre_value_hash() != cell_write.pre_value_hash() {
        return Err(SparseMerkleCellTransitionErrorV1::PreValueMismatch);
    }
    if witness.post_value_hash() != cell_write.post_value_hash() {
        return Err(SparseMerkleCellTransitionErrorV1::PostValueMismatch);
    }
    Ok(ValidatedSparseMerkleCellTransitionV1 {
        economic_action_id: witness.economic_action_id(),
        cell_key: witness.cell_key(),
        pre_value_hash: witness.pre_value_hash(),
        post_value_hash: witness.post_value_hash(),
        derived_pre_root: witness.claimed_pre_root(),
        derived_post_root: witness.claimed_post_root(),
    })
}

impl ValidatedSparseMerkleCellTransitionV1 {
    pub const fn economic_action_id(&self) -> EconomicActionIdV1 {
        self.economic_action_id
    }

    pub const fn cell_key(&self) -> CommitmentV3 {
        self.cell_key
    }

    pub const fn pre_value_hash(&self) -> ValueHashV2 {
        self.pre_value_hash
    }

    pub const fn post_value_hash(&self) -> ValueHashV2 {
        self.post_value_hash
    }

    pub const fn derived_pre_root(&self) -> CommitmentV3 {
        self.derived_pre_root
    }

    pub const fn derived_post_root(&self) -> CommitmentV3 {
        self.derived_post_root
    }
}
