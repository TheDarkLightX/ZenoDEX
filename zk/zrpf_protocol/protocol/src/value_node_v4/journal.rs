use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use serde::{de, Deserialize, Deserializer, Serialize};
use sha2::Digest;

use super::super::{
    CommitmentV3, NodeJournalV3, ProfileIdV3, ProgramIdV3, MAX_IMMEDIATE_CHILDREN_V3,
};
use super::bounded::deserialize_bounded_vec;
use super::subtree::hash::{
    checked_len_u32, commitment, domain_hasher, write_commitment, write_u16, write_u32,
};
use super::{
    SemanticSubtreeV2, ValueNodeErrorV4, MAX_NODE_JOURNAL_BYTES_V4, NODE_JOURNAL_VERSION_V4,
};

const VERIFIER_ID_DOMAIN_V4: &[u8] = b"zenodex.zrpf.verifier_id.v4";
const SEMANTIC_STATEMENT_HASH_DOMAIN_V4: &[u8] = b"zenodex.zrpf.semantic_statement_hash.v4";
const CHILD_SEMANTIC_JOURNALS_ROOT_DOMAIN_V4: &[u8] =
    b"zenodex.zrpf.child_semantic_journals_root.v4";
const NODE_JOURNAL_HASH_DOMAIN_V4: &[u8] = b"zenodex.zrpf.node_journal_hash.v4";

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NodeJournalInputV4 {
    pub structural: NodeJournalV3,
    pub semantic_subtree: SemanticSubtreeV2,
    pub proof_profile_id: ProfileIdV3,
    pub actual_program_id: ProgramIdV3,
    pub proof_system_id: CommitmentV3,
    pub receipt_security_profile_id: CommitmentV3,
    pub verifier_parameters_root: CommitmentV3,
    pub program_manifest_root: CommitmentV3,
    pub child_semantic_journal_hashes: Vec<CommitmentV3>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
/// Complete proof-backend identity used to derive one V4 verifier ID.
pub struct VerifierIdentityInputV4 {
    pub program_id: ProgramIdV3,
    pub proof_profile_id: ProfileIdV3,
    pub proof_system_id: CommitmentV3,
    pub receipt_security_profile_id: CommitmentV3,
    pub verifier_parameters_root: CommitmentV3,
}

struct SemanticStatementMaterialV4<'a> {
    structural: &'a NodeJournalV3,
    semantic_subtree: &'a SemanticSubtreeV2,
    verifier_identity: VerifierIdentityInputV4,
    program_manifest_root: CommitmentV3,
    child_semantic_journals_root: CommitmentV3,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
/// Proof-system-neutral V4 proposal; receipt authentication is a later boundary.
pub struct NodeJournalV4 {
    journal_version: u16,
    structural: NodeJournalV3,
    semantic_subtree: SemanticSubtreeV2,
    proof_profile_id: ProfileIdV3,
    actual_program_id: ProgramIdV3,
    proof_system_id: CommitmentV3,
    receipt_security_profile_id: CommitmentV3,
    verifier_parameters_root: CommitmentV3,
    verifier_id: CommitmentV3,
    semantic_statement_hash: CommitmentV3,
    program_manifest_root: CommitmentV3,
    child_semantic_journal_hashes: Vec<CommitmentV3>,
    child_semantic_journals_root: CommitmentV3,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct NodeJournalWireV4 {
    journal_version: u16,
    structural: NodeJournalV3,
    semantic_subtree: SemanticSubtreeV2,
    proof_profile_id: ProfileIdV3,
    actual_program_id: ProgramIdV3,
    proof_system_id: CommitmentV3,
    receipt_security_profile_id: CommitmentV3,
    verifier_parameters_root: CommitmentV3,
    verifier_id: CommitmentV3,
    semantic_statement_hash: CommitmentV3,
    program_manifest_root: CommitmentV3,
    #[serde(deserialize_with = "deserialize_child_semantic_journal_hashes")]
    child_semantic_journal_hashes: Vec<CommitmentV3>,
    child_semantic_journals_root: CommitmentV3,
}

fn deserialize_child_semantic_journal_hashes<'de, D>(
    deserializer: D,
) -> Result<Vec<CommitmentV3>, D::Error>
where
    D: Deserializer<'de>,
{
    deserialize_bounded_vec(
        deserializer,
        MAX_IMMEDIATE_CHILDREN_V3,
        "child semantic journal hashes",
    )
}

impl NodeJournalV4 {
    /// Bind one validated V3 structure to one validated semantic subtree.
    pub fn new(input: NodeJournalInputV4) -> Result<Self, ValueNodeErrorV4> {
        input.structural.validate()?;
        input.semantic_subtree.validate()?;
        validate_structural_binding(&input.structural, &input.semantic_subtree)?;
        validate_child_hashes(&input.structural, &input.child_semantic_journal_hashes)?;
        let child_semantic_journals_root =
            derive_child_semantic_journals_root(&input.child_semantic_journal_hashes)?;
        let verifier_identity = VerifierIdentityInputV4 {
            program_id: input.actual_program_id,
            proof_profile_id: input.proof_profile_id,
            proof_system_id: input.proof_system_id,
            receipt_security_profile_id: input.receipt_security_profile_id,
            verifier_parameters_root: input.verifier_parameters_root,
        };
        let verifier_id = derive_verifier_id_v4(verifier_identity)?;
        let semantic_statement_hash =
            derive_semantic_statement_hash_v4(SemanticStatementMaterialV4 {
                structural: &input.structural,
                semantic_subtree: &input.semantic_subtree,
                verifier_identity,
                program_manifest_root: input.program_manifest_root,
                child_semantic_journals_root,
            })?;
        let journal = Self {
            journal_version: NODE_JOURNAL_VERSION_V4,
            structural: input.structural,
            semantic_subtree: input.semantic_subtree,
            proof_profile_id: input.proof_profile_id,
            actual_program_id: input.actual_program_id,
            proof_system_id: input.proof_system_id,
            receipt_security_profile_id: input.receipt_security_profile_id,
            verifier_parameters_root: input.verifier_parameters_root,
            verifier_id,
            semantic_statement_hash,
            program_manifest_root: input.program_manifest_root,
            child_semantic_journal_hashes: input.child_semantic_journal_hashes,
            child_semantic_journals_root,
        };
        journal.validate()?;
        Ok(journal)
    }

    pub fn validate(&self) -> Result<(), ValueNodeErrorV4> {
        if self.journal_version != NODE_JOURNAL_VERSION_V4 {
            return Err(ValueNodeErrorV4::InvalidNodeJournalVersion(
                self.journal_version,
            ));
        }
        self.structural.validate()?;
        self.semantic_subtree.validate()?;
        validate_structural_binding(&self.structural, &self.semantic_subtree)?;
        validate_child_hashes(&self.structural, &self.child_semantic_journal_hashes)?;
        let expected_child_root =
            derive_child_semantic_journals_root(&self.child_semantic_journal_hashes)?;
        if self.child_semantic_journals_root != expected_child_root {
            return Err(ValueNodeErrorV4::CommitmentMismatch(
                "child_semantic_journals_root",
            ));
        }
        let verifier_identity = VerifierIdentityInputV4 {
            program_id: self.actual_program_id,
            proof_profile_id: self.proof_profile_id,
            proof_system_id: self.proof_system_id,
            receipt_security_profile_id: self.receipt_security_profile_id,
            verifier_parameters_root: self.verifier_parameters_root,
        };
        let expected_verifier = derive_verifier_id_v4(verifier_identity)?;
        if self.verifier_id != expected_verifier {
            return Err(ValueNodeErrorV4::VerifierIdMismatch);
        }
        let expected_statement = derive_semantic_statement_hash_v4(SemanticStatementMaterialV4 {
            structural: &self.structural,
            semantic_subtree: &self.semantic_subtree,
            verifier_identity,
            program_manifest_root: self.program_manifest_root,
            child_semantic_journals_root: self.child_semantic_journals_root,
        })?;
        if self.semantic_statement_hash != expected_statement {
            return Err(ValueNodeErrorV4::StatementHashMismatch);
        }
        Ok(())
    }

    pub fn canonical_hash(&self) -> Result<CommitmentV3, ValueNodeErrorV4> {
        self.validate()?;
        let mut hasher = domain_hasher(NODE_JOURNAL_HASH_DOMAIN_V4)?;
        write_u16(&mut hasher, self.journal_version);
        write_commitment(&mut hasher, self.structural.canonical_hash()?);
        write_commitment(&mut hasher, self.semantic_subtree.canonical_hash()?);
        hasher.update(self.proof_profile_id.as_bytes());
        hasher.update(self.actual_program_id.as_bytes());
        for value in [
            self.proof_system_id,
            self.receipt_security_profile_id,
            self.verifier_parameters_root,
            self.verifier_id,
            self.semantic_statement_hash,
            self.program_manifest_root,
        ] {
            write_commitment(&mut hasher, value);
        }
        write_u32(
            &mut hasher,
            checked_len_u32(
                self.child_semantic_journal_hashes.len(),
                "child_semantic_journal_count",
            )?,
        );
        for child_hash in &self.child_semantic_journal_hashes {
            write_commitment(&mut hasher, *child_hash);
        }
        write_commitment(&mut hasher, self.child_semantic_journals_root);
        commitment(hasher.finalize().into())
    }

    pub const fn structural(&self) -> &NodeJournalV3 {
        &self.structural
    }

    pub const fn semantic_subtree(&self) -> &SemanticSubtreeV2 {
        &self.semantic_subtree
    }

    pub const fn proof_profile_id(&self) -> ProfileIdV3 {
        self.proof_profile_id
    }

    pub const fn actual_program_id(&self) -> ProgramIdV3 {
        self.actual_program_id
    }

    pub const fn proof_system_id(&self) -> CommitmentV3 {
        self.proof_system_id
    }

    pub const fn receipt_security_profile_id(&self) -> CommitmentV3 {
        self.receipt_security_profile_id
    }

    pub const fn verifier_parameters_root(&self) -> CommitmentV3 {
        self.verifier_parameters_root
    }

    pub const fn verifier_id(&self) -> CommitmentV3 {
        self.verifier_id
    }

    pub const fn semantic_statement_hash(&self) -> CommitmentV3 {
        self.semantic_statement_hash
    }

    pub const fn program_manifest_root(&self) -> CommitmentV3 {
        self.program_manifest_root
    }

    pub fn child_semantic_journal_hashes(&self) -> &[CommitmentV3] {
        &self.child_semantic_journal_hashes
    }

    pub const fn child_semantic_journals_root(&self) -> CommitmentV3 {
        self.child_semantic_journals_root
    }

    fn from_wire(wire: NodeJournalWireV4) -> Result<Self, ValueNodeErrorV4> {
        let journal = Self {
            journal_version: wire.journal_version,
            structural: wire.structural,
            semantic_subtree: wire.semantic_subtree,
            proof_profile_id: wire.proof_profile_id,
            actual_program_id: wire.actual_program_id,
            proof_system_id: wire.proof_system_id,
            receipt_security_profile_id: wire.receipt_security_profile_id,
            verifier_parameters_root: wire.verifier_parameters_root,
            verifier_id: wire.verifier_id,
            semantic_statement_hash: wire.semantic_statement_hash,
            program_manifest_root: wire.program_manifest_root,
            child_semantic_journal_hashes: wire.child_semantic_journal_hashes,
            child_semantic_journals_root: wire.child_semantic_journals_root,
        };
        journal.validate()?;
        Ok(journal)
    }
}

impl<'de> Deserialize<'de> for NodeJournalV4 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        Self::from_wire(NodeJournalWireV4::deserialize(deserializer)?).map_err(de::Error::custom)
    }
}

pub fn derive_verifier_id_v4(
    input: VerifierIdentityInputV4,
) -> Result<CommitmentV3, ValueNodeErrorV4> {
    let mut hasher = domain_hasher(VERIFIER_ID_DOMAIN_V4)?;
    hasher.update(input.program_id.as_bytes());
    hasher.update(input.proof_profile_id.as_bytes());
    write_commitment(&mut hasher, input.proof_system_id);
    write_commitment(&mut hasher, input.receipt_security_profile_id);
    write_commitment(&mut hasher, input.verifier_parameters_root);
    write_u16(&mut hasher, NODE_JOURNAL_VERSION_V4);
    commitment(hasher.finalize().into())
}

fn derive_semantic_statement_hash_v4(
    material: SemanticStatementMaterialV4<'_>,
) -> Result<CommitmentV3, ValueNodeErrorV4> {
    let mut hasher = domain_hasher(SEMANTIC_STATEMENT_HASH_DOMAIN_V4)?;
    write_commitment(&mut hasher, material.structural.canonical_hash()?);
    write_commitment(&mut hasher, material.semantic_subtree.canonical_hash()?);
    hasher.update(material.verifier_identity.proof_profile_id.as_bytes());
    hasher.update(material.verifier_identity.program_id.as_bytes());
    for value in [
        material.verifier_identity.proof_system_id,
        material.verifier_identity.receipt_security_profile_id,
        material.verifier_identity.verifier_parameters_root,
        material.program_manifest_root,
        material.child_semantic_journals_root,
    ] {
        write_commitment(&mut hasher, value);
    }
    commitment(hasher.finalize().into())
}

fn derive_child_semantic_journals_root(
    child_hashes: &[CommitmentV3],
) -> Result<CommitmentV3, ValueNodeErrorV4> {
    let mut hasher = domain_hasher(CHILD_SEMANTIC_JOURNALS_ROOT_DOMAIN_V4)?;
    write_u32(
        &mut hasher,
        checked_len_u32(child_hashes.len(), "child_semantic_journal_count")?,
    );
    for child_hash in child_hashes {
        write_commitment(&mut hasher, *child_hash);
    }
    commitment(hasher.finalize().into())
}

fn validate_structural_binding(
    structural: &NodeJournalV3,
    semantic_subtree: &SemanticSubtreeV2,
) -> Result<(), ValueNodeErrorV4> {
    if structural.partition() != semantic_subtree.partition() {
        return Err(ValueNodeErrorV4::StructuralPartitionMismatch);
    }
    if structural.leaf_count() != semantic_subtree.leaf_count() {
        return Err(ValueNodeErrorV4::StructuralLeafCountMismatch);
    }
    if structural.scope().canonical_hash()? != semantic_subtree.scope_hash() {
        return Err(ValueNodeErrorV4::StructuralScopeMismatch);
    }
    Ok(())
}

fn validate_child_hashes(
    structural: &NodeJournalV3,
    child_hashes: &[CommitmentV3],
) -> Result<(), ValueNodeErrorV4> {
    let expected = usize::from(structural.immediate_child_count());
    if child_hashes.len() != expected || child_hashes.len() > MAX_IMMEDIATE_CHILDREN_V3 {
        return Err(ValueNodeErrorV4::InvalidChildSemanticJournalCount {
            actual: child_hashes.len(),
            expected,
        });
    }
    let mut unique = BTreeSet::new();
    for child_hash in child_hashes {
        if !unique.insert(*child_hash) {
            return Err(ValueNodeErrorV4::DuplicateChildSemanticJournal);
        }
    }
    Ok(())
}

pub fn encode_node_journal_v4(journal: &NodeJournalV4) -> Result<Vec<u8>, ValueNodeErrorV4> {
    journal.validate()?;
    let bytes = postcard::to_allocvec(journal).map_err(|_| ValueNodeErrorV4::PostcardDecode)?;
    if bytes.len() > MAX_NODE_JOURNAL_BYTES_V4 {
        return Err(ValueNodeErrorV4::InputTooLarge {
            actual: bytes.len(),
            maximum: MAX_NODE_JOURNAL_BYTES_V4,
        });
    }
    Ok(bytes)
}

pub fn decode_exact_node_journal_v4(bytes: &[u8]) -> Result<NodeJournalV4, ValueNodeErrorV4> {
    if bytes.is_empty() {
        return Err(ValueNodeErrorV4::EmptyInput);
    }
    if bytes.len() > MAX_NODE_JOURNAL_BYTES_V4 {
        return Err(ValueNodeErrorV4::InputTooLarge {
            actual: bytes.len(),
            maximum: MAX_NODE_JOURNAL_BYTES_V4,
        });
    }
    let (journal, remainder): (NodeJournalV4, &[u8]) =
        postcard::take_from_bytes(bytes).map_err(|_| ValueNodeErrorV4::PostcardDecode)?;
    if !remainder.is_empty() {
        return Err(ValueNodeErrorV4::TrailingBytes);
    }
    journal.validate()?;
    let canonical =
        postcard::to_allocvec(&journal).map_err(|_| ValueNodeErrorV4::PostcardDecode)?;
    if canonical != bytes {
        return Err(ValueNodeErrorV4::NonCanonicalEncoding);
    }
    Ok(journal)
}
