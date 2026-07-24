//! Application-neutral proof-shape and child-assumption contracts.
//!
//! `ProofShapeV1` is a reusable static contract over program, profile, child
//! shape, and resource ceilings. `ProofShapeRegistryV1` contains only those
//! static shapes. `AssumptionManifestV1` is a separate instance contract over
//! exact verification claims and child journals. Keeping those identities
//! separate lets compilation and policy caches reuse one registry across proof
//! instances.
//! These types do not verify proofs, authenticate receipts, authorize releases,
//! or grant settlement or production authority.

mod codec;
mod error;
mod hash;
mod ids;
mod manifest;
mod registry;
mod resolution;
mod resource;
mod shape;

pub use codec::*;
pub use error::*;
pub use ids::*;
pub use manifest::*;
pub use registry::*;
pub use resolution::*;
pub use resource::*;
pub use shape::*;

pub const PROOF_SHAPE_VERSION_V1: u16 = 1;
pub const ALLOWED_CHILD_BINDING_VERSION_V1: u16 = 1;
pub const ASSUMPTION_REQUIREMENT_VERSION_V1: u16 = 1;
pub const ASSUMPTION_MANIFEST_VERSION_V1: u16 = 1;
pub const ASSUMPTION_RESOLUTION_VERSION_V1: u16 = 1;
pub const PROOF_SHAPE_REGISTRY_VERSION_V1: u16 = 1;

pub const MAX_ALLOWED_CHILD_BINDINGS_V1: usize = 32;
pub const MAX_REQUIRED_ASSUMPTIONS_V1: usize = 32;
pub const MAX_RESOLVED_CHILD_CLAIMS_V1: usize = 32;
pub const MAX_PROOF_SHAPE_REGISTRY_ENTRIES_V1: usize = 32;

pub const MAX_PROOF_SHAPE_BYTES_V1: usize = 16 * 1024;
pub const MAX_ASSUMPTION_MANIFEST_BYTES_V1: usize = 8 * 1024;
pub const MAX_PROOF_SHAPE_REGISTRY_BYTES_V1: usize = 512 * 1024;

pub const MAX_SHAPE_INPUT_BYTES_V1: u64 = 64 * 1024 * 1024;
pub const MAX_SHAPE_JOURNAL_BYTES_V1: u64 = 16 * 1024 * 1024;
pub const MAX_SHAPE_PROOF_BYTES_V1: u64 = 64 * 1024 * 1024;
pub const MAX_SHAPE_CYCLES_V1: u64 = 1 << 48;
pub const MAX_SHAPE_MEMORY_BYTES_V1: u64 = 16 * 1024 * 1024 * 1024;
pub const MAX_TOTAL_CHILD_JOURNAL_BYTES_V1: u64 =
    MAX_REQUIRED_ASSUMPTIONS_V1 as u64 * MAX_SHAPE_JOURNAL_BYTES_V1;
