use serde::{de, Deserialize, Deserializer, Serialize};

use super::{
    ProofShapeErrorV1, MAX_REQUIRED_ASSUMPTIONS_V1, MAX_SHAPE_CYCLES_V1, MAX_SHAPE_INPUT_BYTES_V1,
    MAX_SHAPE_JOURNAL_BYTES_V1, MAX_SHAPE_MEMORY_BYTES_V1, MAX_SHAPE_PROOF_BYTES_V1,
    MAX_TOTAL_CHILD_JOURNAL_BYTES_V1,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub struct ProofResourceCeilingsV1 {
    max_input_bytes: u64,
    max_journal_bytes: u64,
    max_proof_bytes: u64,
    max_cycles: u64,
    max_memory_bytes: u64,
    max_assumptions: u64,
    max_total_child_journal_bytes: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ProofResourceCeilingsInputV1 {
    pub max_input_bytes: u64,
    pub max_journal_bytes: u64,
    pub max_proof_bytes: u64,
    pub max_cycles: u64,
    pub max_memory_bytes: u64,
    pub max_assumptions: u64,
    pub max_total_child_journal_bytes: u64,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ProofResourceCeilingsWireV1 {
    max_input_bytes: u64,
    max_journal_bytes: u64,
    max_proof_bytes: u64,
    max_cycles: u64,
    max_memory_bytes: u64,
    max_assumptions: u64,
    max_total_child_journal_bytes: u64,
}

impl ProofResourceCeilingsV1 {
    pub fn new(input: ProofResourceCeilingsInputV1) -> Result<Self, ProofShapeErrorV1> {
        let value = Self {
            max_input_bytes: input.max_input_bytes,
            max_journal_bytes: input.max_journal_bytes,
            max_proof_bytes: input.max_proof_bytes,
            max_cycles: input.max_cycles,
            max_memory_bytes: input.max_memory_bytes,
            max_assumptions: input.max_assumptions,
            max_total_child_journal_bytes: input.max_total_child_journal_bytes,
        };
        value.validate()?;
        Ok(value)
    }

    pub fn validate(self) -> Result<(), ProofShapeErrorV1> {
        require_bounded_nonzero(
            self.max_input_bytes,
            MAX_SHAPE_INPUT_BYTES_V1,
            "max_input_bytes",
        )?;
        require_bounded_nonzero(
            self.max_journal_bytes,
            MAX_SHAPE_JOURNAL_BYTES_V1,
            "max_journal_bytes",
        )?;
        require_bounded_nonzero(
            self.max_proof_bytes,
            MAX_SHAPE_PROOF_BYTES_V1,
            "max_proof_bytes",
        )?;
        require_bounded_nonzero(self.max_cycles, MAX_SHAPE_CYCLES_V1, "max_cycles")?;
        require_bounded_nonzero(
            self.max_memory_bytes,
            MAX_SHAPE_MEMORY_BYTES_V1,
            "max_memory_bytes",
        )?;
        if self.max_assumptions > MAX_REQUIRED_ASSUMPTIONS_V1 as u64 {
            return Err(ProofShapeErrorV1::InvalidResourceCeiling("max_assumptions"));
        }
        if self.max_total_child_journal_bytes > MAX_TOTAL_CHILD_JOURNAL_BYTES_V1 {
            return Err(ProofShapeErrorV1::InvalidResourceCeiling(
                "max_total_child_journal_bytes",
            ));
        }
        if (self.max_assumptions == 0) != (self.max_total_child_journal_bytes == 0) {
            return Err(ProofShapeErrorV1::InvalidResourceCeiling(
                "child_resource_coherence",
            ));
        }
        Ok(())
    }

    pub const fn max_input_bytes(self) -> u64 {
        self.max_input_bytes
    }

    pub const fn max_journal_bytes(self) -> u64 {
        self.max_journal_bytes
    }

    pub const fn max_proof_bytes(self) -> u64 {
        self.max_proof_bytes
    }

    pub const fn max_cycles(self) -> u64 {
        self.max_cycles
    }

    pub const fn max_memory_bytes(self) -> u64 {
        self.max_memory_bytes
    }

    pub const fn max_assumptions(self) -> u64 {
        self.max_assumptions
    }

    pub const fn max_total_child_journal_bytes(self) -> u64 {
        self.max_total_child_journal_bytes
    }
}

impl<'de> Deserialize<'de> for ProofResourceCeilingsV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = ProofResourceCeilingsWireV1::deserialize(deserializer)?;
        Self::new(ProofResourceCeilingsInputV1 {
            max_input_bytes: wire.max_input_bytes,
            max_journal_bytes: wire.max_journal_bytes,
            max_proof_bytes: wire.max_proof_bytes,
            max_cycles: wire.max_cycles,
            max_memory_bytes: wire.max_memory_bytes,
            max_assumptions: wire.max_assumptions,
            max_total_child_journal_bytes: wire.max_total_child_journal_bytes,
        })
        .map_err(de::Error::custom)
    }
}

fn require_bounded_nonzero(
    actual: u64,
    maximum: u64,
    field: &'static str,
) -> Result<(), ProofShapeErrorV1> {
    if actual == 0 || actual > maximum {
        return Err(ProofShapeErrorV1::InvalidResourceCeiling(field));
    }
    Ok(())
}
