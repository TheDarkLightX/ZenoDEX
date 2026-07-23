//! Deterministic private-workspace protocol for parallel helper execution.
//!
//! This module adapts the useful parts of system-enforced deterministic
//! parallelism to the ZenoDEX FCIS boundary without granting workers authority
//! over committed state. A logical worker receives one immutable assignment,
//! runs in a separately enforced sandbox, and returns a data-only response.
//! Physical worker count, completion order, host thread IDs, wall-clock time,
//! and scheduler decisions are deliberately absent from the protocol.
//!
//! The imperative shell must still enforce the sandbox profile. The functional
//! core validates exact request/response bindings, deterministic resource
//! budgets, complete logical-partition coverage, canonical semantic rejection
//! precedence, and read/write noninterference. A successful join is only input
//! to normative sequential replay; it is never itself permission to move value.

use core::cmp::Ordering;

use sha2::{Digest, Sha256};
use thiserror::Error;

pub type Hash32 = [u8; 32];
pub type CellId = [u8; 32];

pub const MAX_LOGICAL_PARTITIONS: usize = 4_096;
pub const MAX_FOOTPRINT_CELLS: usize = 4_096;

const PLAN_HASH_DOMAIN: &[u8] = b"zenodex/deterministic-worker-plan/v1";
const RESPONSE_HASH_DOMAIN: &[u8] = b"zenodex/deterministic-worker-response/v1";
const JOIN_HASH_DOMAIN: &[u8] = b"zenodex/deterministic-worker-join/v1";
const STRICT_SANDBOX_PROFILE_V1: &[u8] = b"zenodex/deterministic-private-workspace/v1\0shared_memory=deny\0clock=deny\0randomness=deny\0network=deny\0filesystem=deny\0environment=deny\0process_spawn=deny\0thread_spawn=deny\0participants=explicit\0synchronization=parent_child_only\0budget=fuel_memory_output\0";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct WorkerContext {
    pre_state_root: Hash32,
    command_set_root: Hash32,
    execution_context_hash: Hash32,
    policy_hash: Hash32,
    module_hash: Hash32,
    algorithm_hash: Hash32,
    partition_profile_hash: Hash32,
}

impl WorkerContext {
    #[must_use]
    pub const fn new(
        pre_state_root: Hash32,
        command_set_root: Hash32,
        execution_context_hash: Hash32,
        policy_hash: Hash32,
        module_hash: Hash32,
        algorithm_hash: Hash32,
        partition_profile_hash: Hash32,
    ) -> Self {
        Self {
            pre_state_root,
            command_set_root,
            execution_context_hash,
            policy_hash,
            module_hash,
            algorithm_hash,
            partition_profile_hash,
        }
    }

    fn encode_into(self, output: &mut Vec<u8>) {
        output.extend_from_slice(&self.pre_state_root);
        output.extend_from_slice(&self.command_set_root);
        output.extend_from_slice(&self.execution_context_hash);
        output.extend_from_slice(&self.policy_hash);
        output.extend_from_slice(&self.module_hash);
        output.extend_from_slice(&self.algorithm_hash);
        output.extend_from_slice(&self.partition_profile_hash);
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct DeterministicBudget {
    fuel_limit: u64,
    memory_bytes_limit: u64,
    output_bytes_limit: u32,
}

impl DeterministicBudget {
    pub fn new(
        fuel_limit: u64,
        memory_bytes_limit: u64,
        output_bytes_limit: u32,
    ) -> Result<Self, WorkerProtocolError> {
        if fuel_limit == 0 {
            return Err(WorkerProtocolError::ZeroBudget { field: "fuel" });
        }
        if memory_bytes_limit == 0 {
            return Err(WorkerProtocolError::ZeroBudget { field: "memory" });
        }
        if output_bytes_limit == 0 {
            return Err(WorkerProtocolError::ZeroBudget { field: "output" });
        }
        Ok(Self {
            fuel_limit,
            memory_bytes_limit,
            output_bytes_limit,
        })
    }

    fn encode_into(self, output: &mut Vec<u8>) {
        output.extend_from_slice(&self.fuel_limit.to_be_bytes());
        output.extend_from_slice(&self.memory_bytes_limit.to_be_bytes());
        output.extend_from_slice(&self.output_bytes_limit.to_be_bytes());
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct WorkerAssignment {
    logical_partition: u32,
    partition_input_root: Hash32,
}

impl WorkerAssignment {
    #[must_use]
    pub const fn new(logical_partition: u32, partition_input_root: Hash32) -> Self {
        Self {
            logical_partition,
            partition_input_root,
        }
    }

    #[must_use]
    pub const fn logical_partition(self) -> u32 {
        self.logical_partition
    }

    #[must_use]
    pub const fn partition_input_root(self) -> Hash32 {
        self.partition_input_root
    }

    fn encode_into(self, output: &mut Vec<u8>) {
        output.extend_from_slice(&self.logical_partition.to_be_bytes());
        output.extend_from_slice(&self.partition_input_root);
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct WorkerPlan {
    context: WorkerContext,
    assignments: Vec<WorkerAssignment>,
    budget: DeterministicBudget,
    sandbox_profile_hash: Hash32,
    plan_hash: Hash32,
}

impl WorkerPlan {
    pub fn new(
        context: WorkerContext,
        assignments: Vec<WorkerAssignment>,
        budget: DeterministicBudget,
        sandbox_profile_hash: Hash32,
    ) -> Result<Self, WorkerProtocolError> {
        if assignments.is_empty() {
            return Err(WorkerProtocolError::EmptyPlan);
        }
        if assignments.len() > MAX_LOGICAL_PARTITIONS {
            return Err(WorkerProtocolError::TooManyPartitions {
                count: assignments.len(),
            });
        }
        for (expected, assignment) in assignments.iter().enumerate() {
            let expected_partition = expected as u32;
            if assignment.logical_partition != expected_partition {
                return Err(WorkerProtocolError::NonContiguousPartition {
                    expected: expected_partition,
                    found: assignment.logical_partition,
                });
            }
        }

        let mut encoded = Vec::new();
        context.encode_into(&mut encoded);
        budget.encode_into(&mut encoded);
        encoded.extend_from_slice(&sandbox_profile_hash);
        encoded.extend_from_slice(&(assignments.len() as u32).to_be_bytes());
        for assignment in &assignments {
            assignment.encode_into(&mut encoded);
        }
        let plan_hash = hash_domain(PLAN_HASH_DOMAIN, &encoded);

        Ok(Self {
            context,
            assignments,
            budget,
            sandbox_profile_hash,
            plan_hash,
        })
    }

    #[must_use]
    pub const fn context(&self) -> WorkerContext {
        self.context
    }

    #[must_use]
    pub fn assignments(&self) -> &[WorkerAssignment] {
        &self.assignments
    }

    #[must_use]
    pub const fn budget(&self) -> DeterministicBudget {
        self.budget
    }

    #[must_use]
    pub const fn sandbox_profile_hash(&self) -> Hash32 {
        self.sandbox_profile_hash
    }

    #[must_use]
    pub const fn plan_hash(&self) -> Hash32 {
        self.plan_hash
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AccessFootprint {
    reads: Vec<CellId>,
    writes: Vec<CellId>,
    contexts: Vec<CellId>,
}

impl AccessFootprint {
    pub fn new(
        reads: Vec<CellId>,
        writes: Vec<CellId>,
        contexts: Vec<CellId>,
    ) -> Result<Self, WorkerProtocolError> {
        validate_canonical_cells("reads", &reads)?;
        validate_canonical_cells("writes", &writes)?;
        validate_canonical_cells("contexts", &contexts)?;
        Ok(Self {
            reads,
            writes,
            contexts,
        })
    }

    #[must_use]
    pub fn reads(&self) -> &[CellId] {
        &self.reads
    }

    #[must_use]
    pub fn writes(&self) -> &[CellId] {
        &self.writes
    }

    #[must_use]
    pub fn contexts(&self) -> &[CellId] {
        &self.contexts
    }

    fn encode_into(&self, output: &mut Vec<u8>) {
        encode_cells(output, &self.reads);
        encode_cells(output, &self.writes);
        encode_cells(output, &self.contexts);
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum WorkerOutcome {
    Success {
        patch_root: Hash32,
        effects_root: Hash32,
        receipt_root: Hash32,
    },
    SemanticReject {
        command_index: u32,
        reject_code: u32,
    },
    OperationalFailure {
        failure_code: u32,
    },
}

impl WorkerOutcome {
    fn validate(self) -> Result<(), WorkerProtocolError> {
        match self {
            Self::Success { .. } => Ok(()),
            Self::SemanticReject { reject_code, .. } if reject_code == 0 => {
                Err(WorkerProtocolError::ZeroOutcomeCode {
                    outcome: "semantic_reject",
                })
            }
            Self::OperationalFailure { failure_code } if failure_code == 0 => {
                Err(WorkerProtocolError::ZeroOutcomeCode {
                    outcome: "operational_failure",
                })
            }
            Self::SemanticReject { .. } | Self::OperationalFailure { .. } => Ok(()),
        }
    }

    fn encode_into(self, output: &mut Vec<u8>) {
        match self {
            Self::Success {
                patch_root,
                effects_root,
                receipt_root,
            } => {
                output.push(0);
                output.extend_from_slice(&patch_root);
                output.extend_from_slice(&effects_root);
                output.extend_from_slice(&receipt_root);
            }
            Self::SemanticReject {
                command_index,
                reject_code,
            } => {
                output.push(1);
                output.extend_from_slice(&command_index.to_be_bytes());
                output.extend_from_slice(&reject_code.to_be_bytes());
            }
            Self::OperationalFailure { failure_code } => {
                output.push(2);
                output.extend_from_slice(&failure_code.to_be_bytes());
            }
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct WorkerResponse {
    logical_partition: u32,
    partition_input_root: Hash32,
    context: WorkerContext,
    sandbox_profile_hash: Hash32,
    footprint: AccessFootprint,
    fuel_used: u64,
    memory_bytes_used: u64,
    output_bytes: u32,
    outcome: WorkerOutcome,
    response_hash: Hash32,
}

impl WorkerResponse {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        logical_partition: u32,
        partition_input_root: Hash32,
        context: WorkerContext,
        sandbox_profile_hash: Hash32,
        footprint: AccessFootprint,
        fuel_used: u64,
        memory_bytes_used: u64,
        output_bytes: u32,
        outcome: WorkerOutcome,
    ) -> Result<Self, WorkerProtocolError> {
        outcome.validate()?;
        let mut encoded = Vec::new();
        encoded.extend_from_slice(&logical_partition.to_be_bytes());
        encoded.extend_from_slice(&partition_input_root);
        context.encode_into(&mut encoded);
        encoded.extend_from_slice(&sandbox_profile_hash);
        footprint.encode_into(&mut encoded);
        encoded.extend_from_slice(&fuel_used.to_be_bytes());
        encoded.extend_from_slice(&memory_bytes_used.to_be_bytes());
        encoded.extend_from_slice(&output_bytes.to_be_bytes());
        outcome.encode_into(&mut encoded);
        let response_hash = hash_domain(RESPONSE_HASH_DOMAIN, &encoded);

        Ok(Self {
            logical_partition,
            partition_input_root,
            context,
            sandbox_profile_hash,
            footprint,
            fuel_used,
            memory_bytes_used,
            output_bytes,
            outcome,
            response_hash,
        })
    }

    #[must_use]
    pub const fn logical_partition(&self) -> u32 {
        self.logical_partition
    }

    #[must_use]
    pub const fn response_hash(&self) -> Hash32 {
        self.response_hash
    }

    #[must_use]
    pub const fn outcome(&self) -> WorkerOutcome {
        self.outcome
    }

    #[must_use]
    pub const fn footprint(&self) -> &AccessFootprint {
        &self.footprint
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct CanonicalSemanticReject {
    pub logical_partition: u32,
    pub command_index: u32,
    pub reject_code: u32,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct JoinedWorkerSet {
    plan_hash: Hash32,
    join_hash: Hash32,
    ordered_responses: Vec<WorkerResponse>,
}

impl JoinedWorkerSet {
    #[must_use]
    pub const fn plan_hash(&self) -> Hash32 {
        self.plan_hash
    }

    #[must_use]
    pub const fn join_hash(&self) -> Hash32 {
        self.join_hash
    }

    #[must_use]
    pub fn ordered_responses(&self) -> &[WorkerResponse] {
        &self.ordered_responses
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum WorkerJoinOutcome {
    Ready(JoinedWorkerSet),
    Rejected(CanonicalSemanticReject),
}

#[derive(Clone, Debug, Eq, Error, PartialEq)]
pub enum WorkerProtocolError {
    #[error("worker plan must contain at least one logical partition")]
    EmptyPlan,
    #[error("worker plan contains too many logical partitions: {count}")]
    TooManyPartitions { count: usize },
    #[error("logical partitions must be contiguous: expected {expected}, found {found}")]
    NonContiguousPartition { expected: u32, found: u32 },
    #[error("deterministic resource budget {field} must be positive")]
    ZeroBudget { field: &'static str },
    #[error("{domain} footprint exceeds the maximum cell count: {count}")]
    FootprintTooLarge { domain: &'static str, count: usize },
    #[error("{domain} footprint must be strictly sorted and duplicate-free")]
    NonCanonicalFootprint { domain: &'static str },
    #[error("{outcome} code must be nonzero")]
    ZeroOutcomeCode { outcome: &'static str },
    #[error("duplicate logical worker response for partition {partition}")]
    DuplicatePartition { partition: u32 },
    #[error("missing logical worker response for partition {partition}")]
    MissingPartition { partition: u32 },
    #[error("unexpected logical worker response for partition {partition}")]
    UnexpectedPartition { partition: u32 },
    #[error("worker response context does not match the plan for partition {partition}")]
    ContextMismatch { partition: u32 },
    #[error("worker response input root does not match the assignment for partition {partition}")]
    InputRootMismatch { partition: u32 },
    #[error("worker response sandbox profile does not match the plan for partition {partition}")]
    SandboxProfileMismatch { partition: u32 },
    #[error("worker fuel budget exceeded for partition {partition}")]
    FuelExceeded { partition: u32 },
    #[error("worker memory budget exceeded for partition {partition}")]
    MemoryExceeded { partition: u32 },
    #[error("worker output budget exceeded for partition {partition}")]
    OutputExceeded { partition: u32 },
    #[error("worker operational failure in partition {partition} with code {failure_code}")]
    OperationalFailure {
        partition: u32,
        failure_code: u32,
    },
    #[error("worker access conflict between partitions {left_partition} and {right_partition}")]
    AccessConflict {
        left_partition: u32,
        right_partition: u32,
        cell: CellId,
    },
}

#[must_use]
pub fn strict_sandbox_profile_hash_v1() -> Hash32 {
    hash_domain(
        b"zenodex/deterministic-worker-sandbox-profile/v1",
        STRICT_SANDBOX_PROFILE_V1,
    )
}

pub fn join_worker_responses(
    plan: &WorkerPlan,
    mut responses: Vec<WorkerResponse>,
) -> Result<WorkerJoinOutcome, WorkerProtocolError> {
    responses.sort_by_key(WorkerResponse::logical_partition);

    for pair in responses.windows(2) {
        if pair[0].logical_partition == pair[1].logical_partition {
            return Err(WorkerProtocolError::DuplicatePartition {
                partition: pair[0].logical_partition,
            });
        }
    }

    let mut response_index = 0usize;
    for assignment in &plan.assignments {
        let Some(response) = responses.get(response_index) else {
            return Err(WorkerProtocolError::MissingPartition {
                partition: assignment.logical_partition,
            });
        };
        match response
            .logical_partition
            .cmp(&assignment.logical_partition)
        {
            Ordering::Less => {
                return Err(WorkerProtocolError::UnexpectedPartition {
                    partition: response.logical_partition,
                });
            }
            Ordering::Greater => {
                return Err(WorkerProtocolError::MissingPartition {
                    partition: assignment.logical_partition,
                });
            }
            Ordering::Equal => {}
        }
        validate_response(plan, assignment, response)?;
        response_index += 1;
    }
    if let Some(extra) = responses.get(response_index) {
        return Err(WorkerProtocolError::UnexpectedPartition {
            partition: extra.logical_partition,
        });
    }

    for response in &responses {
        if let WorkerOutcome::OperationalFailure { failure_code } = response.outcome {
            return Err(WorkerProtocolError::OperationalFailure {
                partition: response.logical_partition,
                failure_code,
            });
        }
    }

    let canonical_reject = responses
        .iter()
        .filter_map(|response| match response.outcome {
            WorkerOutcome::SemanticReject {
                command_index,
                reject_code,
            } => Some(CanonicalSemanticReject {
                logical_partition: response.logical_partition,
                command_index,
                reject_code,
            }),
            WorkerOutcome::Success { .. } | WorkerOutcome::OperationalFailure { .. } => None,
        })
        .min();
    if let Some(rejection) = canonical_reject {
        return Ok(WorkerJoinOutcome::Rejected(rejection));
    }

    for left_index in 0..responses.len() {
        for right_index in (left_index + 1)..responses.len() {
            let left = &responses[left_index];
            let right = &responses[right_index];
            if let Some(cell) = first_access_conflict(&left.footprint, &right.footprint) {
                return Err(WorkerProtocolError::AccessConflict {
                    left_partition: left.logical_partition,
                    right_partition: right.logical_partition,
                    cell,
                });
            }
        }
    }

    let mut encoded = Vec::new();
    encoded.extend_from_slice(&plan.plan_hash);
    encoded.extend_from_slice(&(responses.len() as u32).to_be_bytes());
    for response in &responses {
        encoded.extend_from_slice(&response.response_hash);
    }
    let join_hash = hash_domain(JOIN_HASH_DOMAIN, &encoded);

    Ok(WorkerJoinOutcome::Ready(JoinedWorkerSet {
        plan_hash: plan.plan_hash,
        join_hash,
        ordered_responses: responses,
    }))
}

fn validate_response(
    plan: &WorkerPlan,
    assignment: &WorkerAssignment,
    response: &WorkerResponse,
) -> Result<(), WorkerProtocolError> {
    let partition = assignment.logical_partition;
    if response.context != plan.context {
        return Err(WorkerProtocolError::ContextMismatch { partition });
    }
    if response.partition_input_root != assignment.partition_input_root {
        return Err(WorkerProtocolError::InputRootMismatch { partition });
    }
    if response.sandbox_profile_hash != plan.sandbox_profile_hash {
        return Err(WorkerProtocolError::SandboxProfileMismatch { partition });
    }
    if response.fuel_used > plan.budget.fuel_limit {
        return Err(WorkerProtocolError::FuelExceeded { partition });
    }
    if response.memory_bytes_used > plan.budget.memory_bytes_limit {
        return Err(WorkerProtocolError::MemoryExceeded { partition });
    }
    if response.output_bytes > plan.budget.output_bytes_limit {
        return Err(WorkerProtocolError::OutputExceeded { partition });
    }
    Ok(())
}

fn validate_canonical_cells(
    domain: &'static str,
    cells: &[CellId],
) -> Result<(), WorkerProtocolError> {
    if cells.len() > MAX_FOOTPRINT_CELLS {
        return Err(WorkerProtocolError::FootprintTooLarge {
            domain,
            count: cells.len(),
        });
    }
    if cells.windows(2).any(|pair| pair[0] >= pair[1]) {
        return Err(WorkerProtocolError::NonCanonicalFootprint { domain });
    }
    Ok(())
}

fn first_access_conflict(left: &AccessFootprint, right: &AccessFootprint) -> Option<CellId> {
    [
        first_intersection(&left.writes, &right.writes),
        first_intersection(&left.writes, &right.reads),
        first_intersection(&left.reads, &right.writes),
    ]
    .into_iter()
    .flatten()
    .min()
}

fn first_intersection(left: &[CellId], right: &[CellId]) -> Option<CellId> {
    let mut left_index = 0usize;
    let mut right_index = 0usize;
    while left_index < left.len() && right_index < right.len() {
        match left[left_index].cmp(&right[right_index]) {
            Ordering::Less => left_index += 1,
            Ordering::Greater => right_index += 1,
            Ordering::Equal => return Some(left[left_index]),
        }
    }
    None
}

fn encode_cells(output: &mut Vec<u8>, cells: &[CellId]) {
    output.extend_from_slice(&(cells.len() as u32).to_be_bytes());
    for cell in cells {
        output.extend_from_slice(cell);
    }
}

fn hash_domain(domain: &[u8], payload: &[u8]) -> Hash32 {
    let mut hasher = Sha256::new();
    hasher.update((domain.len() as u32).to_be_bytes());
    hasher.update(domain);
    hasher.update((payload.len() as u64).to_be_bytes());
    hasher.update(payload);
    let digest = hasher.finalize();
    let mut output = [0u8; 32];
    output.copy_from_slice(&digest);
    output
}

#[cfg(test)]
mod tests {
    use super::*;

    fn hash(byte: u8) -> Hash32 {
        [byte; 32]
    }

    fn context() -> WorkerContext {
        WorkerContext::new(
            hash(1),
            hash(2),
            hash(3),
            hash(4),
            hash(5),
            hash(6),
            hash(7),
        )
    }

    fn plan(partition_count: u32) -> WorkerPlan {
        let assignments = (0..partition_count)
            .map(|partition| WorkerAssignment::new(partition, hash(20 + partition as u8)))
            .collect();
        WorkerPlan::new(
            context(),
            assignments,
            DeterministicBudget::new(10_000, 1_000_000, 100_000).unwrap(),
            strict_sandbox_profile_hash_v1(),
        )
        .unwrap()
    }

    fn footprint(reads: &[u8], writes: &[u8]) -> AccessFootprint {
        AccessFootprint::new(
            reads.iter().copied().map(hash).collect(),
            writes.iter().copied().map(hash).collect(),
            vec![hash(200)],
        )
        .unwrap()
    }

    fn success(seed: u8) -> WorkerOutcome {
        WorkerOutcome::Success {
            patch_root: hash(seed),
            effects_root: hash(seed + 1),
            receipt_root: hash(seed + 2),
        }
    }

    fn response(
        plan: &WorkerPlan,
        partition: u32,
        footprint: AccessFootprint,
        outcome: WorkerOutcome,
    ) -> WorkerResponse {
        WorkerResponse::new(
            partition,
            plan.assignments()[partition as usize].partition_input_root(),
            plan.context(),
            plan.sandbox_profile_hash(),
            footprint,
            100,
            1_000,
            100,
            outcome,
        )
        .unwrap()
    }

    #[test]
    fn arrival_order_does_not_change_join() {
        let plan = plan(3);
        let responses = vec![
            response(&plan, 0, footprint(&[1], &[10]), success(30)),
            response(&plan, 1, footprint(&[2], &[11]), success(40)),
            response(&plan, 2, footprint(&[3], &[12]), success(50)),
        ];
        let mut reversed = responses.clone();
        reversed.reverse();

        let left = join_worker_responses(&plan, responses).unwrap();
        let right = join_worker_responses(&plan, reversed).unwrap();

        assert_eq!(left, right);
        let WorkerJoinOutcome::Ready(joined) = left else {
            panic!("expected ready join");
        };
        assert_eq!(
            joined
                .ordered_responses()
                .iter()
                .map(WorkerResponse::logical_partition)
                .collect::<Vec<_>>(),
            vec![0, 1, 2]
        );
    }

    #[test]
    fn read_write_conflict_is_rejected_canonically() {
        let plan = plan(2);
        let error = join_worker_responses(
            &plan,
            vec![
                response(&plan, 0, footprint(&[1], &[9]), success(30)),
                response(&plan, 1, footprint(&[9], &[10]), success(40)),
            ],
        )
        .unwrap_err();

        assert_eq!(
            error,
            WorkerProtocolError::AccessConflict {
                left_partition: 0,
                right_partition: 1,
                cell: hash(9),
            }
        );
    }

    #[test]
    fn semantic_rejection_uses_logical_not_completion_order() {
        let plan = plan(3);
        let result = join_worker_responses(
            &plan,
            vec![
                response(
                    &plan,
                    2,
                    footprint(&[], &[]),
                    WorkerOutcome::SemanticReject {
                        command_index: 0,
                        reject_code: 3,
                    },
                ),
                response(
                    &plan,
                    0,
                    footprint(&[], &[]),
                    WorkerOutcome::SemanticReject {
                        command_index: 7,
                        reject_code: 9,
                    },
                ),
                response(&plan, 1, footprint(&[], &[]), success(40)),
            ],
        )
        .unwrap();

        assert_eq!(
            result,
            WorkerJoinOutcome::Rejected(CanonicalSemanticReject {
                logical_partition: 0,
                command_index: 7,
                reject_code: 9,
            })
        );
    }

    #[test]
    fn operational_failure_produces_no_join_candidate() {
        let plan = plan(2);
        let error = join_worker_responses(
            &plan,
            vec![
                response(&plan, 0, footprint(&[], &[]), success(30)),
                response(
                    &plan,
                    1,
                    footprint(&[], &[]),
                    WorkerOutcome::OperationalFailure { failure_code: 5 },
                ),
            ],
        )
        .unwrap_err();

        assert_eq!(
            error,
            WorkerProtocolError::OperationalFailure {
                partition: 1,
                failure_code: 5,
            }
        );
    }

    #[test]
    fn duplicate_and_missing_partitions_fail_closed() {
        let plan = plan(2);
        let duplicate = join_worker_responses(
            &plan,
            vec![
                response(&plan, 0, footprint(&[], &[]), success(30)),
                response(&plan, 0, footprint(&[], &[]), success(40)),
            ],
        )
        .unwrap_err();
        assert_eq!(
            duplicate,
            WorkerProtocolError::DuplicatePartition { partition: 0 }
        );

        let missing = join_worker_responses(
            &plan,
            vec![response(&plan, 0, footprint(&[], &[]), success(30))],
        )
        .unwrap_err();
        assert_eq!(
            missing,
            WorkerProtocolError::MissingPartition { partition: 1 }
        );
    }

    #[test]
    fn exact_context_input_and_sandbox_bindings_are_required() {
        let plan = plan(1);
        let wrong_context = WorkerResponse::new(
            0,
            plan.assignments()[0].partition_input_root(),
            WorkerContext::new(
                hash(99),
                hash(2),
                hash(3),
                hash(4),
                hash(5),
                hash(6),
                hash(7),
            ),
            plan.sandbox_profile_hash(),
            footprint(&[], &[]),
            1,
            1,
            1,
            success(30),
        )
        .unwrap();
        assert_eq!(
            join_worker_responses(&plan, vec![wrong_context]).unwrap_err(),
            WorkerProtocolError::ContextMismatch { partition: 0 }
        );

        let wrong_sandbox = WorkerResponse::new(
            0,
            plan.assignments()[0].partition_input_root(),
            plan.context(),
            hash(250),
            footprint(&[], &[]),
            1,
            1,
            1,
            success(30),
        )
        .unwrap();
        assert_eq!(
            join_worker_responses(&plan, vec![wrong_sandbox]).unwrap_err(),
            WorkerProtocolError::SandboxProfileMismatch { partition: 0 }
        );
    }

    #[test]
    fn deterministic_resource_budget_is_enforced() {
        let plan = plan(1);
        let over_fuel = WorkerResponse::new(
            0,
            plan.assignments()[0].partition_input_root(),
            plan.context(),
            plan.sandbox_profile_hash(),
            footprint(&[], &[]),
            10_001,
            1,
            1,
            success(30),
        )
        .unwrap();

        assert_eq!(
            join_worker_responses(&plan, vec![over_fuel]).unwrap_err(),
            WorkerProtocolError::FuelExceeded { partition: 0 }
        );
    }

    #[test]
    fn footprint_must_arrive_in_canonical_order() {
        assert_eq!(
            AccessFootprint::new(vec![hash(2), hash(1)], vec![], vec![]).unwrap_err(),
            WorkerProtocolError::NonCanonicalFootprint { domain: "reads" }
        );
        assert_eq!(
            AccessFootprint::new(vec![], vec![hash(1), hash(1)], vec![]).unwrap_err(),
            WorkerProtocolError::NonCanonicalFootprint { domain: "writes" }
        );
    }

    #[test]
    fn physical_worker_count_is_not_a_protocol_input() {
        let first = plan(2);
        let second = plan(2);
        assert_eq!(first.plan_hash(), second.plan_hash());
    }
}
