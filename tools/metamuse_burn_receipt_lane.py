from __future__ import annotations

from dataclasses import dataclass
from typing import Any


@dataclass(frozen=True)
class BurnReceiptLaneStep:
    do_burn: int
    receipt_bound: int
    nullifier_unused: int
    policy_ok: int
    burn_amount: int
    receipt_amount: int
    burn_budget: int
    supply_before: int
    supply_after: int
    batch_burn_sum_before: int
    batch_burn_sum_after: int
    expected_valid: int

    def to_json(self) -> dict[str, int]:
        return {
            "do_burn": int(self.do_burn),
            "receipt_bound": int(self.receipt_bound),
            "nullifier_unused": int(self.nullifier_unused),
            "policy_ok": int(self.policy_ok),
            "burn_amount": int(self.burn_amount),
            "receipt_amount": int(self.receipt_amount),
            "burn_budget": int(self.burn_budget),
            "supply_before": int(self.supply_before),
            "supply_after": int(self.supply_after),
            "batch_burn_sum_before": int(self.batch_burn_sum_before),
            "batch_burn_sum_after": int(self.batch_burn_sum_after),
            "expected_valid": int(self.expected_valid),
        }


BURN_RECEIPT_CURATED_STEPS: tuple[BurnReceiptLaneStep, ...] = (
    BurnReceiptLaneStep(
        do_burn=1,
        receipt_bound=1,
        nullifier_unused=1,
        policy_ok=1,
        burn_amount=20,
        receipt_amount=20,
        burn_budget=30,
        supply_before=1000,
        supply_after=980,
        batch_burn_sum_before=50,
        batch_burn_sum_after=70,
        expected_valid=1,
    ),
    BurnReceiptLaneStep(
        do_burn=1,
        receipt_bound=1,
        nullifier_unused=0,
        policy_ok=1,
        burn_amount=20,
        receipt_amount=20,
        burn_budget=30,
        supply_before=1000,
        supply_after=980,
        batch_burn_sum_before=50,
        batch_burn_sum_after=70,
        expected_valid=0,
    ),
    BurnReceiptLaneStep(
        do_burn=1,
        receipt_bound=1,
        nullifier_unused=1,
        policy_ok=1,
        burn_amount=21,
        receipt_amount=20,
        burn_budget=30,
        supply_before=1000,
        supply_after=979,
        batch_burn_sum_before=50,
        batch_burn_sum_after=71,
        expected_valid=0,
    ),
    BurnReceiptLaneStep(
        do_burn=1,
        receipt_bound=1,
        nullifier_unused=1,
        policy_ok=1,
        burn_amount=20,
        receipt_amount=20,
        burn_budget=30,
        supply_before=1000,
        supply_after=980,
        batch_burn_sum_before=50,
        batch_burn_sum_after=69,
        expected_valid=0,
    ),
    BurnReceiptLaneStep(
        do_burn=0,
        receipt_bound=0,
        nullifier_unused=0,
        policy_ok=0,
        burn_amount=0,
        receipt_amount=0,
        burn_budget=30,
        supply_before=1000,
        supply_after=1000,
        batch_burn_sum_before=70,
        batch_burn_sum_after=70,
        expected_valid=1,
    ),
)


STIMULI_BANK: tuple[dict[str, Any], ...] = (
    {
        "stimulus_id": "audit.nullifier",
        "family": "dual_certificate",
        "prompt": "Treat each burn as a consumable receipt with a nullifier. Which minimum public fields prevent double-accounting while keeping cryptography off the Tau path?",
        "design_shift": "Lift replay resistance into explicit host-provided receipt flags.",
    },
    {
        "stimulus_id": "accounting.batch_sum",
        "family": "amortization",
        "prompt": "If auditors only see public receipts and batch roots, what running sum must each accepted burn update so total burn can be recomputed cheaply?",
        "design_shift": "Bind each burn to a public batch burn accumulator.",
    },
    {
        "stimulus_id": "policy.fail_closed",
        "family": "control",
        "prompt": "Assume the crypto verifier and policy binder are external. Which arithmetic relations must still hold locally so any missing host proof forces rejection?",
        "design_shift": "Separate host proof facts from local conservation checks.",
    },
)


LANE_SPEC: dict[str, Any] = {
    "lane_id": "burn_receipt_kernel_v1",
    "title": "Burn Receipt Kernel",
    "representation": "bounded public burn receipt with host-supplied binding flags",
    "abstraction_level": "Tau gate for audited burn accounting, not cryptographic verification",
    "goal": "make buyback/burn receipts replay-resistant and publicly auditable with minimal on-chain/public data",
    "obligations": [
        "accepted burns must bind receipt amount, supply delta, and batch sum delta",
        "replayed receipts must fail closed via nullifier_unused=0",
        "no-burn steps must preserve supply and batch sums",
    ],
    "invariants": [
        "supply_after = supply_before - burn_amount when do_burn=1",
        "batch_burn_sum_after = batch_burn_sum_before + burn_amount when do_burn=1",
        "no burn without receipt_bound and policy_ok",
    ],
    "baseline_families": [
        {
            "name": "tokenomics_buyback_burn_v2",
            "why": "current bounded burn policy spec checks fee splits and burn amount bounds",
            "failure_mode": "does not bind replay resistance or public receipt accumulation",
        }
    ],
    "reformulation_axes": [
        "move from burn amount bounds to receipt-based accounting",
        "separate host proof facts from local arithmetic invariants",
        "add public batch burn accumulation for cheap audits",
    ],
    "performance_descriptors": {
        "asymptotic_profile": "O(1) per receipt",
        "invariant_family": ["replay_guard", "supply_conservation", "public_accumulator"],
        "failure_envelope": ["missing_host_proof_flags", "out_of_range_amounts"],
        "certificate_shape": ["curated_replay_cases", "batch_sum_accounting_cases"],
    },
    "stimulus_ids": [
        "audit.nullifier",
        "accounting.batch_sum",
        "policy.fail_closed",
    ],
    "hypotheses": [
        {
            "hypothesis_id": "burn_receipt_kernel_v1",
            "mechanism_change": "Introduce a dedicated burn receipt kernel with nullifier, receipt-binding, budget, supply, and batch-sum rails.",
            "representation_shift_used": "restrict",
            "expected_metric_delta": [3, 2, 1, 1, 3],
            "null_hypothesis": "The refined burn kernel still permits replay or silent accounting mismatches on the curated receipt corpus.",
            "falsification_recipe": "burn_receipt_replay_rejected",
            "support_recipe": "burn_receipt_accounting_model",
            "formal_obligations": [
                "replay path rejects when nullifier_unused=0",
                "accepted receipt updates supply and batch sum consistently",
                "no-burn path preserves state deltas",
            ],
            "risk_modes": ["host proof flags miswired", "receipt tree/root not anchored elsewhere"],
            "status": "proposed",
        }
    ],
}


def verify_burn_receipt_step(step: BurnReceiptLaneStep) -> bool:
    def sbf(v: int) -> bool:
        return int(v) in (0, 1)

    if not all(sbf(v) for v in (step.do_burn, step.receipt_bound, step.nullifier_unused, step.policy_ok)):
        return False
    if any(v < 0 for v in (
        step.burn_amount,
        step.receipt_amount,
        step.burn_budget,
        step.supply_before,
        step.supply_after,
        step.batch_burn_sum_before,
        step.batch_burn_sum_after,
    )):
        return False
    if any(v > 0x7FFF for v in (step.burn_amount, step.receipt_amount, step.burn_budget, step.batch_burn_sum_before)):
        return False
    if any(v > 0xFFFF for v in (step.supply_before, step.supply_after, step.batch_burn_sum_after)):
        return False
    if int(step.do_burn) == 0:
        return bool(
            step.burn_amount == 0
            and step.receipt_amount == 0
            and step.supply_after == step.supply_before
            and step.batch_burn_sum_after == step.batch_burn_sum_before
        )
    return bool(
        step.receipt_bound == 1
        and step.nullifier_unused == 1
        and step.policy_ok == 1
        and step.burn_amount > 0
        and step.burn_amount == step.receipt_amount
        and step.burn_budget >= step.burn_amount
        and step.supply_before >= step.burn_amount
        and step.supply_after == step.supply_before - step.burn_amount
        and step.batch_burn_sum_after == step.batch_burn_sum_before + step.burn_amount
    )


def lane_packet() -> dict[str, Any]:
    return {
        **LANE_SPEC,
        "stimuli": [stim for stim in STIMULI_BANK if stim["stimulus_id"] in set(LANE_SPEC["stimulus_ids"])],
        "curated_corpus": [step.to_json() for step in BURN_RECEIPT_CURATED_STEPS],
    }
