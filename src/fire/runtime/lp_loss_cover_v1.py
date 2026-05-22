from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path

from src.fire.compiler.fmos_file_v1 import bind_fire_math_object_spec_file
from src.fire.compiler.fmos_v1 import (
    build_fmos_manifest,
    compile_fmos_artifact,
    holder_collateral_required as fmos_holder_collateral_required,
    render_fmos_object_card,
    writer_collateral_required as fmos_writer_collateral_required,
)
from src.fire.pathing_v1 import resolve_fire_spec_path
from src.fire.registry.object_manifest_v1 import FireObjectManifest
from src.fire.runtime.common_v1 import require_bounded_int, run_verified_settlement
from src.fire.verifier.cert_v1 import (
    FireCertEnv,
    FireInterval,
    FireIntervalCertificate,
    _require_sha256_prefixed,
)
from src.fire.verifier.settlement_v1 import FireVerifierReceipt
from src.fire.kernel import fire_lp_loss_cover_v1_ref as ref


IR_HASH = "sha256:bf1509a7c86dfd9cd2d353133de9abf879f2fdf2279c4bd3114636233e8e7be4"
NOTIONAL_MAX = 1_000
VALUE_MAX = 1_000
COLLATERAL_MAX = 1_000_000
OBJECT_NAME = "LPLossCover"
OBJECT_VERSION = "v1"
OBJECT_FAMILY = "capped_lp_loss_cover"
SETTLEMENT_ASSET = "zUSD"
PAYOFF_SUMMARY = "N * min(max(HODL_T - LPV_T - D, 0), Cap)"


@dataclass(frozen=True)
class LPLossCoverTerms:
    n_notional: int
    deductible: int
    cap_amount: int
    hodl_lower: int
    hodl_upper: int
    lpv_lower: int
    lpv_upper: int

    def __post_init__(self) -> None:
        object.__setattr__(
            self, "n_notional", require_bounded_int("n_notional", self.n_notional, minimum=0, maximum=NOTIONAL_MAX)
        )
        object.__setattr__(
            self, "deductible", require_bounded_int("deductible", self.deductible, minimum=0, maximum=VALUE_MAX)
        )
        object.__setattr__(
            self, "cap_amount", require_bounded_int("cap_amount", self.cap_amount, minimum=0, maximum=VALUE_MAX)
        )
        object.__setattr__(
            self, "hodl_lower", require_bounded_int("hodl_lower", self.hodl_lower, minimum=0, maximum=VALUE_MAX)
        )
        object.__setattr__(
            self, "hodl_upper", require_bounded_int("hodl_upper", self.hodl_upper, minimum=0, maximum=VALUE_MAX)
        )
        object.__setattr__(
            self, "lpv_lower", require_bounded_int("lpv_lower", self.lpv_lower, minimum=0, maximum=VALUE_MAX)
        )
        object.__setattr__(
            self, "lpv_upper", require_bounded_int("lpv_upper", self.lpv_upper, minimum=0, maximum=VALUE_MAX)
        )
        if self.hodl_lower > self.hodl_upper:
            raise ValueError("hodl interval out of order")
        if self.lpv_lower > self.lpv_upper:
            raise ValueError("lpv interval out of order")


@dataclass(frozen=True)
class LPLossCoverArtifact:
    terms: LPLossCoverTerms
    artifact_lower: int
    artifact_upper: int
    certificate: FireIntervalCertificate
    cert_sha256: str
    manifest_sha256: str | None = None
    manifest_file_sha256: str | None = None
    ir_hash: str = IR_HASH

    def __post_init__(self) -> None:
        if not isinstance(self.terms, LPLossCoverTerms):
            raise TypeError("terms must be a LPLossCoverTerms")
        object.__setattr__(
            self,
            "artifact_lower",
            require_bounded_int("artifact_lower", self.artifact_lower, minimum=0, maximum=COLLATERAL_MAX),
        )
        object.__setattr__(
            self,
            "artifact_upper",
            require_bounded_int("artifact_upper", self.artifact_upper, minimum=0, maximum=COLLATERAL_MAX),
        )
        if not isinstance(self.certificate, FireIntervalCertificate):
            raise TypeError("certificate must be a FireIntervalCertificate")
        object.__setattr__(self, "cert_sha256", _require_sha256_prefixed("cert_sha256", self.cert_sha256))
        if self.manifest_sha256 is not None:
            object.__setattr__(self, "manifest_sha256", _require_sha256_prefixed("manifest_sha256", self.manifest_sha256))
        if self.manifest_file_sha256 is not None:
            object.__setattr__(
                self, "manifest_file_sha256", _require_sha256_prefixed("manifest_file_sha256", self.manifest_file_sha256)
            )
        if not isinstance(self.ir_hash, str):
            raise TypeError("ir_hash must be a string")


@dataclass(frozen=True)
class LPLossCoverSettlement:
    artifact: LPLossCoverArtifact
    witness_hodl_final: int
    witness_lpv_final: int
    holder_posted: int
    writer_posted: int
    holder_delta: int
    writer_delta: int
    verifier_receipt: FireVerifierReceipt


@dataclass(frozen=True)
class LPLossCoverResult:
    ok: bool
    settlement: LPLossCoverSettlement | None = None
    error: str | None = None


def _compile_state(terms: LPLossCoverTerms) -> ref.State:
    result = ref.step(
        ref.init_state(),
        ref.Command(
            tag="compile_lp_loss_cover",
            args={
                "n_in": terms.n_notional,
                "deductible_in": terms.deductible,
                "cap_in": terms.cap_amount,
                "hodl_lower_in": terms.hodl_lower,
                "hodl_upper_in": terms.hodl_upper,
                "lpv_lower_in": terms.lpv_lower,
                "lpv_upper_in": terms.lpv_upper,
            },
        ),
    )
    if not result.ok or result.state is None:
        raise RuntimeError(result.error or "compile_lp_loss_cover rejected")
    return result.state


def _certificate_env(terms: LPLossCoverTerms) -> FireCertEnv:
    return FireCertEnv(
        exact_values={
            "n_notional": terms.n_notional,
            "deductible": terms.deductible,
            "cap_amount": terms.cap_amount,
        },
        source_bounds={
            "hodl_final": FireInterval(lower=terms.hodl_lower, upper=terms.hodl_upper),
            "lpv_final": FireInterval(lower=terms.lpv_lower, upper=terms.lpv_upper),
        },
    )


def _compiled_state_from_artifact(artifact: LPLossCoverArtifact) -> ref.State:
    state = ref.State(
        artifact_lower=artifact.artifact_lower,
        artifact_upper=artifact.artifact_upper,
        cap_amount=artifact.terms.cap_amount,
        deductible=artifact.terms.deductible,
        hodl_lower=artifact.terms.hodl_lower,
        hodl_upper=artifact.terms.hodl_upper,
        holder_delta=0,
        holder_posted=0,
        lpv_lower=artifact.terms.lpv_lower,
        lpv_upper=artifact.terms.lpv_upper,
        n_notional=artifact.terms.n_notional,
        phase="Compiled",
        witness_hodl_final=0,
        witness_lpv_final=0,
        writer_delta=0,
        writer_posted=0,
    )
    ok, failed = ref.check_invariants(state)
    if not ok:
        raise RuntimeError(f"compiled artifact state violates invariant: {failed}")
    return state


def compile_terms(terms: LPLossCoverTerms) -> LPLossCoverArtifact:
    return compile_fmos_artifact(SPEC, terms)


def holder_collateral_required(artifact: LPLossCoverArtifact) -> int:
    return fmos_holder_collateral_required(artifact)


def writer_collateral_required(artifact: LPLossCoverArtifact) -> int:
    return fmos_writer_collateral_required(artifact)


def build_manifest(artifact: LPLossCoverArtifact) -> FireObjectManifest:
    if not isinstance(artifact, LPLossCoverArtifact):
        raise TypeError("artifact must be a LPLossCoverArtifact")
    return build_fmos_manifest(SPEC, artifact)


def render_object_card(artifact: LPLossCoverArtifact) -> str:
    return render_fmos_object_card(SPEC, artifact)


SPEC_PATH = resolve_fire_spec_path("lp_loss_cover_v1")


SPEC = bind_fire_math_object_spec_file(
    SPEC_PATH,
    terms_type=LPLossCoverTerms,
    artifact_type=LPLossCoverArtifact,
    compile_state=_compile_state,
    compiled_state_from_artifact=_compiled_state_from_artifact,
)


def verify_and_settle(
    *,
    artifact: LPLossCoverArtifact,
    witness_hodl_final: int,
    witness_lpv_final: int,
    holder_posted: int,
    writer_posted: int,
    persisted_bundle_dir: str | Path | None = None,
    expected_bundle_hash: str | None = None,
    expected_bundle_file_sha256: str | None = None,
) -> LPLossCoverResult:
    if not isinstance(artifact, LPLossCoverArtifact):
        raise TypeError("artifact must be a LPLossCoverArtifact")
    witness_hodl_final = require_bounded_int(
        "witness_hodl_final", witness_hodl_final, minimum=0, maximum=VALUE_MAX
    )
    witness_lpv_final = require_bounded_int(
        "witness_lpv_final", witness_lpv_final, minimum=0, maximum=VALUE_MAX
    )
    holder_posted = require_bounded_int("holder_posted", holder_posted, minimum=0, maximum=COLLATERAL_MAX)
    writer_posted = require_bounded_int("writer_posted", writer_posted, minimum=0, maximum=COLLATERAL_MAX)

    ok, err, state, receipt = run_verified_settlement(
        artifact,
        expected_ir_hash=IR_HASH,
        certificate_env=_certificate_env,
        manifest_builder=build_manifest,
        persisted_bundle_dir=persisted_bundle_dir,
        expected_bundle_hash=expected_bundle_hash,
        expected_bundle_file_sha256=expected_bundle_file_sha256,
        compiled_state_from_artifact=_compiled_state_from_artifact,
        ref_module=ref,
        settle_args={
            "witness_hodl_final_in": witness_hodl_final,
            "witness_lpv_final_in": witness_lpv_final,
            "holder_posted_in": holder_posted,
            "writer_posted_in": writer_posted,
        },
        witness_inputs={
            "witness_hodl_final": witness_hodl_final,
            "witness_lpv_final": witness_lpv_final,
        },
    )
    if not ok or state is None or receipt is None:
        return LPLossCoverResult(ok=False, error=err or "settlement_rejected")

    return LPLossCoverResult(
        ok=True,
        settlement=LPLossCoverSettlement(
            artifact=artifact,
            witness_hodl_final=witness_hodl_final,
            witness_lpv_final=witness_lpv_final,
            holder_posted=holder_posted,
            writer_posted=writer_posted,
            holder_delta=state.holder_delta,
            writer_delta=state.writer_delta,
            verifier_receipt=receipt,
        ),
    )


__all__ = [
    "LPLossCoverArtifact",
    "LPLossCoverResult",
    "LPLossCoverSettlement",
    "LPLossCoverTerms",
    "SPEC",
    "build_manifest",
    "compile_terms",
    "holder_collateral_required",
    "render_object_card",
    "verify_and_settle",
    "writer_collateral_required",
]
