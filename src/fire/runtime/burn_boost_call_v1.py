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
from src.fire.kernel import fire_burn_boost_call_v1_ref as ref


IR_HASH = "sha256:b26b68dbadb3313ef59399eeb2f7f180ea9775bffd3e797c27186a0d5daddc61"
NOTIONAL_MAX = 1_000
INDEX_MAX = 1_000
COLLATERAL_MAX = 1_000_000
OBJECT_NAME = "BurnBoostCall"
OBJECT_VERSION = "v1"
OBJECT_FAMILY = "capped_index_call"
SETTLEMENT_ASSET = "zUSD"
PAYOFF_SUMMARY = "N * min(max(BurnIndex_T - K, 0), Cap)"


@dataclass(frozen=True)
class BurnBoostCallTerms:
    n_notional: int
    strike_index: int
    cap_index: int
    source_upper: int

    def __post_init__(self) -> None:
        object.__setattr__(
            self, "n_notional", require_bounded_int("n_notional", self.n_notional, minimum=0, maximum=NOTIONAL_MAX)
        )
        object.__setattr__(
            self, "strike_index", require_bounded_int("strike_index", self.strike_index, minimum=0, maximum=INDEX_MAX)
        )
        object.__setattr__(
            self, "cap_index", require_bounded_int("cap_index", self.cap_index, minimum=0, maximum=INDEX_MAX)
        )
        object.__setattr__(
            self, "source_upper", require_bounded_int("source_upper", self.source_upper, minimum=0, maximum=INDEX_MAX)
        )


@dataclass(frozen=True)
class BurnBoostCallArtifact:
    terms: BurnBoostCallTerms
    artifact_lower: int
    artifact_upper: int
    certificate: FireIntervalCertificate
    cert_sha256: str
    manifest_sha256: str | None = None
    manifest_file_sha256: str | None = None
    ir_hash: str = IR_HASH

    def __post_init__(self) -> None:
        if not isinstance(self.terms, BurnBoostCallTerms):
            raise TypeError("terms must be a BurnBoostCallTerms")
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
class BurnBoostCallSettlement:
    artifact: BurnBoostCallArtifact
    witness_final: int
    holder_posted: int
    writer_posted: int
    holder_delta: int
    writer_delta: int
    verifier_receipt: FireVerifierReceipt


@dataclass(frozen=True)
class BurnBoostCallResult:
    ok: bool
    settlement: BurnBoostCallSettlement | None = None
    error: str | None = None


def _compile_state(terms: BurnBoostCallTerms) -> ref.State:
    result = ref.step(
        ref.init_state(),
        ref.Command(
            tag="compile_burn_boost_call",
            args={
                "n_in": terms.n_notional,
                "strike_in": terms.strike_index,
                "cap_in": terms.cap_index,
                "source_upper_in": terms.source_upper,
            },
        ),
    )
    if not result.ok or result.state is None:
        raise RuntimeError(result.error or "compile_burn_boost_call rejected")
    return result.state


def _certificate_env(terms: BurnBoostCallTerms) -> FireCertEnv:
    return FireCertEnv(
        exact_values={
            "n_notional": terms.n_notional,
            "strike_index": terms.strike_index,
            "cap_index": terms.cap_index,
        },
        source_bounds={
            "burn_final": FireInterval(lower=0, upper=terms.source_upper),
        },
    )


def _compiled_state_from_artifact(artifact: BurnBoostCallArtifact) -> ref.State:
    state = ref.State(
        artifact_lower=artifact.artifact_lower,
        artifact_upper=artifact.artifact_upper,
        cap_index=artifact.terms.cap_index,
        holder_delta=0,
        holder_posted=0,
        n_notional=artifact.terms.n_notional,
        phase="Compiled",
        source_upper=artifact.terms.source_upper,
        strike_index=artifact.terms.strike_index,
        witness_final=0,
        writer_delta=0,
        writer_posted=0,
    )
    ok, failed = ref.check_invariants(state)
    if not ok:
        raise RuntimeError(f"compiled artifact state violates invariant: {failed}")
    return state


def compile_terms(terms: BurnBoostCallTerms) -> BurnBoostCallArtifact:
    return compile_fmos_artifact(SPEC, terms)


def holder_collateral_required(artifact: BurnBoostCallArtifact) -> int:
    return fmos_holder_collateral_required(artifact)


def writer_collateral_required(artifact: BurnBoostCallArtifact) -> int:
    return fmos_writer_collateral_required(artifact)


def build_manifest(artifact: BurnBoostCallArtifact) -> FireObjectManifest:
    if not isinstance(artifact, BurnBoostCallArtifact):
        raise TypeError("artifact must be a BurnBoostCallArtifact")
    return build_fmos_manifest(SPEC, artifact)


def render_object_card(artifact: BurnBoostCallArtifact) -> str:
    return render_fmos_object_card(SPEC, artifact)


SPEC_PATH = resolve_fire_spec_path("burn_boost_call_v1")


SPEC = bind_fire_math_object_spec_file(
    SPEC_PATH,
    terms_type=BurnBoostCallTerms,
    artifact_type=BurnBoostCallArtifact,
    compile_state=_compile_state,
    compiled_state_from_artifact=_compiled_state_from_artifact,
)


def verify_and_settle(
    *,
    artifact: BurnBoostCallArtifact,
    witness_final: int,
    holder_posted: int,
    writer_posted: int,
    persisted_bundle_dir: str | Path | None = None,
    expected_bundle_hash: str | None = None,
    expected_bundle_file_sha256: str | None = None,
) -> BurnBoostCallResult:
    if not isinstance(artifact, BurnBoostCallArtifact):
        raise TypeError("artifact must be a BurnBoostCallArtifact")
    witness_final = require_bounded_int("witness_final", witness_final, minimum=0, maximum=INDEX_MAX)
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
            "witness_final_in": witness_final,
            "holder_posted_in": holder_posted,
            "writer_posted_in": writer_posted,
        },
        witness_inputs={"witness_final": witness_final},
    )
    if not ok or state is None or receipt is None:
        return BurnBoostCallResult(ok=False, error=err or "settlement_rejected")

    return BurnBoostCallResult(
        ok=True,
        settlement=BurnBoostCallSettlement(
            artifact=artifact,
            witness_final=witness_final,
            holder_posted=holder_posted,
            writer_posted=writer_posted,
            holder_delta=state.holder_delta,
            writer_delta=state.writer_delta,
            verifier_receipt=receipt,
        ),
    )


__all__ = [
    "BurnBoostCallArtifact",
    "BurnBoostCallResult",
    "BurnBoostCallSettlement",
    "BurnBoostCallTerms",
    "SPEC",
    "build_manifest",
    "compile_terms",
    "holder_collateral_required",
    "render_object_card",
    "verify_and_settle",
    "writer_collateral_required",
]
