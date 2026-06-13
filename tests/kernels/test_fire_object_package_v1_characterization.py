"""Characterization corpus for ``verify_fire_object_package``.

This is a *golden oracle* test built with the characterization-corpus-first
technique. We construct one VALID FIRE object package bundle, then apply a
catalog of single-point mutations (drop a section, tamper a digest, flip a
rule, malform a body, trip a cross-dependency precondition, ...). For every
mutation we run the verifier through ``_run_capture`` -- a wrapper that records
``(ok, error)`` AND any raised exception, warts and all -- and compare the
result against a committed JSON corpus.

The corpus locks, for the CURRENT behavior of the verifier:

* every reject code reachable from the package layer by a SINGLE mutation (plus
  a representative slice of the codes delegated to sub-verifiers), and
* the first-failure ordering (each single fault pins the code emitted at its
  position; because the verifier evaluates sections in source order, the
  per-position pins compose into the overall precedence -- two ``DOUBLE_*``
  mutations additionally pin a couple of inter-stage precedences directly).

Known coverage boundaries (structural, not holes closeable with single
mutations -- the relevant codes are SHADOWED by an upstream check that fires
first; reaching them needs a multi-fault bundle, out of scope here):

* Cross-dependency ``*_requires_*`` family: the kernel-settlement receipt block
  runs before the kernel-replay receipt block, so the three
  ``kernel_settlement_receipt_requires_*`` codes are locked by dropping each
  prerequisite, but four of the five ``kernel_replay_receipt_requires_*`` codes
  are shadowed by the settlement block's precedence (dropping a shared
  prerequisite surfaces the settlement code first). Only
  ``kernel_replay_receipt_requires_compile_receipt`` is reachable by a single
  drop (settlement does not require the compile receipt).

* Certificate-semantic codes: any certificate-body mutation trips the upstream
  certificate file-sha / manifest-hash integrity gate (in
  ``verify_fire_registry_bundle``) -- and ``FireIntervalCertificate.from_dict``
  drops unknown keys / raises on a bad enum -- BEFORE the package layer
  schema-validates the certificate or compares its instance-gate claims.
  Consequently ``certificate_schema_invalid``,
  ``certificate_instance_gate_claims_missing`` and
  ``certificate_instance_gate_claims_mismatch`` are NOT reachable by a single
  certificate mutation; the corpus locks the upstream gate codes
  (``certificate_file_sha_mismatch`` / ``certificate_manifest_hash_mismatch`` /
  a raised ``ValueError``) at those positions instead. These three source-level
  codes are therefore absent from the corpus by construction.

Regenerate the corpus (only when an intentional behavior change is made and
reviewed) with::

    python3 tests/kernels/test_fire_object_package_v1_characterization.py --regen

Determinism: errors and exception messages embed the bundle directory (an
absolute, per-run scratch path). ``_run_capture`` normalizes that prefix to the
stable token ``<BUNDLE>`` so the committed corpus is reproducible across
machines and runs. ``exc_type`` is recorded separately so an exception-vs-reject
swap (a behavior change) surfaces as a corpus diff.
"""

from __future__ import annotations

import hashlib
import json
import shutil
import sys
import tempfile
from pathlib import Path
from typing import Any, Callable

# Allow ``python3 tests/kernels/test_..._characterization.py --regen`` (run as
# __main__) to import the ``src`` package by putting the repo root on sys.path.
# Under pytest the repo root is already importable; this is a no-op there.
_REPO_ROOT = Path(__file__).resolve().parents[2]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from src.fire.registry.bundle_v1 import FireRegistryBundleManifest, write_fire_registry_bundle
from src.fire.runtime.burn_boost_call_v1 import (
    BurnBoostCallTerms,
    build_manifest,
    compile_terms,
    render_object_card,
)
from src.fire.verifier.object_package_v1 import verify_fire_object_package


FIXTURE_PATH = Path(__file__).parent / "fixtures" / "object_package_v1_characterization.json"

# Stable terms so the valid bundle is reproducible bit-for-bit (modulo the
# scratch directory, which we never hash into the corpus).
_TERMS = BurnBoostCallTerms(n_notional=10, strike_index=4, cap_index=3, source_upper=9)

_CANON = dict(sort_keys=True, separators=(",", ":"), ensure_ascii=True)

# Maps the artifact key inside ``bundle_manifest["artifacts"]`` to the
# ``FireRegistryBundleManifest`` ``*_sha256`` constructor kwarg, so we can
# re-point a single artifact digest and rebuild the manifest (which recomputes
# ``bundle_hash``). Mirrors the helper used by the hand-written test suite.
_ARTIFACT_SHA_FIELD = {
    "object_manifest": "object_manifest_file_sha256",
    "object_instance": "object_instance_file_sha256",
    "object_lock": "object_lock_file_sha256",
    "certificate": "certificate_file_sha256",
    "object_card": "object_card_sha256",
    "compile_receipt": "compile_receipt_sha256",
    "kernel_receipt": "kernel_receipt_sha256",
    "kernel_eval_receipt": "kernel_eval_receipt_sha256",
    "kernel_settlement_receipt": "kernel_settlement_receipt_sha256",
    "kernel_replay_receipt": "kernel_replay_receipt_sha256",
    "proof_tree_certificate": "proof_tree_certificate_sha256",
    "replay_input": "replay_input_sha256",
    "replay_receipt": "replay_receipt_sha256",
}

# Constructor kwargs accepted by ``FireRegistryBundleManifest.build``; used to
# rebuild the manifest from a parsed instance while overriding one field.
_BUILD_FIELDS = (
    "object_name",
    "object_version",
    "object_family",
    "object_manifest_path",
    "object_manifest_file_sha256",
    "object_instance_path",
    "object_instance_file_sha256",
    "object_lock_path",
    "object_lock_file_sha256",
    "certificate_path",
    "certificate_file_sha256",
    "compile_receipt_path",
    "compile_receipt_sha256",
    "kernel_receipt_path",
    "kernel_receipt_sha256",
    "kernel_eval_receipt_path",
    "kernel_eval_receipt_sha256",
    "kernel_settlement_receipt_path",
    "kernel_settlement_receipt_sha256",
    "kernel_replay_receipt_path",
    "kernel_replay_receipt_sha256",
    "proof_tree_certificate_path",
    "proof_tree_certificate_sha256",
    "object_card_path",
    "object_card_sha256",
    "replay_input_path",
    "replay_input_sha256",
    "replay_receipt_path",
    "replay_receipt_sha256",
    "contract_receipts",
)


# --------------------------------------------------------------------------- #
# Low-level bundle helpers (mutation primitives)                              #
# --------------------------------------------------------------------------- #
def _sha256_bytes(payload: bytes) -> str:
    return "sha256:" + hashlib.sha256(payload).hexdigest()


def _write_canonical(path: Path, payload: Any) -> None:
    path.write_text(json.dumps(payload, **_CANON), encoding="utf-8")


def _read_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def _rebuild_manifest(bundle_dir: Path, **overrides: Any) -> None:
    """Rebuild ``bundle_manifest.json`` from its current contents, applying the
    given constructor-kwarg overrides. ``FireRegistryBundleManifest.build``
    recomputes ``bundle_hash``, so the manifest stays internally consistent.
    """
    manifest = FireRegistryBundleManifest.from_dict(_read_json(bundle_dir / "bundle_manifest.json"))
    kwargs = {field: getattr(manifest, field) for field in _BUILD_FIELDS}
    kwargs.update(overrides)
    rebuilt = FireRegistryBundleManifest.build(**kwargs)
    (bundle_dir / "bundle_manifest.json").write_text(
        json.dumps(rebuilt.to_dict(), indent=2, sort_keys=True),
        encoding="utf-8",
    )


def _repoint_artifact_sha(bundle_dir: Path, artifact_key: str) -> None:
    """Recompute the on-disk digest for ``artifact_key`` and rebuild the manifest
    so the file-sha entry matches the (mutated) file. Used after tampering an
    artifact body when we want to push the verifier PAST the file-integrity gate
    into the artifact's semantic checks.
    """
    art = _read_json(bundle_dir / "bundle_manifest.json")["artifacts"][artifact_key]
    new_sha = _sha256_bytes((bundle_dir / art["path"]).read_bytes())
    _rebuild_manifest(bundle_dir, **{_ARTIFACT_SHA_FIELD[artifact_key]: new_sha})


def _tamper_artifact_field(bundle_dir: Path, artifact_key: str, mutate: Callable[[dict], None]) -> None:
    """Apply ``mutate`` to an artifact's JSON, rewrite it canonically, and
    re-point its digest so the verifier reaches the semantic check."""
    path = bundle_dir / _read_json(bundle_dir / "bundle_manifest.json")["artifacts"][artifact_key]["path"]
    payload = _read_json(path)
    mutate(payload)
    _write_canonical(path, payload)
    _repoint_artifact_sha(bundle_dir, artifact_key)


def _drop_artifact_from_manifest(bundle_dir: Path, artifact_key: str) -> None:
    """Unlink the artifact file AND null its path/sha in the manifest, so the
    optional-section ``require_*`` gate (rather than a load error) fires."""
    art = _read_json(bundle_dir / "bundle_manifest.json")["artifacts"].get(artifact_key)
    if art is not None:
        (bundle_dir / art["path"]).unlink(missing_ok=True)
    sha_field = _ARTIFACT_SHA_FIELD[artifact_key]
    path_field = sha_field.replace("_file_sha256", "_path").replace("_sha256", "_path")
    _rebuild_manifest(bundle_dir, **{sha_field: None, path_field: None})


def _proof_tree_claim(bundle_dir: Path, node_id: str, mutate: Callable[[dict], None]) -> None:
    """Mutate a single proof-tree node's claim, then re-point the proof-tree
    digest. Mirrors the hand-written proof-tree drift tests."""

    def _apply(payload: dict) -> None:
        node = next(n for n in payload["proof_tree"] if isinstance(n, dict) and n.get("id") == node_id)
        mutate(node["claim"])

    _tamper_artifact_field(bundle_dir, "proof_tree_certificate", _apply)


# --------------------------------------------------------------------------- #
# Valid bundle construction                                                   #
# --------------------------------------------------------------------------- #
def _build_valid_bundle(dest: Path) -> tuple[FireRegistryBundleManifest, str]:
    artifact = compile_terms(_TERMS)
    return write_fire_registry_bundle(
        dest,
        artifact=artifact,
        build_manifest=build_manifest,
        render_object_card=render_object_card,
        emit_proof_tree_certificate=True,
    )


# --------------------------------------------------------------------------- #
# Capture wrapper (shared by --regen and the comparison test)                 #
# --------------------------------------------------------------------------- #
def _normalize(text: str | None, bundle_dir: Path) -> str | None:
    """Replace the scratch bundle-root prefix with a stable token so recorded
    errors/exceptions are reproducible across machines and runs."""
    if text is None:
        return None
    out = text
    for needle in (str(bundle_dir.resolve()), str(bundle_dir)):
        out = out.replace(needle, "<BUNDLE>")
    return out


def _run_capture(bundle_dir: Path, **kwargs: Any) -> dict:
    """Run the verifier and record outcome warts-and-all.

    Returns a dict with ``ok``, ``error`` (bundle-root-normalized),
    ``has_verification`` (whether a verification object was returned), and, if a
    call raised, ``exc_type`` + normalized ``exc``.
    """
    try:
        ok, err, verification = verify_fire_object_package(bundle_dir, **kwargs)
    except Exception as exc:  # noqa: BLE001 -- characterization records raises verbatim
        return {
            "ok": None,
            "error": None,
            "has_verification": None,
            "exc_type": type(exc).__name__,
            "exc": _normalize(str(exc), bundle_dir),
        }
    return {
        "ok": ok,
        "error": _normalize(err, bundle_dir),
        "has_verification": verification is not None,
        "exc_type": None,
        "exc": None,
    }


# --------------------------------------------------------------------------- #
# Mutation catalog                                                            #
# --------------------------------------------------------------------------- #
# Each entry: (id, verify_kwargs, mutate_fn). ``mutate_fn`` is applied to a
# fresh copy of the valid bundle before the verifier runs. ``mutate_fn is None``
# means "run the unmodified valid bundle" (the OK anchor). Order is the corpus
# order and is stable.
def _mutation_catalog() -> list[tuple[str, dict, Callable[[Path], None] | None]]:
    cat: list[tuple[str, dict, Callable[[Path], None] | None]] = []

    def add(mid: str, mutate: Callable[[Path], None] | None, **kwargs: Any) -> None:
        cat.append((mid, kwargs, mutate))

    # 0. Anchor: the valid bundle must verify OK (with and without proof tree).
    add("valid_baseline", None)
    add("valid_with_proof_tree_required", None, require_proof_tree_cert=True)
    add(
        "valid_with_expected_hashes",
        None,
        expected_bundle_hash="__VALID_BUNDLE_HASH__",
        expected_bundle_file_sha256="__VALID_BUNDLE_FILE_SHA__",
    )

    # 1. Registry-bundle layer (delegated): wrong expected hashes, dropped /
    #    corrupted required section files -> load failures.
    add(
        "expected_bundle_hash_wrong",
        None,
        expected_bundle_hash="sha256:" + ("0" * 64),
    )
    add(
        "expected_bundle_file_sha_wrong",
        None,
        expected_bundle_file_sha256="sha256:" + ("0" * 64),
    )
    add("drop_bundle_manifest_file", lambda d: (d / "bundle_manifest.json").unlink())
    add("drop_object_manifest_file", lambda d: (d / "object_manifest.json").unlink())
    add("drop_object_instance_file", lambda d: (d / "instance_manifest.json").unlink())
    add("drop_object_lock_file", lambda d: (d / "object_lock.json").unlink())
    add("drop_certificate_file", lambda d: (d / "certificate.json").unlink())
    add("empty_object_manifest_body", lambda d: (d / "object_manifest.json").write_text("{}", encoding="utf-8"))
    add("non_object_certificate_body", lambda d: (d / "certificate.json").write_text("[]", encoding="utf-8"))
    add("malformed_json_object_lock", lambda d: (d / "object_lock.json").write_text("{not json", encoding="utf-8"))

    # 2. Schema validation: inject an unexpected key (additionalProperties=false)
    #    into each artifact that the package layer schema-validates. We re-point
    #    the digest so the verifier reaches the schema gate, not the file gate.
    def _inject_unexpected(artifact_key: str) -> Callable[[Path], None]:
        def _m(d: Path) -> None:
            _tamper_artifact_field(d, artifact_key, lambda p: p.__setitem__("unexpected_field", True))

        return _m

    add("schema_invalid_object_package", lambda d: _bundle_manifest_extra_key(d))
    add("schema_invalid_object_manifest", _inject_unexpected("object_manifest"))
    add("schema_invalid_object_instance", _inject_unexpected("object_instance"))
    add("schema_invalid_object_lock", _inject_unexpected("object_lock"))
    # NOTE: any certificate-body mutation trips the upstream certificate
    # file-sha / manifest-hash gate in verify_fire_registry_bundle BEFORE the
    # package layer schema-validates, so this locks ``certificate_file_sha_mismatch``,
    # NOT ``certificate_schema_invalid`` (which is shadowed -- see docstring).
    add("schema_invalid_certificate", _inject_unexpected("certificate"))
    add(
        "schema_invalid_proof_tree_certificate",
        _inject_unexpected("proof_tree_certificate"),
        require_proof_tree_cert=True,
    )
    add("schema_invalid_compile_receipt", _inject_unexpected("compile_receipt"))
    add("schema_invalid_kernel_receipt", _inject_unexpected("kernel_receipt"))
    add("schema_invalid_kernel_eval_receipt", _inject_unexpected("kernel_eval_receipt"))
    add("schema_invalid_kernel_settlement_receipt", _inject_unexpected("kernel_settlement_receipt"))
    add("schema_invalid_kernel_replay_receipt", _inject_unexpected("kernel_replay_receipt"))
    add("schema_invalid_replay_input", _inject_unexpected("replay_input"))

    # 3. Optional-section require gates: drop the section AND null its manifest
    #    path so the require flag (not a load error) fires.
    add(
        "require_compile_receipt_missing",
        lambda d: _drop_artifact_from_manifest(d, "compile_receipt"),
        require_compile_receipt=True,
    )
    add(
        "require_kernel_receipt_missing",
        lambda d: _drop_artifact_from_manifest(d, "kernel_receipt"),
        require_kernel_receipt=True,
    )
    add(
        "require_kernel_eval_receipt_missing",
        lambda d: _drop_artifact_from_manifest(d, "kernel_eval_receipt"),
        require_kernel_eval_receipt=True,
    )
    add(
        "require_kernel_settlement_receipt_missing",
        lambda d: _drop_artifact_from_manifest(d, "kernel_settlement_receipt"),
        require_kernel_settlement_receipt=True,
    )
    add(
        "require_kernel_replay_receipt_missing",
        lambda d: _drop_artifact_from_manifest(d, "kernel_replay_receipt"),
        require_kernel_replay_receipt=True,
    )
    add(
        "require_replay_input_missing",
        lambda d: _drop_artifact_from_manifest(d, "replay_input"),
        require_replay_input=True,
    )
    add(
        "require_proof_tree_cert_missing",
        lambda d: _drop_artifact_from_manifest(d, "proof_tree_certificate"),
        require_proof_tree_cert=True,
    )

    # 4. Delegated receipt semantic drift (representative slice; full coverage
    #    lives in the hand-written suite). Tamper a checked field and re-point
    #    the digest so the sub-verifier runs and rejects.
    add(
        "compile_receipt_object_hash_drift",
        lambda d: _tamper_artifact_field(
            d, "compile_receipt", lambda p: p.__setitem__("object_hash", "sha256:" + ("6" * 64))
        ),
    )
    add(
        "kernel_receipt_model_id_drift",
        lambda d: _tamper_artifact_field(
            d, "kernel_receipt", lambda p: p.__setitem__("kernel_model_id", "fire_drifted_kernel")
        ),
    )
    add(
        "kernel_eval_receipt_upper_drift",
        lambda d: _tamper_artifact_field(
            d, "kernel_eval_receipt", lambda p: p.__setitem__("compiled_artifact_upper", 31)
        ),
    )
    add(
        "kernel_settlement_receipt_payoff_drift",
        lambda d: _tamper_artifact_field(
            d, "kernel_settlement_receipt", lambda p: p.__setitem__("payoff_out", 1)
        ),
    )
    add(
        "kernel_replay_receipt_delta_drift",
        lambda d: _tamper_artifact_field(
            d, "kernel_replay_receipt", lambda p: p.__setitem__("delta_sha256", "sha256:" + ("7" * 64))
        ),
    )

    # 4b. Cross-dependency preconditions (the ``*_requires_*`` family). The valid
    #     baseline has every artifact present, so these branches only fire when a
    #     prerequisite is removed while the dependent receipt stays. The kernel
    #     settlement block runs before the kernel replay block, so dropping a
    #     prerequisite that BOTH require surfaces the settlement code first; only
    #     the four codes reachable by a single drop are locked here. The other
    #     four replay ``*_requires_*`` codes are shadowed by settlement precedence
    #     and are not constructible with a single mutation (documented in the
    #     module docstring / report, not a coverage hole closeable here).
    add(
        "settlement_requires_replay_input",
        lambda d: _drop_artifact_from_manifest(d, "replay_input"),
    )
    add(
        "settlement_requires_kernel_receipt",
        lambda d: _drop_artifact_from_manifest(d, "kernel_receipt"),
    )
    add(
        "settlement_requires_kernel_eval_receipt",
        lambda d: _drop_artifact_from_manifest(d, "kernel_eval_receipt"),
    )
    add(
        "replay_requires_compile_receipt",
        lambda d: _drop_artifact_from_manifest(d, "compile_receipt"),
    )

    # 5. Certificate instance-gate claims. NOTE: like every certificate-body
    #    edit, these trip an upstream certificate-integrity gate first, so they
    #    lock ``certificate_manifest_hash_mismatch`` / a raised ``ValueError``
    #    (bad enum), NOT the package-layer ``certificate_instance_gate_claims_*``
    #    codes, which are shadowed (see docstring coverage boundary). They still
    #    lock real, distinct current behavior.
    add("certificate_gate_claims_missing", lambda d: _certificate_drop_gate_claims(d))
    add("certificate_gate_claims_mismatch", lambda d: _certificate_flip_gate_claim(d))

    # 6. Proof-tree certificate semantic drift (one per summary the package
    #    layer cross-checks).
    add(
        "proof_tree_certificate_sha_drift",
        lambda d: _proof_tree_top_field(d, "certificate_sha256", "sha256:" + ("9" * 64)),
        require_proof_tree_cert=True,
    )
    add(
        "proof_tree_runtime_summary_drift",
        lambda d: _proof_tree_runtime_upper(d, 31),
        require_proof_tree_cert=True,
    )
    add(
        "proof_tree_replay_summary_drift",
        lambda d: _proof_tree_claim(d, "n_replay", lambda c: c.__setitem__("holder_balance", 999)),
        require_proof_tree_cert=True,
    )
    add(
        "proof_tree_integer_eval_summary_drift",
        lambda d: _proof_tree_claim(d, "n_integer_eval", lambda c: c.__setitem__("runtime_node_count", 999)),
        require_proof_tree_cert=True,
    )
    add(
        "proof_tree_unit_summary_drift",
        lambda d: _proof_tree_claim(d, "n_unit", lambda c: c.__setitem__("settlement_asset", "badUSD")),
        require_proof_tree_cert=True,
    )
    add(
        "proof_tree_witness_policy_summary_drift",
        lambda d: _proof_tree_claim(d, "n_witness", lambda c: c.__setitem__("witness_requirements", [])),
        require_proof_tree_cert=True,
    )
    add(
        "proof_tree_param_summary_drift",
        lambda d: _proof_tree_claim(d, "n_param", lambda c: c["parameters"][0].__setitem__("value", 999)),
        require_proof_tree_cert=True,
    )
    add(
        "proof_tree_authorization_summary_drift",
        lambda d: _proof_tree_claim(
            d, "n_authorization", lambda c: c["bound_parties"][0].__setitem__("party_id", "role:attacker")
        ),
        require_proof_tree_cert=True,
    )
    add(
        "proof_tree_nonce_summary_drift",
        lambda d: _proof_tree_claim(d, "n_nonce", lambda c: c.__setitem__("nonce", "bad:nonce")),
        require_proof_tree_cert=True,
    )
    add(
        "proof_tree_maturity_summary_drift",
        lambda d: _proof_tree_claim(d, "n_maturity", lambda c: c.__setitem__("maturity_present", True)),
        require_proof_tree_cert=True,
    )
    add(
        "proof_tree_window_summary_drift",
        lambda d: _proof_tree_claim(d, "n_window", lambda c: c.__setitem__("settlement_window_present", True)),
        require_proof_tree_cert=True,
    )
    add(
        "proof_tree_object_bind_summary_drift",
        lambda d: _proof_tree_claim(
            d, "n_object_hash", lambda c: c.__setitem__("object_manifest_sha256", "sha256:" + ("9" * 64))
        ),
        require_proof_tree_cert=True,
    )
    add(
        "proof_tree_instance_bind_summary_drift",
        lambda d: _proof_tree_claim(
            d, "n_instance_hash", lambda c: c.__setitem__("instance_manifest_sha256", "sha256:" + ("8" * 64))
        ),
        require_proof_tree_cert=True,
    )
    add(
        "proof_tree_dependency_summary_drift",
        lambda d: _proof_tree_claim(
            d, "n_dependency_closed", lambda c: c.__setitem__("object_lock_sha256", "sha256:" + ("7" * 64))
        ),
        require_proof_tree_cert=True,
    )

    # 7. Double faults: pin a couple of inter-stage precedences directly.
    #    (a) schema gate runs before delegated receipt checks.
    add(
        "DOUBLE_schema_invalid_cert_and_compile_drift",
        lambda d: (
            _tamper_artifact_field(
                d, "compile_receipt", lambda p: p.__setitem__("object_hash", "sha256:" + ("6" * 64))
            ),
            _inject_unexpected("certificate")(d),
        ),
    )
    #    (b) registry-bundle load runs before schema validation.
    add(
        "DOUBLE_drop_object_manifest_and_schema_invalid_cert",
        lambda d: (
            _inject_unexpected("certificate")(d),
            (d / "object_manifest.json").unlink(),
        ),
    )

    # 7b. SCHEMA-validation ORDER among the optionals (regression guard for the
    #     proof-tree-before-receipts precedence). HEAD validates the proof-tree
    #     certificate schema BEFORE the receipt schemas, so when BOTH are faulty
    #     the proof-tree code must win. A naive refactor that reuses the LOAD
    #     order (receipts first) flips this -- exactly the bug Codex found. Each
    #     case injects two schema faults and pins HEAD's first-failure code.
    def _double_schema(*artifact_keys: str) -> Callable[[Path], None]:
        def _m(d: Path) -> None:
            for key in artifact_keys:
                _tamper_artifact_field(d, key, lambda p: p.__setitem__("unexpected_field", True))

        return _m

    # proof-tree must beat each receipt and replay_input.
    add(
        "DOUBLE_schema_proof_tree_before_compile",
        _double_schema("proof_tree_certificate", "compile_receipt"),
        require_proof_tree_cert=True,
    )
    add(
        "DOUBLE_schema_proof_tree_before_kernel",
        _double_schema("proof_tree_certificate", "kernel_receipt"),
        require_proof_tree_cert=True,
    )
    add(
        "DOUBLE_schema_proof_tree_before_kernel_replay",
        _double_schema("proof_tree_certificate", "kernel_replay_receipt"),
        require_proof_tree_cert=True,
    )
    add(
        "DOUBLE_schema_proof_tree_before_replay_input",
        _double_schema("proof_tree_certificate", "replay_input"),
        require_proof_tree_cert=True,
    )
    # receipt-vs-receipt order within the optionals (compile before kernel,
    # kernel before kernel_eval, settlement before replay) -- locks the rest of
    # the schema sequence so a future reorder can't slip through.
    add("DOUBLE_schema_compile_before_kernel", _double_schema("compile_receipt", "kernel_receipt"))
    add("DOUBLE_schema_kernel_before_kernel_eval", _double_schema("kernel_receipt", "kernel_eval_receipt"))
    add(
        "DOUBLE_schema_kernel_eval_before_kernel_settlement",
        _double_schema("kernel_eval_receipt", "kernel_settlement_receipt"),
    )
    add(
        "DOUBLE_schema_kernel_settlement_before_kernel_replay",
        _double_schema("kernel_settlement_receipt", "kernel_replay_receipt"),
    )

    return cat


# --- helpers that don't fit the generic primitives ------------------------- #
def _bundle_manifest_extra_key(bundle_dir: Path) -> None:
    """Inject an unexpected key into bundle_manifest.json (the ``object_package``
    schema target). The package layer validates the raw manifest body against
    the object-package schema BEFORE any bundle-hash gate (no expected hash is
    passed here), so this surfaces as ``object_package_schema_invalid``."""
    path = bundle_dir / "bundle_manifest.json"
    payload = _read_json(path)
    payload["unexpected"] = True
    _write_canonical(path, payload)


def _certificate_drop_gate_claims(bundle_dir: Path) -> None:
    def _m(payload: dict) -> None:
        payload.pop("instance_gate_claims", None)

    _tamper_artifact_field(bundle_dir, "certificate", _m)


def _certificate_flip_gate_claim(bundle_dir: Path) -> None:
    def _m(payload: dict) -> None:
        claims = payload.get("instance_gate_claims")
        if isinstance(claims, dict):
            # Flip the authorization claim to a different supported enum value.
            claims["authorization_ok"] = "not_applicable"

    _tamper_artifact_field(bundle_dir, "certificate", _m)


def _proof_tree_top_field(bundle_dir: Path, key: str, value: Any) -> None:
    _tamper_artifact_field(bundle_dir, "proof_tree_certificate", lambda p: p.__setitem__(key, value))


def _proof_tree_runtime_upper(bundle_dir: Path, upper: int) -> None:
    def _m(payload: dict) -> None:
        payload["runtime_certificate_summary"]["root_interval"]["upper"] = upper

    _tamper_artifact_field(bundle_dir, "proof_tree_certificate", _m)


# --------------------------------------------------------------------------- #
# Corpus generation / loading                                                 #
# --------------------------------------------------------------------------- #
def _resolve_kwargs(kwargs: dict, bundle_manifest: FireRegistryBundleManifest, bundle_file_sha: str) -> dict:
    """Substitute placeholder tokens with the live valid-bundle hashes."""
    resolved = dict(kwargs)
    for key, val in resolved.items():
        if val == "__VALID_BUNDLE_HASH__":
            resolved[key] = bundle_manifest.bundle_hash
        elif val == "__VALID_BUNDLE_FILE_SHA__":
            resolved[key] = bundle_file_sha
    return resolved


def _generate_corpus() -> list[dict]:
    with tempfile.TemporaryDirectory() as scratch:
        scratch_root = Path(scratch)
        base = scratch_root / "valid"
        bundle_manifest, bundle_file_sha = _build_valid_bundle(base)

        records: list[dict] = []
        for mid, kwargs, mutate in _mutation_catalog():
            work = scratch_root / f"work_{mid}"
            shutil.copytree(base, work)
            if mutate is not None:
                mutate(work)
            resolved = _resolve_kwargs(kwargs, bundle_manifest, bundle_file_sha)
            outcome = _run_capture(work, **resolved)
            records.append({"id": mid, "kwargs": _serializable_kwargs(kwargs), **outcome})
            shutil.rmtree(work, ignore_errors=True)
    return records


def _serializable_kwargs(kwargs: dict) -> dict:
    """Record the *placeholder* kwargs (not the live hashes) so the corpus is
    reproducible. Tokens stay as tokens."""
    return dict(kwargs)


def _write_corpus(records: list[dict]) -> None:
    FIXTURE_PATH.parent.mkdir(parents=True, exist_ok=True)
    FIXTURE_PATH.write_text(json.dumps(records, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _load_corpus() -> list[dict]:
    return json.loads(FIXTURE_PATH.read_text(encoding="utf-8"))


# --------------------------------------------------------------------------- #
# Tests                                                                       #
# --------------------------------------------------------------------------- #
def test_characterization_corpus_reproduced_exactly() -> None:
    """The verifier must reproduce the committed corpus byte-for-byte (modulo
    the normalized bundle root). This is the behavior lock."""
    expected = _load_corpus()
    actual = _generate_corpus()
    assert len(actual) == len(expected), (
        f"corpus size drift: catalog={len(actual)} fixture={len(expected)}; "
        "regenerate with --regen if intentional"
    )
    for exp, act in zip(expected, actual):
        assert act == exp, (
            f"behavior drift for mutation {act['id']!r}:\n  expected={exp}\n  actual={act}"
        )


def test_corpus_locks_every_distinct_reject_code() -> None:
    """Sanity: the corpus pins a broad set of distinct reject codes, and every
    non-OK entry actually rejects (no mutation silently passes)."""
    corpus = _load_corpus()
    codes: set[str] = set()
    for rec in corpus:
        if rec["id"].startswith("valid"):
            assert rec["ok"] is True, f"{rec['id']} should be the OK anchor"
            assert rec["error"] is None
            continue
        # Every mutation must change behavior away from clean accept.
        rejected = rec["ok"] is False or rec["ok"] is None
        assert rejected, f"mutation {rec['id']!r} did not reject (locks nothing): {rec}"
        if rec["error"]:
            codes.add(rec["error"].split(":", 1)[0])
        elif rec["exc_type"]:
            codes.add(f"<exc:{rec['exc_type']}>")
    # Lower bound below the current count so adding a mutation can't silently
    # drop coverage without tripping this guard.
    assert len(codes) >= 45, f"expected >=45 distinct reject codes, got {len(codes)}: {sorted(codes)}"


# --------------------------------------------------------------------------- #
# Teeth: explicit mutation tests that MUST go red under their mutation.       #
# Each builds a fresh bundle, applies the mutation, and asserts the verifier   #
# rejects with the locked code (proving the corpus has teeth, not just shape). #
# --------------------------------------------------------------------------- #
def _fresh_bundle(tmp_path: Path) -> tuple[Path, FireRegistryBundleManifest, str]:
    d = tmp_path / "burn_bundle"
    bm, sha = _build_valid_bundle(d)
    return d, bm, sha


def test_tooth_empty_required_body_must_fail(tmp_path) -> None:
    """An emptied required section (object_manifest -> {}) MUST be rejected.

    Empty body trips the registry bundle's structural load check rather than a
    path-bearing message; what matters is that an empty required body is never
    accepted. Corpus entry ``empty_object_manifest_body`` locks the exact code.
    """
    d, _, _ = _fresh_bundle(tmp_path)
    (d / "object_manifest.json").write_text("{}", encoding="utf-8")
    ok, err, verification = verify_fire_object_package(d)
    assert ok is False and verification is None
    assert err == "bundle_load_failed:artifact_bound must be a dict"  # catches: empty required body


def test_tooth_dropped_section_must_fail(tmp_path) -> None:
    """A dropped required section file MUST be rejected (load failure)."""
    d, _, _ = _fresh_bundle(tmp_path)
    (d / "object_lock.json").unlink()
    ok, err, verification = verify_fire_object_package(d)
    assert ok is False and verification is None
    assert err is not None and err.startswith("bundle_load_failed")  # catches: dropped section


def test_tooth_downgraded_verdict_must_fail(tmp_path) -> None:
    """A downgraded proof-tree verdict (object-bind hash flipped to a lie) MUST
    be rejected -- the package must not accept a certificate that no longer binds
    the object it claims to certify."""
    d, bm, _ = _fresh_bundle(tmp_path)
    _proof_tree_claim(d, "n_object_hash", lambda c: c.__setitem__("object_manifest_sha256", "sha256:" + ("9" * 64)))
    ok, err, verification = verify_fire_object_package(d, require_proof_tree_cert=True)
    assert ok is False and verification is None
    assert err == "proof_tree_cert_object_bind_summary_mismatch"  # catches: downgraded verdict


# --------------------------------------------------------------------------- #
# Regeneration entry point                                                     #
# --------------------------------------------------------------------------- #
def main(argv: list[str]) -> int:
    if "--regen" in argv:
        records = _generate_corpus()
        _write_corpus(records)
        rejects = sum(1 for r in records if r["ok"] is not True)
        print(f"wrote {len(records)} corpus entries ({rejects} rejecting) -> {FIXTURE_PATH}")
        return 0
    print("usage: python3 test_fire_object_package_v1_characterization.py --regen")
    return 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
