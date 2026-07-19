from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_nginx_config_hardens_api_body_limit_and_static_headers() -> None:
    text = (ROOT / ".docker/nginx.conf").read_text(encoding="utf-8")

    assert "client_max_body_size 512k;" in text
    assert "proxy_pass http://127.0.0.1:8000;" in text
    assert "proxy_pass http://127.0.0.1:8000/;" not in text
    static_block = text.split("location ~* \\.(js|css|png|jpg|jpeg|gif|ico|svg|woff|woff2)$ {", 1)[1]
    for header in (
        'add_header X-Frame-Options "DENY" always;',
        'add_header X-Content-Type-Options "nosniff" always;',
        'add_header Content-Security-Policy "default-src \'self\';',
    ):
        assert header in static_block


def test_production_docker_context_excludes_host_build_and_bytecode_artifacts() -> None:
    text = (ROOT / ".dockerignore").read_text(encoding="utf-8")

    for pattern in (
        "**/__pycache__/",
        "**/*.py[cod]",
        "tools/dex-ui/node_modules/",
        "tools/dex-ui/dist/",
    ):
        assert pattern in text


def test_production_container_requires_chain_bound_demo_free_runtime_config() -> None:
    entrypoint = (ROOT / ".docker/entrypoint.sh").read_text(encoding="utf-8")
    compose = (ROOT / "docker-compose.yml").read_text(encoding="utf-8")
    dockerfile = (ROOT / "Dockerfile").read_text(encoding="utf-8")

    assert 'ZENODEX_ENV="${ZENODEX_ENV:-production}"' in entrypoint
    assert "TAU_DEX_CHAIN_ID is required in production" in entrypoint
    assert "/validate_production_ui_config.py" in entrypoint
    validator = (ROOT / ".docker/validate_production_ui_config.py").read_text(encoding="utf-8")
    assert "FORBIDDEN_CAPABILITY_KEYS" in validator
    for key in ("demoMode", "allowDemoMode", "allowBrowserKeyGeneration"):
        assert f'"{key}"' in validator
    assert "forbidden_capability_key" in validator
    assert "chain_id_mismatch" in validator
    assert "TAU_DEX_CHAIN_ID=${TAU_DEX_CHAIN_ID:?" in compose
    assert "ZENODEX_RUNTIME_CONFIG_PATH:?" in compose
    assert "./src/integration/autotrader_live_api.py" in dockerfile
    assert "./src/integration/confidential_attestation_api.py" in dockerfile
    assert "COPY .docker/validate_production_ui_config.py /validate_production_ui_config.py" in dockerfile


def test_dependency_manifests_split_runtime_from_agent_packages() -> None:
    dockerfile = (ROOT / "Dockerfile").read_text(encoding="utf-8")
    requirements = (ROOT / "requirements.txt").read_text(encoding="utf-8")

    assert (
        "COPY requirements-core.txt ./" in dockerfile
        or "COPY requirements-core.lock.txt ./" in dockerfile
    )
    assert (
        "-r requirements-core.txt" in dockerfile
        or "-r requirements-core.lock.txt" in dockerfile
    )
    assert "requirements-agents" not in dockerfile
    assert "-r requirements-core.txt" in requirements
    assert "-r requirements-agents.txt" in requirements


def test_python_install_surfaces_use_hash_locked_requirements() -> None:
    dockerfile = (ROOT / "Dockerfile").read_text(encoding="utf-8")
    readme = (ROOT / "README.md").read_text(encoding="utf-8")
    prod_gate = (ROOT / "tools/prod_gate.sh").read_text(encoding="utf-8")
    release_gate = (ROOT / "tools/run_release_gate.sh").read_text(encoding="utf-8")

    assert "--require-hashes -r requirements-core.lock.txt" in dockerfile
    assert "--require-hashes -r requirements-dev.lock.txt" in readme
    assert "--require-hashes -r \"$DEV_LOCK\"" in prod_gate
    assert "tools/check_python_hash_locks.py" in release_gate
    assert "tests/test_check_python_hash_locks.py" in release_gate
    assert "tools/check_proof_toolchain_lock.py" in release_gate
    assert "tools/check_zeno_ledger_proof_coverage_matrix.py" in release_gate
    assert "tests/tools/test_check_zeno_ledger_proof_coverage_matrix.py" in release_gate
    assert "tools/build_zeno_ledger_two_machine_evidence.py" in release_gate
    assert "tools/check_zeno_ledger_two_machine_evidence.py" in release_gate
    assert "tests/tools/test_build_zeno_ledger_two_machine_evidence.py" in release_gate
    assert "tests/tools/test_check_zeno_ledger_two_machine_evidence.py" in release_gate
    assert "tools/check_covered_user_interface_boundary.py" in release_gate
    assert "internal/covered_user_interface/COVERED_USER_INTERFACE_BOUNDARY_V0.json" in release_gate
    assert "tests/tools/test_check_covered_user_interface_boundary.py" in release_gate
    assert "tools/check_zeno_economic_games_boundary.py" in release_gate
    assert "internal/tokenomics/ZENO_ECONOMIC_GAMES_BOUNDARY_V0.json" in release_gate
    assert "tests/tools/test_check_zeno_economic_games_boundary.py" in release_gate
    assert "tools/check_zeno_treasury_custody_boundary.py" in release_gate
    assert "internal/tokenomics/ZENO_TREASURY_CUSTODY_BOUNDARY_V0.json" in release_gate
    assert "tests/tools/test_check_zeno_treasury_custody_boundary.py" in release_gate
    assert "tools/check_tokenomics_candidate_model.py" in release_gate
    assert "internal/tokenomics/ZENO_TOKENOMICS_CANDIDATE_MODEL_V0.json" in release_gate
    assert "tools/check_burn_indexed_unlock_accelerator.py" in release_gate
    assert "internal/tokenomics/ZENO_BURN_INDEXED_UNLOCK_ACCELERATOR_V0.json" in release_gate
    assert "tests/tools/test_check_burn_indexed_unlock_accelerator.py" in release_gate
    assert "tools/check_tokenomics_reward_safety_envelope.py" in release_gate
    assert "internal/tokenomics/ZENO_TOKENOMICS_REWARD_SAFETY_ENVELOPE_V0.json" in release_gate
    assert "tests/tools/test_check_tokenomics_candidate_model.py" in release_gate
    assert "tests/tools/test_check_tokenomics_reward_safety_envelope.py" in release_gate
    assert "tools/check_gamification_manifest.py" in release_gate
    assert "internal/gamification/GAMIFICATION_MANIFEST_V0.json" in release_gate
    assert "tests/tools/test_check_gamification_manifest.py" in release_gate
    assert "Proofs/ZenoDEXStakingShareSafety.lean" in release_gate
    assert "tests/formal/test_lean_zenodex_staking_share_safety.py" in release_gate
    assert "tools/upba_v1_grid_economic_profile.py" in release_gate
    assert "tests/tools/test_upba_v1_grid_economic_profile.py" in release_gate
    assert "Proofs/UniformBatchOptimality.lean" in release_gate
    assert "tests/core/test_uniform_batch_optimality.py" in release_gate
    assert "tests/integration/test_dex_engine_uniform_batch_certificate.py" in release_gate
    assert "tools/check_production_boundary.py" in release_gate
    assert "require_uniform_batch_v3_exact_out_grid_optimality" in (
        ROOT / "src/integration/dex_engine.py"
    ).read_text(encoding="utf-8")
    assert "tools/zeno_ledger_risc0_proof_metadata.py" in release_gate
    assert "tools/zeno_ledger_risc0_real_proof_smoke.py" in release_gate
    assert "tools/check_zeno_ledger_risc0_real_proof_smoke_report.py" in release_gate
    assert "tests/integration/test_zeno_ledger_risc0_proof_metadata.py" in release_gate
    assert "tests/test_check_zeno_ledger_risc0_real_proof_smoke_report.py" in release_gate
    assert "tools/confidential_attestation_verifier_rust/Cargo.toml" in release_gate
    assert "tests/integration/test_zeno_ledger_tee_proof_metadata.py" in release_gate
    assert "tests/tools/test_check_confidential_route_quote_bundle.py" in release_gate
    assert "tools/check_zenocover_lp_loss_cover.py" in release_gate
    assert "tests/tools/test_check_zenocover_regulatory_boundary.py" in release_gate
    assert "tests/tools/test_check_zenocover_lp_loss_cover.py" in release_gate
    assert "tests/tools/test_check_zenocover_reserve_solvency.py" in release_gate
    assert "tests/tools/test_check_zenocover_claim_verifier_model.py" in release_gate
    assert "tests/tools/test_check_zenocover_reserve_withdrawal_safety.py" in release_gate
    assert "Proofs/ZenoCoverPayoutCap.lean" in release_gate
    assert "tests/formal/test_lean_zenocover_payout_cap.py" in release_gate
    assert "tools/check_zenocover_attack_queries.py" in release_gate
    assert "tests/tools/test_check_zenocover_attack_queries.py" in release_gate
    assert "tests/integration/test_zeno_ledger_v0.py::test_validator_set_rejects_duplicate_ids_and_zero_voting_power" in release_gate
    assert "tests/integration/test_zeno_ledger_v0.py::test_validate_body_rejects_batch_cutoff_chain_id_mismatch" in release_gate
    assert "tests/integration/test_zeno_ledger_v0.py::test_validate_body_rejects_batch_cutoff_height_mismatch" in release_gate
    assert "tests/integration/test_zeno_ledger_v0.py::test_validate_body_rejects_ingress_receipt_context_mismatch" in release_gate
    assert "tests/integration/test_zeno_ledger_v0.py::test_validate_body_rejects_forced_inclusion_chain_id_mismatch" in release_gate
    assert "tests/integration/test_zeno_ledger_v0.py::test_detect_header_equivocations_reports_conflicting_height" in release_gate
    assert "tests/integration/test_zeno_ledger_node.py::test_zeno_ledger_pull_rejects_peer_before_live_fetch_on_admission_mismatch" in release_gate
    assert "tests/integration/test_zeno_ledger_node.py::test_zeno_ledger_node_public_operator_rejects_inline_auth_tokens" in release_gate
    assert "tests/integration/test_zeno_ledger_node.py::test_zeno_ledger_node_public_operator_rejects_public_fixture_endpoints" in release_gate
    assert "tests/integration/test_zeno_ledger_node.py::test_zeno_ledger_node_public_operator_accepts_local_env_auth_forwarding" in release_gate

    workflow_paths = sorted((ROOT / ".github/workflows").glob("*.yml"))
    assert workflow_paths
    for path in workflow_paths:
        text = path.read_text(encoding="utf-8")
        if "pip install" in text:
            assert "pip install --require-hashes -r requirements-dev.lock.txt" in text
