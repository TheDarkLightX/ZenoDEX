#!/usr/bin/env bash
set -euo pipefail

python3 tools/zenodex_oracle_cli.py doctor
python3 tools/zenodex_oracle_cli.py chaos all

pytest -q \
  tests/test_zenodex_oracle_cli.py \
  tests/test_zenodex_oracle_mvp_completion_audit.py \
  tests/test_zenodex_oracle.py \
  tests/test_zenodex_oracle_chaos.py \
  tests/test_zenodex_oracle_budget.py \
  tests/test_zenodex_oracle_budget_chaos.py \
  tests/test_zenodex_oracle_reporter_lifecycle.py \
  tests/test_zenodex_oracle_reporter_lifecycle_chaos.py \
  tests/test_zenodex_oracle_signed_report.py \
  tests/test_zenodex_oracle_signed_report_chaos.py \
  tests/test_zenodex_oracle_report_admission.py \
  tests/test_zenodex_oracle_report_admission_chaos.py \
  tests/test_zenodex_oracle_median3.py \
  tests/test_zenodex_oracle_median3_chaos.py \
  tests/test_zenodex_oracle_admitted_median3.py \
  tests/test_zenodex_oracle_admitted_median3_chaos.py \
  tests/test_zenodex_oracle_aggregate_read.py \
  tests/test_zenodex_oracle_aggregate_read_chaos.py \
  tests/test_zenodex_oracle_aggregate_adapter.py \
  tests/test_zenodex_oracle_aggregate_adapter_chaos.py \
  tests/test_zenodex_oracle_feed_registry.py \
  tests/test_zenodex_oracle_feed_registry_chaos.py \
  tests/test_zenodex_oracle_source_diversity.py \
  tests/test_zenodex_oracle_source_diversity_chaos.py \
  tests/test_zenodex_oracle_query_policy.py \
  tests/test_zenodex_oracle_query_policy_chaos.py \
  tests/test_zenodex_oracle_adapter.py \
  tests/test_zenodex_oracle_adapter_chaos.py \
  tests/test_zenodex_oracle_consumer_profiles.py \
  tests/test_zenodex_oracle_consumer_profiles_chaos.py \
  tests/test_zeno_oracle_disaster_class_corpus.py \
  tests/test_zenodex_oracle_reporter_economics_replay.py \
  tests/test_zenodex_oracle_economic_security.py \
  tests/test_zenodex_oracle_economic_security_chaos.py

python3 tools/zeno_oracle_disaster_class_corpus.py --format text
pytest -q tests/integration/test_perp_engine.py -k oracle_adapter
pytest -q tests/integration/test_perp_engine_clearinghouse_2p.py -k publish_price_2p
pytest -q tests/integration/test_perp_engine_clearinghouse_3p_transfer.py -k publish_price_3p
pytest -q \
  tests/integration/test_zusd_oracle_contracts.py \
  tests/integration/test_zusd_monetary_policy_persistence.py
pytest -q tests/integration/test_api_server_dex_api.py -k "oracle_contract or price_packet or price_attestation"
