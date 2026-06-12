# Covert-Channel Assurance Scope

This note records the current covert-channel assurance boundary for ZenoDEX
runtime work. It is a regression target for tests, not a complete
noninterference theorem.

## Threat Model

A covert channel is in scope when private or authority-adjacent data can affect
one of these public observations:

- an accepted/rejected authority decision;
- an authority state root, receipt hash, or replay result;
- a public trace, metric, log, reason code, or telemetry payload.

The attacker can choose low-entropy private fields in fixtures, such as request
IDs, strategy labels, sender-like values, and confidential measurements, then
observe public outputs. The tests use those low-entropy sentinels because they
catch accidental echoing better than random secrets.

## Current Rules

- Core authority kernels must be deterministic functions of explicit inputs.
  Selected state and runtime authority kernels are checked for common side-input
  imports and calls such as wall clock, randomness, environment reads, network,
  subprocess, logging, and print output.
- Trace capture is observational. It must run after the authority decision and
  must not feed back into admission decisions or state roots.
- Public traces should contain stable surface names, accept/reject decisions,
  low-cardinality reason codes, state roots where appropriate, and domain
  separated digests for public lanes.
- Private lanes should avoid raw request IDs, measurements, signatures,
  payloads, operations, and strategy labels in public trace keys or values. A
  digest of a low-entropy private value can still leak by dictionary attack, so
  private-lane public traces should prefer reason classes over input digests.
- Advisory or model telemetry may rank candidates, explain failures, and guide
  test generation. It must not authorize settlement, change replay state, or
  become part of an authoritative state root.

## Regression Gates

`tests/runtime/test_covert_channel_assurance.py` currently checks:

- `test_authority_kernels_do_not_depend_on_common_side_inputs`: AST gate over
  selected state and runtime authority kernels.
- `test_trace_capture_does_not_change_replay_decisions_or_state_root`: replay
  guard decisions and final state root are identical with and without trace
  capture.
- `test_confidential_receipt_reason_code_does_not_echo_private_request_or_measurement`:
  confidential-extension public reason codes and trace events do not echo raw
  private request IDs, measurements, or receipt hashes from the fixture.

These gates complement the existing signed Tau transaction payload redaction
regression, which prevents replay-capable BLS signatures from appearing in
default wallet API responses.

## Across ZenoDEX

- `src/core` and `src/state`: highest assurance target. Deterministic kernels
  and state commitments should stay free of side inputs unless a file documents
  a non-authority role.
- `src/runtime`: bridges to Rust shadows and authority selection. It may use
  subprocesses and environment configuration, so it needs parity and
  fail-closed disagreement tests instead of a blanket no-side-input rule.
- `src/integration`: APIs, live clients, and deployment adapters necessarily use
  environment, time, network, and access logs. Their assurance target is
  redaction, bounded payload shape, low-cardinality public errors, and no path
  from telemetry into authority decisions.
- advisory agents and energy/ranking code: telemetry is useful for coverage,
  debugging, and witness triage. The verifier and replay checks remain the
  authority boundary.

## Limits

These tests do not prove constant time behavior, microarchitectural isolation,
traffic-shape privacy, output-size privacy, or host-level log isolation. They
also do not cover every integration telemetry payload. New public telemetry
fields should be added with a replay-equivalence test, a redaction/sentinel
test, and an explicit statement of whether any digest is safe for low-entropy
private inputs.
