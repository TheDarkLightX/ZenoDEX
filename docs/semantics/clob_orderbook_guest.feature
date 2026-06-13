Feature: CLOB orderbook guest consensus semantics

  The CLOB RISC0 guest proves the matching/book-root kernel for already-admitted
  order inputs. The deployed Stage-0 orderbook API still applies the Python
  matching kernel directly and labels results proof_pending.

  Background:
    Given the CLOB matching core is the live authority for book transitions
    And the Stage-0 orderbook API is not proof-gated

  @scenario:clob.place_limit_order.guest.claim_scoped_to_matching_core @layer:guest_differential @status:executable
  Scenario: CLOB guest claim is scoped to the matching core
    Given the CLOB guest executes the shared matching transition
    When the deployed Stage-0 API accepts a limit order
    Then the strongest guest claim is core_equivalent
    And the API response remains proof_pending until a client verifies proof material
