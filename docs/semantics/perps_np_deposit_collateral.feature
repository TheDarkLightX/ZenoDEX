Feature: Perps-NP DepositCollateral consensus semantics

  The perps-NP deposit operation has two layers. The core clearinghouse updates
  account collateral and membership. The transaction envelope handles replay and
  authorization before the core runs.

  Background:
    Given the perps-NP clearing core is the live authority for MarketState updates
    And the transaction envelope is the live authority for replay and authorization

  @scenario:perps_np.deposit_collateral.core.zero_deposit_joins_account @layer:core @status:executable
  Scenario: zero deposit joins an account
    Given no account exists for sender A
    When sender A applies a core deposit for amount 0
    Then account A exists
    And account A collateral is 0
    And account A nonce is unchanged
    And net_deposited_e8 is unchanged

  @scenario:perps_np.deposit_collateral.core.deposit_does_not_consume_nonce @layer:core @status:executable
  Scenario: core deposit does not consume account nonce
    Given sender A has account nonce 7
    When sender A applies a core deposit for amount 100
    Then account A collateral increases by 100
    And account A nonce remains 7

  @scenario:perps_np.deposit_collateral.core.negative_rejects_without_mutation @layer:core @status:executable
  Scenario: negative core deposit rejects without mutation
    Given sender A has an existing account snapshot
    When sender A applies a core deposit for amount -1
    Then the deposit is rejected
    And the account snapshot is unchanged

  @scenario:perps_np.deposit_collateral.guest.modeled_envelope_claim_is_scoped @layer:guest_differential @status:executable
  Scenario: guest differential with modeled envelope cannot claim live equivalence
    Given a guest differential uses a modeled nonce or replay envelope
    When it compares guest execution to Python authority execution
    Then the strongest allowed claim is modeled_envelope_equivalent
    And P0-3b remains open until the live transaction envelope is driven

  @scenario:perps_np.deposit_collateral.envelope.duplicate_tx_rejects_before_core @layer:tx_envelope @status:open_obligation
  Scenario: duplicate transaction envelope is rejected before core execution
    Given sender A has already submitted transaction envelope E
    When sender A submits envelope E again
    Then the transaction is rejected as replay
    And the core deposit transition is not executed
    And the account snapshot is unchanged
