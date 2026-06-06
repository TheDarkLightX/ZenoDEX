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

  @scenario:perps_np.deposit_collateral.guest.claim_scoped_to_live_replay_authority @layer:guest_differential @status:executable
  Scenario: guest differential binds the replay envelope to the live replay authority
    Given the guest differential delegates the nonce decision to replay_guard.admit
    When it compares guest execution to Python authority execution
    Then the strongest allowed claim is live_replay_authority_equivalent
    And the claim is scoped to the strict-sequential replay authority, not the deployed node

  @scenario:perps_np.deposit_collateral.envelope.duplicate_tx_rejects_before_core @layer:tx_envelope @status:executable
  Scenario: duplicate transaction envelope is rejected before core execution
    Given the live replay authority replay_guard.admit has accepted nonce N for sender A
    When sender A submits nonce N again (or a gap nonce)
    Then the live replay authority rejects it before the core deposit runs
    And the strict-sequential policy matches the guest and the chain tx_sequence layer
