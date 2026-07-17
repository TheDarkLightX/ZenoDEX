@normative @zusd @rust @risc0 @formal @security @binding
Feature: zUSD RISC0 minimum-profile proof admission
  A zUSD receipt has minimum-profile authority only when the guest binds the
  exact imported scoped supply, the pinned collateral rule, and a mandatory
  canonical prestate commitment before evaluating the transition.

  @ZUSD-RUST-001 @regression
  Scenario: Imported scoped balances equal imported scoped debt
    Given a version 1 zUSD snapshot with checked unique vault and balance keys
    And the checked sum of vault debt equals total_debt_zusd_e8
    When the checked sum of zUSD balances differs from total_debt_zusd_e8
    Then proof admission rejects with BalanceSupplyMismatch
    And no transition journal is produced

  @ZUSD-V1-RISC0-BASELINE-MCR-024 @regression
  Scenario Outline: The minimum-profile guest admits only the exact Liquity V1 MCR
    Given a DepositMint operation carries MCR <mcr_bps> basis points
    When minimum-profile proof admission evaluates the operation
    Then the result is <result>
    And rejection occurs before transition evaluation or journal construction

    Examples:
      | mcr_bps | result      |
      | 11000   | Admit       |
      | 10001   | McrMismatch |
      | 10999   | McrMismatch |
      | 11001   | McrMismatch |
      | 15000   | McrMismatch |

  @ZUSD-V1-RISC0-PRESTATE-PRESENCE-026 @regression
  Scenario: Optional prestate commitment cannot authorize a minimum-profile receipt
    Given a zUSD transition input sets pre_app_hash_present to false
    When minimum-profile proof admission evaluates the input
    Then it rejects with MissingPreAppHash
    And no transition journal is produced
