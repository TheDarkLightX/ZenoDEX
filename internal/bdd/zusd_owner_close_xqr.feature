@zusd @owner_close @formal @unmounted
Feature: zUSD owner-close exact E18/E8 quotient and residue projection
  The pure F25 kernel returns only a candidate or typed rejection. F15 owns
  composite admission and F16 alone owns committed state and adapter effects.

  Background:
    Given internal collateral uses E18 atoms
    And physical custody uses E8 atoms
    And the exact conversion factor K is 10000000000

  @CE159
  Scenario: exactly divisible close has no owner residue
    Given closed collateral x equals K times positive q
    When the pure owner-close projection runs
    Then physical quotient is q
    And exact residue is zero
    And owner claim is unchanged
    And the candidate requests one positive q-unit physical transfer

  @CE159
  Scenario: quotient transfer and claim residue recompose exactly
    Given closed collateral x equals K times q plus r
    And zero is less than r and r is less than K
    When the pure owner-close projection runs
    Then physical quotient is q
    And exact owner claim credit is r
    And x equals K times q plus r

  @CE159
  Scenario: sub-E8 collateral forbids an adapter transfer
    Given zero is less than closed collateral x and x is less than K
    When the pure owner-close projection runs
    Then physical quotient is zero
    And exact residue equals x
    And the physical directive is NoPhysicalTransfer
    And physical custody and owner external balance are unchanged

  @CE159
  Scenario: independent successor arithmetic failures survive together
    Given an admitted Balanced or SurplusQuarantined custody state
    And the shadow debit would underflow
    And both custody debits would underflow
    And owner external credit would overflow
    And owner claim credit would overflow
    When the pure owner-close projection runs
    Then every failure is returned once in canonical order
    And no candidate is produced

  @CE159
  Scenario: deficit-frozen custody blocks successor arithmetic
    Given custody mode is DeficitFrozen
    When the pure owner-close projection runs
    Then it rejects with DeficitFrozen only
    And no candidate or physical directive is produced

  @CE157
  Scenario: an F25 candidate is not a commit receipt
    Given a valid owner-close projection candidate
    When committed authority is requested from the candidate
    Then the type exposes no committed post root or commit version
    And is_commit_receipt is false
