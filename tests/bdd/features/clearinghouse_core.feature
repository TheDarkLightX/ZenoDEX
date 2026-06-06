# ZenoDEX Front Door -- Layer 1: Clearinghouse Core (PURE)
#
# This feature is the canonical behavior of the N-party perpetuals clearinghouse
# core transition. The core is a pure function of (state, action): no nonce, no
# clock, no I/O. The live authority `src/core/perp_np_clearinghouse.py`, the
# RISC0 guest, and the P0-3 differential must each be checked against these
# scenarios at the claim level they assert. If two artifacts disagree, classify
# the behavior by layer before changing consensus semantics.
#
# Layering (the cure for the P0-3 "is the nonce part of a deposit?" confusion):
#   - Layer 1 (this file): the PURE core. deposit / withdraw / run_epoch. NO nonce.
#   - Layer 2 (tx_envelope.feature, next): the TX-layer wrapper the chain enforces
#     AROUND the core (nonce / replay / sender-binding / deadline). The nonce
#     lives THERE, not here.
#   - Layer 3 (client_acceptance.feature, next): the trustless ClientAccepts rule.
#
# Amounts/prices are written in human units; steps convert to e8 (x1e8).

Feature: Clearinghouse core collateral and epoch transitions

  Background:
    Given an initialized ZENO-PERP market at index price 1.00 with insurance seed 1000

  Scenario: A first deposit opens an account and credits collateral
    When wallet A deposits 5000 collateral
    Then wallet A has collateral 5000
    And wallet A has a flat position
    And collateral conservation holds

  Scenario: A zero-amount deposit is the canonical account-join
    # DECIDES "is deposit(0) allowed?" -> YES. deposit(0) is join_market.
    When wallet A deposits 0 collateral
    Then wallet A has an account
    And wallet A has collateral 0
    And collateral conservation holds

  Scenario: The core deposit does NOT advance an account nonce
    # DECIDES the P0-3 question: the nonce is a TX-envelope concern (Layer 2),
    # outside the pure core transition. The core Account carries a nonce field,
    # and the core deposit transition leaves it untouched.
    Given wallet A has deposited 5000 collateral
    When wallet A deposits 1000 collateral
    Then wallet A has collateral 6000
    And wallet A account nonce is 0

  Scenario: A negative deposit is rejected and is a no-op
    When wallet A deposits -1 collateral
    Then the transition is rejected
    And the market state is unchanged

  Scenario: Withdraw up to collateral succeeds
    Given wallet A has deposited 5000 collateral
    When wallet A withdraws 5000 collateral
    Then wallet A has collateral 0
    And collateral conservation holds

  Scenario: Withdraw exceeding collateral is rejected and is a no-op
    Given wallet A has deposited 5000 collateral
    When wallet A withdraws 5001 collateral
    Then the transition is rejected
    And the market state is unchanged
    And wallet A has collateral 5000

  @pending
  Scenario: A balanced two-wallet epoch conserves value and nets to zero
    # PENDING red-line: confirm the intended run_epoch inputs (clearing price,
    # funding rate, and the matched intents that produce a net-zero book) for
    # the canonical "balanced book" scenario before promoting this to green.
    Given wallet A has deposited 5000 collateral
    And wallet B has deposited 5000 collateral
    When a balanced epoch runs at clearing price 1.00 with funding rate 0
    Then net position across all wallets is 0
    And collateral conservation holds
