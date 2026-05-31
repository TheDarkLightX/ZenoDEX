; ESSO-IR SMT-LIB2 Export
; Model: perp_epoch_isolated_v3
; Query: Inductive check for action 'apply_insurance_claim'

(set-option :produce-models true)
(set-logic ALL)

(declare-const |breaker_active| Bool)
(declare-const |breaker_last_trigger_epoch| Int)
(declare-const |claims_paid| Int)
(declare-const |clearing_price_e8| Int)
(declare-const |clearing_price_epoch| Int)
(declare-const |clearing_price_seen| Bool)
(declare-const |collateral_quote| Int)
(declare-const |depeg_buffer_bps| Int)
(declare-const |entry_price_e8| Int)
(declare-const |epoch_phase| Int)
(declare-const |fee_income| Int)
(declare-const |fee_pool_quote| Int)
(declare-const |funding_cap_bps| Int)
(declare-const |funding_last_applied_epoch| Int)
(declare-const |funding_paid_cumulative| Int)
(declare-const |funding_rate_bps| Int)
(declare-const |index_price_e8| Int)
(declare-const |initial_insurance| Int)
(declare-const |initial_margin_bps| Int)
(declare-const |insurance_balance| Int)
(declare-const |liquidated_this_step| Bool)
(declare-const |liquidation_penalty_bps| Int)
(declare-const |maintenance_margin_bps| Int)
(declare-const |max_oracle_move_bps| Int)
(declare-const |max_oracle_staleness_epochs| Int)
(declare-const |max_position_abs| Int)
(declare-const |min_notional_for_bounty| Int)
(declare-const |now_epoch| Int)
(declare-const |oracle_last_update_epoch| Int)
(declare-const |oracle_seen| Bool)
(declare-const |position_base| Int)
(declare-const |breaker_active_post| Bool)
(declare-const |breaker_last_trigger_epoch_post| Int)
(declare-const |claims_paid_post| Int)
(declare-const |clearing_price_e8_post| Int)
(declare-const |clearing_price_epoch_post| Int)
(declare-const |clearing_price_seen_post| Bool)
(declare-const |collateral_quote_post| Int)
(declare-const |depeg_buffer_bps_post| Int)
(declare-const |entry_price_e8_post| Int)
(declare-const |epoch_phase_post| Int)
(declare-const |fee_income_post| Int)
(declare-const |fee_pool_quote_post| Int)
(declare-const |funding_cap_bps_post| Int)
(declare-const |funding_last_applied_epoch_post| Int)
(declare-const |funding_paid_cumulative_post| Int)
(declare-const |funding_rate_bps_post| Int)
(declare-const |index_price_e8_post| Int)
(declare-const |initial_insurance_post| Int)
(declare-const |initial_margin_bps_post| Int)
(declare-const |insurance_balance_post| Int)
(declare-const |liquidated_this_step_post| Bool)
(declare-const |liquidation_penalty_bps_post| Int)
(declare-const |maintenance_margin_bps_post| Int)
(declare-const |max_oracle_move_bps_post| Int)
(declare-const |max_oracle_staleness_epochs_post| Int)
(declare-const |max_position_abs_post| Int)
(declare-const |min_notional_for_bounty_post| Int)
(declare-const |now_epoch_post| Int)
(declare-const |oracle_last_update_epoch_post| Int)
(declare-const |oracle_seen_post| Bool)
(declare-const |position_base_post| Int)
(declare-const |p_claim_amount| Int)
(declare-const |p_auth_ok| Bool)

(assert (and true (and (<= 0 |breaker_last_trigger_epoch|) (<= |breaker_last_trigger_epoch| 1000000)) (and (<= 0 |claims_paid|) (<= |claims_paid| 1000000000000000)) (and (<= 0 |clearing_price_e8|) (<= |clearing_price_e8| 1000000000000)) (and (<= 0 |clearing_price_epoch|) (<= |clearing_price_epoch| 1000000)) true (and (<= 0 |collateral_quote|) (<= |collateral_quote| 1000000000000000)) (and (<= 0 |depeg_buffer_bps|) (<= |depeg_buffer_bps| 5000)) (and (<= 0 |entry_price_e8|) (<= |entry_price_e8| 1000000000000)) (and (<= 0 |epoch_phase|) (<= |epoch_phase| 2)) (and (<= 0 |fee_income|) (<= |fee_income| 1000000000000000)) (and (<= 0 |fee_pool_quote|) (<= |fee_pool_quote| 1000000000000000)) (and (<= 1 |funding_cap_bps|) (<= |funding_cap_bps| 10000)) (and (<= 0 |funding_last_applied_epoch|) (<= |funding_last_applied_epoch| 1000000)) (and (<= (- 1000000000000000) |funding_paid_cumulative|) (<= |funding_paid_cumulative| 1000000000000000)) (and (<= (- 10000) |funding_rate_bps|) (<= |funding_rate_bps| 10000)) (and (<= 0 |index_price_e8|) (<= |index_price_e8| 1000000000000)) (and (<= 0 |initial_insurance|) (<= |initial_insurance| 1000000000000000)) (and (<= 0 |initial_margin_bps|) (<= |initial_margin_bps| 10000)) (and (<= 0 |insurance_balance|) (<= |insurance_balance| 1000000000000000)) true (and (<= 0 |liquidation_penalty_bps|) (<= |liquidation_penalty_bps| 10000)) (and (<= 0 |maintenance_margin_bps|) (<= |maintenance_margin_bps| 10000)) (and (<= 0 |max_oracle_move_bps|) (<= |max_oracle_move_bps| 10000)) (and (<= 1 |max_oracle_staleness_epochs|) (<= |max_oracle_staleness_epochs| 1000000)) (and (<= 1 |max_position_abs|) (<= |max_position_abs| 1000000)) (and (<= 0 |min_notional_for_bounty|) (<= |min_notional_for_bounty| 1000000000000)) (and (<= 0 |now_epoch|) (<= |now_epoch| 1000000)) (and (<= 0 |oracle_last_update_epoch|) (<= |oracle_last_update_epoch| 1000000)) true (and (<= (- 1000000) |position_base|) (<= |position_base| 1000000)) (=> (not |breaker_active|) (= 0 |breaker_last_trigger_epoch|)) (<= |breaker_last_trigger_epoch| |now_epoch|) (<= |clearing_price_epoch| |now_epoch|) (=> (not |clearing_price_seen|) (and (= 0 |clearing_price_e8|) (= 0 |clearing_price_epoch|))) (=> (not (= 0 |position_base|)) (= |entry_price_e8| |index_price_e8|)) (=> (= 0 |position_base|) (= 0 |entry_price_e8|)) (= |fee_income| |fee_pool_quote|) (and (<= (- 0 |funding_cap_bps|) |funding_rate_bps|) (<= |funding_rate_bps| |funding_cap_bps|)) (<= |funding_last_applied_epoch| |now_epoch|) (= (- (+ |fee_income| |initial_insurance|) |claims_paid|) |insurance_balance|) (>= |insurance_balance| 0) (< |liquidation_penalty_bps| (+ |depeg_buffer_bps| |maintenance_margin_bps|)) (=> (not (= 0 |position_base|)) (>= |collateral_quote| (ite (= 10000 0) 0 (div (* (+ |depeg_buffer_bps| |maintenance_margin_bps|) (ite (= 100000000 0) 0 (div (* (ite (>= |position_base| 0) |position_base| (- 0 |position_base|)) |index_price_e8|) 100000000))) 10000)))) (and (<= (+ |depeg_buffer_bps| |maintenance_margin_bps|) |initial_margin_bps|) (<= |max_oracle_move_bps| (+ |depeg_buffer_bps| |maintenance_margin_bps|))) (<= |oracle_last_update_epoch| |now_epoch|) (=> (not |oracle_seen|) (and (= 0 |index_price_e8|) (= 0 |oracle_last_update_epoch|))) (=> (= 1 |epoch_phase|) (= |clearing_price_epoch| |now_epoch|)) (=> (= 2 |epoch_phase|) (= |now_epoch| |oracle_last_update_epoch|)) (and (<= |epoch_phase| 2) (>= |epoch_phase| 0))))  ; Pre-inv

(assert (and (<= 1 |p_claim_amount|) (<= |p_claim_amount| 1000000000000)))  ; Param domain

(assert (and (<= (+ |p_claim_amount| |claims_paid|) 1000000000000000) (<= |p_claim_amount| |insurance_balance|) (= true |p_auth_ok|) (>= (- (+ |fee_income| |initial_insurance|) (+ |p_claim_amount| |claims_paid|)) 0)))  ; Guard

(assert (= |breaker_active_post| |breaker_active|))  ; Post breaker_active
(assert (= |breaker_last_trigger_epoch_post| |breaker_last_trigger_epoch|))  ; Post breaker_last_trigger_epoch
(assert (= |claims_paid_post| (+ |p_claim_amount| |claims_paid|)))  ; Post claims_paid
(assert (= |clearing_price_e8_post| |clearing_price_e8|))  ; Post clearing_price_e8
(assert (= |clearing_price_epoch_post| |clearing_price_epoch|))  ; Post clearing_price_epoch
(assert (= |clearing_price_seen_post| |clearing_price_seen|))  ; Post clearing_price_seen
(assert (= |collateral_quote_post| |collateral_quote|))  ; Post collateral_quote
(assert (= |depeg_buffer_bps_post| |depeg_buffer_bps|))  ; Post depeg_buffer_bps
(assert (= |entry_price_e8_post| |entry_price_e8|))  ; Post entry_price_e8
(assert (= |epoch_phase_post| |epoch_phase|))  ; Post epoch_phase
(assert (= |fee_income_post| |fee_income|))  ; Post fee_income
(assert (= |fee_pool_quote_post| |fee_pool_quote|))  ; Post fee_pool_quote
(assert (= |funding_cap_bps_post| |funding_cap_bps|))  ; Post funding_cap_bps
(assert (= |funding_last_applied_epoch_post| |funding_last_applied_epoch|))  ; Post funding_last_applied_epoch
(assert (= |funding_paid_cumulative_post| |funding_paid_cumulative|))  ; Post funding_paid_cumulative
(assert (= |funding_rate_bps_post| |funding_rate_bps|))  ; Post funding_rate_bps
(assert (= |index_price_e8_post| |index_price_e8|))  ; Post index_price_e8
(assert (= |initial_insurance_post| |initial_insurance|))  ; Post initial_insurance
(assert (= |initial_margin_bps_post| |initial_margin_bps|))  ; Post initial_margin_bps
(assert (= |insurance_balance_post| (- (+ |fee_income| |initial_insurance|) (+ |p_claim_amount| |claims_paid|))))  ; Post insurance_balance
(assert (= |liquidated_this_step_post| false))  ; Post liquidated_this_step
(assert (= |liquidation_penalty_bps_post| |liquidation_penalty_bps|))  ; Post liquidation_penalty_bps
(assert (= |maintenance_margin_bps_post| |maintenance_margin_bps|))  ; Post maintenance_margin_bps
(assert (= |max_oracle_move_bps_post| |max_oracle_move_bps|))  ; Post max_oracle_move_bps
(assert (= |max_oracle_staleness_epochs_post| |max_oracle_staleness_epochs|))  ; Post max_oracle_staleness_epochs
(assert (= |max_position_abs_post| |max_position_abs|))  ; Post max_position_abs
(assert (= |min_notional_for_bounty_post| |min_notional_for_bounty|))  ; Post min_notional_for_bounty
(assert (= |now_epoch_post| |now_epoch|))  ; Post now_epoch
(assert (= |oracle_last_update_epoch_post| |oracle_last_update_epoch|))  ; Post oracle_last_update_epoch
(assert (= |oracle_seen_post| |oracle_seen|))  ; Post oracle_seen
(assert (= |position_base_post| |position_base|))  ; Post position_base

(assert (not (and true (and (<= 0 |breaker_last_trigger_epoch_post|) (<= |breaker_last_trigger_epoch_post| 1000000)) (and (<= 0 |claims_paid_post|) (<= |claims_paid_post| 1000000000000000)) (and (<= 0 |clearing_price_e8_post|) (<= |clearing_price_e8_post| 1000000000000)) (and (<= 0 |clearing_price_epoch_post|) (<= |clearing_price_epoch_post| 1000000)) true (and (<= 0 |collateral_quote_post|) (<= |collateral_quote_post| 1000000000000000)) (and (<= 0 |depeg_buffer_bps_post|) (<= |depeg_buffer_bps_post| 5000)) (and (<= 0 |entry_price_e8_post|) (<= |entry_price_e8_post| 1000000000000)) (and (<= 0 |epoch_phase_post|) (<= |epoch_phase_post| 2)) (and (<= 0 |fee_income_post|) (<= |fee_income_post| 1000000000000000)) (and (<= 0 |fee_pool_quote_post|) (<= |fee_pool_quote_post| 1000000000000000)) (and (<= 1 |funding_cap_bps_post|) (<= |funding_cap_bps_post| 10000)) (and (<= 0 |funding_last_applied_epoch_post|) (<= |funding_last_applied_epoch_post| 1000000)) (and (<= (- 1000000000000000) |funding_paid_cumulative_post|) (<= |funding_paid_cumulative_post| 1000000000000000)) (and (<= (- 10000) |funding_rate_bps_post|) (<= |funding_rate_bps_post| 10000)) (and (<= 0 |index_price_e8_post|) (<= |index_price_e8_post| 1000000000000)) (and (<= 0 |initial_insurance_post|) (<= |initial_insurance_post| 1000000000000000)) (and (<= 0 |initial_margin_bps_post|) (<= |initial_margin_bps_post| 10000)) (and (<= 0 |insurance_balance_post|) (<= |insurance_balance_post| 1000000000000000)) true (and (<= 0 |liquidation_penalty_bps_post|) (<= |liquidation_penalty_bps_post| 10000)) (and (<= 0 |maintenance_margin_bps_post|) (<= |maintenance_margin_bps_post| 10000)) (and (<= 0 |max_oracle_move_bps_post|) (<= |max_oracle_move_bps_post| 10000)) (and (<= 1 |max_oracle_staleness_epochs_post|) (<= |max_oracle_staleness_epochs_post| 1000000)) (and (<= 1 |max_position_abs_post|) (<= |max_position_abs_post| 1000000)) (and (<= 0 |min_notional_for_bounty_post|) (<= |min_notional_for_bounty_post| 1000000000000)) (and (<= 0 |now_epoch_post|) (<= |now_epoch_post| 1000000)) (and (<= 0 |oracle_last_update_epoch_post|) (<= |oracle_last_update_epoch_post| 1000000)) true (and (<= (- 1000000) |position_base_post|) (<= |position_base_post| 1000000)) (=> (not |breaker_active_post|) (= 0 |breaker_last_trigger_epoch_post|)) (<= |breaker_last_trigger_epoch_post| |now_epoch_post|) (<= |clearing_price_epoch_post| |now_epoch_post|) (=> (not |clearing_price_seen_post|) (and (= 0 |clearing_price_e8_post|) (= 0 |clearing_price_epoch_post|))) (=> (not (= 0 |position_base_post|)) (= |entry_price_e8_post| |index_price_e8_post|)) (=> (= 0 |position_base_post|) (= 0 |entry_price_e8_post|)) (= |fee_income_post| |fee_pool_quote_post|) (and (<= (- 0 |funding_cap_bps_post|) |funding_rate_bps_post|) (<= |funding_rate_bps_post| |funding_cap_bps_post|)) (<= |funding_last_applied_epoch_post| |now_epoch_post|) (= (- (+ |fee_income_post| |initial_insurance_post|) |claims_paid_post|) |insurance_balance_post|) (>= |insurance_balance_post| 0) (< |liquidation_penalty_bps_post| (+ |depeg_buffer_bps_post| |maintenance_margin_bps_post|)) (=> (not (= 0 |position_base_post|)) (>= |collateral_quote_post| (ite (= 10000 0) 0 (div (* (+ |depeg_buffer_bps_post| |maintenance_margin_bps_post|) (ite (= 100000000 0) 0 (div (* (ite (>= |position_base_post| 0) |position_base_post| (- 0 |position_base_post|)) |index_price_e8_post|) 100000000))) 10000)))) (and (<= (+ |depeg_buffer_bps_post| |maintenance_margin_bps_post|) |initial_margin_bps_post|) (<= |max_oracle_move_bps_post| (+ |depeg_buffer_bps_post| |maintenance_margin_bps_post|))) (<= |oracle_last_update_epoch_post| |now_epoch_post|) (=> (not |oracle_seen_post|) (and (= 0 |index_price_e8_post|) (= 0 |oracle_last_update_epoch_post|))) (=> (= 1 |epoch_phase_post|) (= |clearing_price_epoch_post| |now_epoch_post|)) (=> (= 2 |epoch_phase_post|) (= |now_epoch_post| |oracle_last_update_epoch_post|)) (and (<= |epoch_phase_post| 2) (>= |epoch_phase_post| 0)))))  ; NOT post-inv

(check-sat)
(get-model)
