; ESSO-IR SMT-LIB2 Export
; Model: liquity_v1_sp_offset_redistribution_bounded
; Query: Inductive check for action 'partition_offset_and_redistribution'

(set-option :produce-models true)
(set-logic ALL)

(declare-const |branch| Int)
(declare-const |collateral| Int)
(declare-const |collateral_to_redistribute| Int)
(declare-const |collateral_to_sp| Int)
(declare-const |debt| Int)
(declare-const |debt_to_offset| Int)
(declare-const |debt_to_redistribute| Int)
(declare-const |sp_deposits| Int)
(declare-const |branch_post| Int)
(declare-const |collateral_post| Int)
(declare-const |collateral_to_redistribute_post| Int)
(declare-const |collateral_to_sp_post| Int)
(declare-const |debt_post| Int)
(declare-const |debt_to_offset_post| Int)
(declare-const |debt_to_redistribute_post| Int)
(declare-const |sp_deposits_post| Int)
(declare-const |p_new_debt| Int)
(declare-const |p_new_collateral| Int)
(declare-const |p_new_sp_deposits| Int)

(assert (and (and (<= 0 |branch|) (<= |branch| 2)) (and (<= 0 |collateral|) (<= |collateral| 4)) (and (<= 0 |collateral_to_redistribute|) (<= |collateral_to_redistribute| 4)) (and (<= 0 |collateral_to_sp|) (<= |collateral_to_sp| 4)) (and (<= 1 |debt|) (<= |debt| 4)) (and (<= 0 |debt_to_offset|) (<= |debt_to_offset| 4)) (and (<= 0 |debt_to_redistribute|) (<= |debt_to_redistribute| 4)) (and (<= 0 |sp_deposits|) (<= |sp_deposits| 4)) (= (ite (= 0 |sp_deposits|) 0 (ite (< |sp_deposits| |debt|) 1 2)) |branch|) (= (+ |collateral_to_redistribute| |collateral_to_sp|) |collateral|) (= (ite (= |debt| 0) 0 (div (* |collateral| |debt_to_offset|) |debt|)) |collateral_to_sp|) (= (+ |debt_to_offset| |debt_to_redistribute|) |debt|) (= (ite (<= |debt| |sp_deposits|) |debt| |sp_deposits|) |debt_to_offset|)))  ; Pre-inv

(assert (and (and (<= 1 |p_new_debt|) (<= |p_new_debt| 4)) (and (<= 0 |p_new_collateral|) (<= |p_new_collateral| 4)) (and (<= 0 |p_new_sp_deposits|) (<= |p_new_sp_deposits| 4))))  ; Param domain

(assert true)  ; Guard

(assert (= |branch_post| (ite (= 0 |p_new_sp_deposits|) 0 (ite (< |p_new_sp_deposits| |p_new_debt|) 1 2))))  ; Post branch
(assert (= |collateral_post| |p_new_collateral|))  ; Post collateral
(assert (= |collateral_to_redistribute_post| (- |p_new_collateral| (ite (= |p_new_debt| 0) 0 (div (* (ite (<= |p_new_debt| |p_new_sp_deposits|) |p_new_debt| |p_new_sp_deposits|) |p_new_collateral|) |p_new_debt|)))))  ; Post collateral_to_redistribute
(assert (= |collateral_to_sp_post| (ite (= |p_new_debt| 0) 0 (div (* (ite (<= |p_new_debt| |p_new_sp_deposits|) |p_new_debt| |p_new_sp_deposits|) |p_new_collateral|) |p_new_debt|))))  ; Post collateral_to_sp
(assert (= |debt_post| |p_new_debt|))  ; Post debt
(assert (= |debt_to_offset_post| (ite (<= |p_new_debt| |p_new_sp_deposits|) |p_new_debt| |p_new_sp_deposits|)))  ; Post debt_to_offset
(assert (= |debt_to_redistribute_post| (- |p_new_debt| (ite (<= |p_new_debt| |p_new_sp_deposits|) |p_new_debt| |p_new_sp_deposits|))))  ; Post debt_to_redistribute
(assert (= |sp_deposits_post| |p_new_sp_deposits|))  ; Post sp_deposits

(assert (not (and (and (<= 0 |branch_post|) (<= |branch_post| 2)) (and (<= 0 |collateral_post|) (<= |collateral_post| 4)) (and (<= 0 |collateral_to_redistribute_post|) (<= |collateral_to_redistribute_post| 4)) (and (<= 0 |collateral_to_sp_post|) (<= |collateral_to_sp_post| 4)) (and (<= 1 |debt_post|) (<= |debt_post| 4)) (and (<= 0 |debt_to_offset_post|) (<= |debt_to_offset_post| 4)) (and (<= 0 |debt_to_redistribute_post|) (<= |debt_to_redistribute_post| 4)) (and (<= 0 |sp_deposits_post|) (<= |sp_deposits_post| 4)) (= (ite (= 0 |sp_deposits_post|) 0 (ite (< |sp_deposits_post| |debt_post|) 1 2)) |branch_post|) (= (+ |collateral_to_redistribute_post| |collateral_to_sp_post|) |collateral_post|) (= (ite (= |debt_post| 0) 0 (div (* |collateral_post| |debt_to_offset_post|) |debt_post|)) |collateral_to_sp_post|) (= (+ |debt_to_offset_post| |debt_to_redistribute_post|) |debt_post|) (= (ite (<= |debt_post| |sp_deposits_post|) |debt_post| |sp_deposits_post|) |debt_to_offset_post|))))  ; NOT post-inv

(check-sat)
(get-model)
