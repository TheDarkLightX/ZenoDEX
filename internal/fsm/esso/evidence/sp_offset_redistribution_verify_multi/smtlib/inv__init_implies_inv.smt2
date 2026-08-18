; ESSO-IR SMT-LIB2 Export
; Model: liquity_v1_sp_offset_redistribution_bounded
; Query: Init => Inv

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

(assert (= |branch| 1))
(assert (= |collateral| 3))
(assert (= |collateral_to_redistribute| 2))
(assert (= |collateral_to_sp| 1))
(assert (= |debt| 2))
(assert (= |debt_to_offset| 1))
(assert (= |debt_to_redistribute| 1))
(assert (= |sp_deposits| 1))

(assert (not (and (and (<= 0 |branch|) (<= |branch| 2)) (and (<= 0 |collateral|) (<= |collateral| 4)) (and (<= 0 |collateral_to_redistribute|) (<= |collateral_to_redistribute| 4)) (and (<= 0 |collateral_to_sp|) (<= |collateral_to_sp| 4)) (and (<= 1 |debt|) (<= |debt| 4)) (and (<= 0 |debt_to_offset|) (<= |debt_to_offset| 4)) (and (<= 0 |debt_to_redistribute|) (<= |debt_to_redistribute| 4)) (and (<= 0 |sp_deposits|) (<= |sp_deposits| 4)) (= (ite (= 0 |sp_deposits|) 0 (ite (< |sp_deposits| |debt|) 1 2)) |branch|) (= (+ |collateral_to_redistribute| |collateral_to_sp|) |collateral|) (= (ite (= |debt| 0) 0 (div (* |collateral| |debt_to_offset|) |debt|)) |collateral_to_sp|) (= (+ |debt_to_offset| |debt_to_redistribute|) |debt|) (= (ite (<= |debt| |sp_deposits|) |debt| |sp_deposits|) |debt_to_offset|))))

(check-sat)
(get-model)
