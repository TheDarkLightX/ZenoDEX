(set-logic QF_NIA)

; Mathematical integer model for the admitted U256 domain.
; The production Rust carrier is BigUint plus an explicit 0 <= amount <= U256_MAX
; admission check. Quotient and remainder are represented by their Euclidean
; equations, so every product and division below is exact mathematical integer
; arithmetic rather than a solver's machine-width approximation.

(define-fun D () Int 10000)
(define-fun U256_MAX () Int
  115792089237316195423570985008687907853269984665640564039457584007913129639935)

; Q1: q*w cannot exceed the admitted U256 amount width.
(declare-fun amount_qw () Int)
(declare-fun quotient_qw () Int)
(declare-fun residual_qw () Int)
(declare-fun weight_qw () Int)
(push)
(assert (and (>= amount_qw 0) (<= amount_qw U256_MAX)))
(assert (>= quotient_qw 0))
(assert (and (>= residual_qw 0) (< residual_qw D)))
(assert (and (>= weight_qw 0) (<= weight_qw D)))
(assert (= amount_qw (+ (* D quotient_qw) residual_qw)))
(assert (> (* quotient_qw weight_qw) U256_MAX))
(echo "B08_Q1_QW_U256_BOUND")
(check-sat)
(pop)

; Q2: every residual product is strictly below D^2.
(declare-fun residual_rw () Int)
(declare-fun weight_rw () Int)
(push)
(assert (and (>= residual_rw 0) (< residual_rw D)))
(assert (and (>= weight_rw 0) (<= weight_rw D)))
(assert (>= (* residual_rw weight_rw) (* D D)))
(echo "B08_Q2_RESIDUAL_PRODUCT_BOUND")
(check-sat)
(pop)

; Q3: Euclidean base is bounded by the original amount.
(declare-fun amount_base () Int)
(declare-fun quotient_base () Int)
(declare-fun residual_base () Int)
(declare-fun weight_base () Int)
(define-fun base_base () Int
  (+ (* quotient_base weight_base) (div (* residual_base weight_base) D)))
(push)
(assert (and (>= amount_base 0) (<= amount_base U256_MAX)))
(assert (>= quotient_base 0))
(assert (and (>= residual_base 0) (< residual_base D)))
(assert (and (>= weight_base 0) (<= weight_base D)))
(assert (= amount_base (+ (* D quotient_base) residual_base)))
(assert (> base_base amount_base))
(echo "B08_Q3_BASE_BOUND")
(check-sat)
(pop)

; Q4: valid three-role bonus selection preserves amount-wise bounds.
; The shared quotient/remainder variables make the common input relation
; explicit. The policy weights remain arbitrary nonnegative integers summing D.
(declare-fun amount_alloc () Int)
(declare-fun quotient_alloc () Int)
(declare-fun residual_alloc () Int)
(declare-fun weight_alloc_0 () Int)
(declare-fun weight_alloc_1 () Int)
(declare-fun weight_alloc_2 () Int)
(declare-fun bonus_alloc_0 () Int)
(declare-fun bonus_alloc_1 () Int)
(declare-fun bonus_alloc_2 () Int)
(define-fun product_alloc_0 () Int (* residual_alloc weight_alloc_0))
(define-fun product_alloc_1 () Int (* residual_alloc weight_alloc_1))
(define-fun product_alloc_2 () Int (* residual_alloc weight_alloc_2))
(define-fun fraction_alloc_0 () Int (mod product_alloc_0 D))
(define-fun fraction_alloc_1 () Int (mod product_alloc_1 D))
(define-fun fraction_alloc_2 () Int (mod product_alloc_2 D))
(define-fun base_alloc_0 () Int
  (+ (* quotient_alloc weight_alloc_0) (div product_alloc_0 D)))
(define-fun base_alloc_1 () Int
  (+ (* quotient_alloc weight_alloc_1) (div product_alloc_1 D)))
(define-fun base_alloc_2 () Int
  (+ (* quotient_alloc weight_alloc_2) (div product_alloc_2 D)))
(define-fun fraction_sum_alloc () Int
  (+ fraction_alloc_0 fraction_alloc_1 fraction_alloc_2))
(define-fun seat_count_alloc () Int (div fraction_sum_alloc D))
(define-fun bonus_sum_alloc () Int
  (+ bonus_alloc_0 bonus_alloc_1 bonus_alloc_2))
(define-fun allocation_0 () Int (+ base_alloc_0 bonus_alloc_0))
(define-fun allocation_1 () Int (+ base_alloc_1 bonus_alloc_1))
(define-fun allocation_2 () Int (+ base_alloc_2 bonus_alloc_2))
(push)
(assert (and (>= amount_alloc 0) (<= amount_alloc U256_MAX)))
(assert (>= quotient_alloc 0))
(assert (and (>= residual_alloc 0) (< residual_alloc D)))
(assert (= amount_alloc (+ (* D quotient_alloc) residual_alloc)))
(assert (and (>= weight_alloc_0 0) (<= weight_alloc_0 D)))
(assert (and (>= weight_alloc_1 0) (<= weight_alloc_1 D)))
(assert (and (>= weight_alloc_2 0) (<= weight_alloc_2 D)))
(assert (= (+ weight_alloc_0 weight_alloc_1 weight_alloc_2) D))
(assert (and (>= bonus_alloc_0 0) (<= bonus_alloc_0 1)))
(assert (and (>= bonus_alloc_1 0) (<= bonus_alloc_1 1)))
(assert (and (>= bonus_alloc_2 0) (<= bonus_alloc_2 1)))
(assert (or (= bonus_alloc_0 0) (> fraction_alloc_0 0)))
(assert (or (= bonus_alloc_1 0) (> fraction_alloc_1 0)))
(assert (or (= bonus_alloc_2 0) (> fraction_alloc_2 0)))
(assert (= (mod fraction_sum_alloc D) 0))
(assert (= bonus_sum_alloc seat_count_alloc))
(assert (or
  (> allocation_0 amount_alloc)
  (> allocation_1 amount_alloc)
  (> allocation_2 amount_alloc)))
(echo "B08_Q4_ALLOCATION_BOUND")
(check-sat)
(pop)

; Q5: deficit + fraction is inside the exact signed selector interval.
(declare-fun deficit_score () Int)
(declare-fun fraction_score () Int)
(define-fun score () Int (+ deficit_score fraction_score))
(push)
(assert (and (> deficit_score (- D)) (< deficit_score D)))
(assert (and (>= fraction_score 0) (< fraction_score D)))
(assert (or (< score (- D)) (>= score (* 2 D))))
(echo "B08_Q5_SCORE_BOUND")
(check-sat)
(pop)
