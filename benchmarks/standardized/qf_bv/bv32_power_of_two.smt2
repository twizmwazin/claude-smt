; SMT-LIB benchmark: bv32_power_of_two
; Source: Generated from standardized benchmark family
; Expected: sat
; Category: standardized
(set-logic QF_BV)
(declare-const x (_ BitVec 32))
(assert (not (= x (_ bv0 32))))
(assert (= (bvand x (bvsub x (_ bv1 32))) (_ bv0 32)))
(assert (bvugt x (_ bv128 32)))
(check-sat)
(exit)
