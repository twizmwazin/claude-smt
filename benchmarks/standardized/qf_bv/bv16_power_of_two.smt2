; SMT-LIB benchmark: bv16_power_of_two
; Source: Generated from standardized benchmark family
; Expected: sat
; Category: standardized
(set-logic QF_BV)
(declare-const x (_ BitVec 16))
(assert (not (= x (_ bv0 16))))
(assert (= (bvand x (bvsub x (_ bv1 16))) (_ bv0 16)))
(assert (bvugt x (_ bv128 16)))
(check-sat)
(exit)
