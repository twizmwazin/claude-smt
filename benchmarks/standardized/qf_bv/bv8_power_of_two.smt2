; SMT-LIB benchmark: bv8_power_of_two
; Source: Generated from standardized benchmark family
; Expected: sat
; Category: standardized
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (not (= x (_ bv0 8))))
(assert (= (bvand x (bvsub x (_ bv1 8))) (_ bv0 8)))
(check-sat)
(exit)
