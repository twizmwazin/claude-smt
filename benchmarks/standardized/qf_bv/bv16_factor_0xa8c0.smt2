; SMT-LIB benchmark: bv16_factor_0xa8c0
; Source: Generated from standardized benchmark family
; Expected: sat
; Category: standardized
(set-logic QF_BV)
(declare-const x (_ BitVec 16))
(declare-const y (_ BitVec 16))
(assert (= (bvmul x y) #xa8c0))
(assert (not (= x (_ bv0 16))))
(assert (not (= y (_ bv0 16))))
(assert (not (= x (_ bv1 16))))
(assert (not (= y (_ bv1 16))))
(check-sat)
(exit)
