; SMT-LIB benchmark: bv8_factor_0x48
; Source: Generated from standardized benchmark family
; Expected: sat
; Category: standardized
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(assert (= (bvmul x y) #x48))
(assert (not (= x (_ bv0 8))))
(assert (not (= y (_ bv0 8))))
(assert (not (= x (_ bv1 8))))
(assert (not (= y (_ bv1 8))))
(check-sat)
(exit)
