; SMT-LIB benchmark: bv32_factor_0xdeadbeef
; Source: Generated from standardized benchmark family
; Expected: sat
; Category: standardized
(set-logic QF_BV)
(declare-const x (_ BitVec 32))
(declare-const y (_ BitVec 32))
(assert (= (bvmul x y) #xdeadbeef))
(assert (not (= x (_ bv0 32))))
(assert (not (= y (_ bv0 32))))
(assert (not (= x (_ bv1 32))))
(assert (not (= y (_ bv1 32))))
(check-sat)
(exit)
