; SMT-LIB benchmark: bv16_mul_commutative
; Source: Generated from standardized benchmark family
; Expected: unsat
; Category: standardized
(set-logic QF_BV)
(declare-const x (_ BitVec 16))
(declare-const y (_ BitVec 16))
(declare-const z (_ BitVec 16))
(assert (not (= (bvmul x y) (bvmul y x))))
(check-sat)
(exit)
