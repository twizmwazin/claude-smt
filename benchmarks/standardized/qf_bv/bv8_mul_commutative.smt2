; SMT-LIB benchmark: bv8_mul_commutative
; Source: Generated from standardized benchmark family
; Expected: unsat
; Category: standardized
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(declare-const z (_ BitVec 8))
(assert (not (= (bvmul x y) (bvmul y x))))
(check-sat)
(exit)
