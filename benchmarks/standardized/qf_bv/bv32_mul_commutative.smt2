; SMT-LIB benchmark: bv32_mul_commutative
; Source: Generated from standardized benchmark family
; Expected: unsat
; Category: standardized
(set-logic QF_BV)
(declare-const x (_ BitVec 32))
(declare-const y (_ BitVec 32))
(declare-const z (_ BitVec 32))
(assert (not (= (bvmul x y) (bvmul y x))))
(check-sat)
(exit)
