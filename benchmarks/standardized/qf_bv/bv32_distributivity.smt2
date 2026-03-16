; SMT-LIB benchmark: bv32_distributivity
; Source: Generated from standardized benchmark family
; Expected: unsat
; Category: standardized
(set-logic QF_BV)
(declare-const x (_ BitVec 32))
(declare-const y (_ BitVec 32))
(declare-const z (_ BitVec 32))
(assert (not (= (bvand x (bvxor y z)) (bvxor (bvand x y) (bvand x z)))))
(check-sat)
(exit)
