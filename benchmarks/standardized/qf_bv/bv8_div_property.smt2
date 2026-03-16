; SMT-LIB benchmark: bv8_div_property
; Source: Generated from standardized benchmark family
; Expected: unsat
; Category: standardized
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(assert (not (= y (_ bv0 8))))
(assert (not (= (bvadd (bvmul (bvudiv x y) y) (bvurem x y)) x)))
(check-sat)
(exit)
