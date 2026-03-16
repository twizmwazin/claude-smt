; SMT-LIB benchmark: bv16_div_property
; Source: Generated from standardized benchmark family
; Expected: unsat
; Category: standardized
(set-logic QF_BV)
(declare-const x (_ BitVec 16))
(declare-const y (_ BitVec 16))
(assert (not (= y (_ bv0 16))))
(assert (not (= (bvadd (bvmul (bvudiv x y) y) (bvurem x y)) x)))
(check-sat)
(exit)
