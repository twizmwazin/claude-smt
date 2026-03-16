; SMT-LIB benchmark: bv64_demorgan
; Source: Generated from standardized benchmark family
; Expected: unsat
; Category: standardized
(set-logic QF_BV)
(declare-const x (_ BitVec 64))
(declare-const y (_ BitVec 64))
(assert (not (= (bvnot (bvand x y)) (bvor (bvnot x) (bvnot y)))))
(check-sat)
(exit)
