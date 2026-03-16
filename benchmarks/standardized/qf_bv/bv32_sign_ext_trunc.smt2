; SMT-LIB benchmark: bv32_sign_ext_trunc
; Source: Generated from standardized benchmark family
; Expected: unsat
; Category: standardized
(set-logic QF_BV)
(declare-const x (_ BitVec 32))
(assert (not (= ((_ extract 31 0) ((_ sign_extend 32) x)) x)))
(check-sat)
(exit)
