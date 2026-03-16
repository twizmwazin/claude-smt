; SMT-LIB benchmark: bv32_shift_props
; Source: Generated from standardized benchmark family
; Expected: sat
; Category: standardized
(set-logic QF_BV)
(declare-const x (_ BitVec 32))
(declare-const s (_ BitVec 32))
(assert (= s (_ bv16 32)))
(assert (not (= (bvlshr (bvshl x s) s) x)))
(check-sat)
(exit)
