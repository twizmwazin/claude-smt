; SMT-LIB benchmark: bv16_shift_props
; Source: Generated from standardized benchmark family
; Expected: sat
; Category: standardized
(set-logic QF_BV)
(declare-const x (_ BitVec 16))
(declare-const s (_ BitVec 16))
(assert (= s (_ bv8 16)))
(assert (not (= (bvlshr (bvshl x s) s) x)))
(check-sat)
(exit)
