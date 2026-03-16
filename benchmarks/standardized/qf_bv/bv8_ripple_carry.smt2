; SMT-LIB benchmark: bv8_ripple_carry
; Source: Generated from standardized benchmark family
; Expected: sat
; Category: standardized
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(declare-const result (_ BitVec 8))
(assert (= result (bvadd x y)))
(assert (= (bvadd result x) y))
(check-sat)
(exit)
