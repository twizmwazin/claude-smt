; SMT-LIB benchmark: bv32_ripple_carry
; Source: Generated from standardized benchmark family
; Expected: sat
; Category: standardized
(set-logic QF_BV)
(declare-const x (_ BitVec 32))
(declare-const y (_ BitVec 32))
(declare-const result (_ BitVec 32))
(assert (= result (bvadd x y)))
(assert (= (bvadd result x) y))
(check-sat)
(exit)
