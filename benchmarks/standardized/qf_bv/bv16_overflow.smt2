; SMT-LIB benchmark: bv16_overflow
; Source: Generated from standardized benchmark family
; Expected: sat
; Category: standardized
(set-logic QF_BV)
(declare-const x (_ BitVec 16))
(declare-const y (_ BitVec 16))
(declare-const sum (_ BitVec 16))
(assert (= sum (bvadd x y)))
(assert (bvsgt x (_ bv0 16)))
(assert (bvsgt y (_ bv0 16)))
(assert (bvslt sum (_ bv0 16)))
(check-sat)
(exit)
