; SMT-LIB benchmark: bv8_overflow
; Source: Generated from standardized benchmark family
; Expected: sat
; Category: standardized
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(declare-const sum (_ BitVec 8))
(assert (= sum (bvadd x y)))
(assert (bvsgt x (_ bv0 8)))
(assert (bvsgt y (_ bv0 8)))
(assert (bvslt sum (_ bv0 8)))
(check-sat)
(exit)
