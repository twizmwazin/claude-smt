; SMT-LIB benchmark: bv32_overflow
; Source: Generated from standardized benchmark family
; Expected: sat
; Category: standardized
(set-logic QF_BV)
(declare-const x (_ BitVec 32))
(declare-const y (_ BitVec 32))
(declare-const sum (_ BitVec 32))
(assert (= sum (bvadd x y)))
(assert (bvsgt x (_ bv0 32)))
(assert (bvsgt y (_ bv0 32)))
(assert (bvslt sum (_ bv0 32)))
(check-sat)
(exit)
