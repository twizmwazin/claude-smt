; 8-bit puzzle: find 4 variables satisfying a system of constraints
; This creates a moderately hard combinatorial problem
(set-logic QF_BV)
(declare-const w (_ BitVec 8))
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(declare-const z (_ BitVec 8))

; All different
(assert (distinct (bvand w x) (bvand y z)))
(assert (distinct w x))
(assert (distinct w y))
(assert (distinct w z))
(assert (distinct x y))
(assert (distinct x z))
(assert (distinct y z))

; Arithmetic constraints
(assert (= (bvadd w x) (bvadd y z)))
(assert (= (bvxor w y) (bvxor x z)))
(assert (= (bvor w x) #xFF))
(assert (= (bvand y z) #x00))
(assert (bvugt w #x0F))
(assert (bvugt x #x0F))

(check-sat)
(exit)
