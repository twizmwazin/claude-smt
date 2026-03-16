; Pigeonhole principle: 5 pigeons into 4 holes (UNSAT)
; This is a classic hard problem for CDCL solvers
(set-logic QF_UF)
; Pigeon i in hole j: p_i_j
(declare-const p0_0 Bool) (declare-const p0_1 Bool) (declare-const p0_2 Bool) (declare-const p0_3 Bool)
(declare-const p1_0 Bool) (declare-const p1_1 Bool) (declare-const p1_2 Bool) (declare-const p1_3 Bool)
(declare-const p2_0 Bool) (declare-const p2_1 Bool) (declare-const p2_2 Bool) (declare-const p2_3 Bool)
(declare-const p3_0 Bool) (declare-const p3_1 Bool) (declare-const p3_2 Bool) (declare-const p3_3 Bool)
(declare-const p4_0 Bool) (declare-const p4_1 Bool) (declare-const p4_2 Bool) (declare-const p4_3 Bool)

; Each pigeon in at least one hole
(assert (or p0_0 p0_1 p0_2 p0_3))
(assert (or p1_0 p1_1 p1_2 p1_3))
(assert (or p2_0 p2_1 p2_2 p2_3))
(assert (or p3_0 p3_1 p3_2 p3_3))
(assert (or p4_0 p4_1 p4_2 p4_3))

; No two pigeons in same hole
; Hole 0
(assert (not (and p0_0 p1_0))) (assert (not (and p0_0 p2_0))) (assert (not (and p0_0 p3_0))) (assert (not (and p0_0 p4_0)))
(assert (not (and p1_0 p2_0))) (assert (not (and p1_0 p3_0))) (assert (not (and p1_0 p4_0)))
(assert (not (and p2_0 p3_0))) (assert (not (and p2_0 p4_0)))
(assert (not (and p3_0 p4_0)))
; Hole 1
(assert (not (and p0_1 p1_1))) (assert (not (and p0_1 p2_1))) (assert (not (and p0_1 p3_1))) (assert (not (and p0_1 p4_1)))
(assert (not (and p1_1 p2_1))) (assert (not (and p1_1 p3_1))) (assert (not (and p1_1 p4_1)))
(assert (not (and p2_1 p3_1))) (assert (not (and p2_1 p4_1)))
(assert (not (and p3_1 p4_1)))
; Hole 2
(assert (not (and p0_2 p1_2))) (assert (not (and p0_2 p2_2))) (assert (not (and p0_2 p3_2))) (assert (not (and p0_2 p4_2)))
(assert (not (and p1_2 p2_2))) (assert (not (and p1_2 p3_2))) (assert (not (and p1_2 p4_2)))
(assert (not (and p2_2 p3_2))) (assert (not (and p2_2 p4_2)))
(assert (not (and p3_2 p4_2)))
; Hole 3
(assert (not (and p0_3 p1_3))) (assert (not (and p0_3 p2_3))) (assert (not (and p0_3 p3_3))) (assert (not (and p0_3 p4_3)))
(assert (not (and p1_3 p2_3))) (assert (not (and p1_3 p3_3))) (assert (not (and p1_3 p4_3)))
(assert (not (and p2_3 p3_3))) (assert (not (and p2_3 p4_3)))
(assert (not (and p3_3 p4_3)))

(check-sat)
(exit)
