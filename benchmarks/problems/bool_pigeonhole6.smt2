; Pigeonhole principle: 6 pigeons into 5 holes (UNSAT)
(set-logic QF_UF)
(declare-const p0_0 Bool) (declare-const p0_1 Bool) (declare-const p0_2 Bool) (declare-const p0_3 Bool) (declare-const p0_4 Bool)
(declare-const p1_0 Bool) (declare-const p1_1 Bool) (declare-const p1_2 Bool) (declare-const p1_3 Bool) (declare-const p1_4 Bool)
(declare-const p2_0 Bool) (declare-const p2_1 Bool) (declare-const p2_2 Bool) (declare-const p2_3 Bool) (declare-const p2_4 Bool)
(declare-const p3_0 Bool) (declare-const p3_1 Bool) (declare-const p3_2 Bool) (declare-const p3_3 Bool) (declare-const p3_4 Bool)
(declare-const p4_0 Bool) (declare-const p4_1 Bool) (declare-const p4_2 Bool) (declare-const p4_3 Bool) (declare-const p4_4 Bool)
(declare-const p5_0 Bool) (declare-const p5_1 Bool) (declare-const p5_2 Bool) (declare-const p5_3 Bool) (declare-const p5_4 Bool)

; Each pigeon in at least one hole
(assert (or p0_0 p0_1 p0_2 p0_3 p0_4))
(assert (or p1_0 p1_1 p1_2 p1_3 p1_4))
(assert (or p2_0 p2_1 p2_2 p2_3 p2_4))
(assert (or p3_0 p3_1 p3_2 p3_3 p3_4))
(assert (or p4_0 p4_1 p4_2 p4_3 p4_4))
(assert (or p5_0 p5_1 p5_2 p5_3 p5_4))

; No two pigeons in same hole
; Hole 0
(assert (not (and p0_0 p1_0))) (assert (not (and p0_0 p2_0))) (assert (not (and p0_0 p3_0))) (assert (not (and p0_0 p4_0))) (assert (not (and p0_0 p5_0)))
(assert (not (and p1_0 p2_0))) (assert (not (and p1_0 p3_0))) (assert (not (and p1_0 p4_0))) (assert (not (and p1_0 p5_0)))
(assert (not (and p2_0 p3_0))) (assert (not (and p2_0 p4_0))) (assert (not (and p2_0 p5_0)))
(assert (not (and p3_0 p4_0))) (assert (not (and p3_0 p5_0)))
(assert (not (and p4_0 p5_0)))
; Hole 1
(assert (not (and p0_1 p1_1))) (assert (not (and p0_1 p2_1))) (assert (not (and p0_1 p3_1))) (assert (not (and p0_1 p4_1))) (assert (not (and p0_1 p5_1)))
(assert (not (and p1_1 p2_1))) (assert (not (and p1_1 p3_1))) (assert (not (and p1_1 p4_1))) (assert (not (and p1_1 p5_1)))
(assert (not (and p2_1 p3_1))) (assert (not (and p2_1 p4_1))) (assert (not (and p2_1 p5_1)))
(assert (not (and p3_1 p4_1))) (assert (not (and p3_1 p5_1)))
(assert (not (and p4_1 p5_1)))
; Hole 2
(assert (not (and p0_2 p1_2))) (assert (not (and p0_2 p2_2))) (assert (not (and p0_2 p3_2))) (assert (not (and p0_2 p4_2))) (assert (not (and p0_2 p5_2)))
(assert (not (and p1_2 p2_2))) (assert (not (and p1_2 p3_2))) (assert (not (and p1_2 p4_2))) (assert (not (and p1_2 p5_2)))
(assert (not (and p2_2 p3_2))) (assert (not (and p2_2 p4_2))) (assert (not (and p2_2 p5_2)))
(assert (not (and p3_2 p4_2))) (assert (not (and p3_2 p5_2)))
(assert (not (and p4_2 p5_2)))
; Hole 3
(assert (not (and p0_3 p1_3))) (assert (not (and p0_3 p2_3))) (assert (not (and p0_3 p3_3))) (assert (not (and p0_3 p4_3))) (assert (not (and p0_3 p5_3)))
(assert (not (and p1_3 p2_3))) (assert (not (and p1_3 p3_3))) (assert (not (and p1_3 p4_3))) (assert (not (and p1_3 p5_3)))
(assert (not (and p2_3 p3_3))) (assert (not (and p2_3 p4_3))) (assert (not (and p2_3 p5_3)))
(assert (not (and p3_3 p4_3))) (assert (not (and p3_3 p5_3)))
(assert (not (and p4_3 p5_3)))
; Hole 4
(assert (not (and p0_4 p1_4))) (assert (not (and p0_4 p2_4))) (assert (not (and p0_4 p3_4))) (assert (not (and p0_4 p4_4))) (assert (not (and p0_4 p5_4)))
(assert (not (and p1_4 p2_4))) (assert (not (and p1_4 p3_4))) (assert (not (and p1_4 p4_4))) (assert (not (and p1_4 p5_4)))
(assert (not (and p2_4 p3_4))) (assert (not (and p2_4 p4_4))) (assert (not (and p2_4 p5_4)))
(assert (not (and p3_4 p4_4))) (assert (not (and p3_4 p5_4)))
(assert (not (and p4_4 p5_4)))

(check-sat)
(exit)
