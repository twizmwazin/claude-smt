; SMT-LIB benchmark: bv8_nested_ite_6
; Source: Generated from standardized benchmark family
; Expected: sat
; Category: standardized
(set-logic QF_BV)
(declare-const c0 (_ BitVec 8))
(declare-const c1 (_ BitVec 8))
(declare-const c2 (_ BitVec 8))
(declare-const c3 (_ BitVec 8))
(declare-const c4 (_ BitVec 8))
(declare-const c5 (_ BitVec 8))
(declare-const result (_ BitVec 8))
(assert (= result (ite (bvugt c0 (_ bv0 8)) (ite (bvugt c1 (_ bv0 8)) (ite (bvugt c2 (_ bv0 8)) (ite (bvugt c3 (_ bv0 8)) (ite (bvugt c4 (_ bv0 8)) (ite (bvugt c5 (_ bv0 8)) (_ bv127 8) (_ bv126 8)) (ite (bvugt c5 (_ bv0 8)) (_ bv125 8) (_ bv124 8))) (ite (bvugt c4 (_ bv0 8)) (ite (bvugt c5 (_ bv0 8)) (_ bv123 8) (_ bv122 8)) (ite (bvugt c5 (_ bv0 8)) (_ bv121 8) (_ bv120 8)))) (ite (bvugt c3 (_ bv0 8)) (ite (bvugt c4 (_ bv0 8)) (ite (bvugt c5 (_ bv0 8)) (_ bv119 8) (_ bv118 8)) (ite (bvugt c5 (_ bv0 8)) (_ bv117 8) (_ bv116 8))) (ite (bvugt c4 (_ bv0 8)) (ite (bvugt c5 (_ bv0 8)) (_ bv115 8) (_ bv114 8)) (ite (bvugt c5 (_ bv0 8)) (_ bv113 8) (_ bv112 8))))) (ite (bvugt c2 (_ bv0 8)) (ite (bvugt c3 (_ bv0 8)) (ite (bvugt c4 (_ bv0 8)) (ite (bvugt c5 (_ bv0 8)) (_ bv111 8) (_ bv110 8)) (ite (bvugt c5 (_ bv0 8)) (_ bv109 8) (_ bv108 8))) (ite (bvugt c4 (_ bv0 8)) (ite (bvugt c5 (_ bv0 8)) (_ bv107 8) (_ bv106 8)) (ite (bvugt c5 (_ bv0 8)) (_ bv105 8) (_ bv104 8)))) (ite (bvugt c3 (_ bv0 8)) (ite (bvugt c4 (_ bv0 8)) (ite (bvugt c5 (_ bv0 8)) (_ bv103 8) (_ bv102 8)) (ite (bvugt c5 (_ bv0 8)) (_ bv101 8) (_ bv100 8))) (ite (bvugt c4 (_ bv0 8)) (ite (bvugt c5 (_ bv0 8)) (_ bv99 8) (_ bv98 8)) (ite (bvugt c5 (_ bv0 8)) (_ bv97 8) (_ bv96 8)))))) (ite (bvugt c1 (_ bv0 8)) (ite (bvugt c2 (_ bv0 8)) (ite (bvugt c3 (_ bv0 8)) (ite (bvugt c4 (_ bv0 8)) (ite (bvugt c5 (_ bv0 8)) (_ bv95 8) (_ bv94 8)) (ite (bvugt c5 (_ bv0 8)) (_ bv93 8) (_ bv92 8))) (ite (bvugt c4 (_ bv0 8)) (ite (bvugt c5 (_ bv0 8)) (_ bv91 8) (_ bv90 8)) (ite (bvugt c5 (_ bv0 8)) (_ bv89 8) (_ bv88 8)))) (ite (bvugt c3 (_ bv0 8)) (ite (bvugt c4 (_ bv0 8)) (ite (bvugt c5 (_ bv0 8)) (_ bv87 8) (_ bv86 8)) (ite (bvugt c5 (_ bv0 8)) (_ bv85 8) (_ bv84 8))) (ite (bvugt c4 (_ bv0 8)) (ite (bvugt c5 (_ bv0 8)) (_ bv83 8) (_ bv82 8)) (ite (bvugt c5 (_ bv0 8)) (_ bv81 8) (_ bv80 8))))) (ite (bvugt c2 (_ bv0 8)) (ite (bvugt c3 (_ bv0 8)) (ite (bvugt c4 (_ bv0 8)) (ite (bvugt c5 (_ bv0 8)) (_ bv79 8) (_ bv78 8)) (ite (bvugt c5 (_ bv0 8)) (_ bv77 8) (_ bv76 8))) (ite (bvugt c4 (_ bv0 8)) (ite (bvugt c5 (_ bv0 8)) (_ bv75 8) (_ bv74 8)) (ite (bvugt c5 (_ bv0 8)) (_ bv73 8) (_ bv72 8)))) (ite (bvugt c3 (_ bv0 8)) (ite (bvugt c4 (_ bv0 8)) (ite (bvugt c5 (_ bv0 8)) (_ bv71 8) (_ bv70 8)) (ite (bvugt c5 (_ bv0 8)) (_ bv69 8) (_ bv68 8))) (ite (bvugt c4 (_ bv0 8)) (ite (bvugt c5 (_ bv0 8)) (_ bv67 8) (_ bv66 8)) (ite (bvugt c5 (_ bv0 8)) (_ bv65 8) (_ bv64 8)))))))))
(assert (not (= result (_ bv0 8))))
(check-sat)
(exit)
