; Complex 32-bit bitvector multiplication with multiple constraints
; Find x,y such that x*y = 0xDEADBEEF with constraints on x and y
(set-logic QF_BV)
(declare-const x (_ BitVec 32))
(declare-const y (_ BitVec 32))
(assert (= (bvmul x y) #xDEADBEEF))
(assert (bvugt x #x00000001))
(assert (bvugt y #x00000001))
(assert (bvult x y))
(check-sat)
(exit)
